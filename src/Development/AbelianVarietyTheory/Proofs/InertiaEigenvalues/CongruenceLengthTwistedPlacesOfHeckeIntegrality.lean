module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumLocalCongruenceLengthEqRationalLengthStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypeSpaceProjectionToPointEigenspaces
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftHasPointAtLocalisationSamePlace
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassSumEqConstMulPetersson
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypeOrthOfAvTied

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodPartProjectorSpectralAtEveryLocalisation
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EveryHeckeRowGoodAtGoodPointLocalisation
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftGoodRowPointGood
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AtMOfParamRec
noncomputable section

namespace GlobalTheory.LiftLeaf

open GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem atMOfParam_rec {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
    (i : N.Loc) : AtMOfParam N A i := by
  intro x _ Sig hX σ hW
  obtain ⟨P, hP, hB⟩ := hX
  refine ⟨Sig, hW, x, fun w hw => ⟨heckePol N i x w, ?_, rfl⟩⟩
  rw [hB.2.2.2.1 w hw.1]
  exact A.pt_loc i P x hP w hw

theorem atMOfParam (D : D7) (i : D.nd.Loc) : AtMOfParam D.nd D.naut i :=
  atMOfParam_rec D.nd D.naut i

end GlobalTheory.LiftLeaf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LabCompat
open GlobalTheory.LiftLeaf GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.LabelCompat

theorem labCompat : ∀ (D : D7) (i : D.nd.Loc), LabCompat D.nd D.naut i := by
  intro D i σ Sig hσ
  have key : ∀ k, D.nd.lab k σ = fun v =>
      D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v)) := by
    intro k
    funext v
    rw [D.naut.lab_loc i k σ v, hσ.2.2 _ (GlobalTheory.FixedPlaceSplit.isSplitPl_plGw D k v)]
  unfold NData.goodRow goodSig
  refine forall_congr' fun k => ?_
  rw [key k]

end GlobalTheory.LabelCompat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftGoodRowPointGood
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

namespace GlobalTheory.GoodLiftPoint

theorem good_of_lift : ∀ (D : D7), SumRepresentations.Conclusion42 D → ∀ (i : D.nd.Loc) (σ : D.what₂.FT) (P : D.naut.AV i) (x : D.nd.X i), D.nd.goodRow σ → thetaOf D.nd D.naut i σ P → D.naut.ptV i P = some x → x ∈ ZgoodN D.nd D.naut i ∧ AtM D.nd D.naut i σ := by
  intro D h42 i σ P x hg hth hpt
  have hne : D.what₂.isot (D.nd.j i) σ ≠ ⊥ := by
    intro h
    apply hth.1
    rw [h, Submodule.map_bot]
  obtain ⟨Sig, hW, hBC⟩ := (h42 i σ hne).2.1
  have hX : HasParamX D.nd D.naut i x Sig := ⟨P, hpt, hBC P hth⟩
  have hZ : x ∈ ZN D.nd D.naut i := by
    refine ⟨P, hpt, _, hBC P hth, ?_⟩
    unfold twistIso
    exact List.mem_map.2 ⟨muPart D.nd D.naut i, by simp, rfl⟩
  have hgood : x ∈ ZgoodN D.nd D.naut i :=
    ⟨hZ, Sig, hX, (GlobalTheory.LabelCompat.labCompat D i σ Sig hW).1 hg⟩
  exact ⟨hgood, GlobalTheory.LiftLeaf.atMOfParam D i x hgood Sig hX σ hW⟩

end GlobalTheory.GoodLiftPoint
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftGoodRowPointGoodStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLift_goodRow_point_good : ∀ (D : D7), SumRepresentations.Conclusion42 D → ∀ (i : D.nd.Loc) (σ : D.what₂.FT) (P : D.naut.AV i) (x : D.nd.X i), D.nd.goodRow σ → thetaOf D.nd D.naut i σ P → D.naut.ptV i P = some x → x ∈ ZgoodN D.nd D.naut i ∧ AtM D.nd D.naut i σ := by
  first | exact @GlobalTheory.GoodLiftPoint.good_of_lift | exact GlobalTheory.GoodLiftPoint.good_of_lift | (intros; apply GlobalTheory.GoodLiftPoint.good_of_lift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EveryHeckeRowGoodAtGoodPointLocalisation
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

namespace GlobalTheory.ExhaustRows

theorem main : ∀ (D : D7) (M : MtFam D), HeckeTied D M → AVTied D M → ∀ Tn : NormalizedLocalCompatibility D M, HeckeStdTw Tn.B → SumRepresentations.Conclusion42 D → GoodFTAll D → ∀ (i : D.nd.Loc) (σ : D.what₂.FT), D.what₂.isot (D.nd.j i) σ ≠ ⊥ → D.nd.goodRow σ ∧ ∃ i' ∈ D.nd.locs (D.nd.j i) (D.nd.w i), HG D.nd D.naut i' ∧ AtM D.nd D.naut i' σ := by
  intro D M hT hA Tn hS h42 hG i σ hne
  have hg : D.nd.goodRow σ := hG σ
  obtain ⟨P, hP⟩ := ((h42 i) σ hne).1.2
  obtain ⟨i', hi', P', x', hth, hx⟩ := GlobalTheory.T.theta_lift_has_point_at_localisation_same_place D M hT hA Tn hS i σ P hP
  obtain ⟨hxg, hat⟩ := GlobalTheory.T.thetaLift_goodRow_point_good D h42 i' σ P' x' hg hth hx
  exact ⟨hg, i', hi', ⟨x', hxg⟩, hat⟩

end GlobalTheory.ExhaustRows
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EveryHeckeRowGoodAtGoodPointLocalisationStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.every_heckeRow_good_at_goodPointLocalisation : ∀ (D : D7) (M : MtFam D), HeckeTied D M → AVTied D M → ∀ Tn : NormalizedLocalCompatibility D M, HeckeStdTw Tn.B → SumRepresentations.Conclusion42 D → GoodFTAll D → ∀ (i : D.nd.Loc) (σ : D.what₂.FT), D.what₂.isot (D.nd.j i) σ ≠ ⊥ → D.nd.goodRow σ ∧ ∃ i' ∈ D.nd.locs (D.nd.j i) (D.nd.w i), HG D.nd D.naut i' ∧ AtM D.nd D.naut i' σ := by
  first | exact @GlobalTheory.ExhaustRows.main | exact GlobalTheory.ExhaustRows.main | (intros; apply GlobalTheory.ExhaustRows.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GramClassVacuumCombinationOrbitSumModLower
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GramClassVacuumCombinationOrbitSumModLower
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.TypeOrthClassSum

theorem typeOrth_of_classSum : ∀ (D : D7) (M : MtFam D), AVTied D M → ∀ i : D.nd.Loc, ClassSum (M.loc i) → TypeOrth D i := by
  intro D M V i hC
  obtain ⟨hbd, β, T, c, hβ, hT, hc, hin⟩ := hC
  obtain ⟨B, hB, hBc⟩ := GlobalTheory.T.class_sum_eq_const_mul_petersson D.host.E D.R.nV (M.loc i).wt β hβ
  obtain ⟨c', hc', hcc⟩ := hBc (M.loc i).J (M.loc i).χ T hbd (M.loc i).J_open hT
  have hreal : ∀ x, (M.loc i).real x ∈ NG.TypeSp (M.loc i).wt.ρ (M.loc i).J (M.loc i).χ := fun x => by
    rw [← (M.loc i).real_range]; exact LinearMap.mem_range_self _ x
  set r : ℝ := c * c' with hr
  have hr0 : 0 < r := mul_pos hc hc'
  have hsmul : ∀ f f', (((r : ℂ) • B) f f') = (r : ℂ) * B f f' := fun f f' => by
    simp [LinearMap.smul_apply]

  have hcls : ∃ T' : Finset (GAf D.host.E D.R.nV), ∀ g : GAf D.host.E D.R.nV, ∃ (γ : ReciprocityTheory.Aut.GQ D.host.E D.R.nV)
      (t : GAf D.host.E D.R.nV) (u : GAf D.host.E D.R.nV), t ∈ T' ∧ u ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV ∧
      g = (γ : GAf D.host.E D.R.nV) * t * u := by
    classical
    obtain ⟨F, hF⟩ := hbd
    refine ⟨(T ×ˢ F).image (fun p => p.1 * p.2), fun g => ?_⟩
    obtain ⟨t, ⟨htT, γ, κ, hκ, hg⟩, -⟩ := hT g
    obtain ⟨f, hfF, hu⟩ := hF κ hκ
    refine ⟨γ, t * f, f⁻¹ * κ, Finset.mem_image.2 ⟨(t, f), Finset.mem_product.2 ⟨htT, hfF⟩, rfl⟩, hu, ?_⟩
    rw [hg]; group
  have key := GlobalTheory.ThetaExh.typeOrth_of_avTied D M V i ((r : ℂ) • B) ?_ ?_ ?_
  · exact key
  · intro f hf f' hf'
    obtain ⟨h1, h2, h3⟩ := hB f hf f' hf'
    refine ⟨?_, fun hne => ?_, fun h => ?_⟩
    · rw [hsmul, hsmul, h1, map_mul, Complex.conj_ofReal]
    · rw [hsmul, Complex.re_ofReal_mul]; exact mul_pos hr0 (h2 hne)
    · rw [hsmul, hsmul, h3]
  · intro x y
    rw [hin, hsmul, hcc _ (hreal x) _ (hreal y), hr]
    push_cast; ring
  · intro N hN
    exact GlobalTheory.AlgFormsFin.finiteDimensional_forms D D.R.nV (M.loc i).wt hcls N hN

end GlobalTheory.TypeOrthClassSum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GramClassVacuumCombinationOrbitSumModLowerStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gramClass_vacuumCombination_orbitSum_mod_lower : ∀ (D : D7) (M : MtFam D), AVTied D M → ∀ i : D.nd.Loc, ClassSum (M.loc i) → TypeOrth D i := by
  first | exact @GlobalTheory.TypeOrthClassSum.typeOrth_of_classSum | exact GlobalTheory.TypeOrthClassSum.typeOrth_of_classSum | (intros; apply GlobalTheory.TypeOrthClassSum.typeOrth_of_classSum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpecPrOfZSpecTypeTie
noncomputable section
open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin

namespace GlobalTheory.EtaJoin.SpecProj

theorem le_iSup_of_dichotomy {V ι : Type} [AddCommGroup V] [Module ℂ V] (T : ι → Submodule ℂ V) (A B : Submodule ℂ V)
    (hd : Disjoint A B) (ht : ⨆ P, T P = ⊤) (h : ∀ P, T P ≤ A ∨ T P ≤ B) : A ≤ ⨆ P ∈ {P | T P ≤ A}, T P := by
  intro x hx
  have hle : (⊤ : Submodule ℂ V) ≤ (⨆ P ∈ {P | T P ≤ A}, T P) ⊔ B := by
    rw [← ht]
    refine iSup_le fun P => (h P).elim (fun hP => le_sup_of_le_left ?_) le_sup_of_le_right
    exact le_biSup T (show P ∈ {P | T P ≤ A} from hP)
  obtain ⟨a, ha, b, hb, e⟩ := Submodule.mem_sup.1 (hle (Submodule.mem_top (x := x)))
  have ha' : a ∈ A := (iSup₂_le fun P hP => hP : (⨆ P ∈ {P | T P ≤ A}, T P) ≤ A) ha
  have hb0 : b = 0 := Submodule.disjoint_def.1 hd b (by rw [← add_sub_cancel_left a b, e]; exact A.sub_mem hx ha') hb
  rw [← e, hb0, add_zero]; exact ha

theorem specPr_of_zSpec_typeTie : ∀ (D : D7) (i : D.nd.Loc), ZSpec D i → TypeTie D i → SpecPr D i := by
  intro D i hZ hT
  have hd := (Idx.Z0 D (D.nd.mu i) (D.nd.j i)).orthogonal_disjoint
  have mono : ∀ {Y Y' : Set (D.nd.X i)}, Y ⊆ Y' → D.nd.eigSum i Y ≤ D.nd.eigSum i Y' := fun h => biSup_mono h
  constructor
  · intro y hy
    refine mono ?_ (hT _ y (le_iSup_of_dichotomy _ _ _ hd (D.naut.typeV_top i) (fun P => (hZ P).1) hy))
    rintro x ⟨P, hP, hx⟩
    by_contra hn
    exact D.naut.typeV_ne i P (hd hP (((hZ P).2 x hx).2 hn) |> le_bot_iff.1)
  · intro y hy
    refine mono ?_ (hT _ y (le_iSup_of_dichotomy _ _ _ hd.symm (D.naut.typeV_top i) (fun P => (hZ P).1.symm) hy))
    rintro x ⟨P, hP, hx⟩ hn
    exact D.naut.typeV_ne i P (hd (((hZ P).2 x hx).1 hn) hP |> le_bot_iff.1)

end GlobalTheory.EtaJoin.SpecProj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodPartProjectorSpectralAtEveryLocalisation
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

namespace GlobalTheory.EtaJoin.SpecAll

theorem specPr_all : ∀ (D : D7) (M : MtFam D), HeckeTied D M → HeckeRational D M → AVTied D M →
    ∀ Tn : NormalizedLocalCompatibility D M, HeckeStdTw Tn.B → (∀ i : D.nd.Loc, ClassSum (M.loc i)) →
    (∀ i : D.nd.Loc, ThetaCut D (D.nd.mu i) (D.nd.j i)) → D.nd.EigSpan → Rows.IsotInternal D.what₂ →
    SumRepresentations.Conclusion42 D → SumRepresentations.ConclusionZ D → GoodFTAll D → ∀ i, SpecPr D i := by
  intro D M HT HR AV Tn HS CS TC HE II UnitaryCharacterOfReals PZ GF i
  have SU : SplitUnif D := GlobalTheory.SplitConjPlace.splitEx_all D
  have hZ : ZSpec D i :=
    GlobalTheory.EtaJoin.TypeSum.main D M i HT AV SU (GlobalTheory.T.gramClass_vacuumCombination_orbitSum_mod_lower D M AV i (CS i)) (TC i) II PZ
      (GlobalTheory.T.every_heckeRow_good_at_goodPointLocalisation D M HT AV Tn HS UnitaryCharacterOfReals GF i)
  have hT : TypeTie D i := GlobalTheory.T.typeSpace_projection_to_pointEigenspaces D M i HT HR AV SU (GlobalTheory.T.sphericalHeckeScalarOnTypeSpaces_all_places D M HT AV i) HE
  exact GlobalTheory.EtaJoin.SpecProj.specPr_of_zSpec_typeTie D i hZ hT

end GlobalTheory.EtaJoin.SpecAll
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodPartProjectorSpectralAtEveryLocalisationStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_part_projector_spectral_at_every_localisation : ∀ (D : D7) (M : MtFam D), HeckeTied D M → HeckeRational D M → AVTied D M → ∀ Tn : NormalizedLocalCompatibility D M, HeckeStdTw Tn.B → (∀ i : D.nd.Loc, ClassSum (M.loc i)) → (∀ i : D.nd.Loc, ThetaCut D (D.nd.mu i) (D.nd.j i)) → D.nd.EigSpan → Rows.IsotInternal D.what₂ → SumRepresentations.Conclusion42 D → SumRepresentations.ConclusionZ D → GoodFTAll D → ∀ i, SpecPr D i := by
  first | exact @GlobalTheory.EtaJoin.SpecAll.specPr_all | exact GlobalTheory.EtaJoin.SpecAll.specPr_all | (intros; apply GlobalTheory.EtaJoin.SpecAll.specPr_all <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaJEqZeroOfUntwisted
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalFormLengthEqDefiniteFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConcreteProjectorEqOrthogonalProjection
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConcreteProjectorEqOrthogonalProjection
open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin Formalism.DivisionValues

noncomputable section

namespace GlobalTheory.EtaJoin

section Gen

variable {K : Type} [Field K] [StarRing K] {n d : ℕ}

theorem hform_eq_dot (H : Matrix (Fin n) (Fin n) K) (x y : Fin n → K) :
    hform H x y = star x ⬝ᵥ H.mulVec y := by
  simp only [hform, Matrix.toLinearMapₛₗ₂'_apply, dotProduct, Matrix.mulVec, Finset.mul_sum, RingHom.id_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [starRingEnd_apply, Pi.star_apply]; ring

theorem hform_orthProj (H : Matrix (Fin n) (Fin n) K) (E : Matrix (Fin n) (Fin d) K) (Pr : Matrix (Fin d) (Fin n) K)
    (h : IsOrthProj H E Pr) (u : Fin d → K) (x : Fin n → K) :
    hform H (E.mulVec u) (x - E.mulVec (Pr.mulVec x)) = 0 := by
  have e : x - E.mulVec (Pr.mulVec x) = (1 - E * Pr).mulVec x := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec]
  rw [hform_eq_dot, e, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    h.2, Matrix.zero_mulVec, dotProduct_zero]

variable {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] (σ : K →+* ℂ) (J : (Fin n → K) →ₛₗ[σ] W)

theorem semi_expand (y : Fin n → K) : J y = ∑ i, σ (y i) • J (Pi.single i 1) := by
  conv_lhs => rw [← Finset.univ_sum_single y]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (Pi.single i (y i) : Fin n → K) = y i • Pi.single i 1 := by
    ext k; by_cases hk : k = i
    · subst hk; simp
    · simp [Pi.single_apply, hk]
  rw [this, LinearMap.map_smulₛₗ]

theorem semi_injective (hli : LinearIndependent ℂ fun i => J (Pi.single i 1)) : Function.Injective J := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro y hy
  rw [semi_expand σ J y] at hy
  have h0 := (Fintype.linearIndependent_iff.1 hli) (fun i => σ (y i)) hy
  funext i
  exact σ.injective (by rw [h0 i]; simp)

theorem semi_mulVec_mem (E : Matrix (Fin n) (Fin d) K) (c : Fin d → K) :
    J (E.mulVec c) ∈ Submodule.span ℂ (Set.range fun k => J (E.mulVec (Pi.single k 1))) := by
  have e : E.mulVec c = ∑ k, c k • E.mulVec (Pi.single k 1) := by
    conv_lhs => rw [← Finset.univ_sum_single c]
    rw [Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Matrix.mulVec_smul]
    congr 1
    ext a; by_cases ha : a = k
    · subst ha; simp
    · simp [Pi.single_apply, ha]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, map_sum]
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [LinearMap.map_smulₛₗ]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

end Gen

end GlobalTheory.EtaJoin

namespace GlobalTheory.EtaJoin

section Gen2

variable {K : Type} [Field K] [NumberField K] [StarRing K] {n d : ℕ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  {σ : K →+* ℂ} {V : Type} [AddCommGroup V] [Module K V]

theorem tied_orthProj (e : (Fin n → K) ≃ₗ[K] V) (jV : V →ₛₗ[σ] W) (H Eop : Matrix (Fin n) (Fin n) K) (op : W →ₗ[ℂ] W)
    (E : Matrix (Fin n) (Fin d) K) (Pr : Matrix (Fin d) (Fin n) K) (hP : IsOrthProj H E Pr)
    (hF : FormsTie σ (jV.comp e.toLinearMap) H Eop op) (Z : Submodule ℂ W)
    (hZ : Z = Submodule.span ℂ (Set.range fun k => jV (e (E.mulVec (Pi.single k 1))))) :
    Function.Injective (e.toLinearMap ∘ₗ E.mulVecLin) ∧ Z.comap jV = LinearMap.range (e.toLinearMap ∘ₗ E.mulVecLin) ∧
      ∀ x, e x - (e.toLinearMap ∘ₗ E.mulVecLin) (Pr.mulVec x) ∈ (Zᗮ).comap jV := by
  have hin : ∀ x y, inner ℂ (jV (e x)) (jV (e y)) = σ (hform H x y) := hF.inner
  have hJinj : Function.Injective fun x => jV (e x) := fun a b h => semi_injective σ (jV.comp e.toLinearMap) hF.li h
  have hgen : ∀ c, jV (e (E.mulVec c)) ∈ Z := by
    intro c; rw [hZ]; exact semi_mulVec_mem σ (jV.comp e.toLinearMap) E c
  have horth : ∀ x, jV (e (x - E.mulVec (Pr.mulVec x))) ∈ Zᗮ := by
    intro x
    rw [Submodule.mem_orthogonal]
    intro u hu
    rw [hZ] at hu
    induction hu using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨k, rfl⟩ := hv
      show inner ℂ (jV (e (E.mulVec (Pi.single k 1)))) _ = 0
      rw [hin, hform_orthProj _ _ _ hP, map_zero]
    | zero => exact inner_zero_left _
    | add a b _ _ ha hb => rw [inner_add_left, ha, hb, add_zero]
    | smul c a _ ha => rw [inner_smul_left, ha, mul_zero]
  have hEinj : Function.Injective E.mulVec := by
    intro a b hab
    have := congrArg Pr.mulVec hab
    simp only [Matrix.mulVec_mulVec, hP.1, Matrix.one_mulVec] at this
    exact this
  refine ⟨?_, ?_, ?_⟩
  · exact e.injective.comp hEinj
  · ext y
    constructor
    · intro hy
      rw [Submodule.mem_comap] at hy
      obtain ⟨x, rfl⟩ := e.surjective y
      have hw1 : jV (e (x - E.mulVec (Pr.mulVec x))) ∈ Z := by
        rw [map_sub, map_sub]; exact Submodule.sub_mem _ hy (hgen _)
      have hw0 : jV (e (x - E.mulVec (Pr.mulVec x))) = 0 :=
        inner_self_eq_zero.1 ((Submodule.mem_orthogonal _ _).1 (horth x) _ hw1)
      have hw : x = E.mulVec (Pr.mulVec x) := by
        refine sub_eq_zero.1 (hJinj ?_)
        simp only [map_zero]; exact hw0
      exact ⟨Pr.mulVec x, by simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply, LinearEquiv.coe_coe]; rw [← hw]⟩
    · rintro ⟨c, rfl⟩
      exact hgen c
  · intro x
    rw [Submodule.mem_comap]
    have e1 : e x - (e.toLinearMap ∘ₗ E.mulVecLin) (Pr.mulVec x) = e (x - E.mulVec (Pr.mulVec x)) := by
      simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply, LinearEquiv.coe_coe, map_sub]
    rw [e1]; exact horth x

end Gen2

theorem concreteProj_orth : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (m : ℕ) (A : FamIn D.what₂.LL G Pl0 T m) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (tup : T → D.what₂.Tup) (eMt : ∀ (i : Fin m) (t : T), (Fin (lDim D A P ψ i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1)) (s : ℕ), A.fam.Ok s → ∀ (i : Fin m) (t : T), FormsTie D.what₂.embLL ((D.what₂.jMt (tup t) ((i : ℕ) + 1)).comp (eMt i t).toLinearMap) (lH D A P ψ i t) (lE D A P ψ i t) (D.what₂.eMt (tup t) ((i : ℕ) + 1)) → Idx.Z0 D (tup t) ((i : ℕ) + 1) = Submodule.span ℂ (Set.range fun k => (D.what₂.jMt (tup t) ((i : ℕ) + 1)) (eMt i t ((lZ0 D A P ψ Zs i t).mulVec (Pi.single k 1)))) → Function.Injective ((eMt i t).toLinearMap ∘ₗ (lZ0 D A P ψ Zs i t).mulVecLin) ∧ ratSub D (tup t) ((i : ℕ) + 1) (Idx.Z0 D (tup t) ((i : ℕ) + 1)) = LinearMap.range ((eMt i t).toLinearMap ∘ₗ (lZ0 D A P ψ Zs i t).mulVecLin) ∧ ∀ x, eMt i t x - ((eMt i t).toLinearMap ∘ₗ (lZ0 D A P ψ Zs i t).mulVecLin) ((lPrj D A P ψ Zs i t).mulVec x) ∈ ratSub D (tup t) ((i : ℕ) + 1) (Idx.Z0 D (tup t) ((i : ℕ) + 1))ᗮ := by
  intro D G _ _ Pl0 T m A P ψ Zs tup eMt s hOk i t hF hZ
  have hB : BlockHyp (A.fam.L i t) (A.fam.lvlA P ψ) A.fam.v0 s := ⟨hOk.conj, fun χ hχ => hOk.irr χ hχ, hOk.lifts i t⟩
  have hP : IsOrthProj (lH D A P ψ i t) (lZ0 D A P ψ Zs i t) (lPrj D A P ψ Zs i t) :=
    BlockDat.lf_l_proj (Z := Zs.Zl i t) hB
  exact tied_orthProj (eMt i t) (D.what₂.jMt (tup t) ((i : ℕ) + 1)) _ _ _ _ _ hP hF _ hZ

end GlobalTheory.EtaJoin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConcreteProjectorEqOrthogonalProjectionStatement
open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.concreteProjector_eq_orthogonalProjection : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (m : ℕ) (A : FamIn D.what₂.LL G Pl0 T m) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (tup : T → D.what₂.Tup) (eMt : ∀ (i : Fin m) (t : T), (Fin (lDim D A P ψ i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1)) (s : ℕ), A.fam.Ok s → ∀ (i : Fin m) (t : T), FormsTie D.what₂.embLL ((D.what₂.jMt (tup t) ((i : ℕ) + 1)).comp (eMt i t).toLinearMap) (lH D A P ψ i t) (lE D A P ψ i t) (D.what₂.eMt (tup t) ((i : ℕ) + 1)) → Idx.Z0 D (tup t) ((i : ℕ) + 1) = Submodule.span ℂ (Set.range fun k => (D.what₂.jMt (tup t) ((i : ℕ) + 1)) (eMt i t ((lZ0 D A P ψ Zs i t).mulVec (Pi.single k 1)))) → Function.Injective ((eMt i t).toLinearMap ∘ₗ (lZ0 D A P ψ Zs i t).mulVecLin) ∧ ratSub D (tup t) ((i : ℕ) + 1) (Idx.Z0 D (tup t) ((i : ℕ) + 1)) = LinearMap.range ((eMt i t).toLinearMap ∘ₗ (lZ0 D A P ψ Zs i t).mulVecLin) ∧ ∀ x, eMt i t x - ((eMt i t).toLinearMap ∘ₗ (lZ0 D A P ψ Zs i t).mulVecLin) ((lPrj D A P ψ Zs i t).mulVec x) ∈ ratSub D (tup t) ((i : ℕ) + 1) (Idx.Z0 D (tup t) ((i : ℕ) + 1))ᗮ := by
  first | exact @GlobalTheory.EtaJoin.concreteProj_orth | exact GlobalTheory.EtaJoin.concreteProj_orth | (intros; apply GlobalTheory.EtaJoin.concreteProj_orth <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalFormLengthEqDefiniteFamily
open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin

noncomputable section

namespace GlobalTheory.EtaJoin.Side

theorem length_quot_map {R M M' : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    (f : M →ₗ[R] M') (hf : Function.Injective f) (P Q : Submodule R M) :
    Module.length R (P.map f ⧸ (Q.map f).comap (P.map f).subtype) = Module.length R (P ⧸ Q.comap P.subtype) := by
  refine (LinearEquiv.length_eq (Submodule.Quotient.equiv (Q.comap P.subtype) ((Q.map f).comap (P.map f).subtype)
    (Submodule.equivMapOfInjective f hf P) ?_)).symm
  ext ⟨y, hy⟩
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
  constructor
  · rintro ⟨⟨x, hx⟩, hxQ, hxy⟩
    refine ⟨x, hxQ, ?_⟩
    have := congrArg Subtype.val hxy
    simpa using this
  · rintro ⟨x, hxQ, hxy⟩
    obtain ⟨x', hx', rfl⟩ := hy
    have : x = x' := hf hxy
    subst this
    exact ⟨⟨x, hx'⟩, hxQ, rfl⟩


open scoped _root_.Formalism.L2.Col in
theorem lenUW_map {K : Type} [Field K] [NumberField K] {V V' : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
    (φ : V →ₗ[K] V') (hφ : Function.Injective φ) (w : HeightOneSpectrum (𝓞 K)) (A B : Submodule (𝓞 K) V) :
    Formalism.L2.Col.lenUW w (A.map (φ.restrictScalars (𝓞 K))) (B.map (φ.restrictScalars (𝓞 K))) = Formalism.L2.Col.lenUW w A B := by
  unfold Formalism.L2.Col.lenUW Formalism.L2.Col.lenW
  rw [Formalism.L2.Col.atW_map, Formalism.L2.Col.atW_map,
    length_quot_map (φ.restrictScalars (Formalism.L2.Col.Ow w)) hφ]

theorem lat_eq_map (D : D7) (μ : D.what₂.Tup) (j : ℕ) {n : ℕ} (e : (Fin n → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL μ j)
    (N : Submodule (𝓞 D.what₂.LL) (Fin n → D.what₂.LL))
    (hL : OLatTie D.what₂.embLL (D.what₂.MtLat μ j) ((D.what₂.jMt μ j).comp e.toLinearMap) N) :
    lat D μ j = N.map (e.toLinearMap.restrictScalars (𝓞 D.what₂.LL)) := by
  classical
  apply le_antisymm
  · rw [lat, Submodule.span_le]
    intro y hy
    obtain ⟨x, rfl⟩ := e.surjective y
    refine ⟨x, ?_, rfl⟩
    show x ∈ N
    rw [hL.2 x]
    refine ⟨fun v => if v = D.what₂.jMt μ j (e x) then 1 else 0, ?_⟩
    rw [Finset.sum_eq_single (D.what₂.jMt μ j (e x))]
    · simp
    · intro b _ hb
      simp [hb]
    · intro h
      exact absurd hy h
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨c, hc⟩ := (hL.2 x).1 hx
    choose! g hg using D.what₂.MtLat_sub μ j
    have hx' : e x = ∑ v ∈ (D.what₂.MtLat μ j).gen, (c v) • g v := by
      apply GlobalTheory.Mem.LiftForms.jMt_injective μ j
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      have hc' : D.what₂.jMt μ j (e x) = ∑ v ∈ (D.what₂.MtLat μ j).gen, D.what₂.embLL (c v : D.what₂.LL) • v := hc
      rw [hc']
      refine Finset.sum_congr rfl fun v hv => ?_
      rw [← algebraMap_smul D.what₂.LL (c v) (g v), map_smulₛₗ, hg v hv]
    show e x ∈ lat D μ j
    rw [hx']
    refine Submodule.sum_mem _ fun v hv => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    show D.what₂.jMt μ j (g v) ∈ (D.what₂.MtLat μ j).gen
    rw [hg v hv]
    exact hv

theorem zRat_and_etaRat_eq : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (m : ℕ) (A : FamIn D.what₂.LL G Pl0 T m) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (tup : T → D.what₂.Tup) (eMt : ∀ (i : Fin m) (t : T), (Fin (lDim D A P ψ i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1)) (s : ℕ), A.fam.Ok s → ∀ (i : Fin m) (t : T), FormsTie D.what₂.embLL ((D.what₂.jMt (tup t) ((i : ℕ) + 1)).comp (eMt i t).toLinearMap) (lH D A P ψ i t) (lE D A P ψ i t) (D.what₂.eMt (tup t) ((i : ℕ) + 1)) → OLatTie D.what₂.embLL (D.what₂.MtLat (tup t) ((i : ℕ) + 1)) ((D.what₂.jMt (tup t) ((i : ℕ) + 1)).comp (eMt i t).toLinearMap) (lNab D A P ψ i t) → Idx.Z0 D (tup t) ((i : ℕ) + 1) = Submodule.span ℂ (Set.range fun k => (D.what₂.jMt (tup t) ((i : ℕ) + 1)) (eMt i t ((lZ0 D A P ψ Zs i t).mulVec (Pi.single k 1)))) → ZRat D (tup t) ((i : ℕ) + 1) ∧ ∀ w, etaRat D (tup t) ((i : ℕ) + 1) w = A.fam.etaJ P ψ Zs i t (D.plEq w) := by
  intro D G _ _ Pl0 T m A P ψ Zs tup eMt s hOk i t hF hL hZ
  obtain ⟨hinj, hrange, hproj⟩ := GlobalTheory.T.concreteProjector_eq_orthogonalProjection D G Pl0 T m A P ψ Zs tup eMt s hOk i t hF hZ
  have hB : BlockHyp (A.fam.L i t) (A.fam.lvlA P ψ) A.v0 s := ⟨hOk.conj, hOk.irr, hOk.lifts i t⟩
  have hcut := BlockDat.lf_cut_nab (Z := Zs.Zl i t) hB
  have hlat := lat_eq_map D (tup t) ((i : ℕ) + 1) (eMt i t) _ hL
  set e := eMt i t with he
  set ψL := (e.toLinearMap ∘ₗ (lZ0 D A P ψ Zs i t).mulVecLin) with hψL
  set R := ratSub D (tup t) ((i : ℕ) + 1) (Idx.Z0 D (tup t) ((i : ℕ) + 1)) with hR
  set Rp := ratSub D (tup t) ((i : ℕ) + 1) (Idx.Z0 D (tup t) ((i : ℕ) + 1))ᗮ with hRp
  have hbot : ∀ y, y ∈ R → y ∈ Rp → y = 0 := by
    intro y h1 h2
    apply GlobalTheory.Mem.LiftForms.jMt_injective (tup t) ((i : ℕ) + 1)
    rw [map_zero]
    have h3 : D.what₂.jMt (tup t) ((i : ℕ) + 1) y ∈ Idx.Z0 D (tup t) ((i : ℕ) + 1) ⊓ (Idx.Z0 D (tup t) ((i : ℕ) + 1))ᗮ :=
      ⟨h1, h2⟩
    rw [Submodule.inf_orthogonal_eq_bot] at h3
    exact h3
  have hmemR : ∀ z, ψL z ∈ R := fun z => by rw [hrange]; exact LinearMap.mem_range_self _ z
  have hup : up D (tup t) ((i : ℕ) + 1) =
      ((A.fam.L i t).Tl (A.fam.lvlA P ψ) (Zs.Zl i t)).map (ψL.restrictScalars (𝓞 D.what₂.LL)) := by
    ext y
    constructor
    · rintro ⟨hyR, hy⟩
      obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hy
      rw [hlat] at ha
      obtain ⟨x, hx, rfl⟩ := ha
      have hd : y - ψL ((lPrj D A P ψ Zs i t).mulVec x) = 0 := by
        apply hbot
        · exact R.sub_mem hyR (hmemR _)
        · have : y - ψL ((lPrj D A P ψ Zs i t).mulVec x) = (e x - ψL ((lPrj D A P ψ Zs i t).mulVec x)) + b := by
            rw [← hab]
            simp only [LinearMap.restrictScalars_apply, LinearEquiv.coe_coe]
            abel
          rw [this]
          exact Rp.add_mem (hproj x) hb
      refine ⟨(lPrj D A P ψ Zs i t).mulVec x, ⟨x, hx, rfl⟩, ?_⟩
      show ψL _ = y
      exact (sub_eq_zero.1 hd).symm
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨hmemR _, Submodule.mem_sup.2 ⟨e x, ?_, ψL ((lPrj D A P ψ Zs i t).mulVec x) - e x, ?_, ?_⟩⟩
      · rw [hlat]
        exact ⟨x, hx, rfl⟩
      · show _ ∈ Rp
        rw [← neg_sub]
        exact Rp.neg_mem (hproj x)
      · show e x + (ψL ((lPrj D A P ψ Zs i t).mulVec x) - e x) = ψL ((lPrj D A P ψ Zs i t).mulVec x)
        abel
  have hlow : low D (tup t) ((i : ℕ) + 1) =
      ((A.fam.L i t).cutZ (A.fam.lvlA P ψ) (Zs.Zl i t)).map (ψL.restrictScalars (𝓞 D.what₂.LL)) := by
    ext y
    constructor
    · rintro ⟨hy, hyR⟩
      have hyR' : y ∈ R := hyR
      rw [hrange] at hyR'
      obtain ⟨z, rfl⟩ := hyR'
      rw [hlat] at hy
      obtain ⟨x, hx, hxz⟩ := hy
      have hxz' : x = (lZ0 D A P ψ Zs i t).mulVec z := e.injective hxz
      refine ⟨z, ?_, rfl⟩
      rw [← hcut]
      show (lZ0 D A P ψ Zs i t).mulVec z ∈ lNab D A P ψ i t
      rw [← hxz']
      exact hx
    · rintro ⟨z, hz, rfl⟩
      refine ⟨?_, hmemR z⟩
      rw [hlat]
      rw [← hcut] at hz
      exact ⟨(lZ0 D A P ψ Zs i t).mulVec z, hz, rfl⟩
  refine ⟨?_, fun w => ?_⟩
  · rw [ZRat, eq_top_iff]
    intro y _
    obtain ⟨x, rfl⟩ := e.surjective y
    refine Submodule.mem_sup.2 ⟨ψL ((lPrj D A P ψ Zs i t).mulVec x), hmemR _, e x - ψL ((lPrj D A P ψ Zs i t).mulVec x),
      hproj x, ?_⟩
    abel
  · rw [etaRat, hup, hlow, lenUW_map ψL hinj]
    rfl

end GlobalTheory.EtaJoin.Side
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalFormLengthEqDefiniteFamilyStatement
open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalFormLength_eq_definiteFamily : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (m : ℕ) (A : FamIn D.what₂.LL G Pl0 T m) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (tup : T → D.what₂.Tup) (eMt : ∀ (i : Fin m) (t : T), (Fin (lDim D A P ψ i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1)) (s : ℕ), A.fam.Ok s → ∀ (i : Fin m) (t : T), FormsTie D.what₂.embLL ((D.what₂.jMt (tup t) ((i : ℕ) + 1)).comp (eMt i t).toLinearMap) (lH D A P ψ i t) (lE D A P ψ i t) (D.what₂.eMt (tup t) ((i : ℕ) + 1)) → OLatTie D.what₂.embLL (D.what₂.MtLat (tup t) ((i : ℕ) + 1)) ((D.what₂.jMt (tup t) ((i : ℕ) + 1)).comp (eMt i t).toLinearMap) (lNab D A P ψ i t) → Idx.Z0 D (tup t) ((i : ℕ) + 1) = Submodule.span ℂ (Set.range fun k => (D.what₂.jMt (tup t) ((i : ℕ) + 1)) (eMt i t ((lZ0 D A P ψ Zs i t).mulVec (Pi.single k 1)))) → ZRat D (tup t) ((i : ℕ) + 1) ∧ ∀ w, etaRat D (tup t) ((i : ℕ) + 1) w = A.fam.etaJ P ψ Zs i t (D.plEq w) := by
  first | exact @GlobalTheory.EtaJoin.Side.zRat_and_etaRat_eq | exact GlobalTheory.EtaJoin.Side.zRat_and_etaRat_eq | (intros; apply GlobalTheory.EtaJoin.Side.zRat_and_etaRat_eq <;> assumption)
end
end

open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin

namespace GlobalTheory

theorem etaJ_eq_zero_of_untwisted (D : D7) (j : ℕ) (w : D.what₂.places.Pl) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
    (hw : D.what₂.muAt w = D.what₂.mu0) : D.what₂.etaJ j w = 0 := by
  rw [D.etaJ_tie j w h1 h2]
  refine Finset.sum_eq_zero fun i hi => ?_
  exact absurd (by rw [((D.nd.locs_mem j w i).1 hi).2]; exact hw) (D.nd.w_tw i)

theorem etaJ_join : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (m : ℕ) (A : FamIn D.what₂.LL G Pl0 T m) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (tup : T → D.what₂.Tup) (eMt : ∀ (i : Fin m) (t : T), (Fin (lDim D A P ψ i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1)) (s : ℕ), A.fam.Ok s → m ≤ D.R.m → ∀ (S0 : IndefData (A.side P ψ Zs)) (M : MtFam D) (Tn : NormalizedLocalCompatibility D M), TupTie D A S0 tup → (∀ y, y ∈ S0.Tw ↔ S0.μ y ≠ A.μ0) → (∀ (i : Fin m), ∀ y ∈ S0.Tw, FormsTie D.what₂.embLL ((D.what₂.jMt (tup (S0.μ y)) ((i : ℕ) + 1)).comp (eMt i (S0.μ y)).toLinearMap) (lH D A P ψ i (S0.μ y)) (lE D A P ψ i (S0.μ y)) (D.what₂.eMt (tup (S0.μ y)) ((i : ℕ) + 1)) ∧ OLatTie D.what₂.embLL (D.what₂.MtLat (tup (S0.μ y)) ((i : ℕ) + 1)) ((D.what₂.jMt (tup (S0.μ y)) ((i : ℕ) + 1)).comp (eMt i (S0.μ y)).toLinearMap) (lNab D A P ψ i (S0.μ y)) ∧ Idx.Z0 D (tup (S0.μ y)) ((i : ℕ) + 1) = Submodule.span ℂ (Set.range fun k => (D.what₂.jMt (tup (S0.μ y)) ((i : ℕ) + 1)) (eMt i (S0.μ y) ((lZ0 D A P ψ Zs i (S0.μ y)).mulVec (Pi.single k 1))))) → HeckeStdTw Tn.B → (∀ j w, 1 ≤ j → j ≤ D.R.m → D.what₂.muAt w ≠ D.what₂.mu0 → LatStable Tn.B j w) → (∀ i, SpecPr D i) → ∀ (i : Fin m) w, D.what₂.etaJ ((i : ℕ) + 1) w = @ite _ (D.plEq w ∈ S0.Tw) (Classical.propDecidable _) (A.fam.etaJ P ψ Zs i (S0.μ (D.plEq w)) (D.plEq w)) 0 := by
  intro D G _ _ Pl0 T m A P ψ Zs tup eMt s hOk hm S0 M Tn hTup hTw hMt hH hLat hSpec i w
  have hj1 : 1 ≤ (i : ℕ) + 1 := Nat.le_add_left _ _
  have hj2 : (i : ℕ) + 1 ≤ D.R.m := Nat.lt_of_lt_of_le i.2 hm
  by_cases h : D.plEq w ∈ S0.Tw
  · rw [if_pos h]
    have hne : D.what₂.muAt w ≠ D.what₂.mu0 := by
      rw [hTup.muAt w, ← hTup.mu0]
      exact fun e => (hTw _).1 h (hTup.inj e)
    have htw : D.what₂.muTw w = tup (S0.μ (D.plEq w)) :=
      ((D.what₂.muAt_or w).resolve_left hne).symm.trans (hTup.muAt w)
    obtain ⟨hM1, hM2, hM3⟩ := hMt i _ h
    obtain ⟨hZ, hE⟩ := GlobalTheory.T.rationalFormLength_eq_definiteFamily D G Pl0 T m A P ψ Zs tup eMt s hOk i (S0.μ (D.plEq w)) hM1 hM2 hM3
    rw [GlobalTheory.T.sum_localCongruenceLength_eq_rationalLength D M Tn ((i : ℕ) + 1) w hj1 hj2 hne hH (hLat _ w hj1 hj2 hne) (htw ▸ hZ)
      (fun i' _ => hSpec i'), htw]
    exact hE w
  · rw [if_neg h]
    refine etaJ_eq_zero_of_untwisted D _ w hj1 hj2 ?_
    rw [hTup.muAt w, ← hTup.mu0]
    congr 1
    by_contra hn
    exact h ((hTw _).2 hn)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeStableLocalLatticeOfRationalIntegrality
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeStableLocalLatticeOfIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeStableLocalLatticeOfIntegral
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.LatStab

theorem jMt_injective (D : D7) (μ : D.what₂.Tup) (j : ℕ) : Function.Injective (D.what₂.jMt μ j) := by
  classical
  let b := Module.Free.chooseBasis D.what₂.LL (D.what₂.MtL μ j)
  have hli := (D.what₂.jMt_basis μ j b).1
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  have hx' : x = ∑ i ∈ (b.repr x).support, b.repr x i • b i := by
    conv_lhs => rw [← b.linearCombination_repr x]
    rw [Finsupp.linearCombination_apply]; rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hx', map_sum] at hx
  simp only [map_smulₛₗ] at hx
  have h0 := linearIndependent_iff'.1 hli _ _ hx
  apply b.repr.injective
  ext i
  by_cases hi : i ∈ (b.repr x).support
  · simpa using h0 i hi
  · simpa using Finsupp.notMem_support_iff.1 hi

theorem latStable_of_latInt : ∀ (D : D7) (M : MtFam D) (B : NLocBase D M) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
    (w : D.what₂.places.Pl), LatInt D M (B.Qc j w) j h1 h2 w → LatStable B j w := by
  intro D M B j h1 h2 w hI v k hvk x hx
  classical
  obtain ⟨s, ϖ, hcj, hu⟩ := GlobalTheory.SplitConjPlace.splitEx_all D v hvk.1
  have hinj := jMt_injective D (D.what₂.muTw w) j
  let f : D.what₂.Mt (D.what₂.muTw w) j → D.what₂.MtL (D.what₂.muTw w) j := fun g =>
    if h : g ∈ Set.range (D.what₂.jMt (D.what₂.muTw w) j) then h.choose else 0
  have hf : ∀ g ∈ (D.what₂.MtLat (D.what₂.muTw w) j).gen, D.what₂.jMt (D.what₂.muTw w) j (f g) = g := by
    intro g hg
    have h := hI.1 g hg
    simp only [f, dif_pos h]
    exact h.choose_spec
  have key : ∀ y ∈ genSet D (D.what₂.muTw w) j, B.hK j w v k (B.iV j w y) ∈ latLoc B j w := by
    intro y hy
    obtain ⟨c, hc0, hcE⟩ := hI.2 v k s ϖ hvk hcj hu _ hy
    have e1 := B.hL_def j w h1 h2 v k s ϖ hvk hcj hu y
    rw [hcE] at e1
    have e2 := (M (D.what₂.muTw w) j h1 h2).real_inj e1
    have e3 : B.hL j w v k y = ∑ g ∈ (D.what₂.MtLat (D.what₂.muTw w) j).gen, c g • f g := by
      apply hinj
      set_option synthInstance.maxHeartbeats 100000 in
        rw [e2, map_sum]
      refine Finset.sum_congr rfl fun g hg => ?_
      rw [map_smulₛₗ, hf g hg]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [B.hK_def, e3, map_sum]
    refine Submodule.sum_mem _ fun g hg => ?_
    rw [map_smulₛₗ]
    obtain ⟨o, ho⟩ := (B.ec_w j w (c g)).1 (hc0 g)
    rw [← ho, algebraMap_smul]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨f g, ?_, rfl⟩)
    show D.what₂.jMt (D.what₂.muTw w) j (f g) ∈ (D.what₂.MtLat (D.what₂.muTw w) j).gen
    rw [hf g hg]; exact hg
  have hle : latLoc B j w ≤ (latLoc B j w).comap ((B.hK j w v k).restrictScalars (B.Oc j w)) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨y, hy, rfl⟩
    exact key y hy
  exact hle hx

end GlobalTheory.LatStab

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeStableLocalLatticeOfIntegralStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeStableLocalLattice_of_integral : ∀ (D : D7) (M : MtFam D) (B : NLocBase D M) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (w : D.what₂.places.Pl), LatInt D M (B.Qc j w) j h1 h2 w → LatStable B j w := by
  first | exact @GlobalTheory.LatStab.latStable_of_latInt | exact GlobalTheory.LatStab.latStable_of_latInt | (intros; apply GlobalTheory.LatStab.latStable_of_latInt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeStableLocalLatticeOfRationalIntegrality
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty

noncomputable section

namespace GlobalTheory.LatTied

theorem latStable_tied : ∀ (D : D7) (M : MtFam D) (Tn : NormalizedLocalCompatibility D M) (Q : D.what₂.places.Pl → Finset (PlE D.host)),
    (∀ i, D.nd.Q i = Q (D.nd.w i)) → (∀ j h1 h2 w, D.what₂.muAt w ≠ D.what₂.mu0 → LatInt D M (Q w) j h1 h2 w) →
    ∀ j w, 1 ≤ j → j ≤ D.R.m → D.what₂.muAt w ≠ D.what₂.mu0 → GlobalTheory.EtaJoin.LatStable Tn.B j w := by
  intro D M Tn Q hQ hI j w h1 h2 hw
  classical
  by_cases hne : (D.nd.locs j w).Nonempty
  · obtain ⟨i, hi⟩ := hne
    have hwi : D.nd.w i = w := ((D.nd.locs_mem j w i).1 hi).2
    have hQc : Tn.B.Qc j w = Q w := by rw [← Tn.Q_eq j w i hi, hQ i, hwi]
    apply GlobalTheory.T.heckeStableLocalLattice_of_integral D M Tn.B j h1 h2 w
    rw [hQc]; exact hI j h1 h2 w hw
  · have hsub : Subsingleton (heckeAlg Tn.B j w) := by
      by_contra hns
      rw [not_subsingleton_iff_nontrivial] at hns
      obtain ⟨I, hI'⟩ := Ideal.exists_maximal (heckeAlg Tn.B j w)
      obtain ⟨i, hi, -⟩ := Tn.mx_all j w h1 h2 hw I hI'
      exact hne ⟨i, hi⟩
    have h10 : (1 : Module.End (FractionRing (Tn.B.Oc j w)) (Tn.B.V j w)) = 0 := by
      have := congrArg Subtype.val (Subsingleton.elim (1 : heckeAlg Tn.B j w) 0)
      simpa using this
    have hx : ∀ y : Tn.B.V j w, y = 0 := fun y => by
      have := LinearMap.congr_fun h10 y
      simpa using this
    intro v k _ x _
    rw [hx (Tn.B.hK j w v k x)]
    exact Submodule.zero_mem _

end GlobalTheory.LatTied

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeStableLocalLatticeOfRationalIntegralityStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeStableLocalLattice_of_rationalIntegrality : ∀ (D : D7) (M : MtFam D) (Tn : NormalizedLocalCompatibility D M) (Q : D.what₂.places.Pl → Finset (PlE D.host)), (∀ i, D.nd.Q i = Q (D.nd.w i)) → (∀ j h1 h2 w, D.what₂.muAt w ≠ D.what₂.mu0 → LatInt D M (Q w) j h1 h2 w) → ∀ j w, 1 ≤ j → j ≤ D.R.m → D.what₂.muAt w ≠ D.what₂.mu0 → GlobalTheory.EtaJoin.LatStable Tn.B j w := by
  first | exact @GlobalTheory.LatTied.latStable_tied | exact GlobalTheory.LatTied.latStable_tied | (intros; apply GlobalTheory.LatTied.latStable_tied <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RangeAdjointLeOfComp
open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin

noncomputable section

namespace GlobalTheory.EtaJoin

theorem prj_mul_goodOp {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}
    {B : BlockDat K G Pl0} {ℓ : Lvl K G} (Z : Submodule K B.S.Forms) {v0 : InfinitePlace K} {s : ℕ}
    (h : BlockHyp B ℓ v0 s) :
    B.lPr ℓ Z * B.S.lvlOp B.r ℓ.P ℓ.ψ (idemOf ℓ.X) = B.lPr ℓ Z := by
  have hc := idempotent_central K G ℓ.X h.irr
  have h1 := (level_operator_spec K v0 h.conj B.S (h.ok.hpos v0) G B.r h.ok.act ℓ.P ℓ.ψ (idemOf ℓ.X) (hc.2 _).symm).1
  obtain ⟨⟨h2, -⟩, h3⟩ := BlockDat.lf_v_proj h
  have h4 : Formalism.L2.DIV.goodAt ℓ.X ℓ.P ℓ.ψ * idemOf ℓ.X = Formalism.L2.DIV.goodAt ℓ.X ℓ.P ℓ.ψ := by
    unfold Formalism.L2.DIV.goodAt
    rw [mul_assoc, hc.2, ← mul_assoc, hc.1]
  have h5 : B.vPr ℓ * B.S.gaMat B.r (idemOf ℓ.X) = B.vPr ℓ := by
    calc B.vPr ℓ * B.S.gaMat B.r (idemOf ℓ.X)
        = B.vPr ℓ * B.vE ℓ * B.vPr ℓ * B.S.gaMat B.r (idemOf ℓ.X) := by rw [h2, Matrix.one_mul]
      _ = B.vPr ℓ * (B.vE ℓ * B.vPr ℓ * B.S.gaMat B.r (idemOf ℓ.X)) := by simp only [Matrix.mul_assoc]
      _ = B.vPr ℓ * (B.vE ℓ * B.vPr ℓ) := by rw [h3, ← (group_action_matrix_hom K B.S G B.r).2, h4]
      _ = B.vPr ℓ := by rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  unfold BlockDat.lPr
  rw [Matrix.mul_assoc, h1, ← Matrix.mul_assoc, Matrix.mul_assoc (B.Pq ℓ Z), h5]

theorem range_adjoint_le_of_comp {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] (θ : V →ₗ[ℂ] W) (e : V →ₗ[ℂ] V)
    (hs : e.IsSymmetric) (h : θ ∘ₗ e = θ) : LinearMap.range (LinearMap.adjoint θ) ≤ LinearMap.range e := by
  rintro y ⟨x, rfl⟩
  refine ⟨LinearMap.adjoint θ x, ?_⟩
  refine ext_inner_right ℂ fun z => ?_
  rw [hs (LinearMap.adjoint θ x) z, LinearMap.adjoint_inner_left, LinearMap.adjoint_inner_left]
  have := LinearMap.congr_fun h z
  rw [LinearMap.comp_apply] at this
  rw [this]

theorem thetaCut_of_tie : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (m : ℕ) (A : FamIn D.what₂.LL G Pl0 T m) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (tup : T → D.what₂.Tup) (eMt : ∀ (i : Fin m) (t : T), (Fin (lDim D A P ψ i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1)) (s : ℕ), A.fam.Ok s → ∀ (S0 : IndefData (A.side P ψ Zs)) (jW : ∀ i : Fin m, (Fin (S0.dW i) → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Mj ((i : ℕ) + 1)) (i : Fin m) (t : T), FormsTie D.what₂.embLL ((D.what₂.jMt (tup t) ((i : ℕ) + 1)).comp (eMt i t).toLinearMap) (lH D A P ψ i t) (lE D A P ψ i t) (D.what₂.eMt (tup t) ((i : ℕ) + 1)) → (∀ x, D.what₂.thetaP (tup t) ((i : ℕ) + 1) (D.what₂.jMt (tup t) ((i : ℕ) + 1) (eMt i t x)) = jW i ((S0.θ i t).mulVec ((lPrj D A P ψ Zs i t).mulVec x))) → ThetaCut D (tup t) ((i : ℕ) + 1) := by
  intro D G _ _ Pl0 T m A P ψ Zs tup eMt s hOk S0 jW i t hF hθ
  have hB : BlockHyp (A.fam.L i t) (A.fam.lvlA P ψ) A.fam.v0 s := ⟨hOk.conj, fun χ hχ => hOk.irr χ hχ, hOk.lifts i t⟩
  have hP : lPrj D A P ψ Zs i t * lE D A P ψ i t = lPrj D A P ψ Zs i t := prj_mul_goodOp (Zs.Zl i t) hB
  refine range_adjoint_le_of_comp _ _ (D.what₂.eMt_sa _ _) ?_
  refine LinearMap.ext_on_range hF.span fun k => ?_
  rw [LinearMap.comp_apply, hF.op_eq]
  refine (hθ _).trans (Eq.trans ?_ (hθ _).symm)
  rw [Matrix.mulVec_mulVec (Pi.single k 1), hP]

end GlobalTheory.EtaJoin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CongruenceLengthTwistedPlacesOfHeckeIntegrality
open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin GlobalTheory.CoefDuty

namespace GlobalTheory


set_option maxHeartbeats 1000000 in
theorem etaJ_join_closed : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (m : ℕ) (A : FamIn D.what₂.LL G Pl0 T m) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (tup : T → D.what₂.Tup) (eMt : ∀ (i : Fin m) (t : T), (Fin (lDim D A P ψ i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1)) (s : ℕ), A.fam.Ok s → m ≤ D.R.m → ∀ (S0 : IndefData (A.side P ψ Zs)) (M : MtFam D) (Tn : NormalizedLocalCompatibility D M), TupTie D A S0 tup → (∀ y, y ∈ S0.Tw ↔ S0.μ y ≠ A.μ0) → (∀ (i : Fin m), ∀ y ∈ S0.Tw, FormsTie D.what₂.embLL ((D.what₂.jMt (tup (S0.μ y)) ((i : ℕ) + 1)).comp (eMt i (S0.μ y)).toLinearMap) (lH D A P ψ i (S0.μ y)) (lE D A P ψ i (S0.μ y)) (D.what₂.eMt (tup (S0.μ y)) ((i : ℕ) + 1)) ∧ OLatTie D.what₂.embLL (D.what₂.MtLat (tup (S0.μ y)) ((i : ℕ) + 1)) ((D.what₂.jMt (tup (S0.μ y)) ((i : ℕ) + 1)).comp (eMt i (S0.μ y)).toLinearMap) (lNab D A P ψ i (S0.μ y)) ∧ Idx.Z0 D (tup (S0.μ y)) ((i : ℕ) + 1) = Submodule.span ℂ (Set.range fun k => (D.what₂.jMt (tup (S0.μ y)) ((i : ℕ) + 1)) (eMt i (S0.μ y) ((lZ0 D A P ψ Zs i (S0.μ y)).mulVec (Pi.single k 1))))) → HeckeStdTw Tn.B → ∀ (Q : D.what₂.places.Pl → Finset (PlE D.host)), (∀ i, D.nd.Q i = Q (D.nd.w i)) → (∀ j h1 h2 w, D.what₂.muAt w ≠ D.what₂.mu0 → LatInt D M (Q w) j h1 h2 w) → HeckeTied D M → HeckeRational D M → AVTied D M → (∀ i : D.nd.Loc, ClassSum (M.loc i)) → ∀ (jW : ∀ i : Fin m, (Fin (S0.dW i) → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Mj ((i : ℕ) + 1)), m = D.R.m → (∀ (i : Fin m), ∀ y ∈ S0.Tw, ∀ x, D.what₂.thetaP (tup (S0.μ y)) ((i : ℕ) + 1) (D.what₂.jMt (tup (S0.μ y)) ((i : ℕ) + 1) (eMt i (S0.μ y) x)) = jW i ((S0.θ i (S0.μ y)).mulVec ((lPrj D A P ψ Zs i (S0.μ y)).mulVec x))) → D.nd.EigSpan → Rows.IsotInternal D.what₂ → Formalism.MainNotions.SumRepresentations.Conclusion42 D → Formalism.MainNotions.SumRepresentations.ConclusionZ D → GoodFTAll D → ∀ (i : Fin m) w, D.what₂.etaJ ((i : ℕ) + 1) w = @ite _ (D.plEq w ∈ S0.Tw) (Classical.propDecidable _) (A.fam.etaJ P ψ Zs i (S0.μ (D.plEq w)) (D.plEq w)) 0 := by
  intro D G _ _ Pl0 T m A P ψ Zs tup eMt s hOk hm S0 M Tn hTup hTw hMt hStd Q hQ hLatInt hHT hHR hAV hCS jW hmR hθ
    hEig hIsot h42 hZ hGood
  have hLat : ∀ j w, 1 ≤ j → j ≤ D.R.m → D.what₂.muAt w ≠ D.what₂.mu0 → LatStable Tn.B j w :=
    fun j w h1 h2 hne => GlobalTheory.T.heckeStableLocalLattice_of_rationalIntegrality D M Tn Q hQ hLatInt j w h1 h2 hne
  have hTC : ∀ i : D.nd.Loc, ThetaCut D (D.nd.mu i) (D.nd.j i) := by
    intro i
    have hne := D.nd.w_tw i
    have hy : D.plEq (D.nd.w i) ∈ S0.Tw := by
      refine (hTw _).2 fun e => hne ?_
      rw [hTup.muAt, ← hTup.mu0, e]
    have htw : D.what₂.muTw (D.nd.w i) = tup (S0.μ (D.plEq (D.nd.w i))) :=
      ((D.what₂.muAt_or _).resolve_left hne).symm.trans (hTup.muAt _)
    obtain ⟨hj1, hj2⟩ := D.nd.j_range i
    let i' : Fin m := ⟨D.nd.j i - 1, by omega⟩
    have hj : D.nd.j i = (i' : ℕ) + 1 := by simp only [i']; omega
    rw [D.nd.mu_w i, htw, hj]
    exact GlobalTheory.EtaJoin.thetaCut_of_tie D G Pl0 T m A P ψ Zs tup eMt s hOk S0 jW i' _
      (hMt i' _ hy).1 (hθ i' _ hy)
  have hSpec : ∀ i, SpecPr D i :=
    GlobalTheory.T.good_part_projector_spectral_at_every_localisation D M hHT hHR hAV Tn hStd hCS hTC hEig hIsot h42 hZ hGood
  exact GlobalTheory.etaJ_join D G Pl0 T m A P ψ Zs tup eMt s hOk hm S0 M Tn hTup hTw hMt hStd hLat hSpec

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CongruenceLengthTwistedPlacesOfHeckeIntegralityStatement
open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.congruenceLength_twistedPlaces_of_heckeIntegrality : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (m : ℕ) (A : FamIn D.what₂.LL G Pl0 T m) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (tup : T → D.what₂.Tup) (eMt : ∀ (i : Fin m) (t : T), (Fin (lDim D A P ψ i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1)) (s : ℕ), A.fam.Ok s → m ≤ D.R.m → ∀ (S0 : IndefData (A.side P ψ Zs)) (M : MtFam D) (Tn : NormalizedLocalCompatibility D M), TupTie D A S0 tup → (∀ y, y ∈ S0.Tw ↔ S0.μ y ≠ A.μ0) → (∀ (i : Fin m), ∀ y ∈ S0.Tw, FormsTie D.what₂.embLL ((D.what₂.jMt (tup (S0.μ y)) ((i : ℕ) + 1)).comp (eMt i (S0.μ y)).toLinearMap) (lH D A P ψ i (S0.μ y)) (lE D A P ψ i (S0.μ y)) (D.what₂.eMt (tup (S0.μ y)) ((i : ℕ) + 1)) ∧ OLatTie D.what₂.embLL (D.what₂.MtLat (tup (S0.μ y)) ((i : ℕ) + 1)) ((D.what₂.jMt (tup (S0.μ y)) ((i : ℕ) + 1)).comp (eMt i (S0.μ y)).toLinearMap) (lNab D A P ψ i (S0.μ y)) ∧ Idx.Z0 D (tup (S0.μ y)) ((i : ℕ) + 1) = Submodule.span ℂ (Set.range fun k => (D.what₂.jMt (tup (S0.μ y)) ((i : ℕ) + 1)) (eMt i (S0.μ y) ((lZ0 D A P ψ Zs i (S0.μ y)).mulVec (Pi.single k 1))))) → HeckeStdTw Tn.B → ∀ (Q : D.what₂.places.Pl → Finset (PlE D.host)), (∀ i, D.nd.Q i = Q (D.nd.w i)) → (∀ j h1 h2 w, D.what₂.muAt w ≠ D.what₂.mu0 → LatInt D M (Q w) j h1 h2 w) → HeckeTied D M → HeckeRational D M → AVTied D M → (∀ i : D.nd.Loc, ClassSum (M.loc i)) → ∀ (jW : ∀ i : Fin m, (Fin (S0.dW i) → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Mj ((i : ℕ) + 1)), m = D.R.m → (∀ (i : Fin m), ∀ y ∈ S0.Tw, ∀ x, D.what₂.thetaP (tup (S0.μ y)) ((i : ℕ) + 1) (D.what₂.jMt (tup (S0.μ y)) ((i : ℕ) + 1) (eMt i (S0.μ y) x)) = jW i ((S0.θ i (S0.μ y)).mulVec ((lPrj D A P ψ Zs i (S0.μ y)).mulVec x))) → D.nd.EigSpan → Rows.IsotInternal D.what₂ → Formalism.MainNotions.SumRepresentations.Conclusion42 D → Formalism.MainNotions.SumRepresentations.ConclusionZ D → GoodFTAll D → ∀ (i : Fin m) w, D.what₂.etaJ ((i : ℕ) + 1) w = @ite _ (D.plEq w ∈ S0.Tw) (Classical.propDecidable _) (A.fam.etaJ P ψ Zs i (S0.μ (D.plEq w)) (D.plEq w)) 0 := by
  first | exact @GlobalTheory.etaJ_join_closed | exact GlobalTheory.etaJ_join_closed | (intros; apply GlobalTheory.etaJ_join_closed <;> assumption)
end
