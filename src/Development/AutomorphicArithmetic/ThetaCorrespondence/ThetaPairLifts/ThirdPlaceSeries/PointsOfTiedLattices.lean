module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsTrueReading
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaLiftGeneralLinear
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.SphRead
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsBisFurther
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsBisTail
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SClose
public import Development.AutomorphicArithmetic.ThetaCorrespondence.CuspidalSupport.CuspOfCq

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.PairLiftH
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.LocLanglands GlobalTheory.LocGL
open GlobalTheory.WeilDeligne GlobalTheory.ThetaExh GlobalTheory.SplitPairLift

namespace UpperTheory.One.M

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def RepGood {T : WDTie N A} (S : Reading T) : Prop := ∀ i w hw P, GoodI ((S i w hw).rep P)

end UpperTheory.One.M
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalRepOfReadingLaws
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MRepOfLocalH
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.One.M
theorem repOfLocal_h_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ S : Reading P.T, _root_.GlobalTheory.NPin.IsFaithfulReading P S → _root_.GlobalTheory.SplitRead.LawsAlt S → ∀ i, RepOfLoc D.nd D.naut i := by
  intro hL D P S hT hLaws i P₁ P₂ hsplit hns
  apply P.H.av.inj i P₁ P₂
  refine GlobalTheory.T.algebraic_modular_forms_strong_multiplicity_one D.host.E D.R.nV (P.M.loc i).wt (P.H.av.S i P₁) (P.H.av.S i P₂) (P.H.av.irr i P₁) (P.H.av.irr i P₂) ?_ ?_
  · intro s
    have hw := GlobalTheory.T.isSplitPlace_of_splitPlace_realSubfield_host D s
    refine ⟨((S i s.w hw).rep P₁).toIrrRep, ((S i s.w hw).rep P₂).toIrrRep, hT.rep i s hw P₁, hT.rep i s hw P₂, ?_⟩
    have e1 := (S i s.w hw).locV P₁
    have e2 := (S i s.w hw).locV P₂
    rw [hsplit s.w hw, e2] at e1
    exact (_root_.UpperTheory.One.M.RecLawsH.iso (hLaws i s.w hw) _ _ _ (_root_.UpperTheory.One.M.good_cls_of_isLocS_av P i P₂ s _ (hT.rep i s hw P₂))).1 e1.symm
  · intro v hv
    obtain ⟨w, hO, hns', ⟨Dv⟩⟩ := GlobalTheory.T.exists_nonsplit_place_with_inertDatum D D.R.nV v hv
    have hsph : ∀ Q : D.naut.AV i, (P.H.av.rep i Q).SphericalAtPlace v := fun Q => by
      have h := D.nbc.embAV_sph i Q w hns'
      rw [P.H.emb i Q] at h
      exact (P.H.au.sph _ _ _ _ w v hns' hO).1 h
    obtain ⟨α₁, hα₁, e₁⟩ :=
      P.H.au.sat _ _ _ (P.H.av.rep i P₁) v w hO Dv (_root_.UpperTheory.One.M.Sph.exists_satAt_of_overPl_sphAtG _ _ _ v w hO (hsph P₁) Dv)
    obtain ⟨α₂, hα₂, e₂⟩ :=
      P.H.au.sat _ _ _ (P.H.av.rep i P₂) v w hO Dv (_root_.UpperTheory.One.M.Sph.exists_satAt_of_overPl_sphAtG _ _ _ v w hO (hsph P₂) Dv)
    have hu := hns w hns'
    rw [D.nbc.embAV_sat, D.nbc.embAV_sat, P.H.emb, P.H.emb, e₁, e₂] at hu
    refine ⟨w, Dv, α₁, hO, hα₁, ?_⟩
    obtain ⟨f, hf, hf0, U, hU, hUv, hh⟩ := hα₂
    refine ⟨f, hf, hf0, U, hU, hUv, fun h hh' => ?_⟩
    rw [GlobalTheory.T.unitarySatake_eq_of_same_unramifiedBaseChange _ Dv.ϖ Dv.σw _ D.R.nV Dv.unram α₁ α₂ hu h hh']
    exact hh h hh'
end UpperTheory.One.M
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.repOfLoc_of_isTrue_laws : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ S : Reading P.T, _root_.GlobalTheory.NPin.IsFaithfulReading P S → _root_.GlobalTheory.SplitRead.LawsAlt S → ∀ i, RepOfLoc D.nd D.naut i := by
  first | exact @_root_.UpperTheory.One.M.repOfLocal_h_alt | exact _root_.UpperTheory.One.M.repOfLocal_h_alt | (intros; apply _root_.UpperTheory.One.M.repOfLocal_h_alt <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GaloisRepLocalTypesDeterminedAtPlace
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsBisBis
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MBlockParamH
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace UpperTheory.One.M
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL
  GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.SplitRead.BlockParam GlobalTheory.LocLanglands GlobalTheory.LocGL
open GlobalTheory.WeilDeligne (WD Weil ineIncl)
section Local
variable {k : Type} [Field k] [CharZero k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {B : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver B w}
theorem charPol_unr_twist' {rc : ∀ n, Irr k n → WD h} (hrc : _root_.UpperTheory.One.M.RecLawsH rc) {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ)
    (σ : Ine (F := E) B) (c : ℂ) (hc : (rc 1 (detIrr 1 χ hχ)).charPol (ineIncl h σ) = X - C c)
    (n : ℕ) (π : Irr k n) (hn : n = 1) (α : ℂˣ)
    (e : Nonempty (π.π.Equiv (detRep (Fin n) (χ * unrChar k α)))) :
    (rc n π).charPol (ineIncl h σ) = X - C c := by
  subst hn
  let u : Irr k 1 := detIrr 1 (unrChar k α) (isSmoothChar_of_isUnram (isUnram_unrChar k α))
  have he : detRep (Fin 1) (χ * unrChar k α) = twist u.π (detChar (Fin 1) χ) := by
    show _ = twist (detRep (Fin 1) (unrChar k α)) (detChar (Fin 1) χ)
    unfold detRep ofChar
    rw [twist_twist]
    rfl
  have h1 := _root_.UpperTheory.One.M.RecLawsH.twist hrc 1 χ (detIrr 1 χ hχ) u π (good_of_one _ rfl) ⟨.refl _⟩ (he ▸ e)
  rw [h1, charPol_lpChar_of_unr _ _ ((hrc.sph 1 u).2 (isSpherical_detRep (isUnram_unrChar k α))) σ c hc,
    hrc.dim, pow_one]
theorem split_local_of_blockVec {rc : ∀ n, Irr k n → WD h} (hB : BlockSplit k) (hrc : _root_.UpperTheory.One.M.RecLawsH rc) (hs : RecSupp rc)
    {r t : ℕ} {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) (ht : IsTame χ) (π : Irr k (r + t)) (v : π.V) (hv : v ≠ 0)
    (hvb : IsBlockVec χ π.π v) (c : Ine (F := E) B → ℂ)
    (hc : ∀ σ, (rc 1 (detIrr 1 χ hχ)).charPol (ineIncl h σ) = X - C (c σ)) (γ : Ine (F := E) B)
    (hm : ((rc _ π).charPol (ineIncl h γ)).rootMultiplicity (c γ) ≤ t) :
    ∃ a b : WD h, rc _ π = a.lpSum b ∧ a.lpDim = r ∧ b.lpDim = t ∧ b.mono0 ∧
      ∀ σ, b.charPol (ineIncl h σ) = (X - C (c σ)) ^ t := by
  classical
  rcases hB r t χ π v hχ ht hv hvb with ⟨π₁, π₂, hsph, e⟩ | ⟨s, d, σ, hsupp, hcard⟩
  · have hg : GoodI π₂ := GlobalTheory.AVGood.good_of_isSpherical GlobalTheory.T.bernstein_zelevinsky_finiteness _
      (fixed_ne_bot_of_equiv (equivRep ⟨π₂.V, π₂.π, π₂.smooth, π₂.irr⟩) hsph)
    have h1 := _root_.UpperTheory.One.M.RecLawsH.twist hrc t χ (detIrr 1 χ hχ) π₂ (twistIrr π₂ χ hχ) hg ⟨.refl _⟩ ⟨.refl _⟩
    have hu := (hrc.sph t π₂).2 hsph
    refine ⟨rc r π₁, rc t (twistIrr π₂ χ hχ), hrc.prod r t π₁ _ π e, hrc.dim _ _, hrc.dim _ _, ?_, fun σ => ?_⟩
    · rw [h1, WD.monomial_char_iff _ _ (hrc.dim _ _)]
      exact WD.unr_mono0 _ hu
    · rw [h1, charPol_lpChar_of_unr _ _ hu σ _ (hc σ), hrc.dim]
  · exfalso
    set U := {a | d a = 1 ∧ ∃ α : ℂˣ, Nonempty ((σ a).π.Equiv (detRep (Fin (d a)) (χ * unrChar k α)))} with hU
    have hdvd : (X - C (c γ)) ^ U.toFinset.card ∣ (rc _ π).charPol (ineIncl h γ) := by
      rw [hs _ s π d σ hsupp, ← Finset.prod_const]
      refine dvd_trans (dvd_of_eq (Finset.prod_congr rfl fun a ha => ?_))
        (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.subset_univ U.toFinset))
      obtain ⟨h1, α, e⟩ := Set.mem_toFinset.1 ha
      exact (_root_.UpperTheory.One.M.charPol_unr_twist' hrc hχ γ _ (hc γ) _ _ h1 α e).symm
    have := (le_rootMultiplicity_iff (WD.charPol_monic _ _).ne_zero).2 hdvd
    rw [Set.ncard_eq_toFinset_card'] at hcard
    omega
end Local
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem split_param_of_typeBlock : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N) (T : WDTie N A) (S : Reading T) (i : N.Loc) (w : PlE H) (hw : IsSplitPl H w), BlockSplitAll H.E → _root_.GlobalTheory.SplitRead.LawsAlt S → SuppLaws S → TypeBlock S i w hw → (∀ σ ∈ Ine (F := H.E) (N.plOm.1 w), A.inePol (A.locG (A.muC i) w) σ = X - C (iotaO N A i (chi1 N i σ))) → ∀ P : A.AV i, (A.inePol (A.locV i P w) (N.gam0 i w)).rootMultiplicity (iotaO N A i (chi1 N i (N.gam0 i w))) ≤ R.t → ∃ a b : A.LP w, A.locV i P w = A.lpSum a b ∧ A.lpDim a = R.r ∧ A.lpDim b = R.t ∧ A.mono0 b ∧ ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w), A.inePol b σ = (X - C (iotaO N A i (chi1 N i σ))) ^ R.t := by
  intro R H what₂ N A T S i w hw hB hL hS hT hchi P hm
  haveI : CharZero (w.adicCompletion H.E) := charZero_compl w
  obtain ⟨v, hv, hvb⟩ := hT.2 P
  have hμ := (S i w hw).mu_ok.1
  rw [T.inePol w _ _ (N.locNd_chebotarevPlace_mem i w), (S i w hw).locV, WD.inePol_of_mem_Ine _ (N.locNd_chebotarevPlace_mem i w)] at hm
  obtain ⟨a, b, h1, h2, h3, h4, h5⟩ := _root_.UpperTheory.One.M.split_local_of_blockVec (hB w) (hL i w hw) (hS i w hw) hμ hT.1 _ v hv hvb
    (fun σ => iotaO N A i (chi1 N i σ.1)) (fun σ => by
      rw [← hchi σ.1 σ.2, T.inePol w _ _ σ.2, (S i w hw).locMu (detIrr 1 _ hμ) ⟨.refl _⟩,
        WD.inePol_of_mem_Ine _ σ.2]) ⟨_, N.locNd_chebotarevPlace_mem i w⟩ hm
  obtain ⟨a, rfl⟩ := (T.e w).surjective a
  obtain ⟨b, rfl⟩ := (T.e w).surjective b
  refine ⟨a, b, (T.e w).injective ?_, ?_, ?_, (T.mono0 w b).2 h4, fun σ hσ => ?_⟩
  · rw [(S i w hw).locV, h1, T.sum]
  · rw [← T.dim, h2]
  · rw [← T.dim, h3]
  · rw [T.inePol w _ _ hσ, WD.inePol_of_mem_Ine _ hσ, h5]
end UpperTheory.One.M
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead
namespace GlobalTheory.InertialTypes
theorem main_alt_alt : ∀ (D : D7) (T : WDTie D.nd D.naut) (S : Reading T), TameSplitAll D.host.E → BlockSplitAll D.host.E → _root_.GlobalTheory.SplitRead.LawsAlt S → SuppLaws S → ChiIne D.nd D.naut → (∀ i w hw, (w ∈ D.nd.Q i ∨ (w ∈ D.nd.S i ∧ ∀ k, w ∉ placesOver D.host.E (D.host.g k))) → TypeTame S i w hw) → (∀ i w hw, (w ∈ D.nd.S i ∨ w ∈ D.nd.Q i) → TypeBlock S i w hw) → Formalism.MainNotions.SumRepresentations.ArchimedeanSignatureMatching D := by
  intro D T S hTS hBS hL hS hchi hT hB
  refine ⟨fun i P w hSQ hc => ?_, fun i P w hwS _ _ hm => ?_, (GlobalTheory.RowLaws.main _ _ _ _ _ T).2.2⟩
  · have hw := D.nd.SQ_split i w hSQ
    refine _root_.GlobalTheory.TameType.inertialType_of_tame_m_alt _ _ _ _ _ T S i w hw hTS hL (hT i w hw ?_)
      (hchi i w (D.nd.SQ_l i w hSQ)) P
    by_cases hQ : w ∈ D.nd.Q i
    · exact Or.inl hQ
    · refine Or.inr ⟨hSQ.resolve_right hQ, fun k => ?_⟩
      rcases (hc.resolve_left hQ).2 with h | ⟨-, h⟩
      · exact not_mem_placesOver_of_ne D.host.pde_prime (D.host.g_prime k) (D.host.pde_ne_g k).1 h
      · exact not_mem_placesOver_of_ne D.host.pde'_prime (D.host.g_prime k) (D.host.pde_ne_g k).2 h
  · have hw := D.nd.SQ_split i w (Or.inl hwS)
    exact _root_.UpperTheory.One.M.split_param_of_typeBlock _ _ _ _ _ T S i w hw hBS hL hS (hB i w hw (Or.inl hwS))
      (hchi i w (D.nd.SQ_l i w (Or.inl hwS))) P hm
end GlobalTheory.InertialTypes
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TypeTameOfRamified
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TypeTameOfRamified
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField
  IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.TypeTame
theorem typeTame_of_ramified_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7)
    (P : CharacterChoiceData hL D) (S : Reading P.T) (hT : IsFaithfulReading P S)
    (i : D.nd.Loc) (w : PlE D.host) (hw : IsSplitPl D.host w)
    (hg : ∀ k, w ∉ placesOver D.host.E (D.host.g k))
    (htame : GlobalTheory.SplitWeil.IsTame (S i w hw).mu)
    (hram : ¬ GlobalTheory.SplitWeil.IsUnram (S i w hw).mu) : TypeTame S i w hw := by
  refine ⟨htame, hram, fun Q => ?_⟩
  obtain ⟨h1, h2⟩ := D.nd.j_range i
  let j : Fin D.R.m := ⟨D.nd.j i - 1, by omega⟩
  have hj : j.1 + 1 = D.nd.j i := by simp only [j]; omega
  have hcomp := hT.mu i w hw j hj
  obtain ⟨v, hov, hvq⟩ := GlobalTheory.T.exists_realSubfield_place_in_ramified_set D _ w hg (GlobalTheory.T.heckeChar_ramified_of_ramified_localComponent _ _ w _ hcomp hram)
  obtain ⟨s, ξ, hsv, hcs, hlp⟩ := P.H.level.para i j hj v hvq
  obtain ⟨f, hfI, hfT, hf0⟩ : ∃ f, f ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q) ∧
      f ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ ∧ f ≠ 0 := by
    obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (D.naut.typeV_ne i Q)
    rw [P.H.av.typeV] at hy
    refine ⟨(P.M.loc i).real y, hy, ?_, ?_⟩
    · rw [← (P.M.loc i).real_range]; exact ⟨y, rfl⟩
    · intro h; exact hy0 ((P.M.loc i).real_inj (h.trans (map_zero _).symm))
  obtain ⟨K, θ, hKm, hθ, hKi, hθo, hχθ⟩ := GlobalTheory.T.exists_splitPlaceParahoric_subgroup_character _ _ s D.R.r _ _ ξ hlp hcs.1
  have hfK : ∀ κ, TrivOutside {s.v} κ → ∀ h : s.loc D.R.nV κ ∈ K,
      NG.rt D.host.E D.R.nV κ f = ((θ ⟨s.loc D.R.nV κ, h⟩ : ℂˣ) : ℂ) • f := by
    intro κ hκ h
    have hJ : κ ∈ (P.M.loc i).J := (hlp.mem κ hκ).2 ((hKm _).1 h)
    rw [← hχθ κ hκ hJ h]
    exact hfT.2 ⟨κ, hJ⟩
  have hmu_eq : ∀ g (hg : NG.ParaRT s D.R.r g) (d : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ),
      (d : s.v.adicCompletion (maximalRealSubfield D.host.E)) = NG.detDD s D.R.r g →
      θ ⟨g, (hKm g).2 hg⟩ = ξ d := fun g hg d hd => hθ g _ d hd
  rcases GlobalTheory.T.eq_or_isConjPlace_of_over_splitPlace D s w (hsv ▸ hov) with hsw | hconj
  · subst hsw
    obtain ⟨c, T, hc, hci, -⟩ := hT.rep i s hw Q
    obtain ⟨u, hu0, hu⟩ := GlobalTheory.T.exists_localComponent_eigenvector_at_splitPlace_isotypic _ _ (P.M.loc i).wt (P.H.av.S i Q) (P.H.av.irr i Q) s _ (hT.rep i s hw Q) c hc hci
      K θ hKi hθo f hfI hf0 hfK
    refine ⟨u, hu0, GlobalTheory.T.isParahoricTypeVector_of_upperParahoric_eigen _ s D.R.r D.R.t _ ξ _ c hc hci hcomp.1 hcs.1 (fun k => (hcs.2 k).trans (hcomp.2 k).symm) u ?_⟩
    intro g hg d hd
    rw [← hmu_eq g hg d hd]
    exact hu g _
  · obtain ⟨hw', hci'⟩ := GlobalTheory.T.conjugateSplitPlace_eq_conjugatePlace_and_embedding D s w hconj
    subst hw'
    obtain ⟨c, T, hc, hci, -⟩ := hT.rep i (GlobalTheory.TypeTame.conjSP s) hw Q
    obtain ⟨K', θ', hK'i, hθ'o, hK'iff, hθ'eq, hK'of⟩ := GlobalTheory.T.exists_level_character_at_conjugateSplitPlace _ _ s K θ hKi hθo
    have hfK' : ∀ κ, TrivOutside {(GlobalTheory.TypeTame.conjSP s).v} κ → ∀ h' : (GlobalTheory.TypeTame.conjSP s).loc D.R.nV κ ∈ K',
        NG.rt D.host.E D.R.nV κ f = ((θ' ⟨(GlobalTheory.TypeTame.conjSP s).loc D.R.nV κ, h'⟩ : ℂˣ) : ℂ) • f := by
      intro κ hκ h'
      have h := (hK'iff κ).1 h'
      rw [hθ'eq κ h h']
      exact hfK κ hκ h
    obtain ⟨u, hu0, hu⟩ := GlobalTheory.T.exists_localComponent_eigenvector_at_splitPlace_isotypic _ _ (P.M.loc i).wt (P.H.av.S i Q) (P.H.av.irr i Q) (GlobalTheory.TypeTame.conjSP s) _
      (hT.rep i (GlobalTheory.TypeTame.conjSP s) hw Q) c hc hci K' θ' hK'i hθ'o f hfI hf0 hfK'
    have hcsd : IsCSD D.host (P.tp.tup (D.nd.mu i) j) := by
      rw [← P.chr.muC i j hj]; exact (P.chr.csd _).1 (D.naut.muC_csd i)
    refine GlobalTheory.T.exists_parahoricType_vector_at_conjugate_place _ (GlobalTheory.TypeTame.conjSP s) D.R.r D.R.t _ ξ _ c hc hci hcomp.1 htame hcs.1 ?_ u hu0 ?_
    · intro k
      have e : Units.map ((GlobalTheory.TypeTame.conjSP s).i : D.host.E →* s.v.adicCompletion (maximalRealSubfield D.host.E)) k =
          Units.map (s.i : D.host.E →* s.v.adicCompletion (maximalRealSubfield D.host.E))
            (Units.map (MonoidHom.ofClass D.host.conj) k) := by
        apply Units.ext
        exact hci' (k : D.host.E)
      have e2 := hcs.2 (Units.map (MonoidHom.ofClass D.host.conj) k)
      rw [e, e2, hcomp.2 k]
      exact hcsd.1 _ _ hconj k
    · intro g h hg hh d hd
      obtain ⟨h', e⟩ := hK'of g ((hKm g).2 hg) h hh
      rw [← hmu_eq g hg d hd, ← e]
      exact hu h h'
end GlobalTheory.TypeTame
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TypeTameOfRamifiedStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.type_tame_of_tame_not_unram : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ S : Reading P.T, _root_.GlobalTheory.NPin.IsFaithfulReading P S → ∀ i w hw, (∀ k, w ∉ placesOver D.host.E (D.host.g k)) → GlobalTheory.SplitWeil.IsTame (S i w hw).mu → ¬ GlobalTheory.SplitWeil.IsUnram (S i w hw).mu → TypeTame S i w hw := by
  first | exact @_root_.GlobalTheory.TypeTame.typeTame_of_ramified_alt | exact _root_.GlobalTheory.TypeTame.typeTame_of_ramified_alt | (intros; apply _root_.GlobalTheory.TypeTame.typeTame_of_ramified_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ChiIneMain
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead
noncomputable section
namespace GlobalTheory.SplitRead
open Formalism.MainNotions.SumRepresentations.At
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
theorem chiIne_main_alt : ∀ D : D7, Formalism.MainNotions.SumRepresentations.tie0 D → _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D → Formalism.MainNotions.SumRepresentations.adm5 D → MuInt D.nd D.naut →
    ChiIne D.nd D.naut :=
  fun D h0 h2 h5 hMu => _root_.GlobalTheory.SplitRead.chiIne_of_lp_aut_admissible_mult_one D.nd D.naut h0.1 h0.2.1 h2 h5 hMu
end GlobalTheory.SplitRead
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.TypesAtPin
theorem locComp_of_isRc_classMapD_cenLoc : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), (∀ i : D.nd.Loc, Nonempty (RowMod D P.rep (D.nd.j i))) → _root_.GlobalTheory.NRows.RowsAAlt D → Formalism.MainNotions.SumRepresentations.ArchimedeanSignatureMatching D := by
  intro pr hL D P hrow rA
  obtain ⟨S, hTrue, hLaws, hSupp⟩ := _root_.GlobalTheory.T.exists_true_reading_with_laws_suppLaws pr.fin hL D P hrow
  have hTS : TameSplitAll D.host.E := fun w => GlobalTheory.T.tameParahoricRep_splits_as_product pr.bz pr.geo pr.unl pr.mp _
  have hBS : BlockSplitAll D.host.E := fun w => GlobalTheory.T.blockTypeVector_irreducible_splits_as_product pr.bz pr.geo pr.unl pr.mp _
  have hchi : ChiIne D.nd D.naut := _root_.GlobalTheory.SplitRead.chiIne_main_alt D rA.tie0 rA.a2 rA.a5
    (GlobalTheory.MuIntegral.muInt_of_charTied D P.cf P.C P.tp P.chr)
  have hTT : ∀ i w hw, (w ∈ D.nd.Q i ∨ (w ∈ D.nd.S i ∧ ∀ k, w ∉ placesOver D.host.E (D.host.g k))) →
      TypeTame S i w hw := by
    intro i w hw h
    have hng : ∀ k, w ∉ placesOver D.host.E (D.host.g k) := by
      rcases h with hQ | ⟨-, hg⟩
      · exact not_over_g_of_mem_Q D i w hQ
      · exact hg
    have hSQ : w ∈ D.nd.S i ∨ w ∈ D.nd.Q i := by
      rcases h with hQ | ⟨hS, -⟩
      · exact Or.inr hQ
      · exact Or.inl hS
    have ht := _root_.GlobalTheory.MuTameQS.main_alt_alt hL D P S hTrue i w hw hSQ
    exact _root_.GlobalTheory.T.type_tame_of_tame_not_unram hL D P S hTrue i w hw hng ht.1 (ht.2 hng)
  have hTB : ∀ i w hw, (w ∈ D.nd.S i ∨ w ∈ D.nd.Q i) → TypeBlock S i w hw := by
    intro i w hw hSQ
    have ht := _root_.GlobalTheory.MuTameQS.main_alt_alt hL D P S hTrue i w hw hSQ
    by_cases hg : ∃ k, w ∈ placesOver D.host.E (D.host.g k)
    · exact _root_.GlobalTheory.T.type_block_of_tame_at_split_place hL D P S hTrue i w hw hg ht.1
    · have hng : ∀ k, w ∉ placesOver D.host.E (D.host.g k) := fun k hk => hg ⟨k, hk⟩
      have hT : TypeTame S i w hw := hTT i w hw (by
        rcases hSQ with hS | hQ
        · exact Or.inr ⟨hS, hng⟩
        · exact Or.inl hQ)
      refine ⟨hT.1, fun Q => ?_⟩
      obtain ⟨v, hv0, hv⟩ := hT.2.2 Q
      exact ⟨v, hv0, fun h hK h1 _ u hu => hv h hK h1 u hu⟩
  exact _root_.GlobalTheory.InertialTypes.main_alt_alt D P.T S hTS hBS hLaws hSupp hchi hTT hTB
end GlobalTheory.TypesAtPin
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanSignatureMatching_of_modules : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), (∀ i : D.nd.Loc, Nonempty (RowMod D P.rep (D.nd.j i))) → _root_.GlobalTheory.NRows.RowsAAlt D → Formalism.MainNotions.SumRepresentations.ArchimedeanSignatureMatching D := by
  first | exact @_root_.GlobalTheory.TypesAtPin.locComp_of_isRc_classMapD_cenLoc | exact _root_.GlobalTheory.TypesAtPin.locComp_of_isRc_classMapD_cenLoc | (intros; apply _root_.GlobalTheory.TypesAtPin.locComp_of_isRc_classMapD_cenLoc <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PairLiftOfHoweDualityBernstein
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.LocLanglands GlobalTheory.LocGL
open GlobalTheory.WeilDeligne GlobalTheory.ThetaExh GlobalTheory.SplitPairLift
namespace UpperTheory.One.M
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem pairLift_of_howeDuality_bernstein_alt : GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.BernsteinUnitaryProductIrreducible → ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N) (T : WDTie N A) (S : Reading T), _root_.GlobalTheory.SplitRead.LawsAlt S → RowUnit S → PairRead S → RepGood S → ∀ i, PairLift N A i := by
  intro hBZ hB R H what₂ N A T S hL hU hP hG i σ P hpair w hw
  have hne : what₂.isot (N.j i) σ ≠ ⊥ := by
    obtain ⟨f, hf, F, -, hF⟩ := hpair
    intro hb
    rw [hb, Submodule.mem_bot] at hf
    apply hF
    rw [hf, map_zero, inner_zero_right]
  have hrt : R.r < R.t := by
    have := R.rank_add_five_le
    unfold Ranks.r
    omega
  have L := hL i w hw
  set X := S i w hw with hX
  let π' := twistIrr (X.rep P) X.eta_ok.1
  let cμ := detIrr 1 X.mu_ok.1
  let τ := detIrr R.t X.mu_ok.1
  let cη := detIrr 1 X.eta_ok.1.inv
  have h1 : Nonempty (π'.π.Equiv (prod₂ (X.row σ).π τ.π)) :=
    _root_.GlobalTheory.T.theta_lift_general_linear hBZ hB _ R.r R.t X.mu _ _ (X.row σ).π π'.π hrt X.mu_ok.1 X.mu_ok.2 (X.row σ).smooth
      (X.row σ).irr (hU i w hw σ hne) π'.smooth π'.irr (hP i w hw σ P hpair)
  have h2 := L.prod _ _ (X.row σ) τ π' h1
  have h3 := L.det R.t X.mu cμ τ ⟨.refl _⟩ ⟨.refl _⟩
  have hgπ : GoodI π' := by
    have e : cls (⟨π'.V, π'.π, π'.smooth, π'.irr⟩ : IrrRep (GL (Fin (R.r + R.t)) (w.adicCompletion H.E))) = (cls (⟨(X.rep P).V, (X.rep P).π, (X.rep P).smooth, (X.rep P).irr⟩ : IrrRep (GL (Fin (R.r + R.t)) (w.adicCompletion H.E)))).tw X.eta X.eta_ok.1 :=
      (IrrGL.tw_of (X.rep P).π (X.rep P).smooth (X.rep P).irr X.eta X.eta_ok.1).symm
    show UpperTheory.Zero.LLC.Good _
    rw [e]
    exact (GlobalTheory.RecT.good_tw_iff _ _ _).2 (hG i w hw P)
  have h4 := _root_.UpperTheory.One.M.RecLawsH.twist L _ X.eta⁻¹ cη π' (X.rep P) hgπ ⟨.refl _⟩ (by
    show Nonempty ((X.rep P).π.Equiv (twist (twist (X.rep P).π (detChar _ X.eta)) (detChar _ X.eta⁻¹)))
    rw [twist_twist_inv]
    exact ⟨.refl _⟩)
  have h5 := X.locMu cμ ⟨.refl _⟩
  have h6 := X.locEta cη ⟨.refl _⟩
  have h7 : A.lpDim (A.locG A.etaTinv w) = 1 := by
    rw [← T.dim, h6, L.dim]
  apply (T.e w).injective
  unfold liftPar
  rw [T.char _ _ _ h7, T.sum, e_spehLoc, X.locV, X.locW σ hne, h4, h2, h3, h6]
  show _ = ((X.rc _ (X.row σ)).lpSum (speh (T.e w (A.locG (A.muC i) w)) R.t)).lpChar _
  rw [h5]
end UpperTheory.One.M
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.UnitarySphericalComponentOfReading
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.SplitRead
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL
  GlobalTheory.SplitWeil GlobalTheory.RowTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem unitarySphericalComponent_of_reading_alt : GlobalTheory.Published.BernsteinZelevinskyFiniteness →
    ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N) (T : WDTie N A)
      (S : Reading T), _root_.GlobalTheory.SplitRead.LawsAlt S → RowUnit S → GlobalTheory.RowSatakeBound.UnitarySphericalComponent N A := by
  intro hBZ R H what₂ N A T S hL hU i σ hσ w hw hu
  have hloc := (S i w hw).locW σ hσ
  have hsph : IsSpherical ((S i w hw).row σ).π := by
    rw [← (hL i w hw).sph _ _, ← hloc, ← T.unr]
    exact hu
  obtain ⟨α, hα⟩ := GlobalTheory.T.sphericalRepGL_exists_satakeParameters hBZ _ _ _ hsph
  have hfrob : A.frobEig (A.locW i σ w) =
      (Finset.univ.val.map fun j => (α j : ℂ)).map (·⁻¹) := by
    rw [T.frobEig w _ hu, hloc, (hL i w hw).sat _ _ α hα, Multiset.map_map]
    simp
  have h1 : GlobalTheory.RowSatakeBound.IsUnitarySatakeAt w R.r (Finset.univ.val.map fun j => (α j : ℂ)) :=
    GlobalTheory.T.isUnitarySphericalSatake_of_unitarisable_hasSatake H.E w R.r _ α hα (hU i w hw σ hσ)
  rw [hfrob]
  refine ⟨?_, ?_⟩
  · simpa [Multiset.map_map, Function.comp_def] using h1
  · have := GlobalTheory.RowSatakeBound.finite_residue w
    exact GlobalTheory.T.isUnitarySphericalSatakeMultiset_map_inv _ _ _ _ h1
end GlobalTheory.SplitRead
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowUnitOfIsTrue
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.RowUnitProof
end GlobalTheory.RowUnitProof
namespace GlobalTheory.RowUnitProof
theorem rowUnit_of_isTrue_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D),
    (∀ i : D.nd.Loc, Nonempty (RowMod D P.rep (D.nd.j i))) → ∀ S : Reading P.T, _root_.GlobalTheory.NPin.IsFaithfulReading P S → RowUnit S := by
  intro hL D P hX S hS i w hw σ hσ
  obtain ⟨X⟩ := hX i
  obtain ⟨s, rfl⟩ := exists_splitPlace_eq D w hw
  have hB00 : X.B 0 0 = 0 := by
    have h := X.lin 0 X.C.zero_mem 0 X.C.zero_mem 0 X.C.zero_mem 1
    rw [one_smul, add_zero, one_mul] at h
    linear_combination -h
  have hne : Formalism.IndefR.principalLevelFrame.isotIn (D := D) X.ρ X.C (P.rep σ) ≠ ⊥ := by
    obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hσ
    have hmem := (X.isot σ y).1 hy
    intro hbot
    rw [hbot, Submodule.mem_bot] at hmem
    apply hy0
    have h := X.φ_inner y y
    rw [hmem, hB00] at h
    exact inner_self_eq_zero.1 h
  obtain ⟨B', hlin, hherm, hpos, hinv⟩ := GlobalTheory.finTyp_invariant_form_of_isotIn D D.R.r X.A X.ρ X.C X.B X.lin X.herm
    X.pos X.stab X.inv (P.rep σ) hne
  obtain ⟨ι, T, -, -, hTinj, hTS, hTeq⟩ := hS.row i s hw σ hσ
  have hadd : ∀ x y z, B' x (y + z) = B' x y + B' x z := fun x y z => by
    simpa using hlin x y z 1
  have h0 : ∀ x, B' x 0 = 0 := fun x => by
    have h := hadd x 0 0
    rw [add_zero] at h
    linear_combination -h
  have hsmul : ∀ x (c : ℂ) y, B' x (c • y) = c * B' x y := fun x c y => by
    simpa [h0] using hlin x 0 y c
  have hadd' : ∀ x y z, B' (x + y) z = B' x z + B' y z := fun x y z => by
    rw [hherm, hadd, map_add (f := _), ← hherm, ← hherm]
  have hsmul' : ∀ (c : ℂ) x y, B' (c • x) y = starRingEnd ℂ c * B' x y := fun c x y => by
    rw [hherm, hsmul, map_mul, ← hherm]
  let Tm := LinearMap.codRestrict (P.rep σ).S T hTS
  have hTm : ∀ a, ((Tm a : (P.rep σ).S) : GAf D.host.E D.R.r → ℂ) = T a := fun _ => rfl
  refine ⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun v u => B' (Tm u) (Tm v))
    (fun _ _ _ => by simp only [map_add (f := _), hadd]) (fun _ _ _ => by simp only [map_smul, hsmul, smul_eq_mul, RingHom.id_apply])
    (fun _ _ _ => by simp only [map_add (f := _), hadd']) (fun _ _ _ => by simp only [map_smul, hsmul', smul_eq_mul]), ?_, ?_, ?_⟩
  · intro v u
    simp only [LinearMap.mk₂'ₛₗ_apply]
    exact hherm _ _
  · intro v hv
    simp only [LinearMap.mk₂'ₛₗ_apply]
    refine hpos _ fun h => hv (hTinj ?_)
    rw [map_zero]
    exact congrArg Subtype.val h
  · intro g v u
    simp only [LinearMap.mk₂'ₛₗ_apply]
    obtain ⟨x, ⟨hx, hxg⟩, -⟩ := (GlobalTheory.SplitAdelic.main D.host.E D.R.r s).2.2
      (Matrix.GeneralLinearGroup.map ι.symm.toRingHom g)
    have hg : Matrix.GeneralLinearGroup.map ι.toRingHom (s.loc D.R.r x) = g := by
      rw [hxg]
      exact Units.ext (Matrix.ext fun a b => ι.apply_symm_apply _)
    have key : ∀ a, T (((S i s.w hw).row σ).π g a) = NG.rt D.host.E D.R.r x (T a) := fun a => by
      have := hTeq x hx a
      rw [hg] at this
      exact this
    exact hinv x (Tm u) (Tm v) _ _ (key u) (key v)
end GlobalTheory.RowUnitProof
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PairReadOfJoin
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PairReadOfJoin
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.PairReadPf
end GlobalTheory.PairReadPf
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL GlobalTheory.PairReadPf in
attribute [local instance] GlobalTheory.NPin.ThetaMod.acg GlobalTheory.NPin.ThetaMod.mod in
theorem GlobalTheory.NPin.pairRead_of_join_alt : GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), _root_.GlobalTheory.NPin.CharacterChoiceJoin P → ∀ S : Reading P.T, _root_.GlobalTheory.NPin.IsFaithfulReading P S → RowUnit S → PairRead S := by
  intro hBZ hL D P J S hT hRU i w hw σ Q hPairs
  obtain ⟨s, rfl⟩ := exists_splitPlace_w D w hw
  obtain ⟨j, hj⟩ : ∃ j : Fin D.R.m, j.1 + 1 = D.nd.j i :=
    ⟨⟨D.nd.j i - 1, by have := D.nd.j_range i; omega⟩, by have := D.nd.j_range i; simp only; omega⟩
  obtain ⟨f, hf, F, hF, hne⟩ := hPairs
  have hFmem : (P.M.loc i).real F ∈ NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ := by
    have : (P.M.loc i).real F ∈ LinearMap.range (P.M.loc i).real := LinearMap.mem_range_self _ _
    rw [(P.M.loc i).real_range] at this
    exact this.1
  let X := J.rowM i
  let Θ := J.th i j hj
  let Fp : ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ) := ⟨_, hFmem⟩
  let yp : ↥X.C := ⟨X.φ f, X.φ_mem f⟩
  have h0 : Θ.Λ Θ.φ₀ Fp yp ≠ 0 := by
    rw [← Θ.read F f Fp rfl]
    intro h
    apply hne
    show inner ℂ F (LinearMap.adjoint (D.what₂.thetaP (D.nd.mu i) (D.nd.j i)) f) = 0
    rw [LinearMap.adjoint_inner_right, ← inner_conj_symm, h, map_zero]
  have hμc := hT.mu i s.w hw j hj
  have hηc := hT.eta i s.w hw
  have hloc := Θ.loc s _ _ hμc hηc
  let ℓ0 : Θ.Ω →+ ℂ := AddMonoidHom.mk' (fun φ => Θ.Λ φ Fp yp) (by intro a b; simp)
  obtain ⟨ι, φ1, hφ1, hℓ1⟩ := exists_ne_of_mem_iSup _ ℓ0 hloc h0
  obtain ⟨hLin, φ2, ⟨Φ0, rfl⟩, hℓ2⟩ := exists_ne_of_mem_iSup _ ℓ0 hφ1 hℓ1
  obtain ⟨c, hc, hci, hιeq⟩ := hLin
  have hFiso : (Fp : GAf D.host.E D.R.nV → (P.M.loc i).wt.W) ∈
      NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q) := by
    have := hF
    rw [P.H.av.typeV] at this
    exact this
  have hspan := GlobalTheory.T.isotypicPart_spanned_by_splitPlace_localComponent D.host.E D.R.nV (P.M.loc i).wt (P.H.av.S i Q) (P.H.av.irr i Q) s _
    (hT.rep i s hw Q) c hc hci
  let ℓF : ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ) →+ ℂ :=
    AddMonoidHom.mk' (fun F' => Θ.Λ (ι Φ0) F' yp) (by intro a b; simp)
  obtain ⟨T1, F1, hF1, hℓF1⟩ := exists_ne_of_mem_iSup_sub _ _
    (fun T => iSup_le fun hT1 => by rintro _ ⟨v, rfl⟩; exact hT1.1 v) ℓF Fp (hspan hFiso) hℓ2
  obtain ⟨hT1, F2, ⟨a0, ha0⟩, hℓF2⟩ := exists_ne_of_mem_iSup_sub _ _
    (fun hT1 => by rintro _ ⟨v, rfl⟩; exact hT1.1 v) ℓF F1 hF1 hℓF1
  have hσne : D.what₂.isot (D.nd.j i) σ ≠ ⊥ := by
    intro hb
    rw [hb, Submodule.mem_bot] at hf
    subst hf
    exact hne (by simp)
  have hyI : (yp : X.A) ∈ Formalism.IndefR.principalLevelFrame.isotIn (D := D) X.ρ X.C (P.rep σ) := (X.isot σ f).1 hf
  unfold Formalism.IndefR.principalLevelFrame.isotIn at hyI
  let ℓy : ↥X.C →+ ℂ := (Θ.Λ (ι Φ0) F2).toAddMonoidHom
  obtain ⟨Φe, y1, hy1, hℓy1⟩ := exists_ne_of_mem_iSup_sub X.C _
    (fun Φe => iSup_le fun h => h.2) ℓy yp hyI hℓF2
  obtain ⟨hΦe, y2, ⟨f2, hf2⟩, hℓy2⟩ := exists_ne_of_mem_iSup_sub X.C _
    (fun h => h.2) ℓy y1 hy1 hℓy1
  have hΦC : ∀ g : ↥(P.rep σ).S, Φe g ∈ X.C := fun g => hΦe.2 (LinearMap.mem_range_self _ _)
  have hspan2 := GlobalTheory.T.finiteType_spanned_by_splitPlace_localComponent D.host.E D.R.r (P.rep σ) s _ (hT.row i s hw σ hσne) c hc hci
  let ℓ2 : ↥(P.rep σ).S →+ ℂ :=
    AddMonoidHom.mk' (fun g => Θ.Λ (ι Φ0) F2 ⟨Φe g, hΦC g⟩) (by
      intro a b
      have e : (⟨Φe (a + b), hΦC (a + b)⟩ : ↥X.C) = ⟨Φe a, hΦC a⟩ + ⟨Φe b, hΦC b⟩ := by
        apply Subtype.ext; simp
      show Θ.Λ (ι Φ0) F2 ⟨Φe (a + b), hΦC (a + b)⟩ = Θ.Λ (ι Φ0) F2 ⟨Φe a, hΦC a⟩ + Θ.Λ (ι Φ0) F2 ⟨Φe b, hΦC b⟩
      rw [e, map_add (f := _)])
  have hℓ2f2 : ℓ2 f2 ≠ 0 := by
    have e : (⟨Φe f2, hΦC f2⟩ : ↥X.C) = y2 := Subtype.ext hf2
    show Θ.Λ (ι Φ0) F2 ⟨Φe f2, hΦC f2⟩ ≠ 0
    rw [e]; exact hℓy2
  obtain ⟨T2, g1, hg1, hℓg1⟩ := exists_ne_of_mem_iSup_sub _ _
    (fun T => iSup_le fun hT2 => by rintro _ ⟨v, rfl⟩; exact hT2.1 v) ℓ2 f2 (hspan2 f2.2) hℓ2f2
  obtain ⟨hT2, g2, ⟨c0, hc0⟩, hℓg2⟩ := exists_ne_of_mem_iSup_sub _ _
    (fun hT2 => by rintro _ ⟨v, rfl⟩; exact hT2.1 v) ℓ2 g1 hg1 hℓg1
  let T' : ((S i s.w hw).rep Q).V →ₗ[ℂ] ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ) :=
    T1.codRestrict _ hT1.1
  let T'' : ((S i s.w hw).row σ).V →ₗ[ℂ] ↥X.C :=
    (Φe ∘ₗ T2.codRestrict _ hT2.1).codRestrict X.C (fun v => hΦC _)
  have hT'eq : ∀ x : GAf D.host.E D.R.nV, TrivOutside {s.v} x → ∀ a,
      ((T' (((S i s.w hw).rep Q).π (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) a) :
        ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ)) : GAf D.host.E D.R.nV → (P.M.loc i).wt.W) =
        NG.rt D.host.E D.R.nV x (T' a : GAf D.host.E D.R.nV → (P.M.loc i).wt.W) :=
    fun x hx a => hT1.2 x hx a
  have hT''eq : ∀ x : GAf D.host.E D.R.r, TrivOutside {s.v} x → ∀ a,
      ((T'' (((S i s.w hw).row σ).π (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.r x)) a) : ↥X.C) : X.A) =
        X.ρ x (T'' a) := by
    intro x hx a
    have e : (⟨T2 (((S i s.w hw).row σ).π (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.r x)) a),
        hT2.1 _⟩ : ↥(P.rep σ).S) =
        ⟨NG.rt D.host.E D.R.r x (T2 a), (P.rep σ).stable x _ (hT2.1 a)⟩ := Subtype.ext (hT2.2 x hx a)
    show Φe ⟨_, _⟩ = X.ρ x (Φe ⟨T2 a, hT2.1 a⟩)
    rw [e]
    exact hΦe.1 x ⟨T2 a, hT2.1 a⟩
  let b := ((Θ.Λ ∘ₗ ι).compl₂ T').compr₂ (precompₛ T'')
  have hb0 : b Φ0 a0 c0 ≠ 0 := by
    have e1 : T' a0 = F2 := Subtype.ext ha0
    have e2 : T'' c0 = ⟨Φe g2, hΦC g2⟩ := by
      apply Subtype.ext
      show Φe ⟨T2 c0, hT2.1 c0⟩ = Φe g2
      congr 1
      exact Subtype.ext hc0
    show Θ.Λ (ι Φ0) (T' a0) (T'' c0) ≠ 0
    rw [e1, e2]
    exact hℓg2
  refine GlobalTheory.T.thetaPairing_of_invariant_trilinear_form _ D.R.r (D.R.r + D.R.t) _ _ (S i s.w hw).mu ((S i s.w hw).row σ).π
    (GlobalTheory.SmGL.twist ((S i s.w hw).rep Q).π (detChar (Fin (D.R.r + D.R.t)) (S i s.w hw).eta))
    ((hBZ _).1 (Fin D.R.r) _ _ ((S i s.w hw).row σ).smooth ((S i s.w hw).row σ).irr)
    (hRU i s.w hw σ hσne) (S i s.w hw).mu_ok.1 b (fun h => hb0 (by rw [h]; rfl)) ?_
  intro g h Φ Φ' hΦ a c'
  exact GlobalTheory.T.thetaTrilinearForm_localGroup_invariant D P.M i P.rep X _ _ Θ s (S i s.w hw).mu (S i s.w hw).eta ι c hιeq _ _
    ((S i s.w hw).rep Q).π ((S i s.w hw).row σ).π T' hT'eq T'' hT''eq g h Φ Φ' hΦ a c'
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PairReadOfJoinStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairRead_of_join_isTrue_unit :
    GlobalTheory.Published.BernsteinZelevinskyFiniteness →
      ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : CharacterChoiceData hL D),
        CharacterChoiceJoin P → ∀ S : Reading P.T, IsFaithfulReading P S → RowUnit S → PairRead S :=
  GlobalTheory.NPin.pairRead_of_join_alt
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.XiOverO
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace GlobalTheory.ResLoc
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie
  GlobalTheory.SplitRead GlobalTheory.XiOver Formalism.L2.Host
theorem xi_over_o_of_adm2 (D : D7) (C : Formalism.L2.Host.CharFrame D) (nch : NChoice D) (Tp : Formalism.L2.Host.TupTied D C nch)
    (T : Formalism.L2.Host.NCharTied D C nch Tp) (V : Formalism.L2.Host.ValLL0 D C) (hA : Formalism.MainNotions.SumRepresentations.At.TieAut D.nd D.naut)
    (h2 : _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D) (h5 : ChebSplit D.nd) : XiOverO D.nd D.naut := by
  intro i
  obtain ⟨ρ, hρ, hwd, -⟩ := (_root_.UpperTheory.GalS.weak' h2 i).2.2 D.naut.etaTinv (-(D.R.t : ℝ) / 2) (inf_int D hA)
  have hun : ∀ w, w ∉ placesOver D.host.E (D.nd.l i) → D.naut.unr (D.naut.wdOf i ρ w) := fun w hw => by
    rw [hwd w hw]
    exact (D.naut.unr_tw _ _).2 (D.naut.etaTinv_def w).1
  have hfrob : ∀ w, w ∉ placesOver D.host.E (D.nd.l i) → ∀ (B : ValuationSubring D.nd.Om) (σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om),
      IsPlaceOver (F := D.host.E) B w → IsFrob (F := D.host.E) B (normV w) σ →
      D.naut.frobEig (D.naut.lpTw (D.naut.locG D.naut.etaTinv w) (-(D.R.t : ℝ) / 2)) =
        {D.naut.iotaQC i (((ρ σ : GL (Fin 1) (Qbar (D.nd.l i))) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))) 0 0)} := by
    intro w hw B σ hB hσ
    have e := D.naut.wdOf_frob i ρ w hw hρ (hun w hw) B σ hB hσ
    obtain ⟨a, ha⟩ := Multiset.card_eq_one.1
      ((D.naut.frobEig_card _ (hun w hw)).trans (D.naut.wdOf_dim i ρ w))
    rw [ha, charpoly_fin_one] at e
    simp only [Multiset.map_singleton, Multiset.prod_singleton, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_C] at e
    have e2 := C_injective (sub_right_injective e)
    rw [← hwd w hw, ha]
    exact congrArg _ e2.symm
  let d : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* Qbar (D.nd.l i) :=
    (Units.coeHom _).comp (Matrix.GeneralLinearGroup.det.comp ρ)
  have hde : ∀ g, d g = ((ρ g : GL (Fin 1) (Qbar (D.nd.l i))) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))) 0 0 :=
    fun g => Matrix.det_fin_one _
  have hd : Continuous d := by
    have : (d : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om → Qbar (D.nd.l i)) = fun g =>
        ((ρ g : GL (Fin 1) (Qbar (D.nd.l i))) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))) 0 0 := funext hde
    rw [this]
    exact (continuous_apply_apply 0 0).comp hρ
  have hfin : (placesOver D.host.E (D.nd.l i)).Finite :=
    GlobalTheory.SplitRead.finite_placesOver _ (Fact.out : (D.nd.l i).Prime).ne_zero
  have hS : closure {σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om | ∃ w ∉ placesOver D.host.E (D.nd.l i), IsSplitPl D.host w ∧
      ∃ B : ValuationSubring D.nd.Om, IsPlaceOver (F := D.host.E) B w ∧ IsFrob (F := D.host.E) B (normV w) σ} = Set.univ := by
    have hd := (h5 hfin.toFinset).closure_eq
    convert hd using 4 with σ
    simp [Set.Finite.mem_toFinset]
  obtain ⟨ξ, hξc, hξ⟩ := exists_integral_char D.nd D.naut i d hd _ hS (by
    rintro σ ⟨w, hw, -, B, hB, hσ⟩
    obtain ⟨x, hx⟩ := frob_value D C nch Tp T V w
    have e := hfrob w hw B σ hB hσ
    rw [hx, Multiset.singleton_inj, ← D.naut.iota_LL i x, ← hde] at e
    exact ⟨_, (D.naut.iotaQC i).injective e⟩)
  refine ⟨ξ, hξc, fun w hw => ⟨fun σ hσ => ?_, fun B σ hB hσ => ?_⟩⟩
  · have h1 := (D.naut.wdOf_unr i ρ w hw hρ).1 (hun w hw) σ hσ
    apply Units.ext
    apply iota_inj D.nd D.naut i
    rw [hξ, hde, h1]
    simp
  · rw [hfrob w hw B σ hB hσ, ← hde, ← hξ]
    rfl
end
end GlobalTheory.ResLoc
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SGalIso
set_option synthInstance.maxHeartbeats 200000

section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
theorem UpperTheory.GalS.galIsoN_of_tie0_adm2_adm7 : ∀ D : D7, Formalism.MainNotions.SumRepresentations.tie0 D → _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D →
    ∀ i, UpperTheory.GalS.GalIsoN D.nd D.naut i := by
  intro D hT hG _ i P Pa hB
  obtain ⟨ρ, c, s, o, -⟩ := UpperTheory.GalS.isoRep D hT (_root_.UpperTheory.GalS.weak' hG) i P Pa hB
  exact ⟨ρ, c, s, o⟩
end
end

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.One.M
theorem UpperTheory.One.M.repGood_of_isTrue' {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) {S : Reading P.T} (hT : _root_.GlobalTheory.NPin.IsFaithfulReading P S) :
    RepGood S := by
  intro i w hw Q
  obtain ⟨s, rfl⟩ := GlobalTheory.PairReadPf.exists_splitPlace_w D w hw
  exact _root_.UpperTheory.One.M.good_cls_of_isLocS_av P i Q s _ (hT.rep i s hw Q)
namespace UpperTheory.One.M
theorem latticesB_closing_alt : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), _root_.GlobalTheory.NPin.CharacterChoiceJoin P →
    _root_.GlobalTheory.NRows.RowsAAlt D → Formalism.MainNotions.SumRepresentations.adm1 D → (∀ i : D.nd.Loc, GlobalTheory.RowCopy.LamPos D (D.nd.mu i) (D.nd.j i)) →
    GlobalTheory.NRows.RowsB D ∧ ∀ i, PairLift D.nd D.naut i ∧ SplitBC D.nd D.naut i ∧ RepOfLoc D.nd D.naut i := by
  intro hPr hL D P J hA h1 hpos
  have hRM : ∀ i : D.nd.Loc, Nonempty (RowMod D P.rep (D.nd.j i)) := fun i => ⟨J.rowM i⟩
  obtain ⟨S, hT, hLaws, -⟩ := _root_.GlobalTheory.T.exists_true_reading_with_laws_suppLaws hPr.fin hL D P hRM
  have hU : RowUnit S := _root_.GlobalTheory.RowUnitProof.rowUnit_of_isTrue_alt hL D P hRM S hT
  have hPR : PairRead S := _root_.GlobalTheory.T.pairRead_of_join_isTrue_unit hPr.bz hL D P J S hT hU
  have hpair : ∀ i, PairLift D.nd D.naut i :=
    _root_.UpperTheory.One.M.pairLift_of_howeDuality_bernstein_alt hPr.bz hPr.bern _ _ _ D.nd D.naut P.T S hLaws hU hPR (_root_.UpperTheory.One.M.repGood_of_isTrue' P hT)
  have hIf := _root_.GlobalTheory.AdmIface.main_alt_alt D
  have hcheb : ChebSplit D.nd := (hIf.2.1 hA.a5).1
  have hsplit : ∀ i, SplitBC D.nd D.naut i := fun i =>
    _root_.UpperTheory.GalS.splitBC_of_galIso _ _ _ D.nd D.naut i (_root_.UpperTheory.GalS.galIsoN_of_tie0_adm2_adm7 D hA.tie0 hA.a2 hA.temp i) hcheb hA.an2
  have hrep : ∀ i, RepOfLoc D.nd D.naut i := _root_.GlobalTheory.T.repOfLoc_of_isTrue_laws hL D P S hT hLaws
  have hbc : ∀ i, BCEx D.nd D.naut i := hIf.1 h1
  have horth : ∀ i, GlobalTheory.ThetaExh.TypeOrth D.nd D.naut i := fun i => _root_.GlobalTheory.T.type_orthogonality_of_form' hL D P i (J.form i)
  refine ⟨⟨?_, GlobalTheory.RowTie.split_theta_correspondence_of_local_pairings D hpair, _root_.GlobalTheory.T.archimedeanSignatureMatching_of_modules hPr hL D P hRM hA,
    GlobalTheory.Proof.ThetaOneGenusOne.thetaOne_of_ties D hpos hpair horth hbc hsplit hrep⟩, fun i => ⟨hpair i, hsplit i, hrep i⟩⟩
  exact GlobalTheory.RowSizeClosing.rowSize_of_unitarySphericalComponent D
    (_root_.GlobalTheory.SplitRead.unitarySphericalComponent_of_reading_alt hPr.bz _ _ _ D.nd D.naut P.T S hLaws hU)
end UpperTheory.One.M
end
section
namespace GlobalTheory.ResLoc
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal _root_.Formalism.L2 _root_.Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open GlobalTheory.EigTie (ResTied IsRowPar plRed resTied_of_plSide)
open GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting (IsGaloisRepOf Zbar GalE OnW)
open UpperTheory.One.M
theorem exists_paired_point_of_thetaT_ne_zero (hP : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt) (hH : GlobalTheory.Published.HarishChandraFinite) (hD : GlobalTheory.Published.CuspRapidDecay)
    {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} (X : _root_.GlobalTheory.NRows.LinkedData hL D) :
    GlobalTheory.ThetaExh.ParamLaws D.nd D.naut ∧ GlobalTheory.SplitRead.XiOverO D.nd D.naut ∧ (∀ i, GlobalTheory.RowTie.PairLift D.nd D.naut i) ∧
      ∀ (i : D.nd.Loc) σ, (∃ f ∈ D.what₂.isot (D.nd.j i) σ, D.what₂.thetaT (D.nd.mu i) (D.nd.j i) f ≠ 0) →
        ∃ (i' : D.nd.Loc) (P' : D.naut.AV i') (x' : D.nd.X i'), D.nd.j i' = D.nd.j i ∧ D.nd.w i' = D.nd.w i ∧
          GlobalTheory.ThetaExh.Pairs D.nd D.naut i' σ P' ∧ D.naut.ptV i' P' = some x' := by
  obtain ⟨J⟩ := _root_.GlobalTheory.T.nonempty_join_of_agree hH hD hL D X.P X.X X.agree
  have hRM : ∀ i : D.nd.Loc, Nonempty (GlobalTheory.NPin.RowMod D X.P.rep (D.nd.j i)) := fun i => ⟨J.rowM i⟩
  obtain ⟨S, hT, hLaws, -⟩ := _root_.GlobalTheory.T.exists_true_reading_with_laws_suppLaws hP.fin hL D X.P hRM
  have hU := _root_.GlobalTheory.RowUnitProof.rowUnit_of_isTrue_alt hL D X.P hRM S hT
  have hPR := _root_.GlobalTheory.T.pairRead_of_join_isTrue_unit hP.bz hL D X.P J S hT hU
  exact ⟨GlobalTheory.RowLaws.paramLaws_of_tie X.P.T,
    _root_.GlobalTheory.ResLoc.xi_over_o_of_adm2 D X.P.cf X.P.C X.P.tp X.P.chr X.P.val (_root_.GlobalTheory.AutomorphismSplitting.tieAut_and_split_alt hP.fin hL D X.P).1
      (_root_.UpperTheory.GalS.galClose_alt hP hL D X.P) (GlobalTheory.ChebSplitDense.chebSplit hP.cheb D.nd),
    _root_.UpperTheory.One.M.pairLift_of_howeDuality_bernstein_alt hP.bz hP.bern _ _ _ D.nd D.naut X.P.T S hLaws hU hPR (_root_.UpperTheory.One.M.repGood_of_isTrue' X.P hT),
    exists_pair_point D X.P.M X.P.H.hecke X.P.H.av X.P.H.cover (_root_.GlobalTheory.T.heckeStdTw_cover' hL D X.P)⟩
end GlobalTheory.ResLoc
end
end
end
