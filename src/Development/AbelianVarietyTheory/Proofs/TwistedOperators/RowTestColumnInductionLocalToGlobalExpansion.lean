module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestDoubleCosetPointsChainPlaceByPlace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeVacuumCombinationLocalModel
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatDictionaryScalarLargeDepth

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCombinationOperatorColumnProduct
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCombinationOperatorColumnProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.LocAsm

private theorem B_update_mul_eq_mul {X : ℕ → Type} (B : ∀ j, (X j → ℂ) →ₗ[ℂ] (X j → ℂ)) (j : ℕ)
    (a : (∀ i, X i) → X j → ℂ) (R : (∀ i, X i) → ℂ)
    (ha : ∀ u x, a (Function.update u j x) = a u) (hR : ∀ u x, R (Function.update u j x) = R u)
    (u : ∀ i, X i) :
    B j (fun x => a (Function.update u j x) (Function.update u j x j) * R (Function.update u j x)) (u j) =
      B j (a u) (u j) * R u := by
  have hfun : (fun x => a (Function.update u j x) (Function.update u j x j) * R (Function.update u j x)) =
      R u • a u := by
    funext x
    rw [ha, hR, Function.update_self, Pi.smul_apply, smul_eq_mul, mul_comm]
  rw [hfun, map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]

theorem exists_prod_op {X : ℕ → Type} (A : ∀ j, (X j → ℂ) →ₗ[ℂ] (X j → ℂ)) (n : ℕ) :
    ∃ Tc : ((∀ j, X j) → ℂ) →ₗ[ℂ] ((∀ j, X j) → ℂ), ∀ (C : ∀ j, X j → X (j + 1) → ℂ) (g : (∀ j, X j) → ℂ),
      (∀ u u' : ∀ j, X j, (∀ j, 2 * n ≤ j → u j = u' j) → g u = g u') →
      (fun u : ∀ j, X j => (∏ k ∈ Finset.range n,
          A (2 * k) (fun x => A (2 * k + 1) (C (2 * k) x) (u (2 * k + 1))) (u (2 * k))) * g u) =
        Tc (fun u => (∏ k ∈ Finset.range n, C (2 * k) (u (2 * k)) (u (2 * k + 1))) * g u) := by
  classical

  let op : ∀ j, ((∀ i, X i) → ℂ) →ₗ[ℂ] ((∀ i, X i) → ℂ) := fun j =>
    { toFun := fun F u => A j (fun x => F (Function.update u j x)) (u j)
      map_add' := fun F G => by
        funext u
        have e : (fun x => (F + G) (Function.update u j x)) =
            (fun x => F (Function.update u j x)) + (fun x => G (Function.update u j x)) := rfl
        rw [e, map_add (f := _)]
        rfl
      map_smul' := fun c F => by
        funext u
        have e : (fun x => (c • F) (Function.update u j x)) = c • (fun x => F (Function.update u j x)) := rfl
        rw [e, map_smul]
        rfl }
  induction n with
  | zero => exact ⟨LinearMap.id, fun C g _ => by simp⟩
  | succ n ih =>
    obtain ⟨T, hT⟩ := ih
    refine ⟨T ∘ₗ op (2 * n) ∘ₗ op (2 * n + 1), fun C g hg => ?_⟩

    obtain ⟨R, hRR⟩ : ∃ R : (∀ j, X j) → ℂ,
        R = fun u => (∏ k ∈ Finset.range n, C (2 * k) (u (2 * k)) (u (2 * k + 1))) * g u := ⟨_, rfl⟩
    have hR : ∀ j, 2 * n ≤ j → j < 2 * n + 2 → ∀ (u : ∀ i, X i) x, R (Function.update u j x) = R u := by
      intro j hj1 hj2 u x
      subst hRR
      dsimp only
      congr 1
      · refine Finset.prod_congr rfl fun k hk => ?_
        have hk' := Finset.mem_range.mp hk
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      · exact hg _ _ fun i hi => Function.update_of_ne (by omega) _ _

    obtain ⟨g', hgG⟩ : ∃ g' : (∀ j, X j) → ℂ,
        g' = fun u => A (2 * n) (fun x => A (2 * n + 1) (C (2 * n) x) (u (2 * n + 1))) (u (2 * n)) * g u :=
      ⟨_, rfl⟩
    have hg' : ∀ u u' : ∀ j, X j, (∀ j, 2 * n ≤ j → u j = u' j) → g' u = g' u' := by
      intro u u' h
      subst hgG
      dsimp only
      rw [h (2 * n) le_rfl, h (2 * n + 1) (by omega), hg u u' fun j hj => h j (by omega)]

    have h1 : op (2 * n + 1) (fun u => (∏ k ∈ Finset.range (n + 1), C (2 * k) (u (2 * k)) (u (2 * k + 1))) * g u) =
        fun u => A (2 * n + 1) (C (2 * n) (u (2 * n))) (u (2 * n + 1)) * R u := by
      have hF : (fun u => (∏ k ∈ Finset.range (n + 1), C (2 * k) (u (2 * k)) (u (2 * k + 1))) * g u) =
          fun u => (fun w : ∀ j, X j => C (2 * n) (w (2 * n))) u (u (2 * n + 1)) * R u := by
        funext u
        subst hRR
        simp only [Finset.prod_range_succ]
        ring
      rw [hF]
      funext v
      refine B_update_mul_eq_mul A (2 * n + 1) (fun w => C (2 * n) (w (2 * n))) R ?_ (hR _ (by omega) (by omega)) v
      intro w x
      show C (2 * n) (Function.update w (2 * n + 1) x (2 * n)) = C (2 * n) (w (2 * n))
      rw [Function.update_of_ne (by omega)]

    have h2 : op (2 * n) (fun u => A (2 * n + 1) (C (2 * n) (u (2 * n))) (u (2 * n + 1)) * R u) =
        fun u => (∏ k ∈ Finset.range n, C (2 * k) (u (2 * k)) (u (2 * k + 1))) * g' u := by
      funext v
      have e := B_update_mul_eq_mul A (2 * n) (fun w x => A (2 * n + 1) (C (2 * n) x) (w (2 * n + 1))) R
        (fun w y => by
          funext x
          show A (2 * n + 1) (C (2 * n) x) (Function.update w (2 * n) y (2 * n + 1)) = A (2 * n + 1) (C (2 * n) x) (w (2 * n + 1))
          rw [Function.update_of_ne (by omega)])
        (hR _ le_rfl (by omega)) v
      refine e.trans ?_
      subst hRR hgG
      dsimp only
      ring
    rw [LinearMap.comp_apply, LinearMap.comp_apply, h1, h2, ← hT C g' hg']
    funext u
    subst hgG
    simp only [Finset.prod_range_succ]
    ring

noncomputable def combLin {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ) :
    (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) where
  toFun := comb ψ S T c
  map_add' f g := by
    funext w
    simp only [comb, heisO, Finset.sum_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  map_smul' a f := by
    funext w
    simp only [comb, heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring

theorem exists_comb_op : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ c : Combs ch.G, ∃ Tc : (ColPt ch.G → ℂ) →ₗ[ℂ] (ColPt ch.G → ℂ), ∀ C : BiFam ch.G, (fun u => evT (combC ch.W c C) 1 u 0) = Tc (fun u => evT C 1 u 0) := by
  refine ⟨0, fun _ _ _ => ⟨0, fun D _ _ _ Γ _ _ Pl0 T A Ks _ _ _ R _ _ ch _ _ => ?_⟩⟩
  intro c
  obtain ⟨Tc, hTc⟩ := exists_prod_op (X := fun j => WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))))
    (fun j => combLin ch.W.ψ _ _ (c.1 j)) (D.R.m / 2)
  refine ⟨Tc, fun C => ?_⟩
  exact hTc C (fun _ => ∏ i, (1 : SchRow ch.G) i ((0 : RowPt ch.G) i)) fun _ _ _ => rfl

end GlobalTheory.LocAsm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCombinationOperatorColumnProductStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_combinationOperator_columnProduct : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ c : Combs ch.G, ∃ Tc : (ColPt ch.G → ℂ) →ₗ[ℂ] (ColPt ch.G → ℂ), ∀ C : BiFam ch.G, (fun u => evT (combC ch.W c C) 1 u 0) = Tc (fun u => evT C 1 u 0) := by
  first | exact @GlobalTheory.LocAsm.exists_comb_op | exact GlobalTheory.LocAsm.exists_comb_op | (intros; apply GlobalTheory.LocAsm.exists_comb_op <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumDatumTrivialCombinationLargeDepth
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumDatumTrivialCombinationLargeDepth
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.VacComb

variable {D : D7}

theorem eq_zero_of_isHalf_zero {m n : ℕ} {x : Mx D m n} (hx : IsHalf (0 : AE D) x) : x = 0 := by
  ext i j
  have := hx i j
  simp at this
  simpa using this.symm

theorem isHalf_zero_zero {m n : ℕ} (e : AE D) : IsHalf e (0 : Mx D m n) := by
  intro i j
  simp

theorem heisenbergSymplecticForm_zero_right_eq_zero (S T : HSp D) (x : WO S T) : symplO S T x 0 = 0 := by
  simp [symplO, hO]

theorem heisO_zero_eq_self (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f : WO S T → ℂ) : heisO ψ S T 0 f = f := by
  funext w
  simp [heisO, symplOH, heisenbergSymplecticForm_zero_right_eq_zero]

theorem heisenbergTranslationCombination_single_one_eq_translate (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) (f : WO S T → ℂ) :
    GlobalTheory.SeeSaw.comb ψ S T (Finsupp.single w 1) f = heisO ψ S T w f := by
  unfold GlobalTheory.SeeSaw.comb
  rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton, Finsupp.single_eq_same, one_smul]

theorem isFinComb_single_zero {S T : HSp D} : IsFinComb (Finsupp.single (0 : WO S T) (1 : ℂ)) := by
  intro u hu
  rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hu
  subst hu
  ext i j
  simp [Matrix.map]

theorem vacuum_isCombOf {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (t : T)
    (p : Pair T) : IsCombOf W (FinDatum.vacuum G t p) (Finsupp.single 0 1) := by
  refine ⟨isFinComb_single_zero, ?_, ?_⟩
  · intro u hu
    rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hu
    subst hu
    exact isHalf_zero_zero _
  · have he : (FinDatum.vacuum G t p).e = 0 := rfl
    intro f₀ _ _
    show AllSome _ _
    rw [heisenbergTranslationCombination_single_one_eq_translate, heisO_zero_eq_self]
    refine ⟨⟨(LinearMap.proj (R := ℂ) (φ := fun _ : WO (G.pS p) (G.pT p) => ℂ) 0).smulRight f₀, ?_, ?_, ?_⟩, ?_⟩
    · intro Φ _ x hx
      obtain rfl := eq_zero_of_isHalf_zero hx
      simp [heisO_zero_eq_self]
    · intro Φ _ y hy
      have hy0 : IsHalf (0 : AE D) y := by rw [he, map_zero] at hy; exact hy
      obtain rfl := eq_zero_of_isHalf_zero hy0
      simp [heisO_zero_eq_self, heisenbergSymplecticForm_zero_right_eq_zero]
    · have h0 : halfInd (0 : AE D) (latO (G.pS p) (G.pT p) ↑(G.latS p) ↑(G.latT p) fun _ => True) 0 = 1 := by
        rw [halfInd, if_pos ⟨zero_mem _, isHalf_zero_zero _⟩]
      rw [he]
      simp [h0]
    · intro Tm hT
      have := hT.vac
      rw [one_smul] at this
      exact this.symm

end GlobalTheory.VacComb


open GlobalTheory.VacComb in
theorem GlobalTheory.VacComb.main : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (j : Fin D.R.m), IsCombOf ch.W (FinDatum.vacuum ch.G t (.top t j)) (Finsupp.single 0 1) := by
  refine ⟨0, fun _ _ _ => ⟨0, ?_⟩⟩
  intros
  exact fun t j => vacuum_isCombOf _ t _
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumDatumTrivialCombinationLargeDepthStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuumDatum_trivialCombination_largeDepth : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (j : Fin D.R.m), IsCombOf ch.W (FinDatum.vacuum ch.G t (.top t j)) (Finsupp.single 0 1) := by
  first | exact @GlobalTheory.VacComb.main | exact GlobalTheory.VacComb.main | (intros; apply GlobalTheory.VacComb.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIdemSumPlacesUnique
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIdemSumPlacesUnique
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.IdemSumSet

theorem subset_of_isIdemSum {D : D7} {e : Formalism.L2.Theta.AE D} {P P' : Finset (Formalism.L2.DIV.Pl D.host.E)}
    (h : Formalism.IndefR.Datum.IsIdemSum e P) (h' : Formalism.IndefR.Datum.IsIdemSum e P') : P ⊆ P' := by
  intro w hw
  obtain ⟨⟨es, hes, he⟩, -⟩ := h
  obtain ⟨⟨fs, hfs, hf⟩, -⟩ := h'
  have hw' := hes w hw

  have hpick : es w * e = es w := by
    rw [he, Finset.mul_sum, Finset.sum_eq_single w]
    · exact hw'.1.1
    · intro v hv hvw
      exact (GlobalTheory.PlaceIdemUniq.idemAt_unique_orth D _ _ w v hw' (hes v hv)).2 (Ne.symm hvw)
    · intro hn
      exact absurd hw hn

  by_contra hout
  apply GlobalTheory.LevelPlaces.ne_zero_of_isIdemAt hw'
  rw [← hpick, hf, Finset.mul_sum]
  refine Finset.sum_eq_zero fun v hv => ?_
  refine (GlobalTheory.PlaceIdemUniq.idemAt_unique_orth D _ _ w v hw' (hfs v hv)).2 ?_
  rintro rfl
  exact hout hv

theorem places_eq_of_isIdemSum : ∀ (D : D7) (e : AE D) (P P' : Finset (Pl D.host.E)), IsIdemSum e P → IsIdemSum e P' → P = P' := by
  intro D e P P' h h'
  ext w
  exact ⟨fun hw => subset_of_isIdemSum h h' hw, fun hw => subset_of_isIdemSum h' h hw⟩

end GlobalTheory.IdemSumSet
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIdemSumPlacesUniqueStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIdemSum_places_unique : ∀ (D : D7) (e : AE D) (P P' : Finset (Pl D.host.E)), IsIdemSum e P → IsIdemSum e P' → P = P' := by
  first | exact @GlobalTheory.IdemSumSet.places_eq_of_isIdemSum | exact GlobalTheory.IdemSumSet.places_eq_of_isIdemSum | (intros; apply GlobalTheory.IdemSumSet.places_eq_of_isIdemSum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsPassPlaceModelsLargeDepth
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsPassPlaceModelsLargeDepth
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.FockPlace

open GlobalTheory.FinTranslate GlobalTheory.FockCompare

variable {D : D7}

theorem finPart_eInf_smul (a : AE D) : finPart D (eInf D • a) = 0 := by
  induction a using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | add a b ha hb => rw [smul_add, RingHom.map_add (f := _), ha, hb, add_zero]
  | tmul a x =>
    rw [TensorProduct.smul_tmul']
    show (sndA D.host.F (eInf D • a)) ⊗ₜ[D.host.F] x = 0
    rw [show sndA D.host.F (eInf D • a) = 0 from zero_mul _, TensorProduct.zero_tmul]

theorem infPart_eInf_smul (a : AE D) : infPart D (eInf D • a) = infPart D a := by
  induction a using TensorProduct.induction_on with
  | zero => simp only [smul_zero]
  | add a b ha hb => rw [smul_add, RingHom.map_add (f := _), ha, hb, RingHom.map_add (f := _)]
  | tmul a x =>
    rw [TensorProduct.smul_tmul']
    show (fstA D.host.F (eInf D • a)) ⊗ₜ[D.host.F] x = (fstA D.host.F a) ⊗ₜ[D.host.F] x
    rw [show fstA D.host.F (eInf D • a) = fstA D.host.F a from one_mul _]

theorem infPart_eq_zero {θ : InfFam D} (hθ : IsInfFam θ) {a : AE D} (h : ∀ τ, θ τ (infPart D a) = 0) :
    infPart D a = 0 := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have := hσ.ext (eInf D • a) (finPart_eInf_smul a) fun τ => by rw [infPart_eInf_smul, h]
  rw [← infPart_eInf_smul, this, map_zero]

variable {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

theorem exists_extension (hψ : IsStdChar D ψ (-1)) (F₀ : (WO S T → ℂ) → (WO S T → ℂ))
    (hlin : ∀ (c : ℂ) f g, IsThetaFunO ψ S T f → IsThetaFunO ψ S T g → F₀ (c • f + g) = c • F₀ f + F₀ g)
    (hcomm : ∀ u : WO S T, u.map (infPart D) = 0 → ∀ f, IsThetaFunO ψ S T f →
      F₀ (heisO ψ S T u f) = heisO ψ S T u (F₀ f)) :
    ∃ F : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ), (∀ f, IsThetaFunO ψ S T f → F f = F₀ f) ∧
      ∀ u : WO S T, u.map (infPart D) = 0 → ∀ f, F (heisO ψ S T u f) = heisO ψ S T u (F f) := by
  let U : Submodule ℂ (WO S T → ℂ) :=
    { carrier := {g | IsThetaFunO ψ S T g}
      add_mem' := fun ha hb => GlobalTheory.OrientedHeis.theta_add ha hb
      zero_mem' := GlobalTheory.OrientedHeis.theta_zero
      smul_mem' := fun c _ hg => GlobalTheory.OrientedHeis.theta_smul c hg }
  have h0 : F₀ 0 = 0 := by
    have := hlin 1 0 0 GlobalTheory.OrientedHeis.theta_zero GlobalTheory.OrientedHeis.theta_zero
    rw [one_smul, one_smul, add_zero] at this
    exact left_eq_add.1 this
  let L₀ : U →ₗ[ℂ] (WO S T → ℂ) :=
    { toFun := fun g => F₀ g
      map_add' := fun a b => by
        have := hlin 1 a b a.2 b.2
        rwa [one_smul, one_smul] at this
      map_smul' := fun c a => by
        have := hlin c a 0 a.2 GlobalTheory.OrientedHeis.theta_zero
        rwa [add_zero, h0, add_zero] at this }
  obtain ⟨L, hL⟩ := L₀.exists_extend
  have hL' : ∀ g, IsThetaFunO ψ S T g → L g = F₀ g := fun g hg => LinearMap.congr_fun hL ⟨g, hg⟩
  have hr : ∀ w : WO S T, (eInf D • w).map (finPart D) = 0 := fun w =>
    Matrix.ext fun i j => finPart_eInf_smul (w i j)
  have hf : ∀ w : WO S T, (w - eInf D • w).map (infPart D) = 0 := fun w => Matrix.ext fun i j => by
    show infPart D (w i j - eInf D • w i j) = 0
    rw [RingHom.map_sub, infPart_eInf_smul, sub_self]
  let F : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) :=
    LinearMap.pi fun w => (LinearMap.proj (eInf D • w) : (WO S T → ℂ) →ₗ[ℂ] ℂ) ∘ₗ L ∘ₗ heisL S T ψ (w - eInf D • w)
  have hF : ∀ g w, F g w = L (heisO ψ S T (w - eInf D • w) g) (eInf D • w) := fun _ _ => rfl
  refine ⟨F, fun f h => funext fun w => ?_, fun u hu f => funext fun w => ?_⟩
  · rw [hF, hL' _ (isThetaFunO_heisO hψ.1.1 hψ.1.2.1 h (hf w)), hcomm _ (hf w) f h, heisO,
      symplOH_real_fin (hf w) (hr w), ψ.map_zero_eq_one, one_mul, add_sub_cancel]
  · have e : symplOH S T w u = symplOH S T (w - eInf D • w) u := by
      conv_lhs => rw [← sub_add_cancel w (eInf D • w)]
      rw [symplOH_add_left, symplOH_real_fin hu (hr w), add_zero]
    rw [hF, heisO_heisO, map_smul, heisO, hF, smul_add, smul_fin hu, add_zero, e, add_sub_right_comm]
    rfl

theorem eq_zero_of_fixed (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (hS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) (hT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ))
    (τ : D.what₂.Tau) (i : Fin T.rank) (j : Fin S.rank) {g : WO S T → ℂ}
    (hg : ∀ y : WO S T, y.map (finPart D) = 0 → (∀ τ', τ' ≠ τ → ∀ a b, θ τ' (infPart D (y a b)) = 0) →
      heisO ψ S T y g = g) : g = 0 := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨om, J, h1, h2, -, -, -, h3⟩ := GlobalTheory.OrientedRealForm.exists_real_form D ψ θ S T sS sT hψ hθ hS hT
  let z : RW T S := fun τ' _ _ => if τ' = τ then 1 else 0
  have hz : z ≠ 0 := fun h => by simpa [z] using congrFun (congrFun (congrFun h τ) i) j
  have hz' : ∀ τ', τ' ≠ τ → z τ' = 0 := fun τ' h => by
    funext a b
    simp [z, h]
  have hp := h3 z hz
  have key : ∀ x : RW T S, (∀ τ', τ' ≠ τ → x τ' = 0) → heisO ψ S T (iotaW σ T S x) g = g := fun x hx =>
    hg _ (hσ.real_iota T S x) fun τ' h a b =>
      (congrFun (congrFun (congrFun (hσ.pi_iota T S x) τ') a) b).trans (by rw [hx τ' h]; rfl)
  have a1 : ∀ τ', τ' ≠ τ → ((om z (J z))⁻¹ • z) τ' = 0 := fun τ' h => by rw [Pi.smul_apply, hz' τ' h, smul_zero]
  have a2 : ∀ τ', τ' ≠ τ → (J z) τ' = 0 := fun τ' h => by
    rw [h2, hz' τ' h]
    show Complex.I • (sT τ' * (0 : Matrix (Fin T.rank) (Fin S.rank) ℂ) * sS τ') = 0
    rw [Matrix.mul_zero, Matrix.zero_mul, smul_zero]
  have a3 := key ((om z (J z))⁻¹ • z + J z) fun τ' h => by rw [Pi.add_apply, a1 τ' h, a2 τ' h, add_zero]
  have e := heisO_heisO S T ψ (iotaW σ T S ((om z (J z))⁻¹ • z)) (iotaW σ T S (J z)) g
  rw [map_add (f := _)] at a3
  rw [key _ a2, key _ a1, h1 _ _ (hσ.real_iota T S _), hσ.pi_iota, hσ.pi_iota, map_smul, LinearMap.smul_apply,
    smul_eq_mul, inv_mul_cancel₀ hp.ne', Complex.ofReal_one, mul_one, Complex.exp_neg, Complex.exp_pi_mul_I] at e
  erw [a3] at e
  funext w
  have := congrFun e w
  rw [Pi.smul_apply, smul_eq_mul] at this
  show g w = 0
  linear_combination (1 / 2 : ℂ) * this

theorem isSBHalf_halfInd (e : AE D) (Λ : AddSubgroup (WO S T)) : IsSBHalf e Λ (halfInd e Λ) := by
  have h : ∀ t, halfInd e Λ t ≠ 0 → t ∈ Λ ∧ IsHalf e t := fun t ht => by
    by_contra hn
    exact ht (if_neg hn)
  refine ⟨fun t ht => (h t ht).2, 1, one_pos, fun u hu hu' t => ?_, fun t ht => by rw [one_smul]; exact (h t ht).1⟩
  rw [one_smul]
  unfold halfInd
  refine if_congr (and_congr (Λ.add_mem_cancel_right hu) (forall₂_congr fun i j => ?_)) rfl rfl
  rw [Matrix.add_apply, mul_add, hu' i j, add_left_inj]

theorem placeModel_eq_zero (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (hS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) (hT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ))
    {e : AE D} {Λ : AddSubgroup (WO S T)} (hΛ : ∀ u ∈ Λ, (u : WO S T).map (infPart D) = 0) {c : ℂ} {f₀ : WO S T → ℂ}
    {Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)} (hTm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ c f₀ Tm)
    {x : WO S T} (hx : IsHalf e x ∨ IsHalf (cA D e) x) (hx' : x.map (infPart D) ≠ 0)
    {Φ : WO S T → ℂ} (hΦ : IsSBHalf e Λ Φ) : Tm Φ = 0 := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have h1 : ∃ i j τ, θ τ (infPart D (x i j)) ≠ 0 := by
    by_contra! h
    exact hx' (Matrix.ext fun i j => infPart_eq_zero hθ (h i j))
  obtain ⟨i, j, τ, h1⟩ := h1
  have hc : θ τ (infPart D (cA D e)) = starRingEnd ℂ (θ τ (infPart D e)) := comp_cA hθ τ e
  have h2 : θ τ (infPart D (cA D e)) = 1 := by
    rcases hx with hx | hx
    · have := congrArg (fun a => θ τ (infPart D a)) (hx i j)
      simp only [RingHom.map_mul] at this
      rw [hc, (mul_eq_right₀ h1).1 this, map_one]
    · have := congrArg (fun a => θ τ (infPart D a)) (hx i j)
      simp only [RingHom.map_mul] at this
      exact (mul_eq_right₀ h1).1 this
  refine eq_zero_of_fixed hψ hθ hS hT τ i j fun y hy hy' => ?_
  have h3 : IsHalf (cA D e) y := fun a b => by
    have hf : finPart D (y a b) = 0 := congrFun (congrFun hy a) b
    rw [← sub_eq_zero]
    refine hσ.ext _ (by rw [RingHom.map_sub, RingHom.map_mul, hf, mul_zero, sub_zero]) fun τ' => ?_
    rw [RingHom.map_sub, RingHom.map_mul, RingHom.map_sub, RingHom.map_mul]
    by_cases h : τ' = τ
    · rw [h, h2, one_mul, sub_self]
    · rw [hy' τ' h, mul_zero, sub_zero]
  rw [← hTm.modul Φ hΦ y h3]
  congr 1
  funext t
  by_cases ht : Φ t = 0
  · rw [ht, mul_zero]
  obtain ⟨-, k, hk, -, h4⟩ := hΦ
  have h5 : t.map (infPart D) = 0 := Matrix.ext fun a b => infPart_eq_zero hθ fun τ' => by
    have h6 : infPart D (k • t a b) = 0 := congrFun (congrFun (hΛ _ (h4 t ht)) a) b
    have h7 := congrArg (θ τ') h6
    have h9 : θ τ' (infPart D (k • t a b)) = k • θ τ' (infPart D (t a b)) :=
      ((θ τ').comp (infPart D)).toAddMonoidHom.map_nsmul k (t a b)
    rw [h9, RingHom.map_zero, nsmul_eq_mul] at h7
    exact (mul_eq_zero.1 h7).resolve_left (Nat.cast_ne_zero.2 hk.ne')
  have h8 : symplO S T t y = 0 :=
    Prod.ext (GlobalTheory.OrientedHeis.fst_symplO (Or.inl h5)) (GlobalTheory.OrientedHeis.snd_symplO (Or.inr hy))
  rw [h8, ψ.map_zero_eq_one, one_mul]

theorem isThetaAt_map {e : AE D} {Λ : AddSubgroup (WO S T)} {c : ℂ} {f₀ Φ f : WO S T → ℂ}
    (F : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ))
    (hF : ∀ x, IsHalf e x ∨ IsHalf (cA D e) x → ∀ g, F (heisO ψ S T x g) = heisO ψ S T x (F g))
    (h : IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ c f₀ Φ f) :
    IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ c (F f₀) Φ (F f) := by
  obtain ⟨⟨Tm, hT⟩, hall⟩ := h
  have hT' : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ c (F f₀) (F ∘ₗ Tm) :=
    { trans := fun Φ hΦ x hx => by
        rw [LinearMap.comp_apply, LinearMap.comp_apply, hT.trans Φ hΦ x hx, hF x (Or.inl hx)]
      modul := fun Φ hΦ y hy => by
        rw [LinearMap.comp_apply, LinearMap.comp_apply, hT.modul Φ hΦ y hy, hF y (Or.inr hy)]
      vac := by rw [LinearMap.comp_apply, hT.vac] }
  refine ⟨⟨_, hT'⟩, fun T₁ h₁ => ?_⟩
  have hh : ∀ x a b d, heisO ψ S T x (a + (b - d)) = heisO ψ S T x a + (heisO ψ S T x b - heisO ψ S T x d) :=
    fun x a b d => ((heisL S T ψ x).map_add _ _).trans (congrArg _ ((heisL S T ψ x).map_sub _ _))
  have h₂ : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ c f₀ (Tm + (T₁ - F ∘ₗ Tm)) :=
    { trans := fun Φ hΦ x hx => by
        rw [LinearMap.add_apply, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.sub_apply, hT.trans Φ hΦ x hx,
          h₁.trans Φ hΦ x hx, hT'.trans Φ hΦ x hx, hh]
      modul := fun Φ hΦ y hy => by
        rw [LinearMap.add_apply, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.sub_apply, hT.modul Φ hΦ y hy,
          h₁.modul Φ hΦ y hy, hT'.modul Φ hΦ y hy, hh]
      vac := by rw [LinearMap.add_apply, LinearMap.sub_apply, hT.vac, h₁.vac, hT'.vac, sub_self, add_zero] }
  have e1 : f = Tm Φ := hall Tm hT
  have e2 : f = (Tm + (T₁ - F ∘ₗ Tm)) Φ := hall _ h₂
  rw [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply, ← e1] at e2
  exact (sub_eq_zero.1 (left_eq_add.1 e2)).symm

theorem isThetaAt_pureTensorO (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (hS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) (hT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ))
    (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    {e : AE D} {Λ : AddSubgroup (WO S T)} (hΛ : ∀ u ∈ Λ, (u : WO S T).map (infPart D) = 0) {f₀ Φ f : WO S T → ℂ}
    (h₀ : IsThetaFunO ψ S T f₀) (hΦ : IsSBHalf e Λ Φ) (h : IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Φ f)
    (P : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ 1 (pureTensorO ψ θ S T sS sT BS BT f₀ P) Φ
      (pureTensorO ψ θ S T sS sT BS BT f P) := by
  obtain ⟨F, hF, hF'⟩ := exists_extension hψ (fun g => pureTensorO ψ θ S T sS sT BS BT g P)
    (fun c f g hf hg => GlobalTheory.FockFiniteHeis.pureTensorO_lin ψ θ S T hψ hθ sS BS sT BT c hf hg P)
    (fun u hu f hf => ((finite_translate D ψ θ S T hψ hθ f hf).2 u hu).2 sS BS sT BT P)
  have hf := GlobalTheory.GalLift.Vec.theta_of_thetaAt hψ hθ h h₀
  have e₀ : F f₀ = pureTensorO ψ θ S T sS sT BS BT f₀ P := hF f₀ h₀
  have e₁ : F f = pureTensorO ψ θ S T sS sT BS BT f P := hF f hf
  rw [← e₀, ← e₁]
  by_cases hx : ∀ x : WO S T, IsHalf e x ∨ IsHalf (cA D e) x → x.map (infPart D) = 0
  · exact isThetaAt_map F (fun x h => hF' x (hx x h)) h
  · push_neg at hx
    obtain ⟨x, hx, hx'⟩ := hx
    obtain ⟨Tm, hTm⟩ := h.1
    have a : f₀ = 0 := by
      rw [← hTm.vac, one_smul]
      exact placeModel_eq_zero hψ hθ hS hT hΛ hTm hx hx' (isSBHalf_halfInd e Λ)
    have b : f = 0 := (h.2 Tm hTm).trans (placeModel_eq_zero hψ hθ hS hT hΛ hTm hx hx' hΦ)
    subst a b
    rwa [map_zero]

theorem main : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (e : AE D) (v f : SchDown ch.G t) (P : PolDown ch.G) (j : Fin D.R.m) (φ : WO (ch.G.pS (.mu t D.R.m j)) (ch.G.pT (.mu t D.R.m j)) → ℂ), IsThetaFunO ch.W.ψ _ _ (v j) → IsLocVec ch.W (.mu t D.R.m j) e (v j) φ (f j) → IsThetaFunO ch.W.ψ _ _ (fockD ch.W t v P j) ∧ IsLocVec ch.W (.mu t D.R.m j) e (fockD ch.W t v P j) φ (fockD ch.W t f P j) := by
  refine ⟨0, fun _ _ _ => ⟨0, fun D _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ch _ _ t e v f P j φ hv h => ?_⟩⟩
  exact ⟨GlobalTheory.GalLift.Vec.theta_pureTensorO ch.W.ψ_std ch.W.θ_is _ _ _ _ hv (P j), h.1,
    isThetaAt_pureTensorO ch.W.ψ_std ch.W.θ_is (ch.W.cart_is (.grid D.R.m j) ⟨le_rfl, j.2.le⟩)
      (ch.W.cart_is (.grid D.R.m (j + 1)) ⟨le_rfl, j.2⟩) _ _ (fun _ hu => GlobalTheory.VacGood.infPart_latO hu) hv h.1 h.2 (P j)⟩

end GlobalTheory.FockPlace

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsPassPlaceModelsLargeDepthStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockVectors_pass_placeModels_largeDepth : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (e : AE D) (v f : SchDown ch.G t) (P : PolDown ch.G) (j : Fin D.R.m) (φ : WO (ch.G.pS (.mu t D.R.m j)) (ch.G.pT (.mu t D.R.m j)) → ℂ), IsThetaFunO ch.W.ψ _ _ (v j) → IsLocVec ch.W (.mu t D.R.m j) e (v j) φ (f j) → IsThetaFunO ch.W.ψ _ _ (fockD ch.W t v P j) ∧ IsLocVec ch.W (.mu t D.R.m j) e (fockD ch.W t v P j) φ (fockD ch.W t f P j) := by
  first | exact @GlobalTheory.FockPlace.main | exact GlobalTheory.FockPlace.main | (intros; apply GlobalTheory.FockPlace.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIdemSumEqSumSinglePlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIdemSumEqSumSinglePlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory.IdemSingleSum

theorem sum_mul_sum_orth {R ι : Type} [Ring R] [DecidableEq ι] (f : ι → R) (hid : ∀ i, f i * f i = f i)
    (horth : ∀ i j, i ≠ j → f i * f j = 0) (S S' : Finset ι) :
    (∑ i ∈ S, f i) * (∑ j ∈ S', f j) = ∑ i ∈ S ∩ S', f i := by
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  calc ∑ i ∈ S, ∑ j ∈ S', f i * f j = ∑ i ∈ S, if i ∈ S' then f i else 0 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases hi : i ∈ S'
        · rw [if_pos hi, Finset.sum_eq_single_of_mem i hi fun j _ hji => horth i j (Ne.symm hji), hid]
        · rw [if_neg hi]
          exact Finset.sum_eq_zero fun j hj => horth i j fun hij => hi (by rw [hij]; exact hj)
    _ = ∑ i ∈ S ∩ S', f i := Finset.sum_ite_mem S S' f

theorem isIdemAt_of_single {D : D7} {a : AE D} {w : Pl D.host.E} (h : IsIdemSum a {w}) :
    Formalism.L2.NTheta.IsIdemAt a w := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := h
  simpa using hes w (Finset.mem_singleton_self w)

private theorem mul_self_eq_of_isIdemAt {D : D7} {x : AE D} {w : Formalism.L2.DIV.Pl D.host.E}
    (hx : Formalism.L2.NTheta.IsIdemAt x w) : x * x = x := by
  have h := GlobalTheory.PartialIdemSum.mul_sum_of_isIdemAt hx {w} (fun _ => x) (by simpa using hx)
  simpa only [Finset.sum_singleton, Finset.mem_singleton_self, if_true] using h

private theorem mul_eq_zero_of_isIdemAt_of_ne {D : D7} {x y : AE D} {w w' : Formalism.L2.DIV.Pl D.host.E}
    (hx : Formalism.L2.NTheta.IsIdemAt x w) (hy : Formalism.L2.NTheta.IsIdemAt y w') (hne : w ≠ w') : x * y = 0 := by
  have h := GlobalTheory.PartialIdemSum.mul_sum_of_isIdemAt hx {w'} (fun _ => y) (by simpa using hy)
  rwa [Finset.sum_singleton, if_neg (by simpa using hne)] at h

private theorem eq_of_isIdemAt_of_isIdemAt {D : D7} {x y : AE D} {w : Formalism.L2.DIV.Pl D.host.E}
    (hx : Formalism.L2.NTheta.IsIdemAt x w) (hy : Formalism.L2.NTheta.IsIdemAt y w) : x = y := by
  have h1 := GlobalTheory.PartialIdemSum.mul_sum_of_isIdemAt hx {w} (fun _ => y) (by simpa using hy)
  have h2 := GlobalTheory.PartialIdemSum.mul_sum_of_isIdemAt hy {w} (fun _ => x) (by simpa using hx)
  simp only [Finset.sum_singleton, Finset.mem_singleton_self, if_true] at h1 h2
  calc x = x * y := h1.symm
    _ = y * x := mul_comm x y
    _ = y := h2

theorem sum_single : ∀ (D : D7) (e : AE D) (P : Finset (Pl D.host.E)), IsIdemSum e P → ∀ (eL : P → AE D), (∀ w, IsIdemSum (eL w) {w.1}) → e = ∑ w, eL w ∧ (∀ S : Finset P, IsIdemSum (∑ w ∈ S, eL w) (S.map (Function.Embedding.subtype _))) ∧ ∀ S S' : Finset P, (∑ w ∈ S, eL w) * (∑ w ∈ S', eL w) = ∑ w ∈ S ∩ S', eL w := by
  intro D e P he eL hL
  obtain ⟨⟨es, hes, hsum⟩, he0⟩ := he
  have hat : ∀ w : P, Formalism.L2.NTheta.IsIdemAt (eL w) w.1 := fun w => isIdemAt_of_single (hL w)
  have hprod : ∀ S S' : Finset P, (∑ w ∈ S, eL w) * (∑ w ∈ S', eL w) = ∑ w ∈ S ∩ S', eL w := fun S S' =>
    sum_mul_sum_orth eL (fun w => mul_self_eq_of_isIdemAt (hat w))
      (fun w w' hne => mul_eq_zero_of_isIdemAt_of_ne (hat w) (hat w') fun h => hne (Subtype.ext h)) S S'
  have htot : e = ∑ w, eL w := by
    rw [hsum, ← Finset.sum_coe_sort P es]
    exact Finset.sum_congr rfl fun w _ => (eq_of_isIdemAt_of_isIdemAt (hat w) (hes w.1 w.2)).symm
  refine ⟨htot, fun S => ⟨⟨es, ?_, ?_⟩, ?_⟩, hprod⟩
  · intro PP hPP
    obtain ⟨w, -, rfl⟩ := Finset.mem_map.1 hPP
    exact hes w.1 w.2
  · rw [Finset.sum_map]
    exact Finset.sum_congr rfl fun w _ => eq_of_isIdemAt_of_isIdemAt (hat w) (hes w.1 w.2)
  · have hse : (∑ w ∈ S, eL w) * e = ∑ w ∈ S, eL w := by
      rw [htot, hprod, Finset.inter_univ]
    set s := ∑ w ∈ S, eL w
    calc s * cA D s = (s * e) * cA D (e * s) := by rw [hse, mul_comm e s, hse]
      _ = s * (e * cA D e) * cA D s := by rw [map_mul]; ring
      _ = 0 := by rw [he0, mul_zero, zero_mul]

end GlobalTheory.IdemSingleSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIdemSumEqSumSinglePlacesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIdemSum_eq_sum_singlePlaces : ∀ (D : D7) (e : AE D) (P : Finset (Pl D.host.E)), IsIdemSum e P → ∀ (eL : P → AE D), (∀ w, IsIdemSum (eL w) {w.1}) → e = ∑ w, eL w ∧ (∀ S : Finset P, IsIdemSum (∑ w ∈ S, eL w) (S.map (Function.Embedding.subtype _))) ∧ ∀ S S' : Finset P, (∑ w ∈ S, eL w) * (∑ w ∈ S', eL w) = ∑ w ∈ S ∩ S', eL w := by
  first | exact @GlobalTheory.IdemSingleSum.sum_single | exact GlobalTheory.IdemSingleSum.sum_single | (intros; apply GlobalTheory.IdemSingleSum.sum_single <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColumnAtReadsPlacePartLargeDepth
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColumnAtReadsPlacePartLargeDepth
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.ColAtPart

theorem colAt_smul_of_mul_idem : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (w : locPl ch.G t) (eL e' : AE D), IsIdemSum eL {w.1} → e' * eL = eL → ∀ u : ∀ j : Fin D.R.m, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))), ch.S.colAt t w.1 (fun j => e' • u j) = ch.S.colAt t w.1 u := by
  unfold Big
  refine ⟨0, fun _ _ _ => ⟨0, ?_⟩⟩
  intros
  beta_reduce
  intro t w eL e' hL he u
  have hw := (GlobalTheory.FunObj.Comparison₂.cpt_idemSum hL).2.1 w.1 (Finset.mem_singleton_self _)

  have h1 := congrArg ((cpt w.1).comp (toEAf _)) he
  simp only [map_mul, RingHom.comp_apply, hw, mul_one] at h1
  funext j
  simp only [GridChoice.colAt]
  split_ifs with hj
  · congr 1
    congr 1
    congr 1
    ext a b
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, RingHom.comp_apply, map_mul, h1, one_mul]
  · rfl

end GlobalTheory.ColAtPart
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColumnAtReadsPlacePartLargeDepthStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnAt_reads_placePart_largeDepth : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (w : locPl ch.G t) (eL e' : AE D), IsIdemSum eL {w.1} → e' * eL = eL → ∀ u : ∀ j : Fin D.R.m, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))), ch.S.colAt t w.1 (fun j => e' • u j) = ch.S.colAt t w.1 u := by
  first | exact @GlobalTheory.ColAtPart.colAt_smul_of_mul_idem | exact GlobalTheory.ColAtPart.colAt_smul_of_mul_idem | (intros; apply GlobalTheory.ColAtPart.colAt_smul_of_mul_idem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestColumnInductionLocalToGlobalExpansion
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.LocAsm


set_option maxHeartbeats 1000000 in
theorem columnInduction : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (s : ℤˣ) (t : T) (β : CosFam ch.G t) (ζ : locPl ch.G t → ℂ), (∀ w : locPl ch.G t, GlobalTheory.LocAsm.PlaceCl ch s t w (β w) (ζ w)) → ∀ (M : Vol ch.G) (hM : M.Is t) (b b₀ : Pts ch.G), IsRep t ch.S.B s β b → IsBase t ch.S.B b₀ → ∀ e : AE D, IsIdemSum e (locPl ch.G t) → ∀ (φ : (∀ w : locPl ch.G t, ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid ch.G t w.1).rank b.tgt)) (Fin ((locGrid ch.G t w.1).rank b.src)) (Kw w.1) → ℂ)), (∀ w : locPl ch.G t, ∀ b ∈ GlobalTheory.SplitFlip.oppositePath D.R.m, GlobalTheory.SplitFlip.IsNatDatum (unifAt w.1) (depthAt ch.G w.1) (φ w b)) → ∀ (fd : SchDown ch.G t), (∀ j : Fin D.R.m, IsLocVec ch.W (.mu t D.R.m j) e (ch.rm.vT D.R.m j) (fun y => if IsHalf e y then ∏ w : locPl ch.G t, φ w (.theta D.R.m j) (ch.S.B.coord t w.1 (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) (fd j)) → ∀ (eL : locPl ch.G t → AE D), (∀ w, IsIdemSum (eL w) {w.1}) → ∀ (I : locPl ch.G t → Type) (S : ∀ w, Finset (I w)) (x : ∀ w, I w → ℂ) (d : ∀ w, I w → ∀ j : Fin D.R.m, FinDatum ch.G t (.top t j)) (c : ∀ w, I w → Combs ch.G), (∀ w, ∀ i ∈ S w, ∀ j : Fin D.R.m, (d w i j).e = eL w ∧ IsCombOf ch.W (d w i j) ((c w i).1 j)) → (∀ w (y : ∀ j : Fin D.R.m, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1)))), (∀ j, IsHalf (eL w) (y j)) → ∑ i ∈ S w, x w i * ∏ j, (d w i j).fn (y j) = flatTensor one_le_sLen (psiAt ch.W w.1) (unitVol w.1) (moved (locGrid ch.G t w.1) (keepAt ch.G w.1) ((repsAt ch.G t w.1).elt (β w)) ((locGrid ch.G t w.1).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) (GlobalTheory.LocAsm.exOne (φ w)))) (ch.S.colAt t w.1 y) 0) → ∃ (J : Type) (SJ : Finset J) (xJ : J → ℂ) (dJ : J → ∀ j : Fin D.R.m, FinDatum ch.G t (.top t j)) (cJ : J → ∀ j : ℕ, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))) →₀ ℂ), (∀ a ∈ SJ, ∀ j : Fin D.R.m, (dJ a j).e = e ∧ IsCombOf ch.W (dJ a j) (cJ a j)) ∧ (∀ u : ∀ j : Fin D.R.m, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))), (∀ j, IsHalf e (u j)) → ∑ a ∈ SJ, xJ a * ∏ j, (dJ a j).fn (u j) = ∏ w : locPl ch.G t, flatTensor one_le_sLen (psiAt ch.W w.1) (unitVol w.1) (moved (locGrid ch.G t w.1) (keepAt ch.G w.1) ((repsAt ch.G t w.1).elt (β w)) ((locGrid ch.G t w.1).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) (GlobalTheory.LocAsm.exOne (φ w)))) (ch.S.colAt t w.1 u) 0) ∧ ∀ (P : PolDown ch.G) (p : Pts ch.G), IsRealPt p → ∀ u : ColPt ch.G, evT (conAt ch.W hM (fockD ch.W t fd P) (p * b)) 1 u 0 = (∏ w, ζ w) * ∑ a ∈ SJ, xJ a * evT (combC ch.W (cJ a, 0) (conAt ch.W hM (fockD ch.W t (fun j => ch.rm.vT D.R.m j) P) (p * b₀))) 1 u 0 := by
  refine big_mono (fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch h => ?_)
    (((GlobalTheory.T.rowTest_doubleCosetPoints_chain_place_by_place.and GlobalTheory.T.subset_place_vectors_and_steps).and (GlobalTheory.T.fockVectors_pass_placeModels_largeDepth.and GlobalTheory.T.exists_combinationOperator_columnProduct)).and ((GlobalTheory.T.columnCombinations_compose_largeDepth.and GlobalTheory.T.productFiniteDatum_largeDepth).and (GlobalTheory.T.columnAt_reads_placePart_largeDepth.and GlobalTheory.T.vacuumDatum_trivialCombination_largeDepth)))
  obtain ⟨⟨⟨hA, hB⟩, hC, hD⟩, ⟨hE, hF⟩, hG, hZ⟩ := h
  intro s t β ζ hζ M hM b b₀ hb hb₀ e he φ hφ fd hfd eL heL I S x d c hdc hexp
  obtain ⟨he_sum, hsub, hmul⟩ := GlobalTheory.T.isIdemSum_eq_sum_singlePlaces D e (locPl ch.G t) he eL heL
  obtain ⟨V, hV0, hVu, hVth, hVst⟩ := hB t e he φ hφ fd hfd eL heL
  have hpts := fun (p : Pts ch.G) (hp : IsRealPt p) => hA s t β b b₀ hb hb₀ eL heL p hp
  choose q hq0 hqu hqst using hpts
  choose Tc hTc using hD
  obtain ⟨fl, hfl⟩ : ∃ fl : locPl ch.G t → (∀ j : Fin D.R.m, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1)))) → ℂ,
      ∀ w y, fl w y = flatTensor one_le_sLen (psiAt ch.W w.1) (unitVol w.1)
        (moved (locGrid ch.G t w.1) (keepAt ch.G w.1) ((repsAt ch.G t w.1).elt (β w))
          ((locGrid ch.G t w.1).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) (GlobalTheory.LocAsm.exOne (φ w)))) (ch.S.colAt t w.1 y) 0 :=
    ⟨_, fun _ _ => rfl⟩
  have hexp' : ∀ w y, (∀ j, IsHalf (eL w) (y j)) → ∑ i ∈ S w, x w i * ∏ j, (d w i j).fn (y j) = fl w y :=
    fun w y hy => (hexp w y hy).trans (hfl w y).symm
  have hflG : ∀ (w' : locPl ch.G t) (e' : AE D), e' * eL w' = eL w' → ∀ u, fl w' (fun j => e' • u j) = fl w' u := by
    intro w' e' he' u
    rw [hfl, hfl, hG t w' (eL w') e' (heL w') he' u]

  have hcomb1 : ∀ (S' T' : HSp D) (f : WO S' T' → ℂ), comb ch.W.ψ S' T' (Finsupp.single 0 1) f = f := by
    intro S' T' f
    rw [GlobalTheory.DisjComb.comb_single]
    funext y
    simp [heisO, symplOH, symplO, hO]
  have hcombC1 : ∀ C : BiFam ch.G, combC ch.W ((fun _ => Finsupp.single 0 1), 0) C = C := by
    intro C
    funext j y z
    simp only [combC, biComb, hcomb1]

  have hidem : ∀ (S' : Finset (locPl ch.G t)), (∑ w ∈ S', eL w) * (∑ w ∈ S', eL w) = ∑ w ∈ S', eL w := by
    intro S'
    rw [hmul, Finset.inter_self]
  have hidem1 : ∀ w : locPl ch.G t, eL w * eL w = eL w := by
    intro w
    have h := hmul {w} {w}
    rw [Finset.inter_self, Finset.sum_singleton] at h
    exact h
  have hsubmul : ∀ (S' : Finset (locPl ch.G t)) (w : locPl ch.G t), w ∈ S' → (∑ w ∈ S', eL w) * eL w = eL w := by
    intro S' w hw
    have h := hmul S' {w}
    rw [Finset.inter_singleton_of_mem hw, Finset.sum_singleton] at h
    exact h
  have hhalf : ∀ (a : AE D), a * a = a → ∀ {m n : ℕ} (y : Mx D m n), IsHalf a (a • y) := by
    intro a ha m n y i j
    simp only [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, ha]
  have key : ∀ S' : Finset (locPl ch.G t), ∃ (J : Type) (SJ : Finset J) (xJ : J → ℂ)
      (dJ : J → ∀ j : Fin D.R.m, FinDatum ch.G t (.top t j))
      (cJ : J → ∀ j : ℕ, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))) →₀ ℂ),
      (∀ a ∈ SJ, ∀ j : Fin D.R.m, (dJ a j).P = S'.map (Function.Embedding.subtype _) ∧
        (dJ a j).e = ∑ w ∈ S', eL w ∧ IsCombOf ch.W (dJ a j) (cJ a j)) ∧
      (∀ u : ∀ j : Fin D.R.m, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))), (∀ j, IsHalf (∑ w ∈ S', eL w) (u j)) →
        ∑ a ∈ SJ, xJ a * ∏ j, (dJ a j).fn (u j) = ∏ w ∈ S', fl w u) ∧
      ∀ (P : PolDown ch.G) (p : Pts ch.G) (hp : IsRealPt p) (u : ColPt ch.G),
        evT (conAt ch.W hM (fockD ch.W t (V S') P) (q p hp S')) 1 u 0 = (∏ w ∈ S', ζ w) * ∑ a ∈ SJ, xJ a *
          evT (combC ch.W (cJ a, 0) (conAt ch.W hM (fockD ch.W t (fun j => ch.rm.vT D.R.m j) P) (p * b₀))) 1 u 0 := by
    intro S'
    induction S' using Finset.induction_on with
    | empty =>
      refine ⟨Unit, {()}, fun _ => 1, fun _ j => FinDatum.vacuum ch.G t (.top t j), fun _ _ => Finsupp.single 0 1, ?_, ?_, ?_⟩
      · intro a _ j
        refine ⟨?_, ?_, hZ t j⟩
        · rw [Finset.map_empty]; rfl
        · rw [Finset.sum_empty]; rfl
      · intro u hu
        have h0 : ∀ j, u j = 0 := by
          intro j
          ext a b'
          have := hu j a b'
          rw [Finset.sum_empty, zero_mul] at this
          exact this.symm
        simp only [Finset.sum_singleton, Finset.prod_empty, one_mul]
        refine Finset.prod_eq_one fun j _ => ?_
        rw [h0 j]
        show halfInd (0 : AE D) _ 0 = 1
        unfold halfInd
        rw [if_pos ⟨zero_mem _, fun a b' => by simp⟩]
      · intro P p hp u
        simp only [hV0, hq0 p hp, Finset.prod_empty, Finset.sum_singleton, one_mul, hcombC1]
    | insert w S₀ hw ih =>
      obtain ⟨J, SJ, xJ, dJ, cJ, h1, h2, h3⟩ := ih
      have hPw : ∀ i ∈ S w, ∀ j : Fin D.R.m, (d w i j).P = {w.1} := by
        intro i hi j
        have h := (d w i j).e_is
        rw [(hdc w i hi j).1] at h
        exact GlobalTheory.T.isIdemSum_places_unique D _ _ _ h (heL w)
      have hsum : ∑ w' ∈ insert w S₀, eL w' = eL w + ∑ w' ∈ S₀, eL w' := Finset.sum_insert hw
      have hmap : (insert w S₀).map (Function.Embedding.subtype (· ∈ locPl ch.G t)) =
          {w.1} ∪ S₀.map (Function.Embedding.subtype (· ∈ locPl ch.G t)) := by
        rw [Finset.map_insert, Finset.insert_eq]; rfl
      have hs : IsIdemSum (eL w + ∑ w' ∈ S₀, eL w') ({w.1} ∪ S₀.map (Function.Embedding.subtype _)) := by
        have := hsub (insert w S₀)
        rwa [hsum, hmap] at this
      have hF' : ∀ (k : I w × J) (j : Fin D.R.m),
          ∃ (dd : FinDatum ch.G t (.top t j)) (cc : WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))) →₀ ℂ), k.1 ∈ S w → k.2 ∈ SJ →
            dd.P = (d w k.1 j).P ∪ (dJ k.2 j).P ∧ dd.e = (d w k.1 j).e + (dJ k.2 j).e ∧ IsCombOf ch.W dd cc ∧
            (∀ y, IsHalf dd.e y → dd.fn y = (d w k.1 j).fn ((d w k.1 j).e • y) * (dJ k.2 j).fn ((dJ k.2 j).e • y)) ∧
            ∀ f, comb ch.W.ψ _ _ cc f = comb ch.W.ψ _ _ ((c w k.1).1 j) (comb ch.W.ψ _ _ (cJ k.2 j) f) := by
        intro k j
        by_cases hk : k.1 ∈ S w ∧ k.2 ∈ SJ
        · have hId : IsIdemSum ((d w k.1 j).e + (dJ k.2 j).e) ((d w k.1 j).P ∪ (dJ k.2 j).P) := by
            rw [(hdc w k.1 hk.1 j).1, (h1 k.2 hk.2 j).2.1, hPw k.1 hk.1 j, (h1 k.2 hk.2 j).1]
            exact hs
          obtain ⟨dd, cc, hh⟩ := hF t j (d w k.1 j) (dJ k.2 j) ((c w k.1).1 j) (cJ k.2 j) hId
            (hdc w k.1 hk.1 j).2 (h1 k.2 hk.2 j).2.2
          exact ⟨dd, cc, fun _ _ => hh⟩
        · exact ⟨FinDatum.vacuum ch.G t (.top t j), 0, fun h1' h2' => absurd ⟨h1', h2'⟩ hk⟩
      choose dF cF hdF using hF'
      refine ⟨I w × J, S w ×ˢ SJ, fun k => x w k.1 * xJ k.2, dF,
        fun k j => if h : j < D.R.m then cF k ⟨j, h⟩ else 0, ?_, ?_, ?_⟩
      · intro k hk j
        obtain ⟨hk1, hk2⟩ := Finset.mem_product.1 hk
        obtain ⟨hP, he', hc, -, -⟩ := hdF k j hk1 hk2
        refine ⟨?_, ?_, ?_⟩
        · rw [hP, hPw k.1 hk1 j, (h1 k.2 hk2 j).1, hmap]
        · rw [he', (hdc w k.1 hk1 j).1, (h1 k.2 hk2 j).2.1, hsum]
        · dsimp only
          rw [dite_eq_left j.2]
          exact hc
      · intro u hu
        have hu' : ∀ j, IsHalf (eL w + ∑ w' ∈ S₀, eL w') (u j) := fun j => by rw [← hsum]; exact hu j
        have hfn : ∀ k ∈ S w ×ˢ SJ, ∀ j, (dF k j).fn (u j) =
            (d w k.1 j).fn (eL w • u j) * (dJ k.2 j).fn ((∑ w' ∈ S₀, eL w') • u j) := by
          intro k hk j
          obtain ⟨hk1, hk2⟩ := Finset.mem_product.1 hk
          obtain ⟨-, he', -, hfn', -⟩ := hdF k j hk1 hk2
          rw [hfn' (u j) (by rw [he', (hdc w k.1 hk1 j).1, (h1 k.2 hk2 j).2.1]; exact hu' j), (hdc w k.1 hk1 j).1,
            (h1 k.2 hk2 j).2.1]
        have hA' : ∑ i ∈ S w, x w i * ∏ j, (d w i j).fn (eL w • u j) = fl w u :=
          (hexp' w _ fun j => hhalf _ (hidem1 w) (u j)).trans (hflG w (eL w) (hidem1 w) u)
        have hB' : ∑ a ∈ SJ, xJ a * ∏ j, (dJ a j).fn ((∑ w' ∈ S₀, eL w') • u j) = ∏ w' ∈ S₀, fl w' u :=
          (h2 _ fun j => hhalf _ (hidem S₀) (u j)).trans
            (Finset.prod_congr rfl fun w' hw' => hflG w' _ (hsubmul S₀ w' hw') u)
        rw [Finset.sum_congr rfl fun k hk => by rw [Finset.prod_congr rfl fun j _ => hfn k hk j],
          Finset.sum_product, Finset.prod_insert hw, ← hA', ← hB', Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.prod_mul_distrib]
        ring
      · intro P p hp u
        obtain ⟨r, r₀, h, hr, hr₀, htl, hhr, hhr₀⟩ := hqst p hp S₀ w hw
        have hloc := fun j => hC t (eL w) (V S₀) (V (insert w S₀)) P j _ (hVth S₀ j) (hVst S₀ w hw j)
        have hPC := hζ w (eL w) (heL w) M hM r r₀ h hr hr₀ htl (GlobalTheory.LocAsm.exOne (φ w)) (fun _ _ _ => rfl)
          (fockD ch.W t (V S₀) P) (fockD ch.W t (V (insert w S₀)) P) (fun j => (hloc j).1) (fun j => (hloc j).2)
          (I w) (S w) (x w) (d w) (c w) (hdc w) (hexp w) u
        rw [← hhr, hPC, hhr₀]
        have hIH : (fun u => evT (conAt ch.W hM (fockD ch.W t (V S₀) P) (q p hp S₀)) 1 u 0) =
            (∏ w' ∈ S₀, ζ w') • ∑ a ∈ SJ, xJ a • (fun u => evT (combC ch.W (cJ a, 0)
              (conAt ch.W hM (fockD ch.W t (fun j => ch.rm.vT D.R.m j) P) (p * b₀))) 1 u 0) := by
          funext u'
          rw [h3 P p hp u']
          simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
        have hstep : ∀ i ∈ S w, evT (combC ch.W (c w i) (conAt ch.W hM (fockD ch.W t (V S₀) P) (q p hp S₀))) 1 u 0 =
            (∏ w' ∈ S₀, ζ w') * ∑ a ∈ SJ, xJ a * evT (combC ch.W ((fun j => if h : j < D.R.m then cF (i, a) ⟨j, h⟩ else 0), 0)
              (conAt ch.W hM (fockD ch.W t (fun j => ch.rm.vT D.R.m j) P) (p * b₀))) 1 u 0 := by
          intro i hi
          set_option synthInstance.maxHeartbeats 100000 in
            rw [congrFun (hTc (c w i) _) u, hIH, map_smul, map_sum]
          simp only [map_smul, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
          congr 1
          refine Finset.sum_congr rfl fun a ha => ?_
          congr 1
          rw [← congrFun (hTc (c w i) _) u]
          refine hE (c w i) (cJ a) _ ?_ _ u
          intro j hj f
          rw [dite_eq_left hj]
          exact (hdF (i, a) ⟨j, hj⟩ hi ha).2.2.2.2 f
        rw [Finset.prod_insert hw, Finset.sum_product, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [hstep i hi]
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        ring
  obtain ⟨J, SJ, xJ, dJ, cJ, h1, h2, h3⟩ := key Finset.univ
  refine ⟨J, SJ, xJ, dJ, cJ, fun a ha j => ⟨(h1 a ha j).2.1.trans he_sum.symm, (h1 a ha j).2.2⟩, fun u hu => ?_,
    fun P p hp u => ?_⟩
  · rw [h2 u (fun j => by rw [← he_sum]; exact hu j)]
    exact Finset.prod_congr rfl fun w _ => hfl w u
  · have := h3 P p hp u
    rwa [hVu, hqu p hp] at this

end GlobalTheory.LocAsm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestColumnInductionLocalToGlobalExpansionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowTest_columnInduction_localToGlobalExpansion : Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (s : ℤˣ) (t : T) (β : CosFam ch.G t) (ζ : locPl ch.G t → ℂ), (∀ w : locPl ch.G t, GlobalTheory.LocAsm.PlaceCl ch s t w (β w) (ζ w)) → ∀ (M : Vol ch.G) (hM : M.Is t) (b b₀ : Pts ch.G), IsRep t ch.S.B s β b → IsBase t ch.S.B b₀ → ∀ e : AE D, IsIdemSum e (locPl ch.G t) → ∀ (φ : (∀ w : locPl ch.G t, ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin ((locGrid ch.G t w.1).rank b.tgt)) (Fin ((locGrid ch.G t w.1).rank b.src)) (Kw w.1) → ℂ)), (∀ w : locPl ch.G t, ∀ b ∈ GlobalTheory.SplitFlip.oppositePath D.R.m, GlobalTheory.SplitFlip.IsNatDatum (unifAt w.1) (depthAt ch.G w.1) (φ w b)) → ∀ (fd : SchDown ch.G t), (∀ j : Fin D.R.m, IsLocVec ch.W (.mu t D.R.m j) e (ch.rm.vT D.R.m j) (fun y => if IsHalf e y then ∏ w : locPl ch.G t, φ w (.theta D.R.m j) (ch.S.B.coord t w.1 (X := (D.R.m, j + 1)) (Y := (D.R.m, j)) ⟨le_rfl, j.2⟩ ⟨le_rfl, j.2.le⟩ (y.map fun a => cpt w.1 (toEAf D a))) else 0) (fd j)) → ∀ (eL : locPl ch.G t → AE D), (∀ w, IsIdemSum (eL w) {w.1}) → ∀ (I : locPl ch.G t → Type) (S : ∀ w, Finset (I w)) (x : ∀ w, I w → ℂ) (d : ∀ w, I w → ∀ j : Fin D.R.m, FinDatum ch.G t (.top t j)) (c : ∀ w, I w → Combs ch.G), (∀ w, ∀ i ∈ S w, ∀ j : Fin D.R.m, (d w i j).e = eL w ∧ IsCombOf ch.W (d w i j) ((c w i).1 j)) → (∀ w (y : ∀ j : Fin D.R.m, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1)))), (∀ j, IsHalf (eL w) (y j)) → ∑ i ∈ S w, x w i * ∏ j, (d w i j).fn (y j) = flatTensor one_le_sLen (psiAt ch.W w.1) (unitVol w.1) (moved (locGrid ch.G t w.1) (keepAt ch.G w.1) ((repsAt ch.G t w.1).elt (β w)) ((locGrid ch.G t w.1).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) (GlobalTheory.LocAsm.exOne (φ w)))) (ch.S.colAt t w.1 y) 0) → ∃ (J : Type) (SJ : Finset J) (xJ : J → ℂ) (dJ : J → ∀ j : Fin D.R.m, FinDatum ch.G t (.top t j)) (cJ : J → ∀ j : ℕ, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))) →₀ ℂ), (∀ a ∈ SJ, ∀ j : Fin D.R.m, (dJ a j).e = e ∧ IsCombOf ch.W (dJ a j) (cJ a j)) ∧ (∀ u : ∀ j : Fin D.R.m, WO (ch.G.V (.top j)) (ch.G.V (.top (j + 1))), (∀ j, IsHalf e (u j)) → ∑ a ∈ SJ, xJ a * ∏ j, (dJ a j).fn (u j) = ∏ w : locPl ch.G t, flatTensor one_le_sLen (psiAt ch.W w.1) (unitVol w.1) (moved (locGrid ch.G t w.1) (keepAt ch.G w.1) ((repsAt ch.G t w.1).elt (β w)) ((locGrid ch.G t w.1).lines₂ (GlobalTheory.SplitFlip.oppositePath D.R.m) (GlobalTheory.LocAsm.exOne (φ w)))) (ch.S.colAt t w.1 u) 0) ∧ ∀ (P : PolDown ch.G) (p : Pts ch.G), IsRealPt p → ∀ u : ColPt ch.G, evT (conAt ch.W hM (fockD ch.W t fd P) (p * b)) 1 u 0 = (∏ w, ζ w) * ∑ a ∈ SJ, xJ a * evT (combC ch.W (cJ a, 0) (conAt ch.W hM (fockD ch.W t (fun j => ch.rm.vT D.R.m j) P) (p * b₀))) 1 u 0 := by
  first | exact @GlobalTheory.LocAsm.columnInduction | exact GlobalTheory.LocAsm.columnInduction | (intros; apply GlobalTheory.LocAsm.columnInduction <;> assumption)
end
