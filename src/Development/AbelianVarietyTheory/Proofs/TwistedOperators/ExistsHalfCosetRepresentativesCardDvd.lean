module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCosetExpansionExpDepth

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateIdempotentChartPlacesInjective
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateIdempotentChartPlacesInjective
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

noncomputable section

namespace GlobalTheory.ChartPlaces

variable {D : D7}

theorem mul_eq_zero_of_ne {P : Finset (Formalism.L2.DIV.Pl D.host.E)} {es : Formalism.L2.DIV.Pl D.host.E → AE D}
    (hes : ∀ Q ∈ P, Formalism.L2.NTheta.IsIdemAt (es Q) Q) {Q Q' : Formalism.L2.DIV.Pl D.host.E} (hQ : Q ∈ P) (hQ' : Q' ∈ P)
    (hne : Q ≠ Q') : es Q * es Q' = 0 := by
  refine (GlobalTheory.PlaceModelSum.eq_or_mul_eq_zero (hes Q hQ).1 (hes Q' hQ').1).resolve_left fun h => hne ?_
  refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
  by_cases hx : x = 0
  · rw [hx]; exact iff_of_true (zero_mem _) (zero_mem _)
  · rw [(hes Q hQ).2 x hx, (hes Q' hQ').2 x hx, h]

theorem chart_places_injective : ∀ {D : D7} (e : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (es : Formalism.L2.DIV.Pl D.host.E → AE D), (∀ Q ∈ P, Formalism.L2.NTheta.IsIdemAt (es Q) Q) → e = ∑ Q ∈ P, es Q → e * cA D e = 0 → ∀ v : ↥P → HeightOneSpectrum (𝓞 D.host.F), (∀ Q : ↥P, ∃ π : AE D →+* Fv D.host.F (v Q), GlobalTheory.SplitHecke.Chart (cA D (es Q)) (v Q) π) → Function.Injective v := by
  intro D e P es hes hsum hec v hπ
  have hsplit : ∀ Q ∈ P, Formalism.L2.Theta.IsSplitIdem D (es Q) := fun Q hQ => (hes Q hQ).1
  have horth : ∀ Q ∈ P, ∀ Q' ∈ P, Q' ≠ Q → es Q * es Q' = 0 :=
    fun Q hQ Q' hQ' hne => mul_eq_zero_of_ne hes hQ hQ' (Ne.symm hne)

  have habs : ∀ Q ∈ P, es Q * e = es Q := fun Q hQ => by
    rw [hsum]; exact GlobalTheory.PlaceModelSum.mul_sum_orth hsplit horth hQ

  have hcross : ∀ Q ∈ P, ∀ Q' ∈ P, es Q' * cA D (es Q) = 0 := fun Q hQ Q' hQ' => by
    have h1 : cA D (es Q) * cA D e = cA D (es Q) := by rw [← map_mul, habs Q hQ]
    calc es Q' * cA D (es Q) = (es Q' * e) * (cA D e * cA D (es Q)) := by
          rw [habs Q' hQ', mul_comm (cA D e), h1]
      _ = es Q' * (e * cA D e) * cA D (es Q) := by ring
      _ = 0 := by rw [hec, mul_zero, zero_mul]
  intro Q Q' hvv
  by_contra hne
  have hne' : (Q : Formalism.L2.DIV.Pl D.host.E) ≠ Q' := fun h => hne (Subtype.ext h)
  obtain ⟨π, hπc⟩ := hπ Q
  obtain ⟨π', hπc'⟩ := hπ Q'
  have hs' : Formalism.L2.Theta.IsSplitIdem D (cA D (es Q')) := GlobalTheory.PlaceModelSum.isSplitIdem_cA (hsplit Q' Q'.2)
  obtain ⟨hid', hort', v', ε', ⟨α', rfl, hα1, hα0⟩, hsum'⟩ := hs'

  have hπ'1 : π' (cA D (es Q')) = 1 := by
    have := (hπc'.2.1 (1 - cA D (es Q'))).2 (by rw [mul_sub, mul_one, hid', sub_self])
    rwa [map_sub, map_one, sub_eq_zero, eq_comm] at this
  have hπ'0 : π' (cA D (cA D (es Q'))) = 0 := (hπc'.2.1 _).2 hort'
  have hw1 : evalV D.host.F (v Q') α' = 1 := by
    have := hπc'.2.2.1 (pairA D.host.F 0 α')
    rw [← hsum', map_add (f := _), hπ'1, hπ'0, add_zero] at this
    exact this.symm
  have hwv : v Q' = v' := by
    by_contra h
    rw [hα0 _ h] at hw1
    exact zero_ne_one hw1

  have hA : π (cA D (es Q')) = 0 := (hπc.2.1 _).2 (by
    rw [← map_mul, mul_eq_zero_of_ne hes Q.2 Q'.2 hne', map_zero])
  have hB : π (cA D (cA D (es Q'))) = 0 := (hπc.2.1 _).2 (by
    rw [cA_cA, mul_comm]; exact hcross Q Q.2 Q' Q'.2)
  have hC := hπc.2.2.1 (pairA D.host.F 0 α')
  rw [← hsum', map_add (f := _), hA, hB, add_zero] at hC
  have h0 : evalV D.host.F (v Q) α' = 0 := hC.symm
  rw [hvv.trans hwv, hα1] at h0
  exact one_ne_zero h0

end GlobalTheory.ChartPlaces
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateIdempotentChartPlacesInjectiveStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_idempotent_chart_places_injective : ∀ {D : D7} (e : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (es : Formalism.L2.DIV.Pl D.host.E → AE D), (∀ Q ∈ P, Formalism.L2.NTheta.IsIdemAt (es Q) Q) → e = ∑ Q ∈ P, es Q → e * cA D e = 0 → ∀ v : ↥P → HeightOneSpectrum (𝓞 D.host.F), (∀ Q : ↥P, ∃ π : AE D →+* Fv D.host.F (v Q), GlobalTheory.SplitHecke.Chart (cA D (es Q)) (v Q) π) → Function.Injective v := by
  first | exact @GlobalTheory.ChartPlaces.chart_places_injective | exact GlobalTheory.ChartPlaces.chart_places_injective | (intros; apply GlobalTheory.ChartPlaces.chart_places_injective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProdCardAdicCompletionIntegersQuotDvdPowFinrank
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProdCardAdicCompletionIntegersQuotDvdPowFinrank
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

namespace GlobalTheory

theorem prod_card_quot_natCast_dvd_pow_finrank : ∀ (F : Type) [Field F] [NumberField F] (s : Finset (HeightOneSpectrum (𝓞 F))) (k : ℕ), 0 < k → ∏ v ∈ s, Nat.card (v.adicCompletionIntegers F ⧸ Ideal.span {(k : v.adicCompletionIntegers F)}) ∣ k ^ Module.finrank ℚ F := by
  intro F _ _ s k hk
  classical
  set I : Ideal (𝓞 F) := Ideal.span {(k : 𝓞 F)} with hIdef
  have hI : I ≠ 0 := by
    rw [hIdef, Ne, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hk.ne'
  have hmap : ∀ v : HeightOneSpectrum (𝓞 F),
      I.map (algebraMap (𝓞 F) (v.adicCompletionIntegers F)) =
        Ideal.span {(k : v.adicCompletionIntegers F)} := by
    intro v
    rw [hIdef, Ideal.map_span, Set.image_singleton, map_natCast]
  obtain ⟨hfin, hprod⟩ := GlobalTheory.LocalDifferentProduct.finprod_card_quot_map hI
  simp only [hmap] at hfin hprod
  have hnorm : Ideal.absNorm I = k ^ Module.finrank ℚ F := by
    rw [hIdef, Ideal.absNorm_span_singleton]
    have e : (k : 𝓞 F) = algebraMap ℤ (𝓞 F) (k : ℤ) := by simp
    rw [e, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank, Int.natAbs_pow]
    simp
  rw [← hnorm, ← hprod, finprod_eq_prod_of_mulSupport_subset (s := s ∪ hfin.toFinset) _
    (by intro x hx; simp [hx])]
  exact Finset.prod_dvd_prod_of_subset _ _ _ Finset.subset_union_left

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProdCardAdicCompletionIntegersQuotDvdPowFinrankStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_card_adicCompletionIntegers_quot_dvd_pow_finrank : ∀ (F : Type) [Field F] [NumberField F] (s : Finset (HeightOneSpectrum (𝓞 F))) (k : ℕ), 0 < k → ∏ v ∈ s, Nat.card (v.adicCompletionIntegers F ⧸ Ideal.span {(k : v.adicCompletionIntegers F)}) ∣ k ^ Module.finrank ℚ F := by
  first | exact @GlobalTheory.prod_card_quot_natCast_dvd_pow_finrank | exact GlobalTheory.prod_card_quot_natCast_dvd_pow_finrank | (intros; apply GlobalTheory.prod_card_quot_natCast_dvd_pow_finrank <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexNsmulIdempotentHalfAtSplitPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexNsmulIdempotentHalfAtSplitPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

namespace GlobalTheory.HalfIndex

theorem relIndex_nsmul_half : ∀ {D : D7} (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), Submodule.IsFullLattice D.host.E ΛS → Submodule.IsFullLattice D.host.E ΛT → ∀ (c : AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), IsSplitIdem D c → GlobalTheory.SplitHecke.Chart c v π → ∀ k : ℕ, 0 < k → (AddSubgroup.map (nsmulAddMonoidHom k) ((latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ⊓ GlobalTheory.PlaceModel.half S T c)).relIndex ((latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ⊓ GlobalTheory.PlaceModel.half S T c) = Nat.card (v.adicCompletionIntegers D.host.F ⧸ Ideal.span {(k : v.adicCompletionIntegers D.host.F)}) ^ (S.rank * T.rank) := by
  intro D S T ΛS ΛT hS hT c v π hc hπ k hk
  haveI : CharZero (Fv D.host.F v) := algebraRat.charZero _
  obtain ⟨σ, q1, q2⟩ := GlobalTheory.SplitLinear.exists_section (S := S) (T := T) hc.1 hπ
  have inj : Function.Injective σ := fun w w' h => by rw [← q1 w, h, q1]
  have hinf : infPart D c = 0 := GlobalTheory.PlaceModelSum.infPart_split hc
  set L0 := latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True with hL0
  set L := L0.comap σ with hL
  have hM : L0 ⊓ GlobalTheory.PlaceModel.half S T c = L.map σ := by
    rw [hL, AddSubgroup.map_comap_eq, ← GlobalTheory.SplitLinear.section_range hπ q1 q2, inf_comm]
  let nk : Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v) →+ Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v) :=
    nsmulAddMonoidHom k
  have hcomm : (L.map σ).map (nsmulAddMonoidHom k) = (L.map nk).map σ := by
    rw [AddSubgroup.map_map, AddSubgroup.map_map]
    congr 1
    exact AddMonoidHom.ext fun w => (map_nsmul σ k w).symm
  have e1 : ((L0 ⊓ GlobalTheory.PlaceModel.half S T c).map (nsmulAddMonoidHom k)).relIndex (L0 ⊓ GlobalTheory.PlaceModel.half S T c) =
      (L.map nk).relIndex L := by
    rw [hM, hcomm, AddSubgroup.relIndex_map_map_of_injective _ _ inj]
  have hk0 : (k : Fv D.host.F v) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have hnk : ∀ w, nk w = (k : Fv D.host.F v) • w := fun w => (Nat.cast_smul_eq_nsmul (Fv D.host.F v) k w).symm
  have nkinj : Function.Injective nk := fun w w' h => by
    rw [hnk, hnk] at h
    exact smul_right_injective _ hk0 h
  have nksurj : Function.Surjective nk := fun w => ⟨(k : Fv D.host.F v)⁻¹ • w, by rw [hnk, smul_inv_smul₀ hk0]⟩
  have e2 : (L.map nk).relIndex L = L.relIndex (L.comap nk) := by
    rw [← AddSubgroup.relIndex_map_map_of_injective L (L.comap nk) nkinj,
      AddSubgroup.map_comap_eq_self_of_surjective nksurj]
  let u : (Fv D.host.F v)ˣ := Units.mk0 _ hk0
  have hH : ∀ w : Matrix (Fin T.rank) (Fin S.rank) (Fv D.host.F v),
      ((k : Fv D.host.F v) • (1 : Matrix (Fin T.rank) (Fin T.rank) (Fv D.host.F v))) * w * (1 : Matrix (Fin S.rank) (Fin S.rank) (Fv D.host.F v)) = nk w := fun w => by
    rw [hnk, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul]
  have hA := GlobalTheory.SplitLinear.relIndex_matrix_lattice D.host.F v S.rank T.rank L (L.comap nk)
    (fun o ho m hm => GlobalTheory.SplitLinear.section_smul hc.1 hπ q1 q2 o ho m hm)
    (GlobalTheory.SplitLinear.section_den hS.toIsLattice hT.toIsLattice hπ q1 q2) (fun w => ?_)
    ((k : Fv D.host.F v) • 1) 1 1 (u ^ T.rank) (by simp) (by simp [u, Matrix.det_smul]) (fun m hm => ?_) (fun w => ?_)
  rotate_left
  · obtain ⟨N, hN, h1⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO' hS hT (σ w)
      (GlobalTheory.PlaceDatum.infPart_of_half hinf (q2 w))
    exact ⟨N, hN, by rwa [AddSubgroup.mem_comap, map_nsmul]⟩
  · rw [hH]
    exact nsmul_mem hm k
  · rw [hH]
    rfl
  have hkc : (((k : v.adicCompletionIntegers D.host.F)) : Fv D.host.F v) = (k : Fv D.host.F v) := by simp
  have hv : Valued.v (k : Fv D.host.F v) ≠ 0 := by simpa using hk0
  have h1 : Valued.v (k : Fv D.host.F v) ≤ 1 := hkc ▸ (k : v.adicCompletionIntegers D.host.F).2
  have hl : WithZero.log (Valued.v (k : Fv D.host.F v)) ≤ 0 := by
    rw [← WithZero.exp_le_exp, WithZero.exp_log hv, WithZero.exp_zero]; exact h1
  obtain ⟨e, he⟩ : ∃ e : ℕ, WithZero.log (Valued.v (k : Fv D.host.F v)) = -(e : ℤ) :=
    ⟨(-WithZero.log (Valued.v (k : Fv D.host.F v))).toNat, by omega⟩
  have he' : Valued.v (k : Fv D.host.F v) = WithZero.exp (-(e : ℤ)) := by
    rw [← he, WithZero.exp_log hv]
  have hcard := (GlobalTheory.CNorm.isAdicComplete_and_card_quotient_adicCompletionIntegers D.host.F v).2
    (k : v.adicCompletionIntegers D.host.F) e (by rw [hkc]; exact he')
  have hu : GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV D.host.F v u = (((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ e)⁻¹ := by
    rw [GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV, Units.val_mk0, he, zpow_neg, zpow_natCast]
  have h1' : GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV D.host.F v 1 = 1 := by simp [GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.absV]
  rw [e1, e2, hcard]
  apply Nat.cast_injective (R := ℝ)
  rw [hA, GlobalTheory.SplitLinear.absV_pow, hu, h1']
  push_cast
  rw [one_pow, one_mul, ← pow_mul, inv_pow, inv_inv, mul_comm T.rank S.rank]

end GlobalTheory.HalfIndex
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexNsmulIdempotentHalfAtSplitPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_nsmul_idempotentHalf_at_splitPlace : ∀ {D : D7} (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), Submodule.IsFullLattice D.host.E ΛS → Submodule.IsFullLattice D.host.E ΛT → ∀ (c : AE D) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), IsSplitIdem D c → GlobalTheory.SplitHecke.Chart c v π → ∀ k : ℕ, 0 < k → (AddSubgroup.map (nsmulAddMonoidHom k) ((latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ⊓ GlobalTheory.PlaceModel.half S T c)).relIndex ((latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ⊓ GlobalTheory.PlaceModel.half S T c) = Nat.card (v.adicCompletionIntegers D.host.F ⧸ Ideal.span {(k : v.adicCompletionIntegers D.host.F)}) ^ (S.rank * T.rank) := by
  exact @_root_.GlobalTheory.HalfIndex.relIndex_nsmul_half
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexNsmulHalfOrthogonalIdempotentSum
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexNsmulHalfOrthogonalIdempotentSum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

noncomputable section

namespace GlobalTheory.HalfSplit

def kIdx (k : ℕ) (A : Type) [AddCommGroup A] : ℕ := (nsmulAddMonoidHom k : A →+ A).range.index

theorem relIndex_eq_kIdx {G : Type} [AddCommGroup G] (H : AddSubgroup G) (k : ℕ) :
    (AddSubgroup.map (nsmulAddMonoidHom k) H).relIndex H = kIdx k H := by
  unfold kIdx AddSubgroup.relIndex
  congr 1
  ext x
  simp only [AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_map, AddMonoidHom.mem_range, nsmulAddMonoidHom_apply]
  constructor
  · rintro ⟨y, hy, hyx⟩
    exact ⟨⟨y, hy⟩, Subtype.ext (by simpa using hyx)⟩
  · rintro ⟨y, rfl⟩
    exact ⟨y, y.2, by simp⟩

theorem kIdx_congr {A B : Type} [AddCommGroup A] [AddCommGroup B] (e : A ≃+ B) (k : ℕ) :
    kIdx k A = kIdx k B := by
  unfold kIdx
  rw [← AddSubgroup.index_map_equiv _ e]
  congr 1
  ext x
  simp only [AddSubgroup.mem_map, AddMonoidHom.mem_range, nsmulAddMonoidHom_apply]
  constructor
  · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
    exact ⟨e y, by simp⟩
  · rintro ⟨y, rfl⟩
    exact ⟨k • e.symm y, ⟨e.symm y, rfl⟩, by simp⟩

theorem kIdx_prod {A B : Type} [AddCommGroup A] [AddCommGroup B] (k : ℕ) :
    kIdx k (A × B) = kIdx k A * kIdx k B := by
  unfold kIdx
  rw [← AddSubgroup.index_prod]
  congr 1
  ext ⟨a, b⟩
  simp only [AddSubgroup.mem_prod, AddMonoidHom.mem_range, nsmulAddMonoidHom_apply]
  constructor
  · rintro ⟨⟨x, y⟩, hxy⟩
    exact ⟨⟨x, congrArg Prod.fst hxy⟩, ⟨y, congrArg Prod.snd hxy⟩⟩
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    exact ⟨(x, y), Prod.ext hx hy⟩

theorem kIdx_subsingleton {A : Type} [AddCommGroup A] [Subsingleton A] (k : ℕ) : kIdx k A = 1 :=
  AddSubgroup.index_eq_one.2 (eq_top_iff.2 fun x _ => ⟨0, Subsingleton.elim _ _⟩)

variable {R M : Type} [Ring R] [AddCommGroup M] [Module R M]

section split

variable (h : R → AddSubgroup M) (hmem : ∀ e u, u ∈ h e ↔ e • u = u) (Λ : AddSubgroup M) {e f : R}

include hmem in
theorem smul_mem_inf (he : e * e = e) (hΛe : ∀ u ∈ Λ, e • u ∈ Λ) {u : M} (hu : u ∈ Λ) : e • u ∈ Λ ⊓ h e :=
  AddSubgroup.mem_inf.2 ⟨hΛe u hu, (hmem _ _).2 (by rw [smul_smul, he])⟩

def splitEquiv (he : e * e = e) (hf : f * f = f) (hef : e * f = 0) (hfe : f * e = 0)
    (hΛe : ∀ u ∈ Λ, e • u ∈ Λ) (hΛf : ∀ u ∈ Λ, f • u ∈ Λ) :
    ↥(Λ ⊓ h (e + f)) ≃+ ↥(Λ ⊓ h e) × ↥(Λ ⊓ h f) where
  toFun u := (⟨e • u.1, smul_mem_inf h hmem Λ he hΛe (AddSubgroup.mem_inf.1 u.2).1⟩,
    ⟨f • u.1, smul_mem_inf h hmem Λ hf hΛf (AddSubgroup.mem_inf.1 u.2).1⟩)
  invFun p := ⟨p.1.1 + p.2.1, AddSubgroup.mem_inf.2 ⟨add_mem (AddSubgroup.mem_inf.1 p.1.2).1
      (AddSubgroup.mem_inf.1 p.2.2).1, (hmem _ _).2 (by
        have h1 := (hmem _ _).1 (AddSubgroup.mem_inf.1 p.1.2).2
        have h2 := (hmem _ _).1 (AddSubgroup.mem_inf.1 p.2.2).2
        have h3 : f • (p.1.1 : M) = 0 := by rw [← h1, smul_smul, hfe, zero_smul]
        have h4 : e • (p.2.1 : M) = 0 := by rw [← h2, smul_smul, hef, zero_smul]
        rw [smul_add, add_smul, add_smul, h1, h2, h3, h4, add_zero, zero_add])⟩⟩
  left_inv u := by
    apply Subtype.ext
    change e • (u : M) + f • (u : M) = u
    rw [← add_smul]
    exact (hmem _ _).1 (AddSubgroup.mem_inf.1 u.2).2
  right_inv p := by
    have h1 := (hmem _ _).1 (AddSubgroup.mem_inf.1 p.1.2).2
    have h2 := (hmem _ _).1 (AddSubgroup.mem_inf.1 p.2.2).2
    have h3 : f • (p.1.1 : M) = 0 := by rw [← h1, smul_smul, hfe, zero_smul]
    have h4 : e • (p.2.1 : M) = 0 := by rw [← h2, smul_smul, hef, zero_smul]
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · change e • ((p.1 : M) + p.2) = p.1
      rw [smul_add, h1, h4, add_zero]
    · change f • ((p.1 : M) + p.2) = p.2
      rw [smul_add, h2, h3, zero_add]
  map_add' u v := by
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · change e • ((u : M) + v) = e • (u : M) + e • (v : M)
      exact smul_add _ _ _
    · change f • ((u : M) + v) = f • (u : M) + f • (v : M)
      exact smul_add _ _ _

end split

theorem sum_idem {ι : Type} (s : Finset ι) (cs : ι → R) (hid : ∀ i ∈ s, cs i * cs i = cs i)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → cs i * cs j = 0) :
    (∑ i ∈ s, cs i) * (∑ i ∈ s, cs i) = ∑ i ∈ s, cs i := by
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_eq_single i (fun j hj hji => horth i hi j hj (Ne.symm hji)) (fun h => absurd hi h), hid i hi]

theorem kIdx_half_sum (h : R → AddSubgroup M) (hmem : ∀ e u, u ∈ h e ↔ e • u = u) (Λ : AddSubgroup M)
    {ι : Type} (P : Finset ι) (cs : ι → R) (hid : ∀ i ∈ P, cs i * cs i = cs i)
    (horth : ∀ i ∈ P, ∀ j ∈ P, i ≠ j → cs i * cs j = 0) (hΛ : ∀ i ∈ P, ∀ u ∈ Λ, cs i • u ∈ Λ) (k : ℕ) :
    kIdx k ↥(Λ ⊓ h (∑ i ∈ P, cs i)) = ∏ i ∈ P, kIdx k ↥(Λ ⊓ h (cs i)) := by
  classical
  induction P using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.prod_empty]
    haveI : Subsingleton ↥(Λ ⊓ h 0) := ⟨fun a b => by
      have ha := (hmem _ _).1 (AddSubgroup.mem_inf.1 a.2).2
      have hb := (hmem _ _).1 (AddSubgroup.mem_inf.1 b.2).2
      rw [zero_smul] at ha hb
      exact Subtype.ext (ha.symm.trans hb)⟩
    exact kIdx_subsingleton k
  | insert a s ha ih =>
    have hs : ∀ i ∈ s, i ∈ insert a s := fun i hi => Finset.mem_insert_of_mem hi
    have ha' : a ∈ insert a s := Finset.mem_insert_self a s
    have hne : ∀ j ∈ s, a ≠ j := fun j hj haj => ha (haj ▸ hj)
    rw [Finset.sum_insert ha, Finset.prod_insert ha,
      ← ih (fun i hi => hid i (hs i hi)) (fun i hi j hj => horth i (hs i hi) j (hs j hj))
        (fun i hi => hΛ i (hs i hi)),
      kIdx_congr (splitEquiv h hmem Λ (hid a ha')
        (sum_idem s cs (fun i hi => hid i (hs i hi)) (fun i hi j hj => horth i (hs i hi) j (hs j hj)))
        (by rw [Finset.mul_sum]; exact Finset.sum_eq_zero fun j hj => horth a ha' j (hs j hj) (hne j hj))
        (by rw [Finset.sum_mul]; exact Finset.sum_eq_zero fun j hj => horth j (hs j hj) a ha' (hne j hj).symm)
        (hΛ a ha')
        (fun u hu => by rw [Finset.sum_smul]; exact AddSubgroup.sum_mem _ fun i hi => hΛ i (hs i hi) u hu)),
      kIdx_prod]

theorem relIndex_nsmul_half_sum : ∀ {D : D7} (S T : HSp D) (Λ : AddSubgroup (WO S T)) {ι : Type} (P : Finset ι) (cs : ι → AE D), (∀ i ∈ P, cs i * cs i = cs i) → (∀ i ∈ P, ∀ j ∈ P, i ≠ j → cs i * cs j = 0) → (∀ i ∈ P, ∀ u ∈ Λ, cs i • u ∈ Λ) → ∀ k : ℕ, (AddSubgroup.map (nsmulAddMonoidHom k) (Λ ⊓ GlobalTheory.PlaceModel.half S T (∑ i ∈ P, cs i))).relIndex (Λ ⊓ GlobalTheory.PlaceModel.half S T (∑ i ∈ P, cs i)) = ∏ i ∈ P, (AddSubgroup.map (nsmulAddMonoidHom k) (Λ ⊓ GlobalTheory.PlaceModel.half S T (cs i))).relIndex (Λ ⊓ GlobalTheory.PlaceModel.half S T (cs i)) := by
  intro D S T Λ ι P cs hid horth hΛ k
  rw [relIndex_eq_kIdx]
  simp only [relIndex_eq_kIdx]
  exact kIdx_half_sum (GlobalTheory.PlaceModel.half S T) (fun e u => GlobalTheory.PlaceModel.mem_half S T) Λ P cs hid horth hΛ k

end GlobalTheory.HalfSplit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexNsmulHalfOrthogonalIdempotentSumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_nsmul_half_orthogonal_idempotent_sum : ∀ {D : D7} (S T : HSp D) (Λ : AddSubgroup (WO S T)) {ι : Type} (P : Finset ι) (cs : ι → AE D), (∀ i ∈ P, cs i * cs i = cs i) → (∀ i ∈ P, ∀ j ∈ P, i ≠ j → cs i * cs j = 0) → (∀ i ∈ P, ∀ u ∈ Λ, cs i • u ∈ Λ) → ∀ k : ℕ, (AddSubgroup.map (nsmulAddMonoidHom k) (Λ ⊓ GlobalTheory.PlaceModel.half S T (∑ i ∈ P, cs i))).relIndex (Λ ⊓ GlobalTheory.PlaceModel.half S T (∑ i ∈ P, cs i)) = ∏ i ∈ P, (AddSubgroup.map (nsmulAddMonoidHom k) (Λ ⊓ GlobalTheory.PlaceModel.half S T (cs i))).relIndex (Λ ⊓ GlobalTheory.PlaceModel.half S T (cs i)) := by
  first | exact @GlobalTheory.HalfSplit.relIndex_nsmul_half_sum | exact GlobalTheory.HalfSplit.relIndex_nsmul_half_sum | (intros; apply GlobalTheory.HalfSplit.relIndex_nsmul_half_sum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHalfCosetRepresentativesCardDvd
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

noncomputable section

namespace GlobalTheory.HalfCosetCount


set_option maxHeartbeats 2000000 in
theorem halfCoset_reps_card : ∀ {D : D7} (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (e : AE D) (P : Finset (Pl D.host.E)), IsIdemSum e P → ∀ k : ℕ, 0 < k → ∃ R : Finset (WO S T), (∀ y ∈ R, IsHalf (cA D e) y ∧ k • y ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ∧ (∀ y : WO S T, IsHalf (cA D e) y → k • y ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) → ∃! r, r ∈ R ∧ y - r ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ∧ R.card ∣ k ^ (D.R.f * S.rank * T.rank) := by
  intro D S T ΛS ΛT hS hT e P he k hk
  classical
  obtain ⟨⟨es, hes, rfl⟩, hec⟩ := he
  set Λ := (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) with hΛ
  set c := cA D (∑ Q ∈ P, es Q) with hcdef
  have hc : c = ∑ Q ∈ P, cA D (es Q) := map_sum _ _ _
  have hes_orth : ∀ Q ∈ P, ∀ Q' ∈ P, Q ≠ Q' → es Q * es Q' = 0 := fun Q hQ Q' hQ' hne =>
    (GlobalTheory.PlaceModelSum.eq_or_mul_eq_zero (hes Q hQ).1 (hes Q' hQ').1).resolve_left fun h => hne
      (HeightOneSpectrum.ext (Ideal.ext fun x => by
        by_cases hx : x = 0
        · rw [hx]; exact iff_of_true (zero_mem _) (zero_mem _)
        · rw [(hes Q hQ).2 x hx, (hes Q' hQ').2 x hx, h]))
  have hidem : ∀ Q ∈ P, cA D (es Q) * cA D (es Q) = cA D (es Q) := fun Q hQ => by
    rw [← map_mul, (hes Q hQ).1.1]
  have horth : ∀ Q ∈ P, ∀ Q' ∈ P, Q ≠ Q' → cA D (es Q) * cA D (es Q') = 0 := fun Q hQ Q' hQ' hne => by
    rw [← map_mul, hes_orth Q hQ Q' hQ' hne, map_zero]
  have hstab : ∀ Q ∈ P, ∀ u ∈ Λ, cA D (es Q) • u ∈ Λ := fun Q hQ u hu =>
    GlobalTheory.PlaceModelSum.idem_smul_latO (hidem Q hQ) hu
  have hch : ∀ Q : ↥P, ∃ w : HeightOneSpectrum (𝓞 D.host.F), ∃ π : AE D →+* Fv D.host.F w,
      GlobalTheory.SplitHecke.Chart (cA D (es Q)) w π := fun Q =>
    GlobalTheory.SplitChart.exists_chart _ (GlobalTheory.PlaceModelSum.isSplitIdem_cA (hes Q Q.2).1)
  choose v π hπ using hch
  have hvinj : Function.Injective v :=
    GlobalTheory.T.conjugate_idempotent_chart_places_injective _ P es (fun Q hQ => hes Q hQ) rfl hec v fun Q => ⟨π Q, hπ Q⟩

  have hcount : (AddSubgroup.map (nsmulAddMonoidHom k) (Λ ⊓ GlobalTheory.PlaceModel.half S T c)).relIndex
      (Λ ⊓ GlobalTheory.PlaceModel.half S T c) =
      (∏ Q : ↥P, Nat.card ((v Q).adicCompletionIntegers D.host.F ⧸
        Ideal.span {(k : (v Q).adicCompletionIntegers D.host.F)})) ^ (S.rank * T.rank) := by
    rw [hc, GlobalTheory.T.relIndex_nsmul_half_orthogonal_idempotent_sum S T Λ P (fun Q => cA D (es Q)) hidem horth hstab k, ← Finset.prod_pow,
      ← Finset.prod_attach P]
    refine Finset.prod_congr rfl fun Q _ => ?_
    exact GlobalTheory.T.relIndex_nsmul_idempotentHalf_at_splitPlace S T ΛS ΛT
      (by first | exact GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull S ΛS hS
                | exact (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull S ΛS hS).toIsLattice)
      (by first | exact GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull T ΛT hT
                | exact (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull T ΛT hT).toIsLattice) _ (v Q) (π Q)
      (GlobalTheory.PlaceModelSum.isSplitIdem_cA (hes Q Q.2).1) (hπ Q) k hk
  have hdvd : (AddSubgroup.map (nsmulAddMonoidHom k) (Λ ⊓ GlobalTheory.PlaceModel.half S T c)).relIndex
      (Λ ⊓ GlobalTheory.PlaceModel.half S T c) ∣ k ^ (D.R.f * S.rank * T.rank) := by
    have h1 := GlobalTheory.T.prod_card_adicCompletionIntegers_quot_dvd_pow_finrank D.host.F (Finset.univ.image v) k hk
    rw [Finset.prod_image fun x _ y _ h => hvinj h, Formalism.MainNotions.J.finrank_F_eq] at h1
    rw [hcount, mul_assoc, pow_mul k D.R.f]
    exact pow_dvd_pow_of_dvd h1 _

  set M := Λ ⊓ GlobalTheory.PlaceModel.half S T c with hM
  set Y := Λ.comap (nsmulAddMonoidHom k) ⊓ GlobalTheory.PlaceModel.half S T c with hY
  have hinj : Function.Injective (nsmulAddMonoidHom k : WO S T →+ WO S T) := fun x y h => nsmul_cancel_mx hk h
  have hu : IsUnit (k : AE D) := by
    rw [← map_natCast (algebraMap D.host.F (AE D))]
    exact (isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 hk.ne')).map _
  have hYM : Y.map (nsmulAddMonoidHom k) = M := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨hy1, hy2⟩ := AddSubgroup.mem_inf.1 hy
      exact AddSubgroup.mem_inf.2 ⟨hy1, (GlobalTheory.PlaceModel.half S T c).nsmul_mem hy2 k⟩
    · intro hx
      obtain ⟨hx1, hx2⟩ := AddSubgroup.mem_inf.1 hx
      have key : k • ((↑hu.unit⁻¹ : AE D) • x) = x := by
        rw [← Nat.cast_smul_eq_nsmul (AE D), smul_smul, IsUnit.mul_val_inv, one_smul]
      refine ⟨(↑hu.unit⁻¹ : AE D) • x, AddSubgroup.mem_inf.2 ⟨?_, ?_⟩, key⟩
      · rw [AddSubgroup.mem_comap]
        change k • _ ∈ Λ
        rw [key]; exact hx1
      · refine (GlobalTheory.PlaceModel.mem_half S T).2 ?_
        have hx3 : c • x = x := (GlobalTheory.PlaceModel.mem_half S T).1 hx2
        rw [smul_comm c (↑hu.unit⁻¹ : AE D) x, hx3]
  have hMY : M.relIndex Y = (M.map (nsmulAddMonoidHom k)).relIndex M := by
    rw [← AddSubgroup.relIndex_map_map_of_injective (f := (nsmulAddMonoidHom k : WO S T →+ WO S T)) M Y hinj, hYM]
  have hne : (M.addSubgroupOf Y).index ≠ 0 := by
    change M.relIndex Y ≠ 0
    rw [hMY]
    exact fun h => (pow_pos hk _).ne' (Nat.eq_zero_of_zero_dvd (h ▸ hdvd))
  haveI : Finite (↥Y ⧸ M.addSubgroupOf Y) := AddSubgroup.index_ne_zero_iff_finite.1 hne
  obtain ⟨R, hRc, hRY, hRu⟩ := GlobalTheory.SplitLinear.exists_reps M Y
  refine ⟨R, fun y hy => ?_, fun y hy1 hy2 => ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := AddSubgroup.mem_inf.1 (hRY y hy)
    exact ⟨(GlobalTheory.PlaceModel.isHalf_iff S T).2 h2, h1⟩
  · have hyY : y ∈ Y := AddSubgroup.mem_inf.2 ⟨hy2, (GlobalTheory.PlaceModel.isHalf_iff S T).1 hy1⟩
    obtain ⟨r, ⟨hr, hyr⟩, huniq⟩ := hRu y hyY
    refine ⟨r, ⟨hr, (AddSubgroup.mem_inf.1 hyr).1⟩, fun r' hr' => huniq r' ⟨hr'.1, AddSubgroup.mem_inf.2 ⟨hr'.2, ?_⟩⟩⟩
    exact sub_mem ((GlobalTheory.PlaceModel.isHalf_iff S T).1 hy1) (AddSubgroup.mem_inf.1 (hRY r' hr'.1)).2
  · rw [hRc, hMY]
    exact hdvd

end GlobalTheory.HalfCosetCount
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHalfCosetRepresentativesCardDvdStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_halfCosetRepresentatives_card_dvd : ∀ {D : D7} (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (e : AE D) (P : Finset (Pl D.host.E)), IsIdemSum e P → ∀ k : ℕ, 0 < k → ∃ R : Finset (WO S T), (∀ y ∈ R, IsHalf (cA D e) y ∧ k • y ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ∧ (∀ y : WO S T, IsHalf (cA D e) y → k • y ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) → ∃! r, r ∈ R ∧ y - r ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ∧ R.card ∣ k ^ (D.R.f * S.rank * T.rank) := by
  first | exact @GlobalTheory.HalfCosetCount.halfCoset_reps_card | exact GlobalTheory.HalfCosetCount.halfCoset_reps_card | (intros; apply GlobalTheory.HalfCosetCount.halfCoset_reps_card <;> assumption)
end
