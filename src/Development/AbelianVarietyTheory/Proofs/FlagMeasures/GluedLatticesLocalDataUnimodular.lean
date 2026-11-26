module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalTermLatticeOverInnerDatumFgSpan
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicTransportMeasureThird

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LinearIndependentChangedRationalFramesOfUnitrian
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LinearIndependentChangedRationalFramesOfUnitrian
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GenMass

open Formalism.MainNotions.S.Loc

section General

theorem linInd_of_change {R W ι : Type} [CommRing R] [AddCommGroup W] [Module R W] [Fintype ι] [DecidableEq ι]
    {v w : ι → W} (B : Matrix ι ι R) (hB : IsUnit B.det) (hv : LinearIndependent R v)
    (hw : ∀ j, w j = ∑ i, B i j • v i) : LinearIndependent R w := by
  rw [Fintype.linearIndependent_iff] at hv ⊢
  intro g hg
  have h1 : ∑ i, (B.mulVec g) i • v i = 0 := by
    rw [← hg]
    simp only [Matrix.mulVec, dotProduct, Finset.sum_smul, hw, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm]
  have h2 : B.mulVec g = 0 := funext (hv _ h1)
  have h3 : g = B⁻¹.mulVec (B.mulVec g) := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hB, Matrix.one_mulVec]
  intro i
  rw [h3, h2, Matrix.mulVec_zero, Pi.zero_apply]

theorem isUnit_ringInverse_of_ne {R : Type} [CommRing R] {y : R} (h : Ring.inverse y ≠ 0) :
    IsUnit (Ring.inverse y) := by
  by_cases hy : IsUnit y
  · obtain ⟨u, rfl⟩ := hy
    rw [Ring.inverse_unit]
    exact Units.isUnit _
  · exact absurd (Ring.inverse_non_unit y hy) h

theorem det_uni_eq_one {K : Type} [CommRing K] {n : ℕ} {A : Matrix (Fin n) (Fin n) K} (hA : Uni A) :
    A.det = 1 := by
  obtain ⟨hlow, hdiag⟩ := hA
  rw [Matrix.det_of_isUpperTriangular (fun i j hij => hlow i j hij)]
  simp [hdiag]

end General

section Main

variable {D : D7}

theorem exists_place (D : D7) : Nonempty (PlF D) := by
  obtain ⟨P, hne, hP⟩ :=
    Ring.not_isField_iff_exists_prime.1 (NumberField.RingOfIntegers.not_isField D.host.F)
  exact ⟨⟨P, hP, hne⟩⟩

private theorem linearIndependent_frameD_of_T_ne_zero {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r : ℕ}
    (Fr : LocNG.FrameD H r) (hT : Fr.T ≠ 0) : LinearIndependent E Fr.f := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have key : ∀ y, H.h (∑ i, g i • Fr.f i) y = ∑ i, g i * H.h (Fr.f i) y := by
    intro y
    have hs : ∀ s : Finset (Fin (r + 1)),
        H.h (∑ i ∈ s, g i • Fr.f i) y = ∑ i ∈ s, g i * H.h (Fr.f i) y := by
      intro s
      refine Finset.induction_on s (by simp [H.h_zero_left]) ?_
      intro a s ha ih
      rw [Finset.sum_insert ha, Finset.sum_insert ha, H.h_add_left, H.h_smul_left, ih]
    exact hs Finset.univ
  have hlast : g (Fin.last r) = 0 := by
    have hz := key (Fr.f (Fin.last r))
    rw [hg, H.h_zero_left, Fin.sum_univ_castSucc] at hz
    have hoff : ∀ i : Fin r, H.h (Fr.f i.castSucc) (Fr.f (Fin.last r)) = 0 :=
      fun i => Fr.h_iso _ _ (Or.inl (Fin.castSucc_ne_last i))
    simp only [hoff, mul_zero, Finset.sum_const_zero, zero_add, Fr.h_zz] at hz
    have hu : IsUnit (-(algebraMap F E Fr.T)) := ((Ne.isUnit hT).map (algebraMap F E)).neg
    exact hu.mul_left_eq_zero.1 hz.symm
  intro i
  refine Fin.lastCases hlast (fun j => ?_) i
  have he := key (Fr.es j)
  rw [hg, H.h_zero_left, Fin.sum_univ_castSucc, hlast, zero_mul, add_zero] at he
  simp only [Fr.h_es, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at he
  exact he.symm

theorem local_pair_linInd (Z : LocDat D) (p : PlF D) (P : LocNG.FPair (locH Z p) D.R.rS)
    (hR : P.RelG (LocNG.theta (Z.M p))) :
    LinearIndependent (D.s.atP p).Ep (Sum.elim P.A.f P.B.f) := by
  obtain ⟨hX, -, -, -, -, -, hN⟩ := hR
  obtain ⟨-, hT, -, hT', -⟩ := hN
  exact LinearIndependent.sum_type (linearIndependent_frameD_of_T_ne_zero P.A hT) (linearIndependent_frameD_of_T_ne_zero P.B hT')
    (disjoint_iff.2 hX)

end Main

section Final

variable {D : D7}

theorem base_frames_linInd (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (Tn T'n : ℕ)
    (F : LFlag (D.sp.Y 0) D.R.rS (Tn : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (T'n : D.host.E))
    (hB : Based Z FP Tn T'n F F') (hR : ∀ p, (FP p).RelG (LocNG.theta (Z.M p))) :
    LinearIndependent D.host.E (Sum.elim (frame F) (frame F')) := by
  obtain ⟨p⟩ := exists_place D
  have hloc := local_pair_linInd Z p (FP p) (hR p)
  obtain ⟨hA, hA', -, -⟩ := hB p
  have hu : ∀ i, Sum.elim (FP p).A.f (FP p).B.f i =
      Sum.elim (frFac Z.δ p) (frFac Z.δ p) i • baseChange₂ D p (Sum.elim (frame F) (frame F') i) := by
    rintro (a | a)
    · simp only [Sum.elim_inl, hA]
    · simp only [Sum.elim_inr, hA']
  have hs : ∀ i, Ring.inverse (Sum.elim (frFac Z.δ p) (frFac Z.δ p) i) *
      Sum.elim (frFac Z.δ p) (frFac Z.δ p) i = 1 := by
    intro i
    have hne : Sum.elim (frFac Z.δ p) (frFac Z.δ p) i ≠ 0 := by
      intro h0
      apply hloc.ne_zero i
      rw [hu i, h0, zero_smul]
    refine Ring.inverse_mul_cancel _ ?_
    rcases i with a | a
    · exact isUnit_ringInverse_of_ne hne
    · exact isUnit_ringInverse_of_ne hne
  rw [Fintype.linearIndependent_iff] at hloc ⊢
  intro g hg
  have h1 : ∑ i, ((D.s.atP p).ιE (g i) * Ring.inverse (Sum.elim (frFac Z.δ p) (frFac Z.δ p) i)) •
      Sum.elim (FP p).A.f (FP p).B.f i = 0 := by
    have hmap := congrArg (baseChange₂ D p) hg
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_zero] at hmap
    rw [← hmap]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hu i, smul_smul, mul_assoc, hs i, mul_one, baseChange_smul₂]
  intro i
  have h2 := hloc _ h1 i
  have h3 : (D.s.atP p).ιE (g i) = 0 := by
    have h4 := congrArg (· * Sum.elim (frFac Z.δ p) (frFac Z.δ p) i) h2
    simpa only [mul_assoc, hs i, mul_one, zero_mul] using h4
  exact (map_eq_zero_iff _ (D.s.atP p).ιE.injective).1 h3

theorem changed_frames_linInd : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (Tn T'n : ℕ) (F G : LFlag (D.sp.Y 0) D.R.rS (Tn : D.host.E)) (F' G' : LFlag (D.sp.Y 0) D.R.rS (T'n : D.host.E)), Based Z FP Tn T'n F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → Tri D.host.E (frame F) (frame G) → Tri D.host.E (frame F') (frame G') → LinearIndependent D.host.E (Sum.elim (frame G) (frame G')) := by
  intro D Z FP Tn T'n F G F' G' hB hR hG hG'
  have hbase := base_frames_linInd Z FP Tn T'n F F' hB hR
  obtain ⟨A, hA, hcA⟩ := hG
  obtain ⟨A', hA', hcA'⟩ := hG'
  refine linInd_of_change (Matrix.fromBlocks A 0 0 A') ?_ hbase ?_
  · rw [Matrix.det_fromBlocks_zero₂₁, det_uni_eq_one hA, det_uni_eq_one hA', mul_one]
    exact isUnit_one
  · rintro (b | b)
    · simp only [Sum.elim_inl, Fintype.sum_sum_type, Sum.elim_inr, Matrix.fromBlocks_apply₁₁,
        Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, zero_smul, Finset.sum_const_zero, add_zero]
      exact hcA b
    · simp only [Sum.elim_inr, Fintype.sum_sum_type, Sum.elim_inl, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, zero_smul, Finset.sum_const_zero, zero_add]
      exact hcA' b

end Final
end GlobalTheory.GenMass
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LinearIndependentChangedRationalFramesOfUnitrianStatement
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearIndependent_changedRationalFrames_of_unitriangular : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (Tn T'n : ℕ) (F G : LFlag (D.sp.Y 0) D.R.rS (Tn : D.host.E)) (F' G' : LFlag (D.sp.Y 0) D.R.rS (T'n : D.host.E)), Based Z FP Tn T'n F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → Tri D.host.E (frame F) (frame G) → Tri D.host.E (frame F') (frame G') → LinearIndependent D.host.E (Sum.elim (frame G) (frame G')) := by
  first | exact @GlobalTheory.GenMass.changed_frames_linInd | exact GlobalTheory.GenMass.changed_frames_linInd | (intros; apply GlobalTheory.GenMass.changed_frames_linInd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GluedLatticesLocalDataUnimodular
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GlueDat

variable {D : D7}

private theorem infinite_finPlaces (K : Type) [Field K] [NumberField K] :
    Infinite (IsDedekindDomain.HeightOneSpectrum (𝓞 K)) := by
  have h : ∀ p : Nat.Primes, ∃ la : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
      la.asIdeal.comap (algebraMap ℤ (𝓞 K)) = Ideal.span {((p : ℕ) : ℤ)} := fun p => by
    haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
    haveI : (Ideal.span {((p : ℕ) : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
    obtain ⟨M, hM, hc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 K) (Ideal.span {((p : ℕ) : ℤ)})
      (by rw [(RingHom.injective_iff_ker_eq_bot _).1 (algebraMap ℤ (𝓞 K)).injective_int]; exact bot_le)
    exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField K)⟩, hc⟩
  choose f hf using h
  refine Infinite.of_injective f fun p q hpq => ?_
  have e : Ideal.span {((p : ℕ) : ℤ)} = Ideal.span {((q : ℕ) : ℤ)} := by rw [← hf p, ← hf q, hpq]
  have := Int.associated_iff_natAbs.1 (Ideal.span_singleton_eq_span_singleton.1 e)
  exact Subtype.ext (by simpa using this)


private theorem isFullLattice_of_local_span {D : D7} (Z : LocDat D) (p : PlF D) (Λ : LV D)
    (hΛ : Submodule.IsLattice D.host.E Λ)
    (hspan : Submodule.span (D.s.atP p).Ep (lattice₂ D Z.M p Λ : Set (Vp D p)) = ⊤) :
    Submodule.IsFullLattice D.host.E Λ := by
  let U := Submodule.span D.host.E (Λ : Set (VS D).V)
  let b := Module.finBasis D.host.E U
  let W := Submodule.span (D.s.atP p).Ep
    (Set.range fun i => baseChange₂ D p (b i : (VS D).V))
  have hW (x : U) : baseChange₂ D p (x : (VS D).V) ∈ W := by
    have hx := congrArg (fun y : U => baseChange₂ D p (y : (VS D).V)) (b.sum_repr x)
    change baseChange₂ D p (U.subtype (∑ i, b.repr x i • b i)) = _ at hx
    rw [map_sum, map_sum] at hx
    rw [← hx]
    exact W.sum_mem fun i _ => by
      rw [map_smul, baseChange_smul₂]
      exact W.smul_mem _ (Submodule.subset_span (Set.mem_range_self i))
  have htop : W = ⊤ := by
    apply top_le_iff.mp
    rw [← hspan, lattice₂, Submodule.span_span_of_tower]
    refine Submodule.span_le.2 ?_
    rintro y ⟨x, hx, heq⟩
    rw [← heq]
    exact hW ⟨x, Submodule.subset_span hx⟩
  refine { toIsLattice := hΛ, span_eq_top := Submodule.eq_of_le_of_finrank_le le_top ?_ }
  rw [finrank_top, Module.finrank_eq_card_basis (VS D).frame, Fintype.card_fin]
  simpa only [Module.finrank_fin_fun, Fintype.card_fin] using
    finrank_le_of_span_eq_top (show Submodule.span (D.s.atP p).Ep _ = ⊤ from htop)

theorem finrank_loc (p : PlF D) :
    Module.finrank (D.s.atP p).Ep (Vp D p) = D.R.k + 2 * D.R.rS + 1 := by
  rw [finrank_Vp]
  have h1 := D.R.m_even
  have h2 := D.R.two_le_m
  have h3 := D.R.m_add_three_le_k
  obtain ⟨c, hc⟩ := h1
  simp only [Ranks.r, Ranks.rS]
  omega

theorem localLattice_fg (Z : LocDat D) (Λ : LV D) (h : Submodule.IsLattice D.host.E Λ) (p : PlF D) :
    (lattice₂ D Z.M p Λ).FG := by
  obtain ⟨S, hS, hspan⟩ := Submodule.fg_def.mp (LatLoc.isLattice_map (LatLoc.cE D) Λ h).fg
  change Submodule.span (𝓞 D.host.E) S = LatLoc.cL Λ at hspan
  have hfg : ((GlobalTheory.HL.placesOf Z).lat p (LatLoc.cL Λ)).FG := by
    rw [← hspan, GlobalTheory.HL.PlacesRec.lat_span]
    exact Submodule.fg_span (hS.image _)
  rw [LatLoc.localLattice_eq]
  exact hfg

theorem orbit (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) {Tn T'n : ℕ}
    (F G : LFlag (D.sp.Y 0) D.R.rS (Tn : D.host.E)) (F' G' : LFlag (D.sp.Y 0) D.R.rS (T'n : D.host.E))
    (hB : Based Z FP Tn T'n F F') (hR : ∀ p, (FP p).RelG (LocNG.theta (Z.M p)))
    (hG : Tri D.host.E (frame F) (frame G)) (hG' : Tri D.host.E (frame F') (frame G')) (p : PlF D) :
    (∃ n ∈ (FP p).A.N, scaled Z p (frame G) = fun b => n ((FP p).A.f b)) ∧
    (∃ n ∈ (FP p).B.N, scaled Z p (frame G') = fun b => n ((FP p).B.f b)) := by
  obtain ⟨A, hA, hAc⟩ := hG
  obtain ⟨A', hA', hAc'⟩ := hG'
  obtain ⟨Ap, hAp, -⟩ := GlobalTheory.T.rational_unitriangular_frame_change_local_scalings D Z _ _ A hA hAc
  obtain ⟨Ap', hAp', -⟩ := GlobalTheory.T.rational_unitriangular_frame_change_local_scalings D Z _ _ A' hA' hAc'
  have hN := (hR p).2.2.2.2.2.2
  have hfA : (FP p).A.f = scaled Z p (frame F) := (hB p).1
  have hfB : (FP p).B.f = scaled Z p (frame F') := (hB p).2.1
  refine ⟨?_, ?_⟩
  · exact (GlobalTheory.T.frameDual_unipotentGroup_acts_unitriangular_onto (Z.M p) (Z.agree p).1 (locH Z p) D.R.rS (FP p).A hN.2.1).2.2 (scaled Z p (frame G))
      (by rw [hfA]; exact ⟨Ap p, (hAp p).1, (hAp p).2⟩)
  · exact (GlobalTheory.T.frameDual_unipotentGroup_acts_unitriangular_onto (Z.M p) (Z.agree p).1 (locH Z p) D.R.rS (FP p).B hN.2.2.2.1).2.2 (scaled Z p (frame G'))
      (by rw [hfB]; exact ⟨Ap' p, (hAp' p).1, (hAp' p).2⟩)

theorem mem_iff_of_img {α : Type*} {S S' : Set α} {f : α → α} (hf : Function.Injective f) (hS : f '' S = S')
    {a b : α} (hb : b = f a) : a ∈ S ↔ b ∈ S' := by
  subst hb; rw [← hS]; exact (hf.mem_set_image).symm

end GlobalTheory.GlueDat


open GlobalTheory.GlueDat in
theorem GlobalTheory.GlueDat.glued_data : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (u u' : D.what₂.Word) (F G : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' G' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (P : Finset (PlF D)) (d0 : Dat Z FP), 4 * D.R.rS + 7 ≤ D.R.k → BaseOK (Tu D u) (Tu D u') F F' P d0 → StdOff Z P F G F' G' → ∀ Λ : LV D, (Λ ∈ Formalism.L2.SG.Pf.Cnt.GlueSet (VS D).hT (Formalism.L2.SG.Pf.Cnt.UPair D G.fl G') (Formalism.L2.SG.Pf.Cnt.MMof D G.fl G') ↔ ∃ y : Dat Z FP, Λ ∈ globSet G G' y) ∧ (∀ y y' : Dat Z FP, Λ ∈ globSet G G' y → Λ ∈ globSet G G' y' → y = y') ∧ (∀ y : Dat Z FP, Λ ∈ globSet G G' y → (∀ p, p ∉ P → LocNG.Datum.Rel (d0 p) (y p)) ∧ {p | y p ≠ d0 p}.Finite) ∧ ∀ (y y' : Dat Z FP), ∀ h ∈ H0 F F', RMoves h y y' → (Λ ∈ globSet G G' y ↔ Formalism.HermitianLatticesTheory.gmap h Λ ∈ globSet G G' y') := by
  intro D Z FP u u' F G F' G' P d0 hk hB hS Λ
  have hOK : ∀ p, (Z.M p).OK := fun p => (Z.agree p).1
  have hR := hB.2.1
  have hO := fun p => orbit Z FP F G F' G' hB.1 hR hS.1 hS.2.1 p
  have hLM := fun p (L : Submodule (Z.M p).L.O (Vp D p)) =>
    GlobalTheory.T.generic_local_terms_selfDual_lattices (Z.M p) (hOK p) (locH Z p) D.R.rS D.R.k (FP p) (finrank_loc p) (hR p)
      (scaled Z p (frame G)) (scaled Z p (frame G')) (hO p).1 (hO p).2 L
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [GlobalTheory.T.glued_unimodular_lattice_iff_local_completions D Z FP u u' G G' (GlobalTheory.T.linearIndependent_changedRationalFrames_of_unitriangular D Z FP _ _ F G F' G' hB.1 hR hS.1 hS.2.1) Λ]
    constructor
    · rintro ⟨hL, hp⟩
      have : ∀ p, ∃ d, lattice₂ D Z.M p Λ ∈ locSet G G' p d := fun p =>
        (hLM p _).1.1 ⟨(hp p).1, localLattice_fg Z Λ hL p, (hp p).2.1, (hp p).2.2⟩
      choose y hy using this
      exact ⟨y, hL, hy⟩
    · rintro ⟨y, hL, hy⟩
      refine ⟨hL, fun p => ?_⟩
      obtain ⟨h1, -, h3, h4⟩ := (hLM p _).1.2 ⟨y p, hy p⟩
      exact ⟨h1, h3, h4⟩
  · intro y y' h h'
    funext p
    exact (hLM p _).2 (y p) (y' p) (h.2 p).1 (h'.2 p).1
  · intro y hy
    refine ⟨fun p hp => ?_, ?_⟩
    · obtain ⟨A, A', hA, hA', hint, hc, hc'⟩ := hS.2.2.2.2 p hp
      have := GlobalTheory.T.hermitian_orbit_unique_lattice_integral_frames (Z.M p) (hOK p) (locH Z p) D.R.rS D.R.k (FP p) hk (finrank_loc p) (hR p)
        (hB.2.2.1 p hp) A A' (fun a b hab => ⟨hA.1 a b hab, hA'.1 a b hab⟩) (fun a => ⟨hA.2 a, hA'.2 a⟩) hint
        (scaled Z p (frame G)) (scaled Z p (frame G'))
        (fun j => by rw [(hB.1 p).1]; exact hc j) (fun j => by rw [(hB.1 p).2.1]; exact hc' j)
        (d0 p) (hB.2.2.2.1 p) (y p)
      exact this.2 ⟨_, (hy.2 p).1⟩
    · obtain ⟨Λ₀, hΛ₀, hΛ₀p⟩ := hB.2.2.2.2
      haveI : Infinite (PlF D) := infinite_finPlaces D.host.F
      obtain ⟨q, hq⟩ := Infinite.exists_notMem_finset P
      have hfull : Submodule.IsFullLattice D.host.E Λ :=
        isFullLattice_of_local_span Z q Λ hy.1
          (GlobalTheory.T.localTermLattice_over_innerDatum_fg_span D Z FP q (y q) _ (hy.2 q).1).2
      have hfull₀ : Submodule.IsFullLattice D.host.E Λ₀ :=
        isFullLattice_of_local_span Z q Λ₀ hΛ₀
          (GlobalTheory.T.localTermLattice_over_innerDatum_fg_span D Z FP q (d0 q) _ (hΛ₀p q hq)).2
      refine (((LatLoc.lattices_local_global D Z).1 Λ Λ₀ hfull hfull₀).1.union P.finite_toSet).subset ?_
      intro p hp
      by_contra hc
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not, Finset.mem_coe] at hc
      apply hp
      exact (GlobalTheory.T.hermitianDatum_of_term_read_on_lattice (Z.M p) (hOK p) (locH Z p) D.R.rS D.R.k (FP p) (finrank_loc p) (hR p)).2
        (y p) (d0 p) _ _ (hy.2 p).1 (hΛ₀p p hc.2) (by dsimp only [tm]; rw [hc.1]) (by dsimp only [tm]; rw [hc.1])
        (fun g _ => by dsimp only [tm]; rw [hc.1])
  · intro y y' h hh hmv
    have hloc : ∀ p, ∃ g : Vp D p ≃ₗ[(D.s.atP p).Ep] Vp D p, g ∈ (FP p).UW0 ∧
        LocNG.Datum.Moves g (y p) (y' p) ∧
        lattice₂ D Z.M p (Formalism.HermitianLatticesTheory.gmap h Λ) = LocNG.img g (lattice₂ D Z.M p Λ) := by
      intro p
      obtain ⟨g, hext, hU, huniq, himg, -⟩ := GlobalTheory.T.rational_isometry_extends_local_isometry D Z p h hh.1
      obtain ⟨g', hext', hm⟩ := hmv p
      obtain rfl : g' = g := huniq g' hext'
      refine ⟨g', Subgroup.subset_closure ⟨hU, fun b => ⟨?_, ?_⟩⟩, hm, (himg Λ).symm⟩
      · rw [(hB.1 p).1]
        show g' (frFac Z.δ p b • baseChange₂ D p (frame F b)) = _
        rw [map_smul, hext', hh.2.1 b]
        rfl
      · rw [(hB.1 p).2.1]
        show g' (frFac Z.δ p b • baseChange₂ D p (frame F' b)) = _
        rw [map_smul, hext', hh.2.2 b]
        rfl
    choose g hgU hgm hgimg using hloc
    have hset := fun p => (GlobalTheory.T.unitaryComplement_moves_hermitianTerms (Z.M p) (hOK p) (locH Z p) D.R.rS D.R.k (FP p) (finrank_loc p) (hR p)
      (scaled Z p (frame G)) (scaled Z p (frame G')) (hO p).1 (hO p).2 (g p) (hgU p) (y p) (y' p) (hgm p)).2
    have hlat : Submodule.IsLattice D.host.E (Formalism.HermitianLatticesTheory.gmap h Λ) ↔ Submodule.IsLattice D.host.E Λ := by
      constructor
      · intro hl
        have e : Λ = Formalism.HermitianLatticesTheory.gmap h.symm (Formalism.HermitianLatticesTheory.gmap h Λ) := by
          ext x; simp [Formalism.HermitianLatticesTheory.gmap]
        rw [e]; exact LatLoc.isLattice_map _ _ hl
      · exact LatLoc.isLattice_map _ _
    show (Submodule.IsLattice D.host.E Λ ∧ ∀ p, lattice₂ D Z.M p Λ ∈ locSet G G' p (y p)) ↔
      (Submodule.IsLattice D.host.E (Formalism.HermitianLatticesTheory.gmap h Λ) ∧ ∀ p, lattice₂ D Z.M p (Formalism.HermitianLatticesTheory.gmap h Λ) ∈ locSet G G' p (y' p))
    rw [hlat]
    refine and_congr_right fun _ => forall_congr' fun p => ?_
    have e := hgimg p
    have key : ∀ L, L ∈ LocNG.img (g p) '' locSet G G' p (y p) ↔ L ∈ locSet G G' p (y' p) :=
      fun L => Set.ext_iff.mp (hset p) L
    have hinj : Function.Injective (LocNG.img (M := Z.M p) (g p)) := fun L₁ L₂ e =>
      Submodule.map_injective_of_injective (f := ((g p : Vp D p →ₗ[(D.s.atP p).Ep] Vp D p).restrictScalars (Z.M p).L.O))
        (g p).injective e
    exact mem_iff_of_img hinj (Set.ext key) e
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GluedLatticesLocalDataUnimodularStatement
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_gluedLattices_iff_existsUnique_localDatum : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (u u' : D.what₂.Word) (F G : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' G' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (P : Finset (PlF D)) (d0 : Dat Z FP), 4 * D.R.rS + 7 ≤ D.R.k → BaseOK (Tu D u) (Tu D u') F F' P d0 → StdOff Z P F G F' G' → ∀ Λ : LV D, (Λ ∈ Formalism.L2.SG.Pf.Cnt.GlueSet (VS D).hT (Formalism.L2.SG.Pf.Cnt.UPair D G.fl G') (Formalism.L2.SG.Pf.Cnt.MMof D G.fl G') ↔ ∃ y : Dat Z FP, Λ ∈ globSet G G' y) ∧ (∀ y y' : Dat Z FP, Λ ∈ globSet G G' y → Λ ∈ globSet G G' y' → y = y') ∧ (∀ y : Dat Z FP, Λ ∈ globSet G G' y → (∀ p, p ∉ P → LocNG.Datum.Rel (d0 p) (y p)) ∧ {p | y p ≠ d0 p}.Finite) ∧ ∀ (y y' : Dat Z FP), ∀ h ∈ H0 F F', RMoves h y y' → (Λ ∈ globSet G G' y ↔ Formalism.HermitianLatticesTheory.gmap h Λ ∈ globSet G G' y') := by
  first | exact @GlobalTheory.GlueDat.glued_data | exact GlobalTheory.GlueDat.glued_data | (intros; apply GlobalTheory.GlueDat.glued_data <;> assumption)
end
