module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitCountRowsDoubleCosetsInnerDatumClass
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SameRowDoubleCosetInnerDataOneRationalClass
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalClassLatticesIffRationalClassLocalFrameP
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GluedTermFrameAdmissibleIntegral
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowLatticeOfLocallyStandardFrame
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalDataOfTermLatticeAndOrbits
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalisedBaseFramesRelevantPair

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnfoldingGenusWeightsSumToMass
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRowTermOfLocalCompletionsTerms
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRowTermOfLocalCompletionsTerms
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowTermReal

variable {D : D7}

theorem gmap_one' (L : LV D) : Formalism.HermitianLatticesTheory.gmap (1 : GV D) L = L := by
  ext x; simp [Formalism.HermitianLatticesTheory.gmap]

theorem gmap_mul' (a b : GV D) (L : LV D) :
    Formalism.HermitianLatticesTheory.gmap (a * b) L = Formalism.HermitianLatticesTheory.gmap a (Formalism.HermitianLatticesTheory.gmap b L) := by
  ext x; simp [Formalism.HermitianLatticesTheory.gmap]

theorem xflag_mono {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) {i j : ℕ} (h : i ≤ j) :
    Xflag F i ≤ Xflag F j :=
  Submodule.span_mono (Set.image_mono fun a (ha : a.1 < i) => show a.1 < j by omega)

theorem adapt_map_xflag {T : D.host.E} {g : GV D} {A B : LFlag (D.sp.Y 0) D.R.rS T} (hg : Adapt g A B)
    (j : ℕ) {x : (VS D).V} (hx : x ∈ Xflag A j) : g x ∈ Xflag B j := by
  change x ∈ Submodule.span D.host.E (A.fl.e '' {i | i.1 < j}) at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, ha, rfl⟩ := hy
    have ha' : a.1 < j := ha
    have h1 := hg.2 a.castSucc
    have e1 : frame A a.castSucc = A.fl.e a := by simp [frame, FlagG.fvec]
    have e2 : frame B a.castSucc = B.fl.e a := by simp [frame, FlagG.fvec]
    rw [e1, e2, Fin.val_castSucc] at h1
    have h2 : B.fl.e a ∈ Xflag B j := Submodule.subset_span ⟨a, ha', rfl⟩
    have h3 := xflag_mono B (le_of_lt ha') h1
    simpa using add_mem h3 h2
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

theorem adapt_mul {T : D.host.E} {g h : GV D} {A B C : LFlag (D.sp.Y 0) D.R.rS T} (hg : Adapt g B C)
    (hh : Adapt h A B) : Adapt (g * h) A C := by
  refine ⟨mul_mem hg.1 hh.1, fun a => ?_⟩
  have e : (g * h) (frame A a) - frame C a =
      g (h (frame A a) - frame B a) + (g (frame B a) - frame C a) := by
    simp only [mul_apply_eq_comp, map_sub]; abel
  rw [e]
  exact add_mem (adapt_map_xflag hg _ (hh.2 a)) (hg.2 a)

theorem adapt_of_nlam {T : D.host.E} {Λ : LV D} {F : LFlag (D.sp.Y 0) D.R.rS T} {n : GV D}
    (hn : n ∈ NLam Λ F) : Adapt n F F := by
  refine ⟨hn.1.1, fun a => ?_⟩
  refine Fin.lastCases ?_ (fun i => ?_) a
  · have hz : frame F (Fin.last _) = F.fl.z := by simp [frame, FlagG.fvec]
    rw [hz, Fin.val_last]
    have hzo : F.fl.z ∈ orth (VS D) (Xsp F) := by
      simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
      intro x hx
      change x ∈ Submodule.span D.host.E (Set.range F.fl.e) at hx
      induction hx using Submodule.span_induction with
      | mem y hy => obtain ⟨a, rfl⟩ := hy; exact F.fl.z_orth a
      | zero => simp
      | add x y _ _ hx hy => simp [map_add (f := _), hx, hy]
      | smul c x _ hx => simp [hx]
    have hX : Xsp F ≤ Xflag F D.R.rS :=
      Submodule.span_mono fun _ ⟨i, h⟩ => ⟨i, i.2, h⟩
    exact hX (hn.2.2 _ hzo)
  · have hi : frame F i.castSucc = F.fl.e i := by simp [frame, FlagG.fvec]
    rw [hi, Fin.val_castSucc]
    exact hn.2.1 i.1 _ (Submodule.subset_span ⟨i, by simp, rfl⟩)

theorem frame_mapLF' {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) {g : GV D}
    (hg : g ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT) (a : Fin (D.R.rS + 1)) : frame (mapLF g F) a = g (frame F a) := by
  simp only [mapLF, dite_eq_left hg, frame, FlagG.fvec, mapFlag]
  refine Fin.lastCases ?_ (fun i => ?_) a <;> simp

end GlobalTheory.RowTermReal

namespace GlobalTheory.RowTermReal

theorem rowLat_first {D : D7} (X : HidaSetting D) {u u' : D.what₂.Word} (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E))
    (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (Z : LocDat D)
    (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (hB : Based Z FP (Tu D u) (Tu D u') F F')
    (Λ : LV D) (y : Dat Z FP) (hL : LocOver Λ y) :
    ∃ g, Adapt g (lf D (X.Fu u)) F ∧ IsRowLat D (X.Fu u) (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) :=
  GlobalTheory.T.rowLattice_of_locally_standard_frame D (Tu D u) (D.mem u).A.T_prime.ne_zero (X.Fu u) F Z
    (fun p => (FP p).A) (fun p => (hB p).1) Λ hL.1 (fun p => by
      obtain ⟨τ, hτ, hlat⟩ := hL.2 p
      have h4 := hτ.2.2.1
      exact h4.elim fun n hn => ⟨n, hn.1, (y p).L, (y p).hL, hlat.symm.trans hn.2.2⟩)

theorem rowLat_second {D : D7} (X : HidaSetting D) {u u' : D.what₂.Word} (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E))
    (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (Z : LocDat D)
    (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (hB : Based Z FP (Tu D u) (Tu D u') F F')
    (Λ : LV D) (y : Dat Z FP) (hL : LocOver Λ y) :
    ∃ g, Adapt g (lf D (X.Fu u')) F' ∧ IsRowLat D (X.Fu u') (Formalism.HermitianLatticesTheory.gmap g⁻¹ Λ) :=
  GlobalTheory.T.rowLattice_of_locally_standard_frame D (Tu D u') (D.mem u').A.T_prime.ne_zero (X.Fu u') F' Z
    (fun p => (FP p).B) (fun p => (hB p).2.1) Λ hL.1 (fun p => by
      obtain ⟨τ, hτ, hlat⟩ := hL.2 p
      have h4 := hτ.2.2.2.1
      exact h4.elim fun n hn => ⟨n, hn.1, (y p).L', (y p).hL', hlat.symm.trans hn.2.2⟩)

theorem exists_term_of_locOver : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (Λ : LV D) (y : Dat Z FP), LocOver Λ y → ∃ t : TauC Y u u', TG F F' t Λ := by
  intro D X Y u u' F F' w hw hG Z FP hB hR Λ y hL
  obtain ⟨g0, hg0, hrow0⟩ := rowLat_first X F F' Z FP hB Λ y hL
  obtain ⟨g0', hg0', hrow0'⟩ := rowLat_second X F F' Z FP hB Λ y hL
  obtain ⟨Λ₁, hΛ₁, σ, hσ, hσΛ⟩ := (GlobalTheory.T.row_representatives_up_to_frame_adapted_isometry D X Y u u).1 _ hrow0
  obtain ⟨Λ₁', hΛ₁', σ', hσ', hσΛ'⟩ := (GlobalTheory.T.row_representatives_up_to_frame_adapted_isometry D X Y u' u').1 _ hrow0'
  have hg : Adapt (g0 * σ) (lf D (X.Fu u)) F := adapt_mul hg0 hσ
  have hg' : Adapt (g0' * σ') (lf D (X.Fu u')) F' := adapt_mul hg0' hσ'
  have hgΛ : Formalism.HermitianLatticesTheory.gmap (g0 * σ)⁻¹ Λ = Λ₁ := by
    rw [mul_inv_rev, gmap_mul', ← hσΛ, ← gmap_mul', inv_mul_cancel, gmap_one']
  have hgΛ' : Formalism.HermitianLatticesTheory.gmap (g0' * σ')⁻¹ Λ = Λ₁' := by
    rw [mul_inv_rev, gmap_mul', ← hσΛ', ← gmap_mul', inv_mul_cancel, gmap_one']
  have hrow : IsRowLat D (X.Fu u) (Formalism.HermitianLatticesTheory.gmap (g0 * σ)⁻¹ Λ) := hgΛ ▸ (Y.rowsOK u).1 Λ₁ hΛ₁
  have hrow' : IsRowLat D (X.Fu u') (Formalism.HermitianLatticesTheory.gmap (g0' * σ')⁻¹ Λ) := hgΛ' ▸ (Y.rowsOK u').1 Λ₁' hΛ₁'
  have hPD := GlobalTheory.T.gluedTerm_frame_admissibleIntegral D X Y u u' F F' w hw hG Z FP hB hR Λ y hL _ _ hg hg' hrow hrow'
  rw [hgΛ] at hPD
  set g := g0 * σ with hgdef
  set g' := g0' * σ' with hg'def
  have hγ : g⁻¹ * g' ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := mul_mem (inv_mem hg.1) hg'.1
  have hγΛ : Formalism.HermitianLatticesTheory.gmap (g⁻¹ * g') Λ₁' = Λ₁ := by
    rw [← hgΛ, ← hgΛ', gmap_mul', ← gmap_mul' g' g'⁻¹, mul_inv_cancel, gmap_one']
  obtain ⟨x, hx⟩ := Formalism.L2.SG.Pf.ratPt_holds D X (g⁻¹ * g') hγ
  let p : GCar X u u' (X.Fu u) (X.Fu u') Λ₁ Λ₁' := ⟨(x, g⁻¹ * g'), hx, hγ, hγΛ, hPD⟩
  let t : TauC Y u u' := ⟨Λ₁, hΛ₁, Λ₁', hΛ₁', Quot.mk _ p⟩
  refine ⟨t, ?_⟩
  obtain ⟨n, hn, n', hn', hrel⟩ := Formalism.L2.SG.Pf.SatGramRep.grel_rep t p rfl
  have hlin : t.lin = n⁻¹ * (g⁻¹ * g') * n'⁻¹ := by
    have h : g⁻¹ * g' = n * t.lin * n' := hrel
    rw [h]; group
  refine ⟨g * n, adapt_mul hg (adapt_of_nlam hn), ?_, ?_⟩
  · have hA : Adapt (g' * n'⁻¹) (lf D (X.Fu u')) F' :=
      adapt_mul hg' (adapt_of_nlam (Formalism.L2.SG.Pf.nlam_inv hn'))
    have htl : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
    have e : g * n * t.lin = g' * n'⁻¹ := by rw [hlin]; group
    refine ⟨mul_mem hg.1 hn.1.1, fun a => ?_⟩
    show (g * n) (frame (mapLF t.lin (lf D (X.Fu u'))) a) - frame F' a ∈ _
    rw [frame_mapLF' _ htl, ← mul_apply_eq_comp, e]
    exact hA.2 a
  · show Λ = Formalism.HermitianLatticesTheory.gmap (g * n) Λ₁
    have hn1 : Formalism.HermitianLatticesTheory.gmap n Λ₁ = Λ₁ := hn.1.2
    rw [gmap_mul', hn1, ← hgΛ, ← gmap_mul', mul_inv_cancel, gmap_one']

end GlobalTheory.RowTermReal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRowTermOfLocalCompletionsTermsStatement
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rowTerm_of_local_completions_terms : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (Λ : LV D) (y : Dat Z FP), LocOver Λ y → ∃ t : TauC Y u u', TG F F' t Λ := by
  first | exact @GlobalTheory.RowTermReal.exists_term_of_locOver | exact GlobalTheory.RowTermReal.exists_term_of_locOver | (intros; apply GlobalTheory.RowTermReal.exists_term_of_locOver <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenusStableUnderRationalComplementGroup
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenusStableUnderRationalComplementGroup
noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GenusStab

theorem finrank_Vp_k (D : D7) (p : PlF D) :
    Module.finrank (D.s.atP p).Ep (Vp D p) = D.R.k + 2 * D.R.rS + 1 := by
  rw [finrank_Vp]
  have h2 := D.R.two_le_m
  obtain ⟨c, hc⟩ := D.R.m_even
  simp only [Ranks.r, Ranks.rS]
  omega

theorem inGen_of_gRel : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (Λ : LV D) (d y y' : Dat Z FP), LocOver Λ y → InGen d y → GRel F F' y y' → InGen d y' := by
  intro D X Y u u' F F' w hw hG Z FP hB hRel Λ d y y' hov hgen hgr
  obtain ⟨hext, hUW, -, hmove⟩ := GlobalTheory.T.rationalAutomorphism_local_extension_moves_lattices D X Y u u' F F' w hw hG Z FP hB hRel
  obtain ⟨h, hh, hmv⟩ := hgr
  obtain ⟨y'', hov'', hmv''⟩ := hmove h hh Λ y hov
  have hact := fun p => GlobalTheory.T.exists_complementUnitary_mulAction_localInnerDatum (Z.M p) (Z.agree p).1 (locH Z p) D.R.rS D.R.k (FP p)
    (finrank_Vp_k D p) (hRel p)
  choose act hiff _ using hact
  have heq : ∀ p, y' p = y'' p := by
    intro p
    obtain ⟨g1, he1, hm1⟩ := hmv p
    obtain ⟨g2, he2, hm2⟩ := hmv'' p
    obtain rfl : g1 = g2 := (hext h p).unique he1 he2
    have hg : g1 ∈ (FP p).UW0 := hUW h hh p g1 he1
    have a1 := ((hiff p) ⟨g1, hg⟩ (y p) (y' p)).1 hm1
    have a2 := ((hiff p) ⟨g1, hg⟩ (y p) (y'' p)).1 hm2
    rw [← a1, ← a2]
  refine ⟨fun p => ?_, ?_⟩
  · obtain ⟨g0, hg0, hm0⟩ := hgen.1 p
    obtain ⟨g1, he1, hm1⟩ := hmv p
    have hg1 : g1 ∈ (FP p).UW0 := hUW h hh p g1 he1
    have a0 := ((hiff p) ⟨g0, hg0⟩ (d p) (y p)).1 hm0
    have a1 := ((hiff p) ⟨g1, hg1⟩ (y p) (y' p)).1 hm1
    refine ⟨g1 * g0, mul_mem hg1 hg0, ((hiff p) ⟨g1 * g0, mul_mem hg1 hg0⟩ (d p) (y' p)).2 ?_⟩
    letI := act p
    let a : (FP p).UW0 := ⟨g1, hg1⟩
    let b : (FP p).UW0 := ⟨g0, hg0⟩
    have hm : (a * b) • d p = a • (b • d p) := mul_smul a b (d p)
    change (a * b) • d p = y' p
    rw [hm]
    change a • (act p).smul b (d p) = y' p
    rw [a0]
    exact a1
  · have full_of_over (L : LV D) (z : Dat Z FP) (hz : LocOver L z) :
        Submodule.IsFullLattice D.host.E L := by
      obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 D.host.F)
      let p : PlF D := ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField D.host.F)⟩
      obtain ⟨t, ht, heq⟩ := hz.2 p
      have hspan : Submodule.span (D.s.atP p).Ep (lattice₂ D Z.M p L : Set (Vp D p)) = ⊤ := by
        rw [← heq]
        exact (GlobalTheory.T.localTermLattice_over_innerDatum_fg_span D Z FP p (z p) t ht).2
      let U := Submodule.span D.host.E (L : Set (VS D).V)
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
      refine { toIsLattice := hz.1, span_eq_top := Submodule.eq_of_le_of_finrank_le le_top ?_ }
      rw [finrank_top, Module.finrank_eq_card_basis (VS D).frame, Fintype.card_fin]
      simpa only [Module.finrank_fin_fun, Fintype.card_fin] using
        finrank_le_of_span_eq_top (show Submodule.span (D.s.atP p).Ep _ = ⊤ from htop)
    have hfin := ((GlobalTheory.T.hermitianLattice_local_global_principle D Z).1 Λ (Formalism.HermitianLatticesTheory.gmap h Λ) (full_of_over Λ y hov) (full_of_over _ y'' hov'')).1
    refine (hfin.union hgen.2).subset fun p hp => ?_
    by_cases hyd : y p = d p
    · left
      intro hl
      apply hp
      rw [heq p, ← hyd]
      obtain ⟨τ, hτ, hL⟩ := hov.2 p
      obtain ⟨τ'', hτ'', hL''⟩ := hov''.2 p
      have hlam : τ''.abelian₂ = τ.abelian₂ := by rw [hL'', hL]; exact hl.symm
      have key := GlobalTheory.T.hermitianDatum_eq_of_same_lattice (Z.M p) (Z.agree p).1 (locH Z p) D.R.rS D.R.k (FP p)
        (finrank_Vp_k D p) (hRel p) (y'' p) (y p) τ'' τ hτ'' hτ
      exact key hlam
    · right
      exact hyd

end GlobalTheory.GenusStab
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenusStableUnderRationalComplementGroupStatement
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genus_stable_under_rationalComplementGroup : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (Λ : LV D) (d y y' : Dat Z FP), LocOver Λ y → InGen d y → GRel F F' y y' → InGen d y' := by
  first | exact @GlobalTheory.GenusStab.inGen_of_gRel | exact GlobalTheory.GenusStab.inGen_of_gRel | (intros; apply GlobalTheory.GenusStab.inGen_of_gRel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenusFamilyCarriedByLatticeInLocalOrbits
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenusFamilyCarriedByLatticeInLocalOrbits
noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold.GlueOrbit

variable {D : D7}

theorem finrank_loc (p : PlF D) :
    Module.finrank (D.s.atP p).Ep (Vp D p) = D.R.k + 2 * D.R.rS + 1 := by
  rw [finrank_Vp]
  have h1 := D.R.m_even
  have h2 := D.R.two_le_m
  have h3 := D.R.m_add_three_le_k
  obtain ⟨c, hc⟩ := h1
  simp only [Ranks.r, Ranks.rS]
  omega

theorem localLattice_fg_and_span_eq_top (Z : LocDat D) (Λ : LV D) (h : Submodule.IsFullLattice D.host.E Λ) (p : PlF D) :
    (lattice₂ D Z.M p Λ).FG ∧ Submodule.span (D.s.atP p).Ep (lattice₂ D Z.M p Λ : Set (Vp D p)) = ⊤ := by
  have hmap : Submodule.IsFullLattice D.host.E (LatLoc.cL Λ) := by
    refine { toIsLattice := LatLoc.isLattice_map _ _ h.toIsLattice, span_eq_top := ?_ }
    change Submodule.span D.host.E (((LatLoc.cE D).toLinearMap) '' (Λ : Set (VS D).V)) = ⊤
    rw [Submodule.span_image, h.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
    exact (LatLoc.cE D).surjective
  have := (GlobalTheory.T.numberField_lattice_determined_by_local_lattices (GlobalTheory.HL.placesOf Z) (nV D) (LatLoc.cL Λ) hmap).2.1 p
  rw [LatLoc.localLattice_eq]
  exact this

theorem img_one {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (L : Submodule M.L.O V) :
    LocNG.img (1 : V ≃ₗ[E] V) L = L := by
  ext x
  simp [LocNG.img]

theorem img_lattice {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (g : V ≃ₗ[E] V) (L : Submodule M.L.O V)
    (h : L.FG ∧ Submodule.span E (L : Set V) = ⊤) :
    (LocNG.img g L).FG ∧ Submodule.span E (LocNG.img g L : Set V) = ⊤ := by
  refine ⟨h.1.map _, ?_⟩
  unfold LocNG.img
  rw [Submodule.map_coe]
  have e1 : (⇑((g : V →ₗ[E] V).restrictScalars M.L.O) : V → V) = ⇑(g : V →ₗ[E] V) := rfl
  rw [e1, Submodule.span_image, h.2, Submodule.map_top, LinearMap.range_eq_top]
  exact g.surjective

theorem glue_local_orbits : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (Λ : LV D) (y y' : Dat Z FP), LocOver Λ y → InGen y y' → ∃ Λ', LocOver Λ' y' ∧ ∀ p, ∃ h ∈ (FP p).UW0, LocNG.img h (lattice₂ D Z.M p Λ) = lattice₂ D Z.M p Λ' := by
  intro D X Y u u' F F' w _ _ Z FP _ hR Λ y y' ⟨hΛ, hτ⟩ ⟨hrel, hfin⟩
  have key : ∀ p, ∃ h ∈ (FP p).UW0, (y' p = y p → h = 1) ∧
      ∃ τ : Loc.Term (Vp D p) (Z.M p) D.R.rS, LocNG.IsTermOver (FP p) (y' p) τ ∧
        τ.abelian₂ = LocNG.img h (lattice₂ D Z.M p Λ) := by
    intro p
    obtain ⟨τ, hτ1, hτ2⟩ := hτ p
    by_cases hp : y' p = y p
    · exact ⟨1, one_mem _, fun _ => rfl, τ, hp ▸ hτ1, by rw [img_one, hτ2]⟩
    · obtain ⟨g, hg, hm⟩ := hrel p
      exact ⟨g, hg, fun h => absurd h hp, _,
        (GlobalTheory.T.unitaryComplement_moves_local_terms_with_data (Z.M p) (Z.agree p).1 (locH Z p) D.R.rS D.R.k (FP p) (finrank_loc p) (hR p) g hg
          (y p) (y' p) τ hτ1 hm).1, by rw [← hτ2]⟩
  choose h hU h1 τ hτ1 hτ2 using key
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 D.host.F)
  let p : PlF D := ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (NumberField.RingOfIntegers.not_isField D.host.F)⟩
  obtain ⟨t, ht, heq⟩ := hτ p
  have hspan : Submodule.span (D.s.atP p).Ep (lattice₂ D Z.M p Λ : Set (Vp D p)) = ⊤ := by
    rw [← heq]
    exact (GlobalTheory.T.localTermLattice_over_innerDatum_fg_span D Z FP p (y p) t ht).2
  have hfull : Submodule.IsFullLattice D.host.E Λ := by
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
  obtain ⟨Λ', hΛ', hp⟩ := (GlobalTheory.T.hermitianLattice_local_global_principle D Z).2 Λ hfull (fun p => LocNG.img (h p) (lattice₂ D Z.M p Λ))
    (fun p => by
      obtain ⟨t, ht, heq⟩ := hτ p
      apply img_lattice
      rw [← heq]
      exact GlobalTheory.T.localTermLattice_over_innerDatum_fg_span D Z FP p (y p) t ht)
    (hfin.subset fun p hp hc => hp (by simp only [h1 p hc, img_one]))
  exact ⟨Λ', ⟨hΛ', fun p => ⟨τ p, hτ1 p, (hτ2 p).trans (hp p).symm⟩⟩, fun p => ⟨h p, hU p, (hp p).symm⟩⟩

end GlobalTheory.Unfold.GlueOrbit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenusFamilyCarriedByLatticeInLocalOrbitsStatement
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genusFamily_carried_by_lattice_in_localOrbits : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (Λ : LV D) (y y' : Dat Z FP), LocOver Λ y → InGen y y' → ∃ Λ', LocOver Λ' y' ∧ ∀ p, ∃ h ∈ (FP p).UW0, LocNG.img h (lattice₂ D Z.M p Λ) = lattice₂ D Z.M p Λ' := by
  first | exact @GlobalTheory.Unfold.GlueOrbit.glue_local_orbits | exact GlobalTheory.Unfold.GlueOrbit.glue_local_orbits | (intros; apply GlobalTheory.Unfold.GlueOrbit.glue_local_orbits <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EquivalenceComplementUnitaryOrbitLocalInnerDatum
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EquivalenceComplementUnitaryOrbitLocalInnerDatum
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OrbitRel

open Formalism.MainNotions.S.Loc ValuativeRel

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]
variable {H : HermSp M V} {r : ℕ}

theorem framePairFixator_unitary_and_fixes_frame (P : Formalism.MainNotions.S.LocNG.FPair H r) {g : V ≃ₗ[E] V} (hg : g ∈ P.UW0) :
    Formalism.MainNotions.S.LocNG.IsUnitary H g ∧ ∀ b, g (P.A.f b) = P.A.f b ∧ g (P.B.f b) = P.B.f b := by
  unfold Formalism.MainNotions.S.LocNG.FPair.UW0 at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one => exact ⟨fun x y => rfl, fun b => ⟨rfl, rfl⟩⟩
  | mul x y _ _ hx hy =>
    refine ⟨fun u v => ?_, fun b => ⟨?_, ?_⟩⟩
    · show H.h (x (y u)) (x (y v)) = H.h u v
      rw [hx.1, hy.1]
    · show x (y (P.A.f b)) = P.A.f b
      rw [(hy.2 b).1, (hx.2 b).1]
    · show x (y (P.B.f b)) = P.B.f b
      rw [(hy.2 b).2, (hx.2 b).2]
  | inv x _ hx =>
    refine ⟨fun u v => ?_, fun b => ⟨?_, ?_⟩⟩
    · show H.h (x.symm u) (x.symm v) = H.h u v
      have := hx.1 (x.symm u) (x.symm v)
      simpa using this.symm
    · show x.symm (P.A.f b) = P.A.f b
      conv_lhs => rw [← (hx.2 b).1]
      simp
    · show x.symm (P.B.f b) = P.B.f b
      conv_lhs => rw [← (hx.2 b).2]
      simp

theorem perp_stable {g : V ≃ₗ[E] V} (hu : Formalism.MainNotions.S.LocNG.IsUnitary H g) {f : Fin (r + 1) → V}
    (hf : ∀ b, g (f b) = f b) {x : V} (hx : x ∈ H.perp (H.X f)) : g x ∈ H.perp (H.X f) := by
  intro v hv
  have hfix : Set.EqOn (g : V →ₗ[E] V) (LinearMap.id : V →ₗ[E] V) (Set.range fun a : Fin r => f a.castSucc) := by
    rintro _ ⟨a, rfl⟩
    simpa using hf a.castSucc
  have hv' : g v = v := LinearMap.eqOn_span' hfix hv
  have := hu x v
  rw [hv'] at this
  rw [this]
  exact hx v hv

theorem rel_equivalence (P : Formalism.MainNotions.S.LocNG.FPair H r) :
    Equivalence (Formalism.MainNotions.S.LocNG.Datum.Rel (P := P)) := by
  refine ⟨fun d => ?_, fun {d d'} h => ?_, fun {d d' d''} h h' => ?_⟩
  · refine ⟨1, P.UW0.one_mem, ?_, ?_, ?_⟩
    · intro x y hxy
      have : y = x := Subtype.ext (by simpa using hxy)
      subst this; exact Iff.rfl
    · intro x y hxy
      have : y = x := Subtype.ext (by simpa using hxy)
      subst this; exact Iff.rfl
    · intro x' y' x y hx' hx
      have e1 : y' = x' := Subtype.ext (by simpa using hx')
      have e2 : y = x := Subtype.ext (by simpa using hx)
      subst e1; subst e2; exact Iff.rfl
  · obtain ⟨g, hg, h1, h2, h3⟩ := h
    refine ⟨g⁻¹, P.UW0.inv_mem hg, ?_, ?_, ?_⟩
    · intro x y hxy
      have : (x : V) = g y := by rw [hxy]; show (x : V) = g (g.symm x); simp
      exact (h1 y x this).symm
    · intro x y hxy
      have : (x : V) = g y := by rw [hxy]; show (x : V) = g (g.symm x); simp
      exact (h2 y x this).symm
    · intro x' y' x y hx' hx
      have a1 : (x' : V) = g y' := by rw [hx']; show (x' : V) = g (g.symm x'); simp
      have a2 : (x : V) = g y := by rw [hx]; show (x : V) = g (g.symm x); simp
      exact (h3 y' x' y x a1 a2).symm
  · obtain ⟨g, hg, h1, h2, h3⟩ := h
    obtain ⟨g', hg', h1', h2', h3'⟩ := h'
    have hs := framePairFixator_unitary_and_fixes_frame P hg
    refine ⟨g' * g, P.UW0.mul_mem hg' hg, ?_, ?_, ?_⟩
    · intro x y hxy
      let z : ↥(H.perp (H.X P.A.f)) :=
        ⟨g x, perp_stable hs.1 (fun b => (hs.2 b).1) x.2⟩
      exact (h1 x z rfl).trans (h1' z y hxy)
    · intro x y hxy
      let z : ↥(H.perp (H.X P.B.f)) :=
        ⟨g x, perp_stable hs.1 (fun b => (hs.2 b).2) x.2⟩
      exact (h2 x z rfl).trans (h2' z y hxy)
    · intro x' y' x y hx' hx
      let z' : ↥(H.perp (H.X P.B.f)) :=
        ⟨g x', perp_stable hs.1 (fun b => (hs.2 b).2) x'.2⟩
      let z : ↥(H.perp (H.X P.A.f)) :=
        ⟨g x, perp_stable hs.1 (fun b => (hs.2 b).1) x.2⟩
      exact (h3 x' z' x z rfl rfl).trans (h3' z' y' z y hx' hx)

theorem relEqv : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, Formalism.MainNotions.S.LocNG.FPair (locH Z p) D.R.rS)
    (p : PlF D), Equivalence (Formalism.MainNotions.S.LocNG.Datum.Rel (P := FP p)) :=
  fun _ _ FP p => rel_equivalence (FP p)

end GlobalTheory.OrbitRel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EquivalenceComplementUnitaryOrbitLocalInnerDatumStatement
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equivalence_complementUnitaryOrbit_localInnerDatum_at_place : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (p : PlF D), Equivalence (LocNG.Datum.Rel (P := FP p)) := by
  first | exact @GlobalTheory.OrbitRel.relEqv | exact GlobalTheory.OrbitRel.relEqv | (intros; apply GlobalTheory.OrbitRel.relEqv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnfoldingGenusWeightsSumToMass
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold.SumK

theorem inGen_symm_of {D : D7} {Z : LocDat D} {FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS}
    (hE : ∀ p, Equivalence (LocNG.Datum.Rel (P := FP p))) {d y y' : Dat Z FP}
    (h : InGen d y) (h' : InGen d y') : InGen y y' := by
  refine ⟨fun p => (hE p).trans ((hE p).symm (h.1 p)) (h'.1 p), ?_⟩
  apply (h.2.union h'.2).subset
  intro p hp
  by_contra hc
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc
  exact hp (by rw [hc.1, hc.2])

theorem weights_add_up_to_mass_of
    (hRelEqv : ∀ (D : D7) (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (p : PlF D), Equivalence (LocNG.Datum.Rel (P := FP p)))
    (hInv : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ (Λ : LV D) (d y y' : Dat Z FP), LocOver Λ y → InGen d y → GRel F F' y y' → InGen d y') :
    ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ TS : Set (TauC Y u u'), LocClosed F F' Z FP TS → ∀ (t₀ : TauC Y u u') (Λ₀ : LV D) (y₀ d : Dat Z FP), t₀ ∈ TS → TG F F' t₀ Λ₀ → LocOver Λ₀ y₀ → InGen d y₀ → ∀ K, K = {κ | ∃ t ∈ TS, ∃ (Λ : LV D) (y : Dat Z FP), TG F F' t Λ ∧ LocOver Λ y ∧ InGen d y ∧ key t = κ} → ∀ ω : K → ℝ, (∀ κ : K, ∀ t : TauC Y u u', key t = κ.1 → ω κ = wt t ^ 2) → ∑' κ : K, ENNReal.ofReal (ω κ) = massA F F' d := by
  intro D X Y u u' F F' w hw hG Z FP hB hR TS hTS t₀ Λ₀ y₀ d ht₀ hTG₀ hLO₀ hIG₀ K hK ω hω
  subst hK
  obtain ⟨hEq, -, hRel⟩ := GlobalTheory.T.rationalClass_lattices_iff_rationalClass_localFramePairs D X Y u u' F F' w hw hG Z FP hB hR
  have hQ : ∀ y y' : Dat Z FP, (Quot.mk (GRel (Z := Z) (FP := FP) F F') y) = Quot.mk _ y' ↔ GRel F F' y y' :=
    fun y y' => ⟨fun h => hEq.eqvGen_iff.1 (Quot.eqvGen_exact h), Quot.sound⟩
  have hout : ∀ o : Quot (GRel (Z := Z) (FP := FP) F F'), ∀ y, Quot.mk _ y = o → GRel F F' o.out y := by
    intro o y h
    exact (hQ _ _).1 (by rw [h, Quot.out_eq])

  have hex : ∀ κ : {κ | ∃ t ∈ TS, ∃ (Λ : LV D) (y : Dat Z FP), TG F F' t Λ ∧ LocOver Λ y ∧ InGen d y ∧ key t = κ},
      ∃ y : Dat Z FP, ∃ t ∈ TS, ∃ Λ : LV D, TG F F' t Λ ∧ LocOver Λ y ∧ InGen d y ∧ key t = κ.1 := by
    rintro ⟨κ, t, ht, Λ, y, h1, h2, h3, h4⟩
    exact ⟨y, t, ht, Λ, h1, h2, h3, h4⟩
  choose yOf hyOf using hex
  set φ := fun κ => (Quot.mk (GRel (Z := Z) (FP := FP) F F') (yOf κ)) with hφ
  have hwd : ∀ (t t' : TauC Y u u') (Λ Λ' : LV D) (y y' : Dat Z FP), TG F F' t Λ → TG F F' t' Λ' →
      LocOver Λ y → LocOver Λ' y' → key t = key t' → GRel F F' y y' := fun t t' Λ Λ' y y' h1 h2 h3 h4 h5 =>
    ((hRel Λ Λ' y y' h3 h4).1).1 (GlobalTheory.T.same_row_doubleCoset_inner_data_one_rational_class D X Y u u' F F' w hw hG t t' Λ Λ' h1 h2 h5)
  have hImg : ∀ κ, InGen d (φ κ).out := by
    intro κ
    obtain ⟨t, -, Λ, h1, h2, h3, -⟩ := hyOf κ
    exact hInv D X Y u u' F F' w hw hG Z FP hB hR Λ d (yOf κ) _ h2 h3 (hEq.symm (hout _ _ rfl))
  unfold massA
  rw [← ENNReal.tsum_fiberwise _ φ]
  refine tsum_congr fun o => ?_
  by_cases ho : InGen d o.out
  · rw [if_pos ho]
    have hIG01 : InGen y₀ o.out := inGen_symm_of (hRelEqv D Z FP) hIG₀ ho
    obtain ⟨Λ₁, hLO₁, hloc⟩ := GlobalTheory.T.genusFamily_carried_by_lattice_in_localOrbits D X Y u u' F F' w hw hG Z FP hB hR Λ₀ y₀ o.out hLO₀ hIG01
    obtain ⟨t₁, hTG₁⟩ := GlobalTheory.T.exists_rowTerm_of_local_completions_terms D X Y u u' F F' w hw hG Z FP hB hR Λ₁ o.out hLO₁
    have ht₁ : t₁ ∈ TS := hTS t₀ t₁ Λ₀ Λ₁ hTG₀ hTG₁ hloc ht₀
    obtain ⟨-, hcarry, hwt, hmass⟩ := GlobalTheory.T.orbitCount_rows_doubleCosets_innerDatum_class D X Y u u' F F' w hw hG t₁ Λ₁ hTG₁ _ rfl
    have hRefl : LRel F F' Λ₁ Λ₁ := ((hRel Λ₁ Λ₁ o.out o.out hLO₁ hLO₁).1).2 (hEq.refl _)
    have hStab : stabL F F' Λ₁ = stabY F F' o.out := (hRel Λ₁ Λ₁ o.out o.out hLO₁ hLO₁).2

    have hfib : Subtype.val '' (φ ⁻¹' {o}) =
        {κ | ∃ (t : TauC Y u u') (Λ' : LV D), TG F F' t Λ' ∧ LRel F F' Λ₁ Λ' ∧ key t = κ} := by
      ext κ
      constructor
      · rintro ⟨b, hb, rfl⟩
        obtain ⟨t, -, Λ, h1, h2, -, h4⟩ := hyOf b
        have hb' : φ b = o := hb
        refine ⟨t, Λ, h1, ((hRel Λ₁ Λ o.out (yOf b) hLO₁ h2).1).2 (hout o _ hb'), h4⟩
      · rintro hκ
        obtain ⟨t, hTG, hkey⟩ := hcarry κ hκ
        have htS : t ∈ TS := hTS t₁ t Λ₁ Λ₁ hTG₁ hTG
          (fun p => ⟨1, Subgroup.one_mem _, by
            simp [LocNG.img]⟩) ht₁
        have hmem : κ ∈ {κ | ∃ t ∈ TS, ∃ (Λ : LV D) (y : Dat Z FP), TG F F' t Λ ∧ LocOver Λ y ∧ InGen d y ∧ key t = κ} :=
          ⟨t, htS, Λ₁, o.out, hTG, hLO₁, ho, hkey⟩
        refine ⟨⟨κ, hmem⟩, ?_, rfl⟩
        show φ ⟨κ, hmem⟩ = o
        obtain ⟨t', -, Λ', h1, h2, -, h4⟩ := hyOf ⟨κ, hmem⟩
        rw [hφ]
        simp only
        rw [← Quot.out_eq o]
        exact Quot.sound (hwd t' t Λ' Λ₁ _ _ h1 hTG h2 hLO₁ (h4.trans hkey.symm))
    have hconst : ∀ b : φ ⁻¹' {o}, ENNReal.ofReal (ω b.1) = ENNReal.ofReal (wt t₁ ^ 2) := by
      intro b
      have hb : b.1.1 ∈ Subtype.val '' (φ ⁻¹' {o}) := ⟨b.1, b.2, rfl⟩
      rw [hfib] at hb
      obtain ⟨t, hTG, hkey⟩ := hcarry _ hb
      rw [hω b.1 t hkey, hwt t Λ₁ hTG hRefl]
    rw [tsum_congr hconst, ENNReal.tsum_set_const, ← Subtype.val_injective.encard_image, hfib, hmass, hStab]
  · rw [if_neg ho]
    refine ENNReal.tsum_eq_zero.2 fun b => (ho ?_).elim
    have hb : φ b.1 = o := b.2
    rw [← hb]
    exact hImg b.1

theorem weights_add_up_to_mass : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ TS : Set (TauC Y u u'), LocClosed F F' Z FP TS → ∀ (t₀ : TauC Y u u') (Λ₀ : LV D) (y₀ d : Dat Z FP), t₀ ∈ TS → TG F F' t₀ Λ₀ → LocOver Λ₀ y₀ → InGen d y₀ → ∀ K, K = {κ | ∃ t ∈ TS, ∃ (Λ : LV D) (y : Dat Z FP), TG F F' t Λ ∧ LocOver Λ y ∧ InGen d y ∧ key t = κ} → ∀ ω : K → ℝ, (∀ κ : K, ∀ t : TauC Y u u', key t = κ.1 → ω κ = wt t ^ 2) → ∑' κ : K, ENNReal.ofReal (ω κ) = massA F F' d :=
  weights_add_up_to_mass_of GlobalTheory.T.equivalence_complementUnitaryOrbit_localInnerDatum_at_place GlobalTheory.T.genus_stable_under_rationalComplementGroup

end GlobalTheory.Unfold.SumK
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnfoldingGenusWeightsSumToMassStatement
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfolding_genus_weights_sum_to_mass : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ (Z : LocDat D) (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS), Based Z FP (Tu D u) (Tu D u') F F' → (∀ p, (FP p).RelG (LocNG.theta (Z.M p))) → ∀ TS : Set (TauC Y u u'), LocClosed F F' Z FP TS → ∀ (t₀ : TauC Y u u') (Λ₀ : LV D) (y₀ d : Dat Z FP), t₀ ∈ TS → TG F F' t₀ Λ₀ → LocOver Λ₀ y₀ → InGen d y₀ → ∀ K, K = {κ | ∃ t ∈ TS, ∃ (Λ : LV D) (y : Dat Z FP), TG F F' t Λ ∧ LocOver Λ y ∧ InGen d y ∧ key t = κ} → ∀ ω : K → ℝ, (∀ κ : K, ∀ t : TauC Y u u', key t = κ.1 → ω κ = wt t ^ 2) → ∑' κ : K, ENNReal.ofReal (ω κ) = massA F F' d := by
  first | exact @GlobalTheory.Unfold.SumK.weights_add_up_to_mass | exact GlobalTheory.Unfold.SumK.weights_add_up_to_mass | (intros; apply GlobalTheory.Unfold.SumK.weights_add_up_to_mass <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowWeightsLocalOrbitsSumEqGenusMass
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.FamDefs Formalism.FourierDecayAlt GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold.GenusRows

section Loc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Formalism.MainNotions.S.Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : Formalism.MainNotions.S.Loc.HermSp M V}
  {r k : ℕ} {P : Formalism.MainNotions.S.LocNG.FPair H r}

theorem rel_symm (hM : M.OK) (hk : Module.finrank E V = k + 2 * r + 1)
    (hR : P.RelG (Formalism.MainNotions.S.LocNG.theta M)) {d d' : Formalism.MainNotions.S.LocNG.Datum P}
    (h : Formalism.MainNotions.S.LocNG.Datum.Rel d d') : Formalism.MainNotions.S.LocNG.Datum.Rel d' d := by
  obtain ⟨act, hmv, -⟩ := GlobalTheory.T.exists_complementUnitary_mulAction_localInnerDatum M hM H r k P hk hR
  obtain ⟨g, hg, hm⟩ := h
  have e1 : act.smul ⟨g, hg⟩ d = d' := (hmv ⟨g, hg⟩ d d').1 hm
  refine ⟨((⟨g, hg⟩ : P.UW0)⁻¹ : P.UW0).1, ((⟨g, hg⟩ : P.UW0)⁻¹ : P.UW0).2, (hmv _ d' d).2 ?_⟩
  letI := act
  rw [← e1]
  change ((⟨g, hg⟩ : P.UW0)⁻¹ : P.UW0) • ((⟨g, hg⟩ : P.UW0) • d) = d
  exact inv_smul_smul _ d

theorem rel_trans (hM : M.OK) (hk : Module.finrank E V = k + 2 * r + 1)
    (hR : P.RelG (Formalism.MainNotions.S.LocNG.theta M)) {a b c : Formalism.MainNotions.S.LocNG.Datum P}
    (h1 : Formalism.MainNotions.S.LocNG.Datum.Rel a b) (h2 : Formalism.MainNotions.S.LocNG.Datum.Rel b c) :
    Formalism.MainNotions.S.LocNG.Datum.Rel a c := by
  obtain ⟨act, hmv, -⟩ := GlobalTheory.T.exists_complementUnitary_mulAction_localInnerDatum M hM H r k P hk hR
  obtain ⟨g, hg, hm⟩ := h1
  obtain ⟨g', hg', hm'⟩ := h2
  have e1 : act.smul ⟨g, hg⟩ a = b := (hmv ⟨g, hg⟩ a b).1 hm
  have e2 : act.smul ⟨g', hg'⟩ b = c := (hmv ⟨g', hg'⟩ b c).1 hm'
  refine ⟨((⟨g', hg'⟩ : P.UW0) * ⟨g, hg⟩ : P.UW0).1, ((⟨g', hg'⟩ : P.UW0) * ⟨g, hg⟩ : P.UW0).2,
    (hmv _ a c).2 ?_⟩
  letI := act
  rw [← e2, ← e1]
  change ((⟨g', hg'⟩ : P.UW0) * ⟨g, hg⟩) • a = (⟨g', hg'⟩ : P.UW0) • ((⟨g, hg⟩ : P.UW0) • a)
  exact mul_smul _ _ a

theorem eq_of_rel_reps (hM : M.OK) (hk : Module.finrank E V = k + 2 * r + 1)
    (hR : P.RelG (Formalism.MainNotions.S.LocNG.theta M)) (R : Formalism.MainNotions.S.LocNG.Reps P) {d₁ d₂ y : Formalism.MainNotions.S.LocNG.Datum P}
    (h₁ : d₁ ∈ R.RD) (h₂ : d₂ ∈ R.RD) (r₁ : Formalism.MainNotions.S.LocNG.Datum.Rel d₁ y)
    (r₂ : Formalism.MainNotions.S.LocNG.Datum.Rel d₂ y) : d₁ = d₂ :=
  R.hRD.2.2 d₁ h₁ d₂ h₂ (rel_trans hM hk hR r₁ (rel_symm hM hk hR r₂))

theorem term_of_rel (hM : M.OK) (hk : Module.finrank E V = k + 2 * r + 1)
    (hR : P.RelG (Formalism.MainNotions.S.LocNG.theta M)) {d d' : Formalism.MainNotions.S.LocNG.Datum P}
    (h : Formalism.MainNotions.S.LocNG.Datum.Rel d d') (ht : ∃ τ, Formalism.MainNotions.S.LocNG.IsTermOver P d τ) :
    ∃ τ, Formalism.MainNotions.S.LocNG.IsTermOver P d' τ := by
  obtain ⟨g, hg, hm⟩ := h
  obtain ⟨τ, hτ⟩ := ht
  exact ⟨_, (GlobalTheory.T.unitaryComplement_moves_local_terms_with_data M hM H r k P hk hR g hg d d' τ hτ hm).1⟩

end Loc


private theorem full_of_local_span (D : D7) (Z : LocDat D) (Λ : LV D)
    (hΛ : Submodule.IsLattice D.host.E Λ) (p : PlF D)
    (hspan : Submodule.span (D.s.atP p).Ep (lattice₂ D Z.M p Λ : Set (Vp D p)) = ⊤) :
    Submodule.IsFullLattice D.host.E Λ := by
  let A := GlobalTheory.HL.placesOf Z
  let L := GlobalTheory.Unfold.LatLoc.cL Λ
  haveI := (A.loc p).lf
  haveI := (A.loc p).char0
  haveI := GlobalTheory.HL.PlacesInt.nontrivial_Ep (A.loc p)
  have hc : Submodule.IsFullLattice D.host.E L := by
    refine { toIsLattice := GlobalTheory.Unfold.LatLoc.isLattice_map _ _ hΛ, span_eq_top := ?_ }
    by_contra hne
    obtain ⟨φ, hφ, hzero⟩ :=
      Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.mpr hne) inferInstance
    let ψ : (Fin (nV D) → (A.loc p).Ep) →ₗ[(A.loc p).Ep] (A.loc p).Ep :=
      ∑ i : Fin (nV D), (A.loc p).ιE (φ fun j => if i = j then 1 else 0) • LinearMap.proj i
    have hψ (z : Fin (nV D) → D.host.E) : ψ (A.bc p z) = (A.loc p).ιE (φ z) := by
      rw [φ.pi_apply_eq_sum_univ z, map_sum]
      simp only [ψ, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply,
        smul_eq_mul, map_mul, GlobalTheory.HL.Places.bc]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    have hlat : A.lat p L ≤ (LinearMap.ker ψ).restrictScalars (A.L p).O := by
      apply Submodule.span_le.mpr
      rintro _ ⟨z, hz, rfl⟩
      have hz' : φ z ∈ (⊥ : Submodule D.host.E D.host.E) := by
        rw [← hzero]
        exact Submodule.mem_map_of_mem (Submodule.subset_span hz)
      change ψ (A.bc p z) = 0
      rw [hψ, (Submodule.mem_bot D.host.E).mp hz', map_zero]
    have hker : Submodule.span (A.loc p).Ep (A.lat p L : Set _) ≤ LinearMap.ker ψ :=
      Submodule.span_le.mpr hlat
    rw [GlobalTheory.Unfold.LatLoc.localLattice_eq Z p Λ] at hspan
    change Submodule.span (A.loc p).Ep (A.lat p L : Set (Fin (nV D) → (A.loc p).Ep)) = ⊤ at hspan
    rw [hspan] at hker
    apply hφ
    apply LinearMap.ext
    intro z
    have hz := LinearMap.mem_ker.mp (hker (Submodule.mem_top (x := A.bc p z)))
    rw [hψ] at hz
    exact (map_eq_zero_iff _ (A.loc p).ιE.injective).mp hz
  refine { toIsLattice := hΛ, span_eq_top := ?_ }
  have hm : (Submodule.span D.host.E (Λ : Set (VS D).V)).map
      (GlobalTheory.Unfold.LatLoc.cE D).toLinearMap = ⊤ := by
    rw [← Submodule.span_image]
    exact hc.span_eq_top
  rw [← Submodule.comap_map_eq_of_injective (GlobalTheory.Unfold.LatLoc.cE D).injective
    (Submodule.span D.host.E (Λ : Set (VS D).V)), hm,
    Submodule.comap_top]

set_option maxHeartbeats 1000000 in
theorem rows_mass_genus : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ {Cl : Type} (TS : Set (TauC Y u u')) (cls : TauC Y u u' → Cl) (Fm : LocFam (zOf Y) Cl (NuC D)), Based (zOf Y) Fm.FP (Tu D u) (Tu D u') F F' → ClsRow TS cls → LocClosed F F' (zOf Y) Fm.FP TS → (∀ p ∈ Fm.P, ∀ d ∈ Fm.Ds p, d ∈ (Fm.R p).RD) → (∀ p, p ∉ Fm.P → ∀ t ∈ TS, ptPN t = toPts w → OverOrb Fm t p (Fm.d0 p)) → (∃ Λ₀ : LV D, Submodule.IsLattice D.host.E Λ₀ ∧ ∀ p, p ∉ Fm.P → ∃ τ, LocNG.IsTermOver (Fm.FP p) (Fm.d0 p) τ ∧ τ.abelian₂ = lattice₂ D (zOf Y).M p Λ₀) → (∀ c ν, (Fm.dat c ν = none → ¬ ∃ t ∈ TS, cls t = c ∧ ptPN t = toPts w ∧ nmlOf Y u u' t = ν) ∧ ∀ d, Fm.dat c ν = some d → (∃ t ∈ TS, cls t = c ∧ ptPN t = toPts w ∧ nmlOf Y u u' t = ν) ∧ ∀ t ∈ TS, cls t = c → ptPN t = toPts w → nmlOf Y u u' t = ν → (∀ p (hp : p ∈ Fm.P), OverOrb Fm t p (d ⟨p, hp⟩).1) ∧ Fm.rw c = (wt t) ^ 2) → ∀ d : (∀ p : {p // p ∈ Fm.P}, {d // d ∈ Fm.Ds p.1}), (∃ x : Cl × NuC D, Fm.dat x.1 x.2 = some d) → ∀ dd : Dat (zOf Y) Fm.FP, (∀ p (hp : p ∈ Fm.P), dd p = (d ⟨p, hp⟩).1) → (∀ p, p ∉ Fm.P → dd p = Fm.d0 p) → (∀ p, ∃ τ, LocNG.IsTermOver (Fm.FP p) (dd p) τ) ∧ ∑' x : {x : Cl × NuC D // Fm.dat x.1 x.2 = some d}, ENNReal.ofReal (Fm.rw x.1.1) = massA F F' dd := by
  intro D X Y u u' F F' w hZ hG Cl TS cls Fm hB hCR hLC hDs hstd hΛ₀ hdat d hx dd hddP hddN
  have hRG : ∀ p, (Fm.FP p).RelG (Formalism.MainNotions.S.LocNG.theta ((zOf Y).M p)) := fun p =>
    (GlobalTheory.T.localisedBaseFrames_relevantPair D (zOf Y) u u' w F F' hZ hG p).2 _ ⟨(hB p).1, (hB p).2.1, (hB p).2.2.1, (hB p).2.2.2⟩
  have hMo : ∀ p, ((zOf Y).M p).OK := fun p => ((zOf Y).agree p).1
  have hrk : ∀ p : PlF D, Module.finrank (D.s.atP p).Ep (Vp D p) = D.R.k + 2 * D.R.rS + 1 := fun p => rank_Vp p
  have luniq : ∀ p (a b : Formalism.MainNotions.S.LocNG.Datum (Fm.FP p)) (τ τ' : Formalism.MainNotions.S.Loc.Term (Vp D p) ((zOf Y).M p) D.R.rS),
      Formalism.MainNotions.S.LocNG.IsTermOver (Fm.FP p) a τ → Formalism.MainNotions.S.LocNG.IsTermOver (Fm.FP p) b τ' → τ.abelian₂ = τ'.abelian₂ → a = b :=
    fun p a b τ τ' h1 h2 h3 => GlobalTheory.T.hermitianDatum_eq_of_same_lattice _ (hMo p) _ _ _ _ (hrk p) (hRG p) a b τ τ' h1 h2 h3
  have hA : ∀ t ∈ TS, ptPN t = toPts w → (∀ p (hp : p ∈ Fm.P), OverOrb Fm t p (d ⟨p, hp⟩).1) →
      ∃ (Λ : LV D) (y : Dat (zOf Y) Fm.FP), TG F F' t Λ ∧ LocOver Λ y ∧ InGen dd y ∧
        ∀ p a, OverOrb Fm t p a ↔ Formalism.MainNotions.S.LocNG.Datum.Rel a (y p) := by
    intro t ht hpt hov
    obtain ⟨Λ, hΛ⟩ := GlobalTheory.T.exists_termLattice_baseFrames_of_basePoint D X Y u u' F F' w hZ hG t hpt
    obtain ⟨y, hy, hyr⟩ := GlobalTheory.T.localData_of_term_lattice_and_orbits D X Y u u' F F' w hZ hG (zOf Y) Fm.FP hB hRG t Λ hΛ
    have hyr' : ∀ p a, OverOrb Fm t p a ↔ Formalism.MainNotions.S.LocNG.Datum.Rel a (y p) := fun p a => hyr p a
    refine ⟨Λ, y, hΛ, hy, ⟨fun p => ?_, ?_⟩, hyr'⟩
    · by_cases hp : p ∈ Fm.P
      · rw [hddP p hp]; exact (hyr' p _).1 (hov p hp)
      · rw [hddN p hp]; exact (hyr' p _).1 (hstd p hp t ht hpt)
    · obtain ⟨Λ₀, hL0, hτ0⟩ := hΛ₀
      by_cases hp0 : ∃ p, p ∉ Fm.P
      · obtain ⟨p0, hp0⟩ := hp0
        obtain ⟨τ0, hτ0o, hτ0l⟩ := hτ0 p0 hp0
        obtain ⟨τ, hτo, hτl⟩ := hy.2 p0
        have hfull : Submodule.IsFullLattice D.host.E Λ :=
          full_of_local_span D (zOf Y) Λ hy.1 p0 (by
            rw [← hτl]
            exact (GlobalTheory.T.localTermLattice_over_innerDatum_fg_span D (zOf Y) Fm.FP p0 (y p0) τ hτo).2)
        have hfull0 : Submodule.IsFullLattice D.host.E Λ₀ :=
          full_of_local_span D (zOf Y) Λ₀ hL0 p0 (by
            rw [← hτ0l]
            exact (GlobalTheory.T.localTermLattice_over_innerDatum_fg_span D (zOf Y) Fm.FP p0 (Fm.d0 p0) τ0 hτ0o).2)
        have hfin := ((GlobalTheory.T.hermitianLattice_local_global_principle D (zOf Y)).1 Λ Λ₀ hfull hfull0).1
        refine ((Fm.P.finite_toSet).union hfin).subset ?_
        intro p hp
        simp only [Set.mem_setOf_eq] at hp
        by_contra hno
        simp only [Set.mem_union, Finset.mem_coe, Set.mem_setOf_eq, not_or, not_not] at hno
        obtain ⟨hpP, hlat⟩ := hno
        obtain ⟨τ0, hτ0o, hτ0l⟩ := hτ0 p hpP
        obtain ⟨τ, hτo, hτl⟩ := hy.2 p
        apply hp
        rw [hddN p hpP]
        exact (luniq p _ _ _ _ hτ0o hτo (by rw [hτ0l, hτl, hlat])).symm
      · exact Fm.P.finite_toSet.subset (by
          intro p hp
          by_contra h
          exact hp0 ⟨p, h⟩)
  obtain ⟨x0, hx0⟩ := hx
  obtain ⟨⟨t0, ht0, hc0, hpt0, hn0⟩, hall0⟩ := (hdat x0.1 x0.2).2 d hx0
  obtain ⟨Λ, y, hΛ, hy, hgen, -⟩ := hA t0 ht0 hpt0 (hall0 t0 ht0 hc0 hpt0 hn0).1
  refine ⟨fun p => ?_, ?_⟩
  · obtain ⟨τ, hτ, -⟩ := hy.2 p
    exact term_of_rel (hMo p) (hrk p) (hRG p) (rel_symm (hMo p) (hrk p) (hRG p) (hgen.1 p)) ⟨τ, hτ⟩
  have hkey_wt : ∀ t t' : TauC Y u u', key t = key t' →
      Formalism.L2.SG.TermOp.wt t = Formalism.L2.SG.TermOp.wt t' := by
    intro t t' h
    have h1 : t.lam = t'.lam := congrArg (fun k => k.1.1.1) h
    have h2 : t.lam' = t'.lam' := congrArg (fun k => k.1.2.1.1) h
    unfold Formalism.L2.SG.TermOp.wt
    rw [h1, h2]
  let K : Set _ := {κ | ∃ t ∈ TS, ∃ (Λ : LV D) (y : Dat (zOf Y) Fm.FP), TG F F' t Λ ∧ LocOver Λ y ∧ InGen dd y ∧
    key t = κ}
  have hKmem : ∀ κ ∈ K, ∃ t : TauC Y u u', key t = κ := by
    rintro κ ⟨t, -, -, -, -, -, -, h⟩
    exact ⟨t, h⟩
  let ω : K → ℝ := fun κ => Formalism.L2.SG.TermOp.wt (Classical.choose (hKmem κ.1 κ.2)) ^ 2
  have hω : ∀ κ : K, ∀ t : TauC Y u u', key t = κ.1 → ω κ = Formalism.L2.SG.TermOp.wt t ^ 2 := by
    intro κ t ht
    show Formalism.L2.SG.TermOp.wt (Classical.choose (hKmem κ.1 κ.2)) ^ 2 = _
    rw [hkey_wt _ _ ((Classical.choose_spec (hKmem κ.1 κ.2)).trans ht.symm)]
  have hsum := GlobalTheory.T.unfolding_genus_weights_sum_to_mass D X Y u u' F F' w hZ hG (zOf Y) Fm.FP hB hRG TS hLC t0 Λ y dd ht0 hΛ hy hgen K rfl ω hω
  rw [← hsum]
  have hsel : ∀ x : {x : Cl × NuC D // Fm.dat x.1 x.2 = some d},
      ∃ t ∈ TS, cls t = x.1.1 ∧ ptPN t = toPts w ∧ nmlOf Y u u' t = x.1.2 :=
    fun x => ((hdat x.1.1 x.1.2).2 d x.2).1
  let tx : {x : Cl × NuC D // Fm.dat x.1 x.2 = some d} → TauC Y u u' := fun x => Classical.choose (hsel x)
  have htx : ∀ x, tx x ∈ TS ∧ cls (tx x) = x.1.1 ∧ ptPN (tx x) = toPts w ∧ nmlOf Y u u' (tx x) = x.1.2 :=
    fun x => Classical.choose_spec (hsel x)
  have hmemK : ∀ x, key (tx x) ∈ K := by
    intro x
    obtain ⟨h1, h2, h3, h4⟩ := htx x
    obtain ⟨Λx, yx, hΛx, hyx, hgx, -⟩ := hA (tx x) h1 h3 ((((hdat x.1.1 x.1.2).2 d x.2).2 (tx x) h1 h2 h3 h4).1)
    exact ⟨tx x, h1, Λx, yx, hΛx, hyx, hgx, rfl⟩
  let f : {x : Cl × NuC D // Fm.dat x.1 x.2 = some d} → K := fun x => ⟨key (tx x), hmemK x⟩
  have hinj : Function.Injective f := by
    intro x1 x2 h
    have hk : key (tx x1) = key (tx x2) := congrArg Subtype.val h
    have hn : nmlOf Y u u' (tx x1) = nmlOf Y u u' (tx x2) := congrArg Prod.snd hk
    have hr : (Y.tO u u').rowOf (tx x1) = (Y.tO u u').rowOf (tx x2) := congrArg Prod.fst hk
    obtain ⟨a1, b1, -, d1⟩ := htx x1
    obtain ⟨a2, b2, -, d2⟩ := htx x2
    have hc := (hCR _ a1 _ a2 hn).2 hr
    apply Subtype.ext
    apply Prod.ext
    · rw [← b1, ← b2, hc]
    · rw [← d1, ← d2, hn]
  have hsurj : Function.Surjective f := by
    rintro ⟨κ, hκ⟩
    obtain ⟨t, ht, Λt, yt, hΛt, hyt0, hgt0, hkt⟩ := hκ
    have hyt : LocOver Λt yt := hyt0
    have hgt : InGen dd yt := hgt0
    subst hkt
    have hpt := (GlobalTheory.T.term_at_base_point_of_frames D X Y u u' F F' w hZ hG t Λt hΛt).2
    cases hdc : Fm.dat (cls t) (nmlOf Y u u' t) with
    | none =>
      exact absurd ⟨t, ht, rfl, hpt, rfl⟩ ((hdat (cls t) (nmlOf Y u u' t)).1 hdc)
    | some d' =>
      have hall := ((hdat (cls t) (nmlOf Y u u' t)).2 d' hdc).2 t ht rfl hpt rfl
      obtain ⟨y', hy', hyr'⟩ := GlobalTheory.T.localData_of_term_lattice_and_orbits D X Y u u' F F' w hZ hG (zOf Y) Fm.FP hB hRG t Λt hΛt
      have hd' : d' = d := by
        funext p
        apply Subtype.ext
        have e1 : Formalism.MainNotions.S.LocNG.Datum.Rel (d' p).1 (y' p.1) := (hyr' p.1 _).1 (hall.1 p.1 p.2)
        have eyy : y' p.1 = yt p.1 := by
          obtain ⟨τ, hτ, hτl⟩ := hy'.2 p.1
          obtain ⟨τ', hτ', hτl'⟩ := hyt.2 p.1
          exact luniq _ _ _ _ _ hτ hτ' (hτl.trans hτl'.symm)
        have e2 : Formalism.MainNotions.S.LocNG.Datum.Rel (d p).1 (yt p.1) := by
          have h := hgt.1 p.1
          rw [hddP p.1 p.2] at h
          exact h
        rw [eyy] at e1
        exact eq_of_rel_reps (hMo p.1) (hrk p.1) (hRG p.1) (Fm.R p.1) (hDs p.1 p.2 _ (d' p).2)
          (hDs p.1 p.2 _ (d p).2) e1 e2
      rw [hd'] at hdc
      refine ⟨⟨(cls t, nmlOf Y u u' t), hdc⟩, ?_⟩
      apply Subtype.ext
      obtain ⟨h1, h2, -, h4⟩ := htx ⟨(cls t, nmlOf Y u u' t), hdc⟩
      have hrow := (hCR _ h1 t ht h4).1 h2
      show key (tx ⟨(cls t, nmlOf Y u u' t), hdc⟩) = key t
      unfold key
      rw [hrow, h4]
  calc ∑' x : {x : Cl × NuC D // Fm.dat x.1 x.2 = some d}, ENNReal.ofReal (Fm.rw x.1.1)
      = ∑' x : {x : Cl × NuC D // Fm.dat x.1 x.2 = some d}, ENNReal.ofReal (ω (f x)) := by
        refine tsum_congr fun x => ?_
        obtain ⟨h1, h2, h3, h4⟩ := htx x
        rw [hω (f x) (tx x) rfl, (((hdat x.1.1 x.1.2).2 d x.2).2 (tx x) h1 h2 h3 h4).2]
    _ = ∑' κ : K, ENNReal.ofReal (ω κ) :=
        (Equiv.ofBijective f ⟨hinj, hsurj⟩).tsum_eq (fun κ => ENNReal.ofReal (ω κ))

end GlobalTheory.Unfold.GenusRows
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowWeightsLocalOrbitsSumEqGenusMassStatement
open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc Formalism.L2.SG.NGLocModel Formalism.L2.SG.FamDefs Formalism.FourierDecayAlt GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowWeights_localOrbits_sum_eq_genusMass : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), ∀ (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (w : Point D.host.E (D.R.rS + 1)), ZhatOM (ZhatL F F') = ptMat w → Gval F F' ≠ 0 → ∀ {Cl : Type} (TS : Set (TauC Y u u')) (cls : TauC Y u u' → Cl) (Fm : LocFam (zOf Y) Cl (NuC D)), Based (zOf Y) Fm.FP (Tu D u) (Tu D u') F F' → ClsRow TS cls → LocClosed F F' (zOf Y) Fm.FP TS → (∀ p ∈ Fm.P, ∀ d ∈ Fm.Ds p, d ∈ (Fm.R p).RD) → (∀ p, p ∉ Fm.P → ∀ t ∈ TS, ptPN t = toPts w → OverOrb Fm t p (Fm.d0 p)) → (∃ Λ₀ : LV D, Submodule.IsLattice D.host.E Λ₀ ∧ ∀ p, p ∉ Fm.P → ∃ τ, LocNG.IsTermOver (Fm.FP p) (Fm.d0 p) τ ∧ τ.abelian₂ = lattice₂ D (zOf Y).M p Λ₀) → (∀ c ν, (Fm.dat c ν = none → ¬ ∃ t ∈ TS, cls t = c ∧ ptPN t = toPts w ∧ nmlOf Y u u' t = ν) ∧ ∀ d, Fm.dat c ν = some d → (∃ t ∈ TS, cls t = c ∧ ptPN t = toPts w ∧ nmlOf Y u u' t = ν) ∧ ∀ t ∈ TS, cls t = c → ptPN t = toPts w → nmlOf Y u u' t = ν → (∀ p (hp : p ∈ Fm.P), OverOrb Fm t p (d ⟨p, hp⟩).1) ∧ Fm.rw c = (wt t) ^ 2) → ∀ d : (∀ p : {p // p ∈ Fm.P}, {d // d ∈ Fm.Ds p.1}), (∃ x : Cl × NuC D, Fm.dat x.1 x.2 = some d) → ∀ dd : Dat (zOf Y) Fm.FP, (∀ p (hp : p ∈ Fm.P), dd p = (d ⟨p, hp⟩).1) → (∀ p, p ∉ Fm.P → dd p = Fm.d0 p) → (∀ p, ∃ τ, LocNG.IsTermOver (Fm.FP p) (dd p) τ) ∧ ∑' x : {x : Cl × NuC D // Fm.dat x.1 x.2 = some d}, ENNReal.ofReal (Fm.rw x.1.1) = massA F F' dd := by
  first | exact @GlobalTheory.Unfold.GenusRows.rows_mass_genus | exact GlobalTheory.Unfold.GenusRows.rows_mass_genus | (intros; apply GlobalTheory.Unfold.GenusRows.rows_mass_genus <;> assumption)
end
