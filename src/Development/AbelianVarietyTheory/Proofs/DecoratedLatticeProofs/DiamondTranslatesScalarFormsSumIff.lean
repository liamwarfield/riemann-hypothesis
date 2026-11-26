module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseChainTopThetaFunctions

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RepresentativeDiamondTranslateSumScalarForm
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsChartPointRightTranslateStabilizerSplitPla
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastRowInvFrame
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.RowModPrime

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem row_of_smul_eq {n : ℕ} (Q : GlobalTheory.LatPair.Pair k (Fin n)) (b b' : Matrix (Fin n) (Fin n) k) (hbb' : b * b' = 1)
    (c : k) (r₀ : Fin n)
    (hQ : ∀ (x : Fin n → k) (a : 𝓀[k]), Q.HasVal x a ↔ ∃ y : Fin n → 𝒪[k], (∀ r, (y r : k) = (b *ᵥ x) r) ∧
      ∃ s : 𝒪[k], (s : k) = c ∧ a = residue 𝒪[k] (s * y r₀))
    (g : GL (Fin n) k) (s : 𝓀[k]ˣ) (hg : g • Q = s • Q) (m : Fin n) :
    ∃ t : 𝒪[k], (t : k) = (b * (g⁻¹).val * b') r₀ m ∧ residue 𝒪[k] t = if m = r₀ then (s : 𝓀[k]) else 0 := by
  obtain ⟨e, he⟩ := Q.exists_hasVal_one
  obtain ⟨y₀, -, sc, hsc, h1⟩ := (hQ e 1).1 he
  have hsc0 : residue 𝒪[k] sc ≠ 0 := by
    intro h
    rw [map_mul, h, zero_mul] at h1
    exact one_ne_zero h1
  let y : Fin n → 𝒪[k] := Pi.single m 1
  have hbx : b *ᵥ (b' *ᵥ Pi.single m 1) = Pi.single m 1 := by
    rw [Matrix.mulVec_mulVec, hbb', Matrix.one_mulVec]
  have hx : Q.HasVal (b' *ᵥ Pi.single m 1) (residue 𝒪[k] (sc * y r₀)) := by
    refine (hQ _ _).2 ⟨y, fun r => ?_, sc, hsc, rfl⟩
    rw [hbx]
    simp only [y, Pi.single_apply]
    split_ifs <;> simp
  have hx2 : (g • Q).HasVal (b' *ᵥ Pi.single m 1) ((s : 𝓀[k]) * residue 𝒪[k] (sc * y r₀)) := by
    rw [hg, GlobalTheory.LatPair.Pair.dia_hasVal, Units.inv_mul_cancel_left]
    exact hx
  have hx3 := GlobalTheory.LatPair.Pair.smul_hasVal.1 hx2
  obtain ⟨y', hy', sc', hsc', h3⟩ := (hQ _ _).1 hx3
  have hss : sc' = sc := Subtype.ext (hsc'.trans hsc.symm)
  rw [hss] at h3
  have hM : (b *ᵥ (g⁻¹ • (b' *ᵥ Pi.single m 1))) r₀ = (b * (g⁻¹).val * b') r₀ m := by
    change (b *ᵥ ((g⁻¹).val *ᵥ (b' *ᵥ Pi.single m 1))) r₀ = _
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_single_one]
    rfl
  refine ⟨y' r₀, (hy' r₀).trans hM, ?_⟩
  rw [map_mul, map_mul] at h3
  have h4 : residue 𝒪[k] sc * residue 𝒪[k] (y' r₀) = residue 𝒪[k] sc * ((s : 𝓀[k]) * residue 𝒪[k] (y r₀)) := by
    rw [← h3]; ring
  have h5 := mul_left_cancel₀ hsc0 h4
  rw [h5]
  simp only [y, Pi.single_apply]
  by_cases h : m = r₀
  · subst h
    simp
  · rw [if_neg (Ne.symm h), if_neg h]
    simp

end GlobalTheory.AdForm.RowModPrime

namespace GlobalTheory.AdForm.RowModPrime

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem resS_eq_rho {D : D7} (q : GlobalTheory.FinPl.SplitPt D k) {P : HeightOneSpectrum (𝓞 D.host.E)}
    (he : Formalism.L2.NTheta.IsIdemAt q.e P) (ρ : 𝓀[k] ≃+* (𝓞 D.host.E ⧸ P.asIdeal))
    (hρ : ∀ (x : 𝓞 D.host.E) (t : 𝒪[k]), (t : k) = q.pr (incA D (x : D.host.E)) →
      ρ (residue 𝒪[k] t) = Ideal.Quotient.mk P.asIdeal x)
    (a : Formalism.L2.Herm.intAf D.host.F D.host.E) (t : 𝒪[k]) (ht : (t : k) = q.prF he a.1) :
    Formalism.L2.DIV.resS D.host.F P a = ρ (residue 𝒪[k] t) := by
  obtain ⟨x, hx0⟩ := GlobalTheory.FunObj.Comparison₂.exists_approx (D := D) P.ne_bot a
  have hx : a - Formalism.L2.DIV.oToS D.host.F D.host.E x ∈ Formalism.L2.DIV.idS D.host.F P.asIdeal := hx0
  have h1 : Formalism.L2.DIV.resS D.host.F P a = Ideal.Quotient.mk P.asIdeal x := by
    rw [← Formalism.L2.DIV.resS_oToS (F := D.host.F) P x, ← sub_eq_zero, ← map_sub]
    exact GlobalTheory.FinPl.SplitPt.resS_eq_zero_of_mem hx
  have h2 := q.val_lt_of_mem_idS he hx
  have e1 : ((Formalism.L2.DIV.oToS D.host.F D.host.E x : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) =
      toEAf D (incA D (x : D.host.E)) := rfl
  have e2 : ((a - Formalism.L2.DIV.oToS D.host.F D.host.E x : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) =
      (a : EAf D) - ((Formalism.L2.DIV.oToS D.host.F D.host.E x : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) := rfl
  rw [e2, map_sub, e1, GlobalTheory.FinPl.SplitPt.prF_toEAf, ← ht] at h2
  have hw : q.pr (incA D (x : D.host.E)) ∈ 𝒪[k] := by
    have ht1 : valuation k (t : k) ≤ 1 := (Valuation.mem_integer_iff _ _).1 t.2
    have e3 : q.pr (incA D (x : D.host.E)) = (t : k) - ((t : k) - q.pr (incA D (x : D.host.E))) := by ring
    rw [Valuation.mem_integer_iff, e3]
    exact (Valuation.map_sub _ _ _).trans (max_le ht1 h2.le)
  let tw : 𝒪[k] := ⟨_, hw⟩
  have h3 : residue 𝒪[k] t = residue 𝒪[k] tw := by
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact (IsLocalRing.mem_maximalIdeal _).2 (Valuation.Integer.not_isUnit_iff_valuation_lt_one.2 (by simpa [tw] using h2))
  rw [h1, h3, hρ x tw rfl]

end GlobalTheory.AdForm.RowModPrime


open GlobalTheory.AdForm.RowModPrime in
theorem GlobalTheory.AdForm.lastRow_inv_frame : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ j (hj : j ≤ B.R.m) (i : ι) (v : (I.atT l u a).vT), Formalism.L2.NTheta.IsIdemAt (p i).e v.1 → ∀ (ρ : 𝓀[k] ≃+* (𝓞 B.fields.E ⧸ v.1.asIdeal)), (∀ (x : 𝓞 B.fields.E) (t : 𝒪[k]), (t : k) = (p i).pr (incA (I.rec7 l Z) (x : B.fields.E)) → ρ (residue 𝒪[k] t) = Ideal.Quotient.mk v.1.asIdeal x) →
    ∀ (g : GL (Fin ((I.rec7 l Z).sp.X j).rank) k) (s : 𝓀[k]ˣ), g • Q j i = s • Q j i → ∀ δ : TC.GA B (B.R.N j), δ.1 = finM _ (rankN (I.rec7 l Z) j hj) ((β j i).gl g) →
      (∀ r r', (δ⁻¹).1 r r' ∈ Formalism.L2.DIV.RInt B.host.F B.host.E) →
      ∀ r r' : Fin (B.R.N j), r.1 + 1 = B.R.N j → HasRes v.1 (adAt B.host.F v.1 ((δ⁻¹).1 r r')) (if r' = r then ρ (s : 𝓀[k]) else 0) := by
  intro B X I hOk hP l Z u a k _ _ _ _ ι p β Q L hStd j hj i v hId ρ hρ g s hg δ hδ hint r r' hr
  have hn : ((I.rec7 l Z).sp.X j).rank = B.R.N j := rankN (I.rec7 l Z) j hj
  let e : Fin ((I.rec7 l Z).sp.X j).rank ≃ Fin (B.R.N j) := finCongr hn
  let f : Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) (EAf (I.rec7 l Z)) →+* Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) k :=
    ((p i).prF hId).mapMatrix
  have hδm : f δ.1 = Matrix.reindex e e ((β j i).b * g.val * (β j i).b') := by
    rw [hδ, ← (β j i).gl_mat g]
    ext x y
    exact GlobalTheory.FinPl.SplitPt.prF_toEAf (p i) hId _
  have hY : Matrix.reindex e e ((β j i).b * g.val * (β j i).b') * Matrix.reindex e e ((β j i).b * (g⁻¹).val * (β j i).b') = 1 := by
    rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
    have : (β j i).b * g.val * (β j i).b' * ((β j i).b * (g⁻¹).val * (β j i).b') = 1 := by
      calc (β j i).b * g.val * (β j i).b' * ((β j i).b * (g⁻¹).val * (β j i).b')
          = (β j i).b * (g.val * ((β j i).b' * (β j i).b) * (g⁻¹).val) * (β j i).b' := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [(β j i).b'b, Matrix.mul_one, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one, (β j i).bb']
    rw [this, Matrix.submatrix_one_equiv]
  have h1 : ((δ⁻¹).1 : Matrix (Fin (B.R.N j)) (Fin (B.R.N j)) (EAf (I.rec7 l Z))) * δ.1 = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hX : f (δ⁻¹).1 * f δ.1 = 1 :=
    (map_mul f _ _).symm.trans ((congrArg f h1).trans (map_one f))
  have hA : f (δ⁻¹).1 = Matrix.reindex e e ((β j i).b * (g⁻¹).val * (β j i).b') := by
    calc f (δ⁻¹).1 = f (δ⁻¹).1 * (f δ.1 * Matrix.reindex e e ((β j i).b * (g⁻¹).val * (β j i).b')) := by
          rw [hδm, hY, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, hX, Matrix.one_mul]
  have hA' : (p i).prF hId ((δ⁻¹).1 r r') = ((β j i).b * (g⁻¹).val * (β j i).b') (e.symm r) (e.symm r') :=
    congrFun (congrFun hA r) r'
  have hr0 : (e.symm r).1 + 1 = ((I.rec7 l Z).sp.X j).rank := by
    show r.1 + 1 = _
    rw [hr]
    exact hn.symm
  have hQ := GlobalTheory.AdForm.stdT_pair_coords I l Z u k ι p β Q L hStd j hj i (e.symm r) hr0
  obtain ⟨t, ht, hres⟩ := row_of_smul_eq (Q j i) (β j i).b (β j i).b' (β j i).bb' _ (e.symm r) hQ g s hg (e.symm r')
  have hmem := hint r r'
  have h := GlobalTheory.Mem.Col2.PtExist.hasRes_redA v.1 hmem
  have hr1 : Formalism.L2.Col.redA v.1 ((δ⁻¹).1 r r') = ρ (residue 𝒪[k] t) :=
    (Formalism.L2.Col.redA_int v.1 hmem).trans (resS_eq_rho (p i) hId ρ hρ ⟨_, hmem⟩ t (ht.trans hA'.symm))
  rw [hr1, hres] at h
  convert h using 2
  by_cases h' : r' = r
  · subst h'; simp
  · rw [if_neg h', if_neg (fun h'' => h' (e.symm.injective h'')), map_zero]

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameImageTrivialOffLevelPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameImageTrivialOffLevelPrime
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.FrameTriv

theorem frame_trivial_off : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ j (hj : j ≤ B.R.m) (i : ι) (v : (I.atT l u a).vT), Formalism.L2.NTheta.IsIdemAt (p i).e v.1 → ∀ (g : GL (Fin ((I.rec7 l Z).sp.X j).rank) k) (δ : TC.GA B (B.R.N j)), δ.1 = finM _ (rankN (I.rec7 l Z) j hj) ((β j i).gl g) →
    ∀ w : HeightOneSpectrum (𝓞 B.fields.E), (w ∈ (B.primes X).vGs ∨ w ∈ I.SQ ∨ (w ∈ (B.primes X).vT u ∧ w ≠ v.1)) →
      ∀ r r', adAt B.host.F w ((δ⁻¹).1 r r') = if r = r' then 1 else 0 := by
  intro B X I hI _ l Z u a k _ _ _ _ ι p β Q L _ j hj i v hidem g δ hδ w hw r r'
  classical
  have hPr : (B.primes X).Ok := l.pr
  have hv : (p i).v = v.1.under (𝓞 B.host.F) := GlobalTheory.LocMod.LevelPlaces.splitPt_v_eq_under (p i) hidem
  have hvT : v.1 ∈ (B.primes X).vT u := v.2
  have hTv : (((B.primes X).T u : ℕ) : 𝓞 B.fields.E) ∈ v.1.asIdeal := T_mem_vT hPr u ⟨v.1, hvT⟩
  have hne : w.under (𝓞 B.host.F) ≠ (p i).v := by
    intro hwv
    rw [hv] at hwv
    have hTw : (((B.primes X).T u : ℕ) : 𝓞 B.fields.E) ∈ w.asIdeal := by
      have h1 : (((B.primes X).T u : ℕ) : 𝓞 B.host.F) ∈ (w.under (𝓞 B.host.F)).asIdeal := by
        rw [hwv]
        show algebraMap _ (𝓞 B.fields.E) _ ∈ v.1.asIdeal
        rw [map_natCast]
        exact hTv
      have h2 : algebraMap _ (𝓞 B.fields.E) (((B.primes X).T u : ℕ) : 𝓞 B.host.F) ∈ w.asIdeal := h1
      rwa [map_natCast] at h2
    rcases hw with h | h | ⟨h, hwne⟩
    · exact Formalism.L2.Col.T_notMem_vGs hPr u ⟨w, h⟩ hTw
    · have hg := (GlobalTheory.Mem.LevTwist.good_of_mem hI h).2
      have e := (GlobalTheory.Mem.ReadTwist.plc_under_eq_iff (F := B.host.F) w (hPr.T_prime u)).2 hTw
      refine hg.2.2 ?_
      rw [e]
      exact hI.T_mem u
    · rcases GlobalTheory.GridPlaces.eq_or_eq_conjP (D := I.rec7 l Z) hwv with e | e
      · exact hwne e
      · have hT0 : (B.primes X).piT u ≠ 0 := fun h0 => by
          have := hPr.piT_norm u
          rw [h0, zero_mul] at this
          exact (hPr.T_prime u).ne_zero (Nat.cast_eq_zero.1 this.symm)
        have a1 : (B.primes X).piT u ∈ v.1.asIdeal := (Formalism.L2.Col.mem_divs hT0 _).1 hvT
        have a2 : (B.primes X).piT u ∈ w.asIdeal := (Formalism.L2.Col.mem_divs hT0 _).1 h
        rw [e] at a2
        have a3 : B.fields.conjO ((B.primes X).piT u) ∈ v.1.asIdeal := (Formalism.L2.Col.mem_conjP _ _).1 a2
        obtain ⟨x, y, hxy⟩ := hPr.piT_cop u
        have : (1 : 𝓞 B.fields.E) ∈ v.1.asIdeal := by
          rw [← hxy]
          exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ a1) (Ideal.mul_mem_left _ _ a3)
        exact v.1.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 this)
  have hb : Formalism.UG.bc (Formalism.UG.prV (E := B.host.E) (w.under (𝓞 B.host.F))) δ = 1 :=
    GlobalTheory.T.splitFrameGL_finiteMatrix_offPlace_eq_one (I.rec7 l Z) k (p i) ((I.rec7 l Z).sp.X j) _ (β j i) g _ (rankN (I.rec7 l Z) j hj) δ hδ _ hne
  have hb' : Formalism.UG.bc (Formalism.UG.prV (E := B.host.E) (w.under (𝓞 B.host.F))) δ⁻¹ = 1 := by
    rw [map_inv, hb, inv_one]
  have h2 : Formalism.UG.prV (E := B.host.E) (w.under (𝓞 B.host.F)) ((δ⁻¹).1 r r') = if r = r' then 1 else 0 := by
    have := congrArg (fun x : GL (Fin (B.R.N j)) _ => x.1 r r') hb'
    simp only [Units.val_one, Matrix.one_apply] at this
    exact this
  have h3 : Formalism.UG.prV (E := B.host.E) (w.under (𝓞 B.host.F)) ((δ⁻¹).1 r r' - if r = r' then 1 else 0) = 0 := by
    rw [map_sub, h2]
    split_ifs <;> simp
  have h4 := (GlobalTheory.Mem.Col2.AdComp.prV_zero_int_iff B.host.F B.host.E _ _).1.1 h3 w rfl
  rw [map_sub, sub_eq_zero] at h4
  rw [h4]
  split_ifs <;> simp

end GlobalTheory.AdForm.FrameTriv

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameImageTrivialOffLevelPrimeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameImage_trivial_off_levelPrime : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ j (hj : j ≤ B.R.m) (i : ι) (v : (I.atT l u a).vT), Formalism.L2.NTheta.IsIdemAt (p i).e v.1 → ∀ (g : GL (Fin ((I.rec7 l Z).sp.X j).rank) k) (δ : TC.GA B (B.R.N j)), δ.1 = finM _ (rankN (I.rec7 l Z) j hj) ((β j i).gl g) →
    ∀ w : HeightOneSpectrum (𝓞 B.fields.E), (w ∈ (B.primes X).vGs ∨ w ∈ I.SQ ∨ (w ∈ (B.primes X).vT u ∧ w ≠ v.1)) →
      ∀ r r', adAt B.host.F w ((δ⁻¹).1 r r') = if r = r' then 1 else 0 := by
  first | exact @GlobalTheory.AdForm.FrameTriv.frame_trivial_off | exact GlobalTheory.AdForm.FrameTriv.frame_trivial_off | (intros; apply GlobalTheory.AdForm.FrameTriv.frame_trivial_off <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameGlInt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FrameGlInt

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mat_int {p : SplitPt D k} {S : HSp D} {L : Lat S} (hL : ∀ z, z ∈ L ↔ z ∈ intVec D S.rank)
    (β : Frame p S (Fin S.rank)) {Λ : Submodule 𝒪[k] (Fin S.rank → k)} (h : β.IsLat L Λ) (g : GL (Fin S.rank) k)
    (hg : g • Λ = Λ) (r s : Fin S.rank) : (β.b * g.val * β.b') r s ∈ 𝒪[k] := by
  have hmem : ∀ x, x ∈ Λ ↔ ∀ r, (β.b *ᵥ x) r ∈ 𝒪[k] := fun x => by
    rw [h x, GlobalTheory.SeeSaw.StdOff.mem_latV_int hL]
    exact forall_congr' fun r =>
      ((p.int_iff _).trans (and_iff_right (GlobalTheory.SeeSaw.StdOff.sec_mem_idAt p _)).symm).symm
  have h1 : β.b' *ᵥ Pi.single s 1 ∈ Λ := (hmem _).2 fun r => by
    rw [Matrix.mulVec_mulVec, β.bb', Matrix.one_mulVec, Pi.single_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  have h2 : g • (β.b' *ᵥ Pi.single s 1) ∈ Λ := hg ▸ Submodule.smul_mem_pointwise_smul _ _ _ h1
  have h3 := (hmem _).1 h2 r
  convert h3 using 1
  rw [show g • (β.b' *ᵥ Pi.single s 1) = g.val *ᵥ (β.b' *ᵥ Pi.single s 1) from rfl, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, Matrix.mulVec_single_one]
  rfl

theorem finM_mul (V : HSp D) {n : ℕ} (hn : V.rank = n) (g h : GA D V) :
    GlobalTheory.AdForm.finM V hn (g * h) = GlobalTheory.AdForm.finM V hn g * GlobalTheory.AdForm.finM V hn h := by
  simp [GlobalTheory.AdForm.finM, Formalism.L2.Theta.mt, Matrix.map_mul, Matrix.submatrix_mul_equiv]

theorem prF_finM (q : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt q.e PP) (V : HSp D)
    {n : ℕ} (hn : V.rank = n) (g : GA D V) (r s : Fin n) :
    q.prF he (GlobalTheory.AdForm.finM V hn g r s) = (Formalism.L2.Theta.mt V g).map q.pr ((finCongr hn).symm r) ((finCongr hn).symm s) := by
  simp [GlobalTheory.AdForm.finM, Matrix.reindex_apply, SplitPt.prF_toEAf]

theorem finM_one (V : HSp D) {n : ℕ} (hn : V.rank = n) : GlobalTheory.AdForm.finM V hn 1 = 1 := by
  simp [GlobalTheory.AdForm.finM, Formalism.L2.Theta.mt]

end GlobalTheory.FrameGlInt

namespace GlobalTheory.FrameGlInt

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


set_option maxHeartbeats 1600000 in
theorem exists_int (p : SplitPt D k) {PP : Formalism.L2.DIV.Pl D.host.E} (he : Formalism.L2.NTheta.IsIdemAt p.e PP) (S : HSp D)
    {n : ℕ} (hn : S.rank = n) (hgram : S.gram.reindex (finCongr hn) (finCongr hn) = 1) {L : Lat S}
    (hL : ∀ z, z ∈ L ↔ z ∈ intVec D S.rank) (β : Frame p S (Fin S.rank)) {Λ : Submodule 𝒪[k] (Fin S.rank → k)}
    (hlat : β.IsLat L Λ) (g : GL (Fin S.rank) k) (hgl : g • Λ = Λ) :
    ∃ δ : GL (Fin n) (GlobalTheory.AdForm.EF D), δ.1 = GlobalTheory.AdForm.finM S hn (β.gl g) ∧
      δ ∈ Formalism.UG.UPts (sigD D) (1 : Matrix (Fin n) (Fin n) D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) ∧
      (∀ r r', δ.1 r r' ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) ∧
      (∀ r r', (δ⁻¹).1 r r' ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) := by
  obtain ⟨⟨x, hx0⟩, hx⟩ := GlobalTheory.AdForm.RdVal.finM_mem S hn _ hgram.symm (β.gl g)
  refine ⟨x, hx, hx0, ?_⟩
  have hgl' : g⁻¹ • Λ = Λ := by
    conv_lhs => rw [← hgl]
    exact inv_smul_smul g _
  have hcomp : ∀ h : GL (Fin S.rank) k, h • Λ = Λ → ∀ r s,
      toEAf D p.e * GlobalTheory.AdForm.finM S hn (β.gl h) r s ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    intro h hh r s
    rw [← p.prF_mem_iff he]
    have e1 := prF_finM p he S hn (β.gl h) r s
    rw [β.gl_mat h] at e1
    exact e1 ▸ mat_int hL β hlat h hh _ _
  set σ := Formalism.UG.sigR (sigD D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) with hσ

  have hu0 : Formalism.UG.cT σ x.1 * ((1 : Matrix (Fin n) (Fin n) D.host.E).map
      (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))) * x.1 =
      (1 : Matrix (Fin n) (Fin n) D.host.E).map (Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) := hx0
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at hu0
  have hinvM : (x⁻¹).1 = Formalism.UG.cT σ x.1 := by
    calc (x⁻¹).1 = (Formalism.UG.cT σ x.1 * x.1) * (x⁻¹).1 := by rw [hu0, one_mul]
      _ = _ := by rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]

  have hxi : (x⁻¹).1 = GlobalTheory.AdForm.finM S hn (β.gl g⁻¹) := by
    have h1 : x.1 * GlobalTheory.AdForm.finM S hn (β.gl g⁻¹) = 1 := by
      rw [hx, ← finM_mul, ← map_mul, mul_inv_cancel, map_one, finM_one]
    calc (x⁻¹).1 = (x⁻¹).1 * (x.1 * GlobalTheory.AdForm.finM S hn (β.gl g⁻¹)) := by rw [h1, mul_one]
      _ = _ := by rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  obtain ⟨hf, -⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D p.e PP he
  have hσmem : ∀ y ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, σ y ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    fun y hy => GlobalTheory.Mem.Col2.sigR_mem_rInt D.sp.cm hy
  have hσσ : ∀ y, σ (σ y) = y := Formalism.L2.DIV.sigR_sigR D.sp.cm
  have hcA : toEAf D (cA D p.e) = σ (toEAf D p.e) := GlobalTheory.AdForm.RdVal.toEAf_sig p.e
  have hint : ∀ r r', x.1 r r' ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    intro r r'
    have hs := congrArg (toEAf D) (β.gl_supp g ((finCongr hn).symm r) ((finCongr hn).symm r'))
    have hxr : x.1 r r' = toEAf D (Formalism.L2.Theta.mt S (β.gl g) ((finCongr hn).symm r) ((finCongr hn).symm r')) := by
      rw [hx]; rfl
    have hcm : toEAf D ((1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) ((finCongr hn).symm r) ((finCongr hn).symm r')) ∈
        Formalism.L2.Herm.intAf D.host.F D.host.E := by
      rw [Matrix.one_apply]; split_ifs
      · rw [RingHom.map_one]; exact one_mem _
      · rw [RingHom.map_zero]; exact zero_mem _
    rw [Matrix.sub_apply, RingHom.map_mul, RingHom.map_sub, RingHom.map_add (f := _), hcA, ← hxr] at hs
    have hdec : x.1 r r' = toEAf D p.e * x.1 r r' + σ (toEAf D p.e * (x⁻¹).1 r' r) +
        (1 - toEAf D p.e - σ (toEAf D p.e)) *
          toEAf D ((1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) ((finCongr hn).symm r) ((finCongr hn).symm r')) := by
      have e2 : σ (toEAf D p.e * (x⁻¹).1 r' r) = σ (toEAf D p.e) * x.1 r r' := by
        rw [hinvM, map_mul]
        show σ (toEAf D p.e) * σ (σ (x.1 r r')) = _
        rw [hσσ]
      rw [e2]
      linear_combination (-1 : GlobalTheory.AdForm.EF D) * hs
    rw [hdec]
    refine add_mem (add_mem ?_ ?_) (mul_mem (sub_mem (sub_mem (one_mem _) hf) (hσmem _ hf)) hcm)
    · exact hx ▸ hcomp g hgl r r'
    · exact hσmem _ (hxi ▸ hcomp g⁻¹ hgl' r' r)
  exact ⟨hint, fun r r' => by
    rw [hinvM]
    exact hσmem _ (hint r' r)⟩

end GlobalTheory.FrameGlInt

theorem GlobalTheory.AdForm.frameGl_int : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ j (hj : j ≤ B.R.m) (i : ι) (v : (I.atT l u a).vT), Formalism.L2.NTheta.IsIdemAt (p i).e v.1 → ∀ (g : GL (Fin ((I.rec7 l Z).sp.X j).rank) k) (s : 𝓀[k]ˣ), g • Q j i = s • Q j i →
    ∃ δ : TC.GA B (B.R.N j), δ.1 = finM _ (rankN (I.rec7 l Z) j hj) ((β j i).gl g) ∧ δ ∈ Formalism.L2.Herm.UstdAf B.sp.cm (B.R.N j) ∧
      (∀ r r', δ.1 r r' ∈ Formalism.L2.DIV.RInt B.host.F B.host.E) ∧ (∀ r r', (δ⁻¹).1 r r' ∈ Formalism.L2.DIV.RInt B.host.F B.host.E) := by
  intro B X I hOk hPins l Z u a k _ _ _ _ ι p β Q L hStd j hj i v hIdem g s hgs
  have hg1 : gramN (I.rec7 l Z) j hj = 1 := ((TC.spaces_in_coordinates I hOk hPins l Z).2.2.2 j hj).1
  obtain ⟨-, hT⟩ := hStd
  obtain ⟨hL, hT'⟩ := hT j hj
  obtain ⟨hlat, -⟩ := hT' i
  have hgl : g • (Q j i).lat = (Q j i).lat := by
    have := congrArg GlobalTheory.LatPair.Pair.lat hgs
    rwa [GlobalTheory.LatPair.Pair.smul_lat, GlobalTheory.LatPair.Pair.dia_lat] at this
  obtain ⟨δ, h1, h2, h3, h4⟩ := GlobalTheory.FrameGlInt.exists_int (p i) hIdem _ (rankN (I.rec7 l Z) j hj) hg1 hL (β j i) hlat g hgl
  exact ⟨δ, h1, h2, h3, h4⟩

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ResidueEqZeroIffValLt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.SplitPt

theorem residue_eq_zero_iff_val_lt {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (t : 𝒪[k]) : residue 𝒪[k] t = 0 ↔ valuation k (t : k) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact Valuation.Integer.not_isUnit_iff_valuation_lt_one

theorem resField_equiv : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k) (PP : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt q.e PP → (∀ x : 𝓞 D.host.E, q.pr (incA D (x : D.host.E)) ∈ 𝒪[k]) ∧ ∃ ρ : 𝓀[k] ≃+* (𝓞 D.host.E ⧸ PP.asIdeal), ∀ (x : 𝓞 D.host.E) (t : 𝒪[k]), (t : k) = q.pr (incA D (x : D.host.E)) → ρ (residue 𝒪[k] t) = Ideal.Quotient.mk PP.asIdeal x := by
  intro D k _ _ _ _ q PP he
  obtain ⟨hint, -⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D q.e PP he
  have hmem : ∀ x : 𝓞 D.host.E, q.pr (incA D (x : D.host.E)) ∈ 𝒪[k] := fun x => by
    rw [q.pr_mem_iff]
    exact mul_mem hint (Formalism.L2.DIV.oToS D.host.F D.host.E x).2
  refine ⟨hmem, ?_⟩
  let ψ : 𝓞 D.host.E →+* 𝒪[k] :=
    ((q.pr.comp (incA D)).comp (algebraMap (𝓞 D.host.E) D.host.E)).codRestrict 𝒪[k] hmem
  have hψ : ∀ x, (ψ x : k) = q.pr (incA D (x : D.host.E)) := fun x => rfl
  let φ : 𝓞 D.host.E →+* 𝓀[k] := (residue 𝒪[k]).comp ψ
  have hker : RingHom.ker φ = PP.asIdeal := by
    ext x
    have e1 : ((Formalism.L2.DIV.oToS D.host.F D.host.E x : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) =
        toEAf D (incA D (x : D.host.E)) := rfl
    rw [RingHom.mem_ker, RingHom.comp_apply, residue_eq_zero_iff_val_lt, hψ, q.mem_iff_val_lt he, e1, prF_toEAf]
  have hsurj : Function.Surjective φ := by
    intro c
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
    set z : EAf D := toEAf D (q.sec a) with hz
    have hprz : q.prF he z = a := by rw [hz, prF_toEAf, q.pr_sec]
    have hoff : (1 - toEAf D q.e) * z = 0 := by
      have he1 : toEAf D q.e * z = z := by
        rw [hz, ← RingHom.map_mul, ← q.sec_pr, q.pr_sec]
      rw [sub_mul, one_mul, he1, sub_self]
    have hzint : z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
      (q.mem_intAf_iff he z).2 ⟨by rw [hoff]; exact zero_mem _, by rw [hprz]; exact a.2⟩
    obtain ⟨x, hx0⟩ := GlobalTheory.FunObj.Comparison₂.exists_approx PP.ne_bot ⟨z, hzint⟩
    have hx : (⟨z, hzint⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) - Formalism.L2.DIV.oToS D.host.F D.host.E x ∈
        Formalism.L2.DIV.idS D.host.F PP.asIdeal := hx0
    have hv := q.val_lt_of_mem_idS he hx
    refine ⟨x, ?_⟩
    show residue 𝒪[k] (ψ x) = residue 𝒪[k] a
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff_val_lt]
    have e1 : (((⟨z, hzint⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) - Formalism.L2.DIV.oToS D.host.F D.host.E x :
        Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) = z - toEAf D (incA D (x : D.host.E)) := rfl
    rw [e1, map_sub, hprz, prF_toEAf] at hv
    have e2 : ((ψ x - a : 𝒪[k]) : k) = -((a : k) - q.pr (incA D (x : D.host.E))) := by
      rw [AddSubgroupClass.coe_sub, hψ]; ring
    rw [e2, Valuation.map_neg]; exact hv
  refine ⟨((Ideal.quotEquivOfEq hker).symm.trans (RingHom.quotientKerEquivOfSurjective hsurj)).symm, ?_⟩
  intro x t ht
  have htx : t = ψ x := Subtype.ext (by rw [ht, hψ])
  rw [RingEquiv.symm_apply_eq, htx]
  rfl

end GlobalTheory.FinPl.SplitPt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsChartPointRightTranslateStabilizerSplitPla
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.DiaChart

theorem decoratedLattice_unitScale_functional_keeps_frames {X : Formalism.L2.Col.Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {y}
    (p : PtY (X := X) (n := n) ST SG Q y) (P : ST) (c : (𝓞 X.E ⧸ P.1.asIdeal)ˣ) (P' : HeightOneSpectrum (𝓞 X.E)) :
    ptFr (p.mv (Formalism.L2.Col.DecoSet.dia1 P c p.1.1.deco)).1.1 P' = ptFr p.1.1 P' := by
  by_cases h : (∀ (P₁ : Q) (x : Formalism.L2.Col.Sp X.E n), p.1.1.1.2 P₁ x ∈ (Formalism.L2.Col.DecoSet.dia1 P c p.1.1.deco).1.at P₁.1 ↔
      x ∈ Formalism.L2.Col.stdAt X.E n P₁.1) ∧ p.1.2 ∈ y.ys (Formalism.L2.Col.DecoSet.dia1 P c p.1.1.deco).1.N
  · have e : p.mv (Formalism.L2.Col.DecoSet.dia1 P c p.1.1.deco) =
        ⟨(⟨(Formalism.L2.Col.DecoSet.dia1 P c p.1.1.deco, p.1.1.1.2), h.1⟩, p.1.2), h.2⟩ := dif_pos h
    rw [e]
    unfold ptFr
    rfl
  · have e : p.mv (Formalism.L2.Col.DecoSet.dia1 P c p.1.1.deco) = p := dif_neg h
    rw [e]

theorem finM_mul' {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) (g h : GA D V) :
    finM V hn (g * h) = finM V hn g * finM V hn h := by
  subst hn
  exact GlobalTheory.AdForm.RdLaw.finM_mul V g h

theorem ptOf_gl_dia : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ j (hj : j ≤ B.R.m) (i : ι) (v : (I.atT l u a).vT), Formalism.L2.NTheta.IsIdemAt (p i).e v.1 →
    ∀ g : 𝓀[k]ˣ → GL (Fin ((I.rec7 l Z).sp.X j).rank) k, (∀ s, g s • Q j i = s • Q j i) →
      ∀ b (c : {c // A.chOf j c = b}), ∃ e : 𝓀[k]ˣ ≃ ((I.atT l u a).Fv v)ˣ, ∀ s,
        ∃ z : TC.GA B (B.R.N j),
          z.1 = finM _ (rankN (I.rec7 l Z) j hj) (A.h j b c * (β j i).gl (g s)) ∧
          TC.PtOf (z * A.kb j b) (extTo I.SQ (((I.atIn u a).A j).diaPt v (e s) c.1).1.1) := by
  intro B X I hOk hPins l Z u a Ch A hA k _ _ _ _ ι p β Q L hStd j hj i v hv g hg b c
  obtain ⟨c, rfl⟩ := c
  obtain ⟨-, ρ, hρ⟩ := GlobalTheory.FinPl.SplitPt.resField_equiv (I.rec7 l Z) k (p i) v.1 hv
  refine ⟨(Units.mapEquiv ρ.toMulEquiv).toEquiv, fun s => ?_⟩
  obtain ⟨δ, hδ, huni, hint, hint'⟩ := GlobalTheory.AdForm.frameGl_int I hOk hPins l Z u a k ι p β Q L hStd j hj i v hv (g s) s (hg s)
  have htriv := GlobalTheory.T.frameImage_trivial_off_levelPrime I hOk hPins l Z u a k ι p β Q L hStd j hj i v hv (g s) δ hδ
  have hrow := GlobalTheory.AdForm.lastRow_inv_frame I hOk hPins l Z u a k ι p β Q L hStd j hj i v hv ρ hρ (g s) s (hg s) δ hδ hint'
  have hR := hA.reads j hj
  let y : TC.GA B (B.R.N j) := ((A.K j hj (A.chOf j c)).y ⟨c, rfl⟩).1
  refine ⟨y * δ, ?_, ?_⟩
  · rw [Units.val_mul, hδ, finM_mul', (hA.h j hj _ ⟨c, rfl⟩).2]
    rfl
  · obtain ⟨p0, hk0, hN0⟩ := hR.k_std (A.chOf j c)
    have hkc := hk0.lat
    rw [hN0] at hkc
    refine GlobalTheory.Mem.Col2.DilPt.isPointOf_last_coordinate_dilation_one_prime_alt _ _ _ _ _ _ _ y δ (A.kb j (A.chOf j c)) (extTo I.SQ ((I.stp u a j).rep c).1.1) _
      ⟨v.1, v.2⟩ ((Units.mapEquiv ρ.toMulEquiv) s) _ (hR.pt c) hk0.uni huni hkc hint hint' htriv
      (fun r r' hr => hR.k_T (A.chOf j c) ⟨v.1, v.2⟩ r r' hr) (fun r r' hr => hrow r r' hr) ?_ ?_
    · rw [extTo_deco, extTo_deco]
      exact GlobalTheory.Mem.Col2.TwAtStd.diaPt_deco B X I u a j ⟨v.1, v.2⟩ _ c
    · funext P'
      rw [extTo_fr, extTo_fr]
      exact decoratedLattice_unitScale_functional_keeps_frames ((I.stp u a j).rep c) ⟨v.1, v.2⟩ _ P'.1

end GlobalTheory.AdForm.DiaChart

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsChartPointRightTranslateStabilizerSplitPlaStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_chartPoint_rightTranslate_stabilizer_splitPlace : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ j (hj : j ≤ B.R.m) (i : ι) (v : (I.atT l u a).vT), Formalism.L2.NTheta.IsIdemAt (p i).e v.1 →
    ∀ g : 𝓀[k]ˣ → GL (Fin ((I.rec7 l Z).sp.X j).rank) k, (∀ s, g s • Q j i = s • Q j i) →
      ∀ b (c : {c // A.chOf j c = b}), ∃ e : 𝓀[k]ˣ ≃ ((I.atT l u a).Fv v)ˣ, ∀ s,
        ∃ z : TC.GA B (B.R.N j),
          z.1 = finM _ (rankN (I.rec7 l Z) j hj) (A.h j b c * (β j i).gl (g s)) ∧
          TC.PtOf (z * A.kb j b) (extTo I.SQ (((I.atIn u a).A j).diaPt v (e s) c.1).1.1) := by
  first | exact @GlobalTheory.AdForm.DiaChart.ptOf_gl_dia | exact GlobalTheory.AdForm.DiaChart.ptOf_gl_dia | (intros; apply GlobalTheory.AdForm.DiaChart.ptOf_gl_dia <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartScalarFormAdelicPointEqClassTransport
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartScalarFormAdelicPointEqClassTransport
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.UG

namespace GlobalTheory.AdForm.RdTrans

theorem finM_inf' {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) (k : GA D V) (hk : k ∈ GinfC V) : finM V hn k = 1 := by
  subst hn
  exact GlobalTheory.AdForm.RdLaw.finM_inf V k hk

end GlobalTheory.AdForm.RdTrans

namespace GlobalTheory.AdForm.RdTrans

theorem infM_fin'' {D : D7} (θ : InfFam D) (V : HSp D) {n : ℕ} (hn : V.rank = n) (k : GA D V) (hk : k ∈ GfC V)
    (τ : D.what₂.Tau) : infM θ V hn k τ = 1 := by
  subst hn
  exact GlobalTheory.AdForm.RdLaw.infM_fin θ V k hk τ

end GlobalTheory.AdForm.RdTrans

namespace GlobalTheory.AdForm.RdTrans

theorem atInf_mul_inv {E : Type} [Field E] {n : ℕ} {ι : Type} (emb : ι → E →+* ℂ) (γ : GL (Fin n) E) (τ : ι) :
    atInf emb γ.val τ * atInf emb (γ⁻¹).val τ = 1 := by
  unfold atInf
  rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem eq_of_mul_eq_one {n : ℕ} (A B C D : Matrix (Fin n) (Fin n) ℂ) (h1 : A * B = 1) (h2 : C * D = 1) (h3 : B = C) :
    A = D := by
  calc A = A * (C * D) := by rw [h2, Matrix.mul_one]
    _ = (A * B) * D := by rw [h3, Matrix.mul_assoc]
    _ = D := by rw [h1, Matrix.one_mul]

end GlobalTheory.AdForm.RdTrans

namespace GlobalTheory.AdForm.RdTrans


set_option maxHeartbeats 1000000 in
theorem exists_level {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (u : B.Word) (a : I.ι) (i : ℕ) {Ch : Type}
    {chOf : (I.stp u a i).Cl → Ch}
    {Lb : Ch → Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)} {U : Ch → Subgroup (TC.GA B (B.R.N i))} {chi : ∀ β, U β →* ℂˣ}
    {y : (I.stp u a i).Cl → TC.GA B (B.R.N i)} {st : ∀ c, (I.stp u a i).Stab c → GL (Fin (B.R.N i)) B.host.E}
    {k : Ch → TC.GA B (B.R.N i)}
    (h : I.Reads u a i chOf Lb U chi y st k) (b : (I.stp u a i).β) (d : (I.stp u a i).D b)
    (hco : cosetIn d = cosetIn ((I.stp u a i).rep ((I.stp u a i).cl b d)))
    (w : TC.GA B (B.R.N i)) (hw : TC.PtOf (w * k (chOf ((I.stp u a i).cl b d))) d.1.1) :
    ∃ x : U (chOf ((I.stp u a i).cl b d)), w = bc (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F))
        ((I.stp u a i).gam b ((I.stp u a i).mv b d)) * y ((I.stp u a i).cl b d) * x.1 ∧
      ((chi _ x : ℂˣ) : ℂ) = B.embLL (((I.stp u a i).chr b ((I.stp u a i).mv b d) : B.LLˣ) : B.LL) := by
  have hg := (I.stp u a i).mv_smul b d
  generalize (I.stp u a i).mv b d = g at hg ⊢
  have hlev := h.lev ((I.stp u a i).cl b d)
  have hchr := h.chr ((I.stp u a i).cl b d)
  generalize y ((I.stp u a i).cl b d) = y' at hlev hchr ⊢
  obtain ⟨γ, κ⟩ := g
  have hk : (I.stp u a i).act b (1, κ) ((I.stp u a i).rep ((I.stp u a i).cl b d)) =
      (I.stp u a i).act b (γ⁻¹, 1) d := by
    refine Eq.trans ?_ (congrArg ((I.stp u a i).act b (γ⁻¹, 1)) hg)
    refine Eq.trans ?_ (((I.stp u a i).actD b).mul_smul (γ⁻¹, 1) (γ, κ) _)
    rw [Prod.mk_mul_mk, inv_mul_cancel, one_mul]
    rfl
  have hpt : TC.PtOf (y' * (y'⁻¹ * (ratAd B.host.F γ⁻¹ * w)) * k (chOf ((I.stp u a i).cl b d)))
      ((I.stp u a i).act b (1, κ) ((I.stp u a i).rep ((I.stp u a i).cl b d))).1.1 := by
    rw [hk, mul_inv_cancel_left, mul_assoc]
    exact GlobalTheory.T.isPointOf_rational_unitary_adelic_mul _ _ _ _ _ _ _ γ⁻¹ _ _ hw
  have hx := (hlev _ _ hpt).2 ⟨(1, κ), map_one (Formalism.L2.Col.ufGL _ _), rfl, by
    refine Eq.trans ?_ hco
    refine (congrArg (fun q : (I.stp u a i).D b => cosetIn q) hk).trans ?_
    exact GlobalTheory.T.couplingCoset_frames_invariant_rational_unitary _ _ _ _ _ _ _ _ _ (GlobalTheory.Mem.FieldsLaws.fields_ok B) l.pr _ _ γ⁻¹ rfl rfl⟩
  refine ⟨⟨_, hx⟩, ?_, hchr ⟨_, hx⟩ (1, κ) (map_one (Formalism.L2.Col.ufGL _ _)) hpt⟩
  show w = ratAd B.host.F γ * y' * (y'⁻¹ * (ratAd B.host.F γ⁻¹ * w))
  rw [mul_assoc, mul_inv_cancel_left, ← mul_assoc]
  unfold ratAd
  rw [← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one, one_mul]

end GlobalTheory.AdForm.RdTrans


set_option maxHeartbeats 4000000 in
theorem GlobalTheory.AdForm.rd_trTo : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ θ, IsInfFam θ → ∀ j (hj : j ≤ B.R.m), ∀ φ ∈ (I.fm l u a).Fi j, ∀ b (c : (I.chain l u a).cls j) (d : (I.stp u a j).D c.1)
    (x : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)) (z : TC.GA B (B.R.N j)), x ∈ GfC _ →
    z.1 = finM _ (rankN (I.rec7 l Z) j hj) x → TC.PtOf (z * A.kb j b) (extTo I.SQ d.1.1) →
    A.chOf j ((I.stp u a j).cl c.1 d) = b →
    cosetIn d = cosetIn ((I.stp u a j).rep ((I.stp u a j).cl c.1 d)) → ∀ y,
      A.rd θ j hj b φ y x = (I.stp u a j).trTo B.fields.emb B.embLL c.1 d (φ ((I.stp u a j).cl c.1 d)) y := by
  intro B X I hI hP l Z u a Ch A hA θ hθ j hj φ hφ b c d x z hx hzx hpt hb hco y
  subst hb
  have hd : Disjoint (B.primes X).vGs (I.Q a) := (LevTwist.levOk_twists B X I hI).2.1.mono_right (I.Q_subset_SQ a)
  have hw : TC.PtOf (z * A.kb j (A.chOf j ((I.stp u a j).cl c.1 d))) d.1.1 := IsPtOf.of_extTo (I.Q_subset_SQ a) hd hpt
  obtain ⟨x₀, hz, hchi⟩ := GlobalTheory.AdForm.RdTrans.exists_level I l u a j (hA.reads j hj) c.1 d hco z hw
  have hg1 := ((GlobalTheory.T.trueColumn_spaces_standard_in_frameCoords I hI hP l Z).2.2.2 j hj).1
  unfold Formalism.L2.Forms.gramN at hg1
  have hγ : (I.stp u a j).gam c.1 ((I.stp u a j).mv c.1 d) ∈ UJ (Formalism.L2.Forms.sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E)
      (Matrix.reindex (finCongr (rankN (I.rec7 l Z) j hj)) (finCongr (rankN (I.rec7 l Z) j hj)) (HSpace.gram ((I.rec7 l Z).sp.X j))) := by
    rw [hg1]
    show cT _ _ * 1 * _ = 1
    rw [Matrix.mul_one]
    exact GlobalTheory.Mem.Col2.StepOk.ufGL_conjTranspose_mul _
  obtain ⟨α, hαQ, hαf, hαi⟩ := GlobalTheory.Core.Mi.exists_GQ_of_unitary θ hθ _ (rankN (I.rec7 l Z) j hj) _ hγ
  obtain ⟨ai, hai, af, haf, hα⟩ := (GlobalTheory.UnitarySplit.real_finite_split _ ((I.rec7 l Z).sp.X j)).1 α
  have hcomm := (GlobalTheory.UnitarySplit.real_finite_split _ ((I.rec7 l Z).sp.X j)).2.1
  have hh := hA.h j hj (A.chOf j ((I.stp u a j).cl c.1 d)) ⟨(I.stp u a j).cl c.1 d, rfl⟩
  let F : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) →* TC.GA B (B.R.N j) := GlobalTheory.ClassSumLevel.finGLHom _ (rankN (I.rec7 l Z) j hj)
  have hFx : F x = z := Units.ext hzx.symm
  have hFh : F (A.h j (A.chOf j ((I.stp u a j).cl c.1 d)) ⟨(I.stp u a j).cl c.1 d, rfl⟩) =
      ((A.K j hj (A.chOf j ((I.stp u a j).cl c.1 d))).y ⟨(I.stp u a j).cl c.1 d, rfl⟩).1 := Units.ext hh.2
  have hFi : F ai = 1 :=
    Units.ext (GlobalTheory.AdForm.RdTrans.finM_inf' _ _ ai hai)
  have hFa : F af =
      bc (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F)) ((I.stp u a j).gam c.1 ((I.stp u a j).mv c.1 d)) := by
    have e : F α = _ := Units.ext hαf
    rw [hα, map_mul, hFi, one_mul] at e
    exact e
  have hFκ : F
      ((A.h j (A.chOf j ((I.stp u a j).cl c.1 d)) ⟨(I.stp u a j).cl c.1 d, rfl⟩)⁻¹ * af⁻¹ * x) = x₀.1 := by
    rw [map_mul, map_mul, map_inv, map_inv, hFx, hFh, hFa, hz]
    have key : ∀ {G : Type} [Group G] (p q r : G), p⁻¹ * q⁻¹ * (q * p * r) = r := by intros; group
    exact key _ _ _
  have hU : (A.h j (A.chOf j ((I.stp u a j).cl c.1 d)) ⟨(I.stp u a j).cl c.1 d, rfl⟩)⁻¹ * af⁻¹ * x ∈
      A.U j (A.chOf j ((I.stp u a j).cl c.1 d)) :=
    (hA.U j hj _ _).2 ⟨mul_mem (mul_mem (inv_mem hh.1) (inv_mem haf)) hx, x₀, by rw [← hFκ]; rfl⟩
  have hchiA := hA.chi j hj _ ⟨_, hU⟩ x₀ (by rw [← hFκ]; rfl)
  have hdec : x = α * (A.h j (A.chOf j ((I.stp u a j).cl c.1 d)) ⟨(I.stp u a j).cl c.1 d, rfl⟩ * ai⁻¹) *
      ((A.h j (A.chOf j ((I.stp u a j).cl c.1 d)) ⟨(I.stp u a j).cl c.1 d, rfl⟩)⁻¹ * af⁻¹ * x) := by
    have e1 := hcomm _ (inv_mem hai) _ hh.1
    have e2 := hcomm _ (inv_mem hai) _ haf
    rw [hα, ← e1]
    have key : ∀ {G : Type} [Group G] (p q r t : G), q * p⁻¹ = p⁻¹ * q → t = p * q * (p⁻¹ * r) * (r⁻¹ * q⁻¹ * t) := by
      intro G _ p q r t h
      calc t = p * (p⁻¹ * q) * q⁻¹ * t := by group
        _ = p * (q * p⁻¹) * q⁻¹ * t := by rw [h]
        _ = p * q * (p⁻¹ * r) * (r⁻¹ * q⁻¹ * t) := by group
    exact key _ _ _ _ e2.symm
  have hinf : ∀ τ, infM θ _ (rankN (I.rec7 l Z) j hj) ai⁻¹ τ =
      atInf (Formalism.L2.Forms.embT (I.rec7 l Z)) (((I.stp u a j).gam c.1 ((I.stp u a j).mv c.1 d))⁻¹ : GL _ _).val τ := by
    intro τ
    have e1 : infM θ _ (rankN (I.rec7 l Z) j hj) α τ = infM θ _ (rankN (I.rec7 l Z) j hj) ai τ := by
      rw [hα, GlobalTheory.AdForm.Model.infM_mul, GlobalTheory.AdForm.RdTrans.infM_fin'' θ _ _ af haf, Matrix.mul_one]
    have e2 : infM θ _ (rankN (I.rec7 l Z) j hj) ai⁻¹ τ * infM θ _ (rankN (I.rec7 l Z) j hj) ai τ = 1 := by
      rw [← GlobalTheory.AdForm.Model.infM_mul, inv_mul_cancel, GlobalTheory.AdForm.Model.infM_one]
    exact GlobalTheory.AdForm.RdTrans.eq_of_mul_eq_one _ _ _ _ e2
      (GlobalTheory.AdForm.RdTrans.atInf_mul_inv (Formalism.L2.Forms.embT (I.rec7 l Z)) ((I.stp u a j).gam c.1 ((I.stp u a j).mv c.1 d)) τ)
      (e1.symm.trans (hαi τ))
  let y' : (I.chain l u a).Y j :=
    ⟨(frMul B.fields.emb B.embLL ((I.stp u a j).gam c.1 ((I.stp u a j).mv c.1 d))⁻¹ ⟨y.1, y.2⟩).1,
      (frMul B.fields.emb B.embLL ((I.stp u a j).gam c.1 ((I.stp u a j).mv c.1 d))⁻¹ ⟨y.1, y.2⟩).2⟩
  have hTr : IsTr (G := fun _ => 1) (infM θ _ (rankN (I.rec7 l Z) j hj) ai⁻¹) ⟨y.1, y.2⟩ ⟨y'.1, y'.2⟩ := by
    intro τ
    rw [hinf τ]
    have he : Formalism.L2.Col.embAt B.embLL B.fields.emb τ = Formalism.L2.Forms.embT (I.rec7 l Z) τ := by
      unfold Formalism.L2.Col.embAt Formalism.L2.Forms.embT
      exact FieldsLaws.embLL_comp_emb B τ
    unfold atInf
    show (((I.stp u a j).gam c.1 ((I.stp u a j).mv c.1 d))⁻¹ : GL _ _).val.map (Formalism.L2.Col.embAt B.embLL B.fields.emb τ) * y.1 τ = _
    rw [he]
    rfl
  have key := (GlobalTheory.AdForm.rd_charts I hI hP l Z u a Ch A hA θ hθ j hj φ hφ).2 (A.chOf j ((I.stp u a j).cl c.1 d)) y α hαQ
    ⟨(I.stp u a j).cl c.1 d, rfl⟩ ai⁻¹ (inv_mem hai) ⟨_, hU⟩ y' hTr
  rw [hdec, key, hchiA]
  exact congrArg₂ (· * ·) hchi rfl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartScalarFormAdelicPointEqClassTransportStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartScalarForm_adelicPoint_eq_classTransport : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ θ, IsInfFam θ → ∀ j (hj : j ≤ B.R.m), ∀ φ ∈ (I.fm l u a).Fi j, ∀ b (c : (I.chain l u a).cls j) (d : (I.stp u a j).D c.1)
    (x : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)) (z : TC.GA B (B.R.N j)), x ∈ GfC _ →
    z.1 = finM _ (rankN (I.rec7 l Z) j hj) x → TC.PtOf (z * A.kb j b) (extTo I.SQ d.1.1) →
    A.chOf j ((I.stp u a j).cl c.1 d) = b →
    cosetIn d = cosetIn ((I.stp u a j).rep ((I.stp u a j).cl c.1 d)) → ∀ y,
      A.rd θ j hj b φ y x = (I.stp u a j).trTo B.fields.emb B.embLL c.1 d (φ ((I.stp u a j).cl c.1 d)) y := by
  first | exact @GlobalTheory.AdForm.rd_trTo | exact GlobalTheory.AdForm.rd_trTo | (intros; apply GlobalTheory.AdForm.rd_trTo <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChOfDil
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm

theorem chOf_dil : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ j, j ≤ B.R.m → ∀ (v : (I.atT l u a).vT) (s : ((I.atT l u a).Fv v)ˣ) (c : (I.chain l u a).cls j),
    A.chOf j ((I.fm l u a).dil j v s c) = A.chOf j c := by
  intro B X I hI hP l Z u a Ch A hA j hj v s c
  exact ((hA.reads j hj).key _ _).2 ⟨rfl, GlobalTheory.Mem.Col2.DiaChart.cosetIn_rep I l u a j v s c⟩

end GlobalTheory.AdForm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GlMemGfC
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FrameGfCImg

theorem gl_mem_GfC : ∀ {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {p : SplitPt D k} {S : HSp D} {n : Type} [Fintype n] [DecidableEq n] (β : Frame p S n) (g : GL n k), β.gl g ∈ GfC S := by
  intro D k _ _ _ _ p S n _ _ β g
  have hg := β.gl_supp g
  have he := p.split
  refine Units.ext (Matrix.ext fun i j => ?_)
  have h : infPart D ((mt S (β.gl g) - 1) i j) = 0 := by
    rw [← hg i j, RingHom.map_mul, RingHom.map_add (f := _), GlobalTheory.SplitScalar.infPart_splitIdem he,
      GlobalTheory.SplitScalar.infPart_splitIdem (GlobalTheory.SplitScalar.isSplitIdem_conj he), add_zero, zero_mul]
  rw [Matrix.sub_apply, RingHom.map_sub, sub_eq_zero] at h
  show infPart D (mt S (β.gl g) i j) = (1 : Matrix _ _ _) i j
  rw [h, Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · rw [RingHom.map_one]
  · rw [RingHom.map_zero]

end GlobalTheory.FrameGfCImg

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RepresentativeDiamondTranslateSumScalarForm
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.AdForm.rd_dia_sum : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ θ, IsInfFam θ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ j (hj : j ≤ B.R.m), ∀ φ ∈ (I.fm l u a).Fi j, ∀ (i : ι) (v : (I.atT l u a).vT), Formalism.L2.NTheta.IsIdemAt (p i).e v.1 →
    ∀ g : 𝓀[k]ˣ → GL (Fin ((I.rec7 l Z).sp.X j).rank) k, (∀ s, g s • Q j i = s • Q j i) →
      ∀ b y (c : {c // A.chOf j c = b}), (∑ᶠ s, A.rd θ j hj b φ y (A.h j b c * (β j i).gl (g s))) = (∑ᶠ s : ((I.atT l u a).Fv v)ˣ, (I.fm l u a).dilT j v s c.1 (φ ((I.fm l u a).dil j v s c.1))) y := by
  intro B X I hok hpins l Z u a Ch A hA θ hθ k _ _ _ _ ι p β Q L hT j hj φ hφ i v hv g hg b y c
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_chartPoint_rightTranslate_stabilizer_splitPlace I hok hpins l Z u a Ch A hA k ι p β Q L hT j hj i v hv g hg b c
  have hs : ∀ s, A.rd θ j hj b φ y (A.h j b c * (β j i).gl (g s)) =
      (I.fm l u a).dilT j v (e s) c.1 (φ ((I.fm l u a).dil j v (e s) c.1)) y := by
    intro s
    obtain ⟨z, hz, hpt⟩ := he s
    have hG : A.h j b c * (β j i).gl (g s) ∈ GfC _ := mul_mem (hA.h j hj b c).1 (GlobalTheory.FrameGfCImg.gl_mem_GfC (β j i) (g s))
    have hch : A.chOf j ((I.stp u a j).cl c.1.1 (((I.atIn u a).A j).diaPt v (e s) c.1)) = b :=
      (GlobalTheory.AdForm.chOf_dil I hok hpins l Z u a Ch A hA j hj v (e s) c.1).trans c.2
    have hco : cosetIn (GlobalTheory.Mem.Col2.DiaChart.dp I u a j v (e s) c.1) =
        cosetIn ((I.stp u a j).rep ((I.stp u a j).cl c.1.1 (GlobalTheory.Mem.Col2.DiaChart.dp I u a j v (e s) c.1))) :=
      (GlobalTheory.Mem.Col2.DiaChart.cosetIn_dia _ v (e s)).trans (GlobalTheory.Mem.Col2.DiaChart.cosetIn_rep I l u a j v (e s) c.1).symm
    exact GlobalTheory.T.chartScalarForm_adelicPoint_eq_classTransport I hok hpins l Z u a Ch A hA θ hθ j hj φ hφ b c.1 _ _ z hG hz hpt hch hco y
  rw [finsum_congr hs]
  rw [finsum_comp_equiv e (f := fun s' => (I.fm l u a).dilT j v s' c.1 (φ ((I.fm l u a).dil j v s' c.1)) y)]
  rw [finsum_apply]
  exact Set.toFinite _
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RepresentativeDiamondTranslateSumScalarFormStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.representative_diamond_translate_sum_scalarForm : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ θ, IsInfFam θ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ j (hj : j ≤ B.R.m), ∀ φ ∈ (I.fm l u a).Fi j, ∀ (i : ι) (v : (I.atT l u a).vT), Formalism.L2.NTheta.IsIdemAt (p i).e v.1 →
    ∀ g : 𝓀[k]ˣ → GL (Fin ((I.rec7 l Z).sp.X j).rank) k, (∀ s, g s • Q j i = s • Q j i) →
      ∀ b y (c : {c // A.chOf j c = b}), (∑ᶠ s, A.rd θ j hj b φ y (A.h j b c * (β j i).gl (g s))) = (∑ᶠ s : ((I.atT l u a).Fv v)ˣ, (I.fm l u a).dilT j v s c.1 (φ ((I.fm l u a).dil j v s c.1))) y := by
  first | exact @GlobalTheory.AdForm.rd_dia_sum | exact GlobalTheory.AdForm.rd_dia_sum | (intros; apply GlobalTheory.AdForm.rd_dia_sum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiamondTranslatesScalarFormsSumIff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.AdForm

theorem diaSum_iff : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ θ, IsInfFam θ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ j (hj : j ≤ B.R.m), ∀ φ ∈ (I.fm l u a).Fi j, ∀ (i : ι) (v : (I.atT l u a).vT), Formalism.L2.NTheta.IsIdemAt (p i).e v.1 →
    ∀ g : 𝓀[k]ˣ → GL (Fin ((I.rec7 l Z).sp.X j).rank) k, (∀ s, g s • Q j i = s • Q j i) →
      ((∀ b y, ∑ᶠ s, rTrans ((β j i).gl (g s)) (A.rd θ j hj b φ y) = 0) ↔
        ∀ c, ∑ᶠ s : ((I.atT l u a).Fv v)ˣ, (I.fm l u a).dilT j v s c (φ ((I.fm l u a).dil j v s c)) = 0) := by
  intro B X I hI hP l Z u a Ch A hA θ hθ k _ _ _ _ ι p β Q L hS j hj φ hφ i v hv g hg
  have hfin : ∀ (f : 𝓀[k]ˣ → GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) → ℂ) x, (∑ᶠ s, f s) x = ∑ᶠ s, f s x :=
    fun f x => finsum_apply (Set.toFinite _) x
  constructor
  · intro H c
    funext y
    have h1 := congrFun (H (A.chOf j c) y) (A.h j _ ⟨c, rfl⟩)
    rw [hfin] at h1
    simp only [GlobalTheory.MixPer.rTrans] at h1
    rw [GlobalTheory.T.representative_diamond_translate_sum_scalarForm I hI hP l Z u a Ch A hA θ hθ k ι p β Q L hS j hj φ hφ i v hv g hg _ y ⟨c, rfl⟩] at h1
    simpa using h1
  · intro H b y
    funext x
    rw [hfin]
    simp only [GlobalTheory.MixPer.rTrans, Pi.zero_apply]
    refine GlobalTheory.T.diamondTranslateSum_eq_zero_of_chartRepresentatives I hI hP l Z u a Ch A hA θ hθ k ι p β Q L hS j hj φ hφ i v hv g hg b y (fun c y' => ?_) x
    rw [GlobalTheory.T.representative_diamond_translate_sum_scalarForm I hI hP l Z u a Ch A hA θ hθ k ι p β Q L hS j hj φ hφ i v hv g hg b y' c]
    exact congrFun (H c.1) y'

end GlobalTheory.AdForm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiamondTranslatesScalarFormsSumIffStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing GlobalTheory.AdForm
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diamondTranslates_scalarForms_sum_iff : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ θ, IsInfFam θ → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
    (p : ι → SplitPt (I.rec7 l Z) k) (β : ∀ j i, Frame (p i) ((I.rec7 l Z).sp.X j) (Fin ((I.rec7 l Z).sp.X j).rank))
    (Q : ∀ j, ι → Pair k (Fin ((I.rec7 l Z).sp.X j).rank)) (L : ∀ j, Lat ((I.rec7 l Z).sp.X j)),
    StdT I l Z u p β Q L → ∀ j (hj : j ≤ B.R.m), ∀ φ ∈ (I.fm l u a).Fi j, ∀ (i : ι) (v : (I.atT l u a).vT), Formalism.L2.NTheta.IsIdemAt (p i).e v.1 →
    ∀ g : 𝓀[k]ˣ → GL (Fin ((I.rec7 l Z).sp.X j).rank) k, (∀ s, g s • Q j i = s • Q j i) →
      ((∀ b y, ∑ᶠ s, rTrans ((β j i).gl (g s)) (A.rd θ j hj b φ y) = 0) ↔
        ∀ c, ∑ᶠ s : ((I.atT l u a).Fv v)ˣ, (I.fm l u a).dilT j v s c (φ ((I.fm l u a).dil j v s c)) = 0) := by
  first | exact @GlobalTheory.AdForm.diaSum_iff | exact GlobalTheory.AdForm.diaSum_iff | (intros; apply GlobalTheory.AdForm.diaSum_iff <;> assumption)
end
