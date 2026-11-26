module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TopStepVectorTheta
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiMapCarriesNormalFrameLines

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodCharacterPrimitiveNormalFrames
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ColPairSmul
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
set_option synthInstance.maxHeartbeats 200000

namespace GlobalTheory.SplitPrimJac

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem colPair (q : GlobalTheory.FinPl.SplitPt D k) (S : HSp D) (x y : Fin S.rank → D.host.E) :
    ∑ r, ∑ t, q.pr (incA D (x r)) * q.pr (cA D (incA D (HSpace.gram S r t))) * q.pr (cA D (incA D (y t))) =
      q.pr (incA D (star (∑ r, ∑ t, star (x r) * HSpace.gram S r t * y t))) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [GlobalTheory.FinPl.FrameLat.cA_incA, star_sum, star_mul', star_star, map_sum, map_mul]

theorem mat_entry (S : HSp D) {m n : Type} [Fintype m] [Fintype n] (A : Matrix (Fin S.rank) m D.host.E)
    (B : Matrix (Fin S.rank) n D.host.E) (b : m) (i : n) :
    (Aᴴ * HSpace.gram S * B) b i = ∑ r, ∑ t, star (A r b) * HSpace.gram S r t * B t i := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem colPair_smul (q : GlobalTheory.FinPl.SplitPt D k) (S : HSp D) (c : k) (x y : Fin S.rank → D.host.E)
    (col : Fin S.rank → k) (hcol : ∀ r, col r = c * q.pr (incA D (x r))) :
    ∑ r, ∑ t, col r * q.pr (cA D (incA D (HSpace.gram S r t))) * q.pr (cA D (incA D (y t))) =
      c * q.pr (incA D (star (∑ r, ∑ t, star (x r) * HSpace.gram S r t * y t))) := by
  rw [← colPair, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [hcol]; ring

end GlobalTheory.SplitPrimJac
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodCharacterPrimitiveNormalFrames
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PrimNormal

theorem z_pair {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (v : Fin S₀.rank → D.host.E) (i : Fin ρ) :
    ∑ r, ∑ t, star ((d.i₀ *ᵥ v) r) * HSpace.gram S r t * d.e t i = 0 := by
  have hent : ∀ c, ∑ r, ∑ t, star (d.i₀ r c) * HSpace.gram S r t * d.e t i = 0 := fun c => by
    rw [← GlobalTheory.SplitPrimJac.mat_entry S d.i₀ d.e c i, d.i₀e, Matrix.zero_apply]
  have e : ∑ r, ∑ t, star ((d.i₀ *ᵥ v) r) * HSpace.gram S r t * d.e t i =
      ∑ c, star (v c) * ∑ r, ∑ t, star (d.i₀ r c) * HSpace.gram S r t * d.e t i := by
    simp only [Matrix.mulVec, dotProduct, star_sum, star_mul', Finset.sum_mul, Finset.mul_sum]
    calc _ = ∑ r, ∑ c, ∑ t, star (d.i₀ r c) * star (v c) * HSpace.gram S r t * d.e t i :=
            Finset.sum_congr rfl fun r _ => Finset.sum_comm
      _ = ∑ c, ∑ r, ∑ t, star (d.i₀ r c) * star (v c) * HSpace.gram S r t * d.e t i := Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun t _ => by ring
  rw [e]
  simp [hent]

end GlobalTheory.PrimNormal

namespace GlobalTheory.PrimNormal

theorem prim_of_normal : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ {a : XGeo D} (y : YRat a) {βT : GL (Fin D.sp.X'.rank) (Lev.EAf D)} {PP : Pl D.host.E} (l : LocX a βT PP) (FY : FYFam l) (sc : ℕ → l.k), IsNormalFr l y FY sc → (∀ j, j ≤ D.R.m → (a.x j).Is) → ∀ (N : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)) (M : ∀ j ρ (h : j + 2 * ρ + 2 = D.R.m), GlobalTheory.FinPl.Lat (y.bes j ρ h).V₀), (∀ j, j < D.R.m → IsSelfDualC (Yc D j) (N j)) → (∀ j c (hc : j + c = l.s + 1), IntIn l.q (Yc D j) (FY j c hc) (N j)) → (∀ j ρ h, IsSelfDualC (y.bes j ρ h).V₀ (M j ρ h)) → (∀ j ρ h (hj : j ≤ l.s + 1) (F₀ : Frame l.k ((y.bes j ρ h).lev (a.x j).vol).V₀.rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Unit)), (ofSplit l.q).IsCoreFrame ((y.bes j ρ h).lev (a.x j).vol) (sc j) (l.FX j hj) F₀ → IntIn l.q _ F₀ (M j ρ h)) → ∀ j ρ (h : j + 2 * ρ + 2 = D.R.m), GlobalTheory.FinPl.PrimAt ψ ((y.bes j ρ h).lev (a.x j).vol).d (N j) ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) := by
  intro D ψ hψ a y βT PP l FY sc hN hx N M hNsd hNint hMsd hMcore j ρ h
  rw [← l.under]
  have hc : j + (2 * ρ + 1) = l.s + 1 := by have := l.hs; omega
  have hB := hN.2.2.2.1 j ρ h (2 * ρ + 1) hc
  have hξ : valuation l.k (ofSplit l.q).xi = 1 := GlobalTheory.QTw.GeoInhab.xi_unit l.q l.unit
  have hsc := hN.1 j
  have hz := hN.2.2.1 j ρ h
  have inner0 : ∀ (x : Fin (Yc D j).rank → D.host.E) (i : Fin ρ),
      (∑ r, ∑ t, star (x r) * HSpace.gram (Yc D j) r t * ((y.bes j ρ h).lev (a.x j).vol).d.e t i) = 0 →
      ∀ (b : l.k) (col : Fin (Yc D j).rank → l.k), (∀ r, col r = b * l.q.pr (incA D (x r))) →
      ∑ r, ∑ t, col r * l.q.pr (cA D (incA D (HSpace.gram (Yc D j) r t))) *
        l.q.pr (cA D (incA D (((y.bes j ρ h).lev (a.x j).vol).d.e t i))) = 0 := by
    intro x i hx b col hcol
    rw [GlobalTheory.SplitPrimJac.colPair_smul l.q _ b x _ col hcol, hx, star_zero, map_zero, map_zero, mul_zero]
  have line : ∀ (i : Fin ρ) (b : AE D), GlobalTheory.FinPl.colMul ((y.bes j ρ h).lev (a.x j).vol).d.jX i b ∈
      GlobalTheory.FinPl.latV (Yc D j) (N j) (· = l.q.v) ↔ b ∈ GlobalTheory.FinPl.intAt D (· = l.q.v) := by
    intro i b
    refine GlobalTheory.PrimSplitLine.colMul_mem_latV_iff D l.k l.q _ _ ρ ((y.bes j ρ h).lev (a.x j).vol).d (N j) _
      (FY j (2 * ρ + 1) hc) i (Sum.inr ⟨i.val, by omega⟩) (Sum.inr ⟨2 * ρ - i.val, by omega⟩)
      (sc j * (ofSplit l.q).xi ^ (ρ - i.val))
      (sc j * (-(ofSplit l.q).hz ((y.bes j ρ h).lev (a.x j).vol) / (ofSplit l.q).xi) * (-1 / (ofSplit l.q).xi) ^ (ρ - 1 - i.val))
      (hNsd j (by omega)) (hNint j _ hc) ?_ ?_ ?_ ?_ b
    · rw [map_mul, map_pow, hsc, hξ, one_pow, one_mul]
    · simp only [map_mul, map_div₀, map_pow, Valuation.map_neg, map_one, hsc, hz, hξ]; simp
    · intro r; exact hB.2.2.1 i ⟨i.val, by omega⟩ rfl r
    · intro m
      rcases m with b | m
      · rw [if_neg Sum.inl_ne_inr]
        have hcol : ∀ r, (FY j (2 * ρ + 1) hc).β r (Sum.inl b) = ∑ e, (l.FX j (by omega)).β e b *
            l.q.pr (incA D ((((y.bes j ρ h).lev (a.x j).vol).d.i₀ * ((y.bes j ρ h).lev (a.x j).vol).o.iA) r e)) := by
          intro r
          rw [hB.2.1 r b, Matrix.mul_apply]
          exact Finset.sum_congr rfl fun e _ => mul_comm _ _
        simp only [hcol, Finset.sum_mul]
        rw [Finset.sum_congr rfl fun r _ => Finset.sum_comm, Finset.sum_comm]
        refine Finset.sum_eq_zero fun e _ => ?_
        simp only [mul_assoc]
        simp only [← mul_assoc]
        refine inner0 (fun r => (((y.bes j ρ h).lev (a.x j).vol).d.i₀ * ((y.bes j ρ h).lev (a.x j).vol).o.iA) r e) i ?_ _ _
          fun r => rfl
        rw [← GlobalTheory.SplitPrimJac.mat_entry, Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_assoc,
          ← Matrix.mul_assoc _ (HSpace.gram _), ((y.bes j ρ h).lev (a.x j).vol).d.i₀e, Matrix.mul_zero, Matrix.zero_apply]
      · by_cases hm : m.val < ρ
        · rw [if_neg (fun he => by cases he; simp at hm; omega)]
          refine inner0 (fun r => ((y.bes j ρ h).lev (a.x j).vol).d.e r ⟨m.val, hm⟩) i ?_ _ _ (hB.2.2.1 ⟨m.val, hm⟩ m rfl)
          rw [← GlobalTheory.SplitPrimJac.mat_entry, ((y.bes j ρ h).lev (a.x j).vol).d.ee, Matrix.zero_apply]
        · by_cases hm' : m.val = ρ
          · rw [if_neg (fun he => by cases he; simp at hm'; omega)]
            refine inner0 (fun r => (((y.bes j ρ h).lev (a.x j).vol).d.i₀ *ᵥ
              vecB ((y.bes j ρ h).lev (a.x j).vol).o ((y.bes j ρ h).lev (a.x j).vol).ζ) r) i ?_ _ _ (hB.2.2.2.1 m hm')
            exact z_pair _ _ i
          · have hi' : 2 * ρ - m.val < ρ := by omega
            have hcol := hB.2.2.2.2 ⟨2 * ρ - m.val, hi'⟩ m (by simp; omega)
            rw [GlobalTheory.SplitPrimJac.colPair_smul l.q _ _ _ _ _ hcol, ← GlobalTheory.SplitPrimJac.mat_entry,
              ((y.bes j ρ h).lev (a.x j).vol).d.e'e, Matrix.one_apply]
            by_cases hii : (⟨2 * ρ - m.val, hi'⟩ : Fin ρ) = i
            · have hmv : m.val = 2 * ρ - i.val := by rw [← hii]; simp; omega
              rw [if_pos hii, if_pos (by congr 1; exact Fin.ext hmv), star_one, map_one, map_one, mul_one, ← hii]
            · rw [if_neg hii, if_neg (fun he => hii (by cases he; ext; simp; omega)), star_zero, map_zero, map_zero,
                mul_zero]
  obtain ⟨ψk, hχ, hcond⟩ := GlobalTheory.QTw.GeoInhab.exists_char l.q l.unit hψ
  have hε : l.q.e + cA D l.q.e ∈ GlobalTheory.FinPl.intAt D (· = l.q.v) :=
    ⟨GlobalTheory.FinPl.FrameLat.sum_mem_idAt l.q, by
      rw [RingHom.map_add (f := _)]
      exact add_mem (GlobalTheory.FinPl.FrameLat.e_mem_intAt l.q).2
        ((GlobalTheory.FinPl.FrameLat.cA_int_iff _).2 (GlobalTheory.FinPl.FrameLat.e_mem_intAt l.q).2)⟩
  intro i i' hii' t ht
  rw [← GlobalTheory.SplitIntChar.int_iff_psiE D l.k l.q ψ ψk hξ hχ hcond t ht]
  constructor
  · intro H
    have h1 := H (l.q.e + cA D l.q.e) ((line i' _).2 hε)
    have ht' : t * (l.q.e + cA D l.q.e) = t := by rw [mul_comm]; exact (GlobalTheory.FinPl.FrameLat.idem_iff l.q t).1 ht
    rwa [line i, ht'] at h1
  · intro H b hb
    rw [line i'] at hb
    rw [line i]
    exact ⟨Ideal.mul_mem_right _ _ H.1, by rw [RingHom.map_mul]; exact GlobalTheory.FinPl.FrameLat.mul_mem_intAE H.2 hb.2⟩

end GlobalTheory.PrimNormal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodCharacterPrimitiveNormalFramesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselPeriodCharacter_primitive_normalFrames : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ {a : XGeo D} (y : YRat a) {βT : GL (Fin D.sp.X'.rank) (Lev.EAf D)} {PP : Pl D.host.E} (l : LocX a βT PP) (FY : FYFam l) (sc : ℕ → l.k), IsNormalFr l y FY sc → (∀ j, j ≤ D.R.m → (a.x j).Is) → ∀ (N : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)) (M : ∀ j ρ (h : j + 2 * ρ + 2 = D.R.m), GlobalTheory.FinPl.Lat (y.bes j ρ h).V₀), (∀ j, j < D.R.m → IsSelfDualC (Yc D j) (N j)) → (∀ j c (hc : j + c = l.s + 1), IntIn l.q (Yc D j) (FY j c hc) (N j)) → (∀ j ρ h, IsSelfDualC (y.bes j ρ h).V₀ (M j ρ h)) → (∀ j ρ h (hj : j ≤ l.s + 1) (F₀ : Frame l.k ((y.bes j ρ h).lev (a.x j).vol).V₀.rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Unit)), (ofSplit l.q).IsCoreFrame ((y.bes j ρ h).lev (a.x j).vol) (sc j) (l.FX j hj) F₀ → IntIn l.q _ F₀ (M j ρ h)) → ∀ j ρ (h : j + 2 * ρ + 2 = D.R.m), GlobalTheory.FinPl.PrimAt ψ ((y.bes j ρ h).lev (a.x j).vol).d (N j) ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) := by
  first | exact @GlobalTheory.PrimNormal.prim_of_normal | exact GlobalTheory.PrimNormal.prim_of_normal | (intros; apply GlobalTheory.PrimNormal.prim_of_normal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiLatticeSplitsAtNormalFramePlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiLatticeSplitsAtNormalFramePlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Fam

theorem monoW_of_normalFrames : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ {a : XGeo D} (y : YRat a) {βT : GL (Fin D.sp.X'.rank) (Lev.EAf D)} {PP : Pl D.host.E} (l : LocX a βT PP) (FY : FYFam l) (sc : ℕ → l.k), IsNormalFr l y FY sc → (∀ j, j ≤ D.R.m → (a.x j).Is) → ∀ (N : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)) (M : ∀ j ρ (h : j + 2 * ρ + 2 = D.R.m), GlobalTheory.FinPl.Lat (y.bes j ρ h).V₀), (∀ j, j < D.R.m → IsSelfDualC (Yc D j) (N j)) → (∀ j c (hc : j + c = l.s + 1), IntIn l.q (Yc D j) (FY j c hc) (N j)) → (∀ j ρ h, IsSelfDualC (y.bes j ρ h).V₀ (M j ρ h)) → (∀ j ρ h (hj : j ≤ l.s + 1) (F₀ : Frame l.k ((y.bes j ρ h).lev (a.x j).vol).V₀.rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Unit)), (ofSplit l.q).IsCoreFrame ((y.bes j ρ h).lev (a.x j).vol) (sc j) (l.FX j hj) F₀ → IntIn l.q _ F₀ (M j ρ h)) → ∀ j ρ (h : j + 2 * ρ + 2 = D.R.m), GlobalTheory.FinPl.MonoAt ((y.jac j ρ h).lev (a.x (j + 1)).vol).d (N (j + 1)) (a.x (j + 1)).L ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) := by
  intro D ψ _ a y βT PP l FY sc hN hx N M hsdN hIntN _ _ j ρ h
  have hs := l.hs
  have hc : j + 1 + 2 * ρ = l.s + 1 := by omega
  have hm := GlobalTheory.JacMono.monoAt_of_jacFrame l.q l.unit ((y.jac j ρ h).lev (a.x (j + 1)).vol)
    (hsdN (j + 1) (by omega)) (hx (j + 1) (by omega)).sd (hN.1 j) (hN.2.2.1 j ρ h) (hN.2.2.2.2.1 j ρ h _ hc)
    (hIntN (j + 1) _ hc) (l.latX (j + 1) (by omega))
  rw [l.under] at hm
  exact hm

end GlobalTheory.Fam

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiLatticeSplitsAtNormalFramePlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierJacobiLattice_splits_at_normalFrame_place : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ {a : XGeo D} (y : YRat a) {βT : GL (Fin D.sp.X'.rank) (Lev.EAf D)} {PP : Pl D.host.E} (l : LocX a βT PP) (FY : FYFam l) (sc : ℕ → l.k), IsNormalFr l y FY sc → (∀ j, j ≤ D.R.m → (a.x j).Is) → ∀ (N : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)) (M : ∀ j ρ (h : j + 2 * ρ + 2 = D.R.m), GlobalTheory.FinPl.Lat (y.bes j ρ h).V₀), (∀ j, j < D.R.m → IsSelfDualC (Yc D j) (N j)) → (∀ j c (hc : j + c = l.s + 1), IntIn l.q (Yc D j) (FY j c hc) (N j)) → (∀ j ρ h, IsSelfDualC (y.bes j ρ h).V₀ (M j ρ h)) → (∀ j ρ h (hj : j ≤ l.s + 1) (F₀ : Frame l.k ((y.bes j ρ h).lev (a.x j).vol).V₀.rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Unit)), (ofSplit l.q).IsCoreFrame ((y.bes j ρ h).lev (a.x j).vol) (sc j) (l.FX j hj) F₀ → IntIn l.q _ F₀ (M j ρ h)) → ∀ j ρ (h : j + 2 * ρ + 2 = D.R.m), GlobalTheory.FinPl.MonoAt ((y.jac j ρ h).lev (a.x (j + 1)).vol).d (N (j + 1)) (a.x (j + 1)).L ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) := by
  first | exact @GlobalTheory.Fam.monoW_of_normalFrames | exact GlobalTheory.Fam.monoW_of_normalFrames | (intros; apply GlobalTheory.Fam.monoW_of_normalFrames <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormalFramePlaceYZeroPrimitiveInHomLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PrHOUpIncAdj
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.RootEx GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.SplitWeil GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LastPrimSplit

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem pr_e (q : GlobalTheory.FinPl.SplitPt D k) : q.pr q.e = 1 := by
  rw [← GlobalTheory.FinPl.FrameLat.sec_one q, q.pr_sec]

theorem incAdj_yZero_apply {ρ : ℕ} (hρ : 0 < ρ) {S T T₀ : HSp D} (d : HypDec T T₀ ρ) (z : Fin S.rank → D.host.E)
    (a : AE D) (i : Fin T.rank) (l : Fin S.rank) :
    d.incAdj S (a • yZero S ρ z) i l =
      cA D a * incA D (D.host.xi0⁻¹ * d.e' i ⟨ρ - 1, by omega⟩ * (star z ᵥ* S.gram) l) := by
  have hell : ∀ i : Fin ρ, cA D (ell D ρ i) = if i = ⟨ρ - 1, by omega⟩ then 1 else 0 := by
    intro i
    simp only [ell, Fin.ext_iff]
    split_ifs with h1 h2 h2 <;> first | (exfalso; omega) | simp
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [HypDec.incAdj_apply, HypDec.incY_apply, yZero, zEll, Matrix.vecMul, dotProduct,
    Matrix.mul_apply, Matrix.smul_apply, Matrix.neg_apply, adj, Matrix.transpose_apply, Matrix.map_apply,
    Matrix.vecMulVec_apply, smul_eq_mul, map_mul, map_neg, hell, map_sum]
  rw [Finset.sum_eq_single (⟨ρ - 1, by omega⟩ : Fin ρ) (fun i _ hi => by simp [hi]) (fun h => absurd (Finset.mem_univ _) h)]
  simp only [if_true, mul_one, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  change incA D (d.e' i _) * (-incA D _ * (cA D a * -incA D (star (z m)) * incA D (S.gram m l))) =
    cA D a * (incA D _ * incA D (d.e' i _) * (incA D (star (z m)) * incA D (S.gram m l)))
  ring

theorem map_row {E : Type} [Field E] (f : E →+* k) {m n : Type} [Fintype m] (w : m → E) (M : Matrix m n E) (j : n) :
    ∑ l, f (w l) * f (M l j) = f ((w ᵥ* M) j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.vecMul, dotProduct, map_sum, RingHom.map_mul]

theorem row_core (q : GlobalTheory.FinPl.SplitPt D k) {ρ : ℕ} (B : BesLev D ρ) {n : Type} [Fintype n] [DecidableEq n] (sc : k)
    (FA : Frame k B.A.rank n) (F₀ : Frame k B.V₀.rank (n ⊕ Unit)) (hF₀ : (ofSplit q).IsCoreFrame B sc FA F₀) :
    (fun l => q.pr (incA D ((star (vecB B.o B.ζ) ᵥ* B.V₀.gram) l))) ᵥ* F₀.β =
      Pi.single (Sum.inr ()) (sc * (ofSplit q).hz B) := by
  set f := q.pr.comp (incA D) with hf
  funext t
  rcases t with t | ⟨⟨⟩⟩
  · rw [Pi.single_eq_of_ne Sum.inl_ne_inr]
    have h0 : (fun l => f ((star (vecB B.o B.ζ) ᵥ* B.V₀.gram) l)) ᵥ* B.o.iA.map f = 0 := by
      funext j
      refine (map_row f _ B.o.iA j).trans ?_
      rw [vecB, Matrix.star_mulVec, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, B.o.orth,
        Matrix.vecMul_zero, Pi.zero_apply, Pi.zero_apply, map_zero]
    have h1 : ((fun l => f ((star (vecB B.o B.ζ) ᵥ* B.V₀.gram) l)) ᵥ* (B.o.iA.map f * FA.β)) t = 0 := by
      rw [← Matrix.vecMul_vecMul, h0, Matrix.zero_vecMul, Pi.zero_apply]
    rw [← h1]
    change ∑ l, f ((star (vecB B.o B.ζ) ᵥ* B.V₀.gram) l) * F₀.β l (Sum.inl t) =
      ∑ l, f ((star (vecB B.o B.ζ) ᵥ* B.V₀.gram) l) * (B.o.iA.map f * FA.β) l t
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hF₀.1 l t]
    rfl
  · rw [Pi.single_eq_same]
    have h0 : (star (vecB B.o B.ζ) ᵥ* B.V₀.gram) ⬝ᵥ vecB B.o B.ζ = star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ := by
      rw [vecB, Matrix.star_mulVec, Matrix.vecMul_vecMul, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, B.o.isoB]
    change ∑ l, f _ * F₀.β l (Sum.inr ()) = sc * f (star B.ζ ⬝ᵥ B.L.gram *ᵥ B.ζ)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← h0, dotProduct, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hF₀.2 l, RingHom.map_mul, mul_left_comm]
    rfl

theorem row_jac (q : GlobalTheory.FinPl.SplitPt D k) {ρ : ℕ} (hρ : 0 < ρ) (J : JacLev D ρ) {n' : Type} [Fintype n'] [DecidableEq n']
    (sc hh : k) (FW₀ : Frame k J.W₀.rank n') (FW : Frame k J.W.rank (n' ⊕ Fin (2 * ρ)))
    (hFW : (ofSplit q).IsJacFrame J sc hh FW₀ FW) :
    (fun l => q.pr (incA D ((J.d.e'ᴴ * J.W.gram) ⟨ρ - 1, by omega⟩ l))) ᵥ* FW.β =
      Pi.single (Sum.inr ⟨ρ - 1, by omega⟩) (sc * (ofSplit q).xi) := by
  set f := q.pr.comp (incA D) with hf
  set i₀ : Fin ρ := ⟨ρ - 1, by omega⟩ with hi₀
  have hcol : ∀ {m : ℕ} (M : Matrix (Fin J.W.rank) (Fin m) D.host.E) (j : Fin m),
      ∑ l, f ((J.d.e'ᴴ * J.W.gram) i₀ l) * f (M l j) = f ((J.d.e'ᴴ * J.W.gram * M) i₀ j) := fun M j => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.mul_apply (M := J.d.e'ᴴ * J.W.gram), map_sum]
    simp only [RingHom.map_mul]
  funext t
  rcases t with t | t
  · rw [Pi.single_eq_of_ne Sum.inl_ne_inr]
    have hz : J.d.e'ᴴ * J.W.gram * J.d.i₀ = 0 := by
      have := congrArg Matrix.conjTranspose J.d.i₀e'
      rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, gram_conjTranspose, conjTranspose_zero,
        ← Matrix.mul_assoc] at this
    have h0 : (fun l => f ((J.d.e'ᴴ * J.W.gram) i₀ l)) ᵥ* J.d.i₀.map f = 0 := by
      funext j
      refine (hcol J.d.i₀ j).trans ?_
      rw [hz, Matrix.zero_apply, map_zero, Pi.zero_apply]
    have h1 : ((fun l => f ((J.d.e'ᴴ * J.W.gram) i₀ l)) ᵥ* (J.d.i₀.map f * FW₀.β)) t = 0 := by
      rw [← Matrix.vecMul_vecMul, h0, Matrix.zero_vecMul, Pi.zero_apply]
    rw [← h1]
    change ∑ l, f ((J.d.e'ᴴ * J.W.gram) i₀ l) * FW.β l (Sum.inl t) =
      ∑ l, f ((J.d.e'ᴴ * J.W.gram) i₀ l) * (J.d.i₀.map f * FW₀.β) l t
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hFW.2.1 l t]
    rfl
  · change ∑ l, f ((J.d.e'ᴴ * J.W.gram) i₀ l) * FW.β l (Sum.inr t) = _
    have hmul : ∀ (c : k) (M : Matrix (Fin J.W.rank) (Fin ρ) D.host.E) (j : Fin ρ),
        (∀ r, FW.β r (Sum.inr t) = c * f (M r j)) →
        ∑ l, f ((J.d.e'ᴴ * J.W.gram) i₀ l) * FW.β l (Sum.inr t) = c * f ((J.d.e'ᴴ * J.W.gram * M) i₀ j) := fun c M j h => by
      rw [← hcol, Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [h, mul_left_comm]
    by_cases ht : t.val < ρ
    · rw [hmul _ _ _ (hFW.2.2.1 ⟨t.val, ht⟩ t rfl), J.d.e'e]
      by_cases h2 : t.val = ρ - 1
      · have h3 : t = ⟨ρ - 1, by omega⟩ := Fin.ext h2
        have h4 : (⟨t.val, ht⟩ : Fin ρ) = i₀ := Fin.ext h2
        have h5 : ρ - (i₀ : ℕ) = 1 := by change ρ - (ρ - 1) = 1; omega
        rw [h4, Matrix.one_apply_eq, map_one, mul_one, h5, pow_one, h3, Pi.single_eq_same]
      · rw [Matrix.one_apply_ne fun h => h2 (congrArg Fin.val h).symm, map_zero, mul_zero,
          Pi.single_eq_of_ne fun h => h2 (congrArg Fin.val (Sum.inr_injective h))]
    · have h6 := t.2
      rw [hmul _ _ _ (hFW.2.2.2 ⟨2 * ρ - 1 - t.val, by omega⟩ t (by change t.val + (2 * ρ - 1 - t.val) + 1 = _; omega)),
        J.d.e'e', Matrix.zero_apply, map_zero, mul_zero, Pi.single_eq_of_ne fun h => ht (by
          have h7 : t.val = ρ - 1 := congrArg Fin.val (Sum.inr_injective h)
          omega)]

end GlobalTheory.LastPrimSplit

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormalFramePlaceYZeroPrimitiveInHomLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitLastPt

open GlobalTheory.FinPl

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem sum_frame_star (q : SplitPt D k) (S : HSp D) {Y : Type} [Fintype Y] [DecidableEq Y] (F : Frame k S.rank Y)
    (u : Fin S.rank → D.host.E) (m : Y) :
    ∑ r, F.β r m * (ofSplit q).pr (star ((S.gram *ᵥ u) r)) =
      ((fun l => q.pr (incA D ((star u ᵥ* S.gram) l))) ᵥ* F.β) m := by
  simp only [Matrix.vecMul, dotProduct]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [mul_comm]
  congr 1
  show q.pr (incA D _) = q.pr (incA D _)
  congr 2
  simp only [Matrix.mulVec, dotProduct, star_sum, star_mul, Pi.star_apply, GlobalTheory.LatVac.gram_star]

theorem pr_cA_e (q : SplitPt D k) : q.pr (cA D q.e) = 0 := by
  have h := congrArg q.pr (FrameLat.cAe_mul_e q)
  rwa [map_mul, GlobalTheory.LastPrimSplit.pr_e, mul_one, map_zero] at h

theorem cA_mem_idAt (q : SplitPt D k) {a : AE D} (ha : a ∈ idAt D (· = q.v)) : cA D a ∈ idAt D (· = q.v) := by
  rw [FrameLat.idem_iff] at ha ⊢
  conv_rhs => rw [← ha]
  rw [RingHom.map_mul, RingHom.map_add (f := _), GlobalTheory.LocSympl.conj_conj, add_comm]

theorem cA_mem_intAt (q : SplitPt D k) {a : AE D} (ha : a ∈ intAt D (· = q.v)) : cA D a ∈ intAt D (· = q.v) := by
  have h1 : a ∈ idAt D (· = q.v) := ha.1
  rw [GlobalTheory.SplitLine.mem_intAt_iff_pr q h1] at ha
  rw [GlobalTheory.SplitLine.mem_intAt_iff_pr q (cA_mem_idAt q h1), GlobalTheory.LocSympl.conj_conj]
  exact ⟨ha.2, ha.1⟩

theorem mul_mem_intAt {a b : AE D} {v : Pl D} (ha : a ∈ intAt D (· = v)) (hb : b ∈ intAt D (· = v)) :
    a * b ∈ intAt D (· = v) :=
  ⟨Ideal.mul_mem_right _ _ ha.1, by rw [map_mul]; exact FrameLat.mul_mem_intAE ha.2 hb.2⟩

theorem line_iff (q : SplitPt D k) (S : HSp D) (L : Lat S) {Y : Type} [Fintype Y] [DecidableEq Y] (F : Frame k S.rank Y)
    (u : Fin S.rank → D.host.E) (c : k) (m₀ m₁ : Y) (c₁ : k) (hL : IsSelfDualC S L) (hI : IntIn q S F L)
    (hc : valuation k c = 1) (hcol : ∀ r, c * (ofSplit q).pr (u r) = F.β r m₀)
    (hrow : (fun l => q.pr (incA D ((star u ᵥ* S.gram) l))) ᵥ* F.β = Pi.single m₁ c₁) (hc₁ : valuation k c₁ = 1) :
    ∀ a ∈ idAt D (· = q.v), (fun r => a * incA D (u r)) ∈ latV S L (· = q.v) ↔ a ∈ intAt D (· = q.v) := by
  refine GlobalTheory.SplitLine.line_mem_latV_iff D k q S L Y F u c m₀ hL hI hc hcol (fun m => ?_) ⟨m₁, ?_⟩
  · rw [sum_frame_star, hrow, Pi.single_apply]
    split_ifs
    · exact (Valuation.mem_integer_iff _ _).2 (le_of_eq hc₁)
    · exact zero_mem _
  · rw [sum_frame_star, hrow, Pi.single_eq_same, hc₁]

theorem pr_hzz (q : SplitPt D k) {ρ : ℕ} (B : BesLev D ρ) {n : Type} [Fintype n] [DecidableEq n] (sc : k) (hsc : sc ≠ 0)
    (FA : Frame k B.A.rank n) (F₀ : Frame k B.V₀.rank (n ⊕ Unit)) (hF₀ : (ofSplit q).IsCoreFrame B sc FA F₀) :
    q.pr (incA D (∑ b, FrameLat.row B.V₀ (vecB B.o B.ζ) b * vecB B.o B.ζ b)) = (ofSplit q).hz B := by
  have h := congrFun (GlobalTheory.LastPrimSplit.row_core q B sc FA F₀ hF₀) (Sum.inr ())
  rw [Pi.single_eq_same] at h
  refine mul_left_cancel₀ hsc ?_
  rw [← h, Matrix.vecMul, dotProduct]
  simp only [hF₀.2]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_mul, map_mul]
  show sc * (q.pr (incA D (FrameLat.row B.V₀ (vecB B.o B.ζ) b)) * q.pr (incA D (vecB B.o B.ζ b))) =
    q.pr (incA D (FrameLat.row B.V₀ (vecB B.o B.ζ) b)) * (sc * q.pr (incA D (vecB B.o B.ζ b)))
  ring

end GlobalTheory.SplitLastPt

namespace GlobalTheory.SplitLastPt

open GlobalTheory.FinPl

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem pairing_mem_intAt (q : SplitPt D k) {ρ : ℕ} (B : BesLev D ρ) {n : Type} [Fintype n] [DecidableEq n] (sc : k)
    (hsc : valuation k sc = 1) (hhz : valuation k ((ofSplit q).hz B) = 1) (FA : Frame k B.A.rank n)
    (F₀ : Frame k B.V₀.rank (n ⊕ Unit)) (hF₀ : (ofSplit q).IsCoreFrame B sc FA F₀) (M : Lat B.V₀)
    (hM : IsSelfDualC B.V₀ M) (hI : IntIn q B.V₀ F₀ M) (yv : Fin B.V₀.rank → AE D)
    (hyv : yv ∈ latV B.V₀ M (· = q.v)) : FrameLat.pairing B.V₀ (vecB B.o B.ζ) yv ∈ intAt D (· = q.v) := by
  have hsc0 : sc ≠ 0 := fun h0 => by simp [h0] at hsc
  have hid : FrameLat.pairing B.V₀ (vecB B.o B.ζ) yv ∈ idAt D (· = q.v) :=
    sum_mem fun b _ => Ideal.mul_mem_left _ _ (FrameLat.latV_supp hyv b)
  rw [GlobalTheory.SplitLine.mem_intAt_iff_pr q hid]
  constructor
  · have hu : (fun b => q.sec (q.pr (yv b))) ∈ latV B.V₀ M (· = q.v) := by
      have h := GlobalTheory.FinPl.LatIndHalf.mul_mem_latV (GlobalTheory.UpMem.finPart_e_int q) hyv
      convert h using 2 with b
      exact q.sec_pr _
    have hw := (hI (F₀.γ *ᵥ fun b => q.pr (yv b))).2 (by
      rwa [Matrix.mulVec_mulVec, F₀.βγ, Matrix.one_mulVec])
    have e : q.pr (FrameLat.pairing B.V₀ (vecB B.o B.ζ) yv) =
        ((fun l => q.pr (incA D ((star (vecB B.o B.ζ) ᵥ* B.V₀.gram) l))) ᵥ* F₀.β) ⬝ᵥ
          (F₀.γ *ᵥ fun b => q.pr (yv b)) := by
      rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, F₀.βγ, Matrix.one_mulVec]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [FrameLat.pairing, map_sum, map_mul, dotProduct]
      rfl
    rw [e, GlobalTheory.LastPrimSplit.row_core q B sc FA F₀ hF₀, single_dotProduct]
    refine mul_mem ?_ (hw _)
    exact (Valuation.mem_integer_iff _ _).2 (by rw [map_mul, hsc, hhz, one_mul])
  · have hx : (fun b => cA D (q.sec (q.pr (cA D (yv b))))) ∈ latV B.V₀ M (· = q.v) := by
      have h := GlobalTheory.FinPl.LatIndHalf.mul_mem_latV
        ((GlobalTheory.FinPl.FrameLat.cA_int_iff q.e).2 (GlobalTheory.UpMem.finPart_e_int q)) hyv
      convert h using 2 with b
      rw [q.sec_pr, RingHom.map_mul, GlobalTheory.LocSympl.conj_conj]
    have hz : (fun i => q.sec (q.pr (incA D (vecB B.o B.ζ i)))) ∈ latV B.V₀ M (· = q.v) := by
      have h := (hI (Pi.single (Sum.inr ()) sc⁻¹)).1 (fun i => by
        by_cases hi : i = Sum.inr ()
        · subst hi
          rw [Pi.single_eq_same]
          exact (Valuation.mem_integer_iff _ _).2 (by rw [map_inv₀, hsc, inv_one])
        · rw [Pi.single_eq_of_ne hi]; exact zero_mem _)
      convert h using 2 with i
      congr 1
      rw [Matrix.mulVec_single]
      change _ = F₀.β i (Sum.inr ()) * sc⁻¹
      rw [hF₀.2]
      show q.pr (incA D _) = sc * q.pr (incA D _) * sc⁻¹
      field_simp
    have h := (FrameLat.csec_mem_iff hM _).1 hx _ hz
    convert h using 1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [FrameLat.pairing, FrameLat.row, map_sum, map_mul, FrameLat.cA_incA, star_sum, star_mul,
      Pi.star_apply, star_star]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]

end GlobalTheory.SplitLastPt

namespace GlobalTheory.SplitLastPt

open GlobalTheory.FinPl


set_option maxHeartbeats 1000000 in
theorem normalFr_incAdj_yZero_mem_latO_iff : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ {a : XGeo D} (y : YRat a) {βT : GL (Fin D.sp.X'.rank) (Lev.EAf D)} {PP : Pl D.host.E} (l : LocX a βT PP) (FY : FYFam l) (sc : ℕ → l.k), IsNormalFr l y FY sc → (∀ j, j ≤ D.R.m → (a.x j).Is) → ∀ (N : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)) (M : ∀ j ρ (h : j + 2 * ρ + 2 = D.R.m), GlobalTheory.FinPl.Lat (y.bes j ρ h).V₀), (∀ j, j < D.R.m → IsSelfDualC (Yc D j) (N j)) → (∀ j c (hc : j + c = l.s + 1), IntIn l.q (Yc D j) (FY j c hc) (N j)) → (∀ j ρ h, IsSelfDualC (y.bes j ρ h).V₀ (M j ρ h)) → (∀ j ρ h (hj : j ≤ l.s + 1) (F₀ : Frame l.k ((y.bes j ρ h).lev (a.x j).vol).V₀.rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Unit)), (ofSplit l.q).IsCoreFrame ((y.bes j ρ h).lev (a.x j).vol) (sc j) (l.FX j hj) F₀ → IntIn l.q _ F₀ (M j ρ h)) → ∀ j ρ (h : j + 2 * ρ + 2 = D.R.m), 0 < ρ → ∀ t ∈ GlobalTheory.FinPl.idAt D (· = ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))), ((y.jac j ρ h).lev (a.x (j + 1)).vol).d.incAdj ((y.bes j ρ h).lev (a.x j).vol).V₀ (t • yZero ((y.bes j ρ h).lev (a.x j).vol).V₀ ρ (vecB ((y.bes j ρ h).lev (a.x j).vol).o ((y.bes j ρ h).lev (a.x j).vol).ζ)) ∈ latO ((y.bes j ρ h).lev (a.x j).vol).V₀ ((y.jac j ρ h).lev (a.x (j + 1)).vol).W (M j ρ h : Set _) (N (j + 1) : Set _) (· = ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) ↔ t ∈ GlobalTheory.FinPl.intAt D (· = ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) := by
  intro D ψ hψ a y βT PP l FY sc hNF hIs N M hN hNI hM hMI j ρ h hρ t ht
  rw [← l.under] at ht ⊢
  obtain ⟨hsc, hstep, hhz, -, hjac, -⟩ := hNF
  have hsc0 : ∀ j, sc j ≠ 0 := fun j h0 => by simpa [h0] using hsc j
  have hxi1 : valuation l.k (ofSplit l.q).xi = 1 := by
    have h2 := hsc (0 + 1 + 1)
    rwa [hstep, map_mul, hsc 0, one_mul] at h2
  have hxi0 : (ofSplit l.q).xi ≠ 0 := fun h0 => by simp [h0] at hxi1
  have hjs : j ≤ l.s + 1 := by have := l.hs; omega
  have hd : j + 1 + 2 * ρ = l.s + 1 := by have := l.hs; omega
  have hjm : j + 1 < D.R.m := by omega
  have hhz1 := hhz j ρ h
  obtain ⟨F₀, hF₀⟩ := (ofSplit l.q).exists_isCoreFrame (hsc0 j) ((y.bes j ρ h).lev (a.x j).vol) (l.FX j hjs)
  have hMI0 := hMI j ρ h hjs F₀ hF₀
  have hNI0 := hNI (j + 1) (2 * ρ) hd
  have hJF := hjac j ρ h (2 * ρ) hd
  have hLineN : ∀ s ∈ idAt D (· = l.q.v),
      (fun r => s * incA D (((y.jac j ρ h).lev (a.x (j + 1)).vol).d.e' r ⟨ρ - 1, by omega⟩)) ∈
        latV ((y.jac j ρ h).lev (a.x (j + 1)).vol).W (N (j + 1)) (· = l.q.v) ↔ s ∈ intAt D (· = l.q.v) :=
    line_iff l.q _ (N (j + 1)) (FY (j + 1) (2 * ρ) hd) _
      (sc j * ((ofSplit l.q).hz ((y.bes j ρ h).lev (a.x j).vol) / (ofSplit l.q).xi))
      (Sum.inr ⟨ρ, by omega⟩) (Sum.inr ⟨ρ - 1, by omega⟩) (sc j * (ofSplit l.q).xi) (hN (j + 1) hjm) hNI0
      (by rw [map_mul, map_div₀, hsc, hhz1, hxi1]; simp)
      (fun r => by
        rw [hJF.2.2.2 ⟨ρ - 1, by omega⟩ ⟨ρ, by omega⟩ (by show ρ + (ρ - 1) + 1 = 2 * ρ; omega) r]
        simp)
      (by rw [← GlobalTheory.LastPrimSplit.row_jac l.q hρ _ (sc j) _ _ _ hJF]; rfl)
      (by rw [map_mul, hsc, hxi1, one_mul])
  have hLineM : ∀ s ∈ idAt D (· = l.q.v),
      (fun r => s * incA D (vecB ((y.bes j ρ h).lev (a.x j).vol).o ((y.bes j ρ h).lev (a.x j).vol).ζ r)) ∈
        latV ((y.bes j ρ h).lev (a.x j).vol).V₀ (M j ρ h) (· = l.q.v) ↔ s ∈ intAt D (· = l.q.v) :=
    line_iff l.q _ (M j ρ h) F₀ _ (sc j) (Sum.inr ()) (Sum.inr ())
      (sc j * (ofSplit l.q).hz ((y.bes j ρ h).lev (a.x j).vol)) (hM j ρ h) hMI0 (hsc j) (fun r => (hF₀.2 r).symm)
      (GlobalTheory.LastPrimSplit.row_core l.q _ (sc j) _ F₀ hF₀) (by rw [map_mul, hsc, hhz1, one_mul])
  have hca : cA D t ∈ idAt D (· = l.q.v) := cA_mem_idAt l.q ht
  have hT : ∀ yv : Fin ((y.bes j ρ h).lev (a.x j).vol).V₀.rank → AE D, Matrix.mulVec (((y.jac j ρ h).lev (a.x (j + 1)).vol).d.incAdj ((y.bes j ρ h).lev (a.x j).vol).V₀ (t • yZero ((y.bes j ρ h).lev (a.x j).vol).V₀ ρ (vecB ((y.bes j ρ h).lev (a.x j).vol).o ((y.bes j ρ h).lev (a.x j).vol).ζ))) yv =
      fun r => (cA D t * incA D D.host.xi0⁻¹ * FrameLat.pairing ((y.bes j ρ h).lev (a.x j).vol).V₀ (vecB ((y.bes j ρ h).lev (a.x j).vol).o ((y.bes j ρ h).lev (a.x j).vol).ζ) yv) * incA D (((y.jac j ρ h).lev (a.x (j + 1)).vol).d.e' r ⟨ρ - 1, by omega⟩) := by
    intro yv
    funext r
    have e1 : ∀ b, (star (vecB ((y.bes j ρ h).lev (a.x j).vol).o ((y.bes j ρ h).lev (a.x j).vol).ζ) ᵥ* ((y.bes j ρ h).lev (a.x j).vol).V₀.gram) b = FrameLat.row ((y.bes j ρ h).lev (a.x j).vol).V₀ (vecB ((y.bes j ρ h).lev (a.x j).vol).o ((y.bes j ρ h).lev (a.x j).vol).ζ) b := fun b => rfl
    simp only [Matrix.mulVec, dotProduct, GlobalTheory.LastPrimSplit.incAdj_yZero_apply hρ, FrameLat.pairing, Finset.mul_sum,
      Finset.sum_mul, e1]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [map_mul]
    ring
  have hpid : ∀ yv ∈ latV ((y.bes j ρ h).lev (a.x j).vol).V₀ (M j ρ h) (· = l.q.v),
      cA D t * incA D D.host.xi0⁻¹ * FrameLat.pairing ((y.bes j ρ h).lev (a.x j).vol).V₀ (vecB ((y.bes j ρ h).lev (a.x j).vol).o ((y.bes j ρ h).lev (a.x j).vol).ζ) yv ∈ idAt D (· = l.q.v) :=
    fun yv hyv => Ideal.mul_mem_left _ _ (sum_mem fun b _ => Ideal.mul_mem_left _ _ (FrameLat.latV_supp hyv b))
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D _ _ (M j ρ h) (N (j + 1)) (hM j ρ h) (hN (j + 1) hjm)]
  have hpinv : ∀ x : D.host.E, l.q.pr (incA D x⁻¹) = (l.q.pr (incA D x))⁻¹ := fun x =>
    map_inv₀ (l.q.pr.comp (incA D)) x
  have hxiv : valuation l.k (l.q.pr (incA D D.host.xi0⁻¹)) = 1 := by
    rw [hpinv, map_inv₀]
    change (valuation l.k (ofSplit l.q).xi)⁻¹ = 1
    rw [hxi1, inv_one]
  have hxiv' : valuation l.k (l.q.pr (incA D (star D.host.xi0⁻¹))) = 1 := by
    rw [star_inv₀, GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg, hpinv, map_inv₀, map_neg, map_neg, Valuation.map_neg]
    change (valuation l.k (ofSplit l.q).xi)⁻¹ = 1
    rw [hxi1, inv_one]
  constructor
  · rintro ⟨-, hmap⟩
    have hε : l.q.e + cA D l.q.e ∈ intAt D (· = l.q.v) := by
      rw [GlobalTheory.SplitLine.mem_intAt_iff_pr l.q (FrameLat.sum_mem_idAt l.q)]
      simp only [map_add (f := _), GlobalTheory.LastPrimSplit.pr_e, pr_cA_e, GlobalTheory.LocSympl.conj_conj, add_zero, zero_add]
      exact ⟨one_mem _, one_mem _⟩
    have hy₀ := (hLineM _ (FrameLat.sum_mem_idAt l.q)).2 hε
    have h1 := hmap _ hy₀
    dsimp only at h1
    rw [l.unit.2, hT] at h1
    have h2 := (hLineN _ (hpid _ hy₀)).1 h1
    have e : FrameLat.pairing ((y.bes j ρ h).lev (a.x j).vol).V₀ (vecB ((y.bes j ρ h).lev (a.x j).vol).o ((y.bes j ρ h).lev (a.x j).vol).ζ) (fun r => (l.q.e + cA D l.q.e) * incA D ((vecB ((y.bes j ρ h).lev (a.x j).vol).o ((y.bes j ρ h).lev (a.x j).vol).ζ) r)) =
        (l.q.e + cA D l.q.e) * incA D (∑ b, FrameLat.row ((y.bes j ρ h).lev (a.x j).vol).V₀ (vecB ((y.bes j ρ h).lev (a.x j).vol).o ((y.bes j ρ h).lev (a.x j).vol).ζ) b * (vecB ((y.bes j ρ h).lev (a.x j).vol).o ((y.bes j ρ h).lev (a.x j).vol).ζ) b) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [FrameLat.pairing, map_sum, map_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun b _ => by ring
    have hid2 := hpid _ hy₀
    rw [e] at h2 hid2
    rw [GlobalTheory.SplitLine.mem_intAt_iff_pr l.q hid2] at h2
    obtain ⟨h3, h4⟩ := h2
    have hpz := pr_hzz l.q ((y.bes j ρ h).lev (a.x j).vol) (sc j) (hsc0 j) _ F₀ hF₀
    have hzz : star (∑ b, FrameLat.row ((y.bes j ρ h).lev (a.x j).vol).V₀ (vecB ((y.bes j ρ h).lev (a.x j).vol).o ((y.bes j ρ h).lev (a.x j).vol).ζ) b * (vecB ((y.bes j ρ h).lev (a.x j).vol).o ((y.bes j ρ h).lev (a.x j).vol).ζ) b) = ∑ b, FrameLat.row ((y.bes j ρ h).lev (a.x j).vol).V₀ (vecB ((y.bes j ρ h).lev (a.x j).vol).o ((y.bes j ρ h).lev (a.x j).vol).ζ) b * (vecB ((y.bes j ρ h).lev (a.x j).vol).o ((y.bes j ρ h).lev (a.x j).vol).ζ) b := by
      simp only [FrameLat.row, star_sum, star_mul, star_star, GlobalTheory.LatVac.gram_star, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by ring
    simp only [map_mul, map_add (f := _), GlobalTheory.LastPrimSplit.pr_e, pr_cA_e, GlobalTheory.LocSympl.conj_conj, FrameLat.cA_incA, hzz, hpz,
      add_zero, zero_add, mul_one, one_mul] at h3 h4
    rw [GlobalTheory.SplitLine.mem_intAt_iff_pr l.q ht]
    rw [Valuation.mem_integer_iff] at h3 h4
    rw [map_mul, map_mul, hxiv, hhz1, mul_one, mul_one] at h3
    rw [map_mul, map_mul, hxiv', hhz1, mul_one, mul_one] at h4
    exact ⟨(Valuation.mem_integer_iff _ _).2 h4, (Valuation.mem_integer_iff _ _).2 h3⟩
  · intro hti
    refine ⟨fun i l' => ?_, fun yv hyv => ?_⟩
    · rw [GlobalTheory.LastPrimSplit.incAdj_yZero_apply hρ]
      exact Ideal.mul_mem_right _ _ hca
    · dsimp only
      rw [l.unit.2, hT]
      refine (hLineN _ (hpid _ hyv)).2 (mul_mem_intAt ?_ ?_)
      · rw [mul_comm]
        exact (l.unit.1 _ (cA_mem_intAt l.q hti)).2
      · exact pairing_mem_intAt l.q ((y.bes j ρ h).lev (a.x j).vol) (sc j) (hsc j) hhz1 _ F₀ hF₀ (M j ρ h) (hM j ρ h) hMI0 yv hyv

end GlobalTheory.SplitLastPt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormalFramePlaceYZeroPrimitiveInHomLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalFrame_place_yZero_primitive_in_hom_lattice : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ {a : XGeo D} (y : YRat a) {βT : GL (Fin D.sp.X'.rank) (Lev.EAf D)} {PP : Pl D.host.E} (l : LocX a βT PP) (FY : FYFam l) (sc : ℕ → l.k), IsNormalFr l y FY sc → (∀ j, j ≤ D.R.m → (a.x j).Is) → ∀ (N : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)) (M : ∀ j ρ (h : j + 2 * ρ + 2 = D.R.m), GlobalTheory.FinPl.Lat (y.bes j ρ h).V₀), (∀ j, j < D.R.m → IsSelfDualC (Yc D j) (N j)) → (∀ j c (hc : j + c = l.s + 1), IntIn l.q (Yc D j) (FY j c hc) (N j)) → (∀ j ρ h, IsSelfDualC (y.bes j ρ h).V₀ (M j ρ h)) → (∀ j ρ h (hj : j ≤ l.s + 1) (F₀ : Frame l.k ((y.bes j ρ h).lev (a.x j).vol).V₀.rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Unit)), (ofSplit l.q).IsCoreFrame ((y.bes j ρ h).lev (a.x j).vol) (sc j) (l.FX j hj) F₀ → IntIn l.q _ F₀ (M j ρ h)) → ∀ j ρ (h : j + 2 * ρ + 2 = D.R.m), 0 < ρ → ∀ t ∈ GlobalTheory.FinPl.idAt D (· = ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))), ((y.jac j ρ h).lev (a.x (j + 1)).vol).d.incAdj ((y.bes j ρ h).lev (a.x j).vol).V₀ (t • yZero ((y.bes j ρ h).lev (a.x j).vol).V₀ ρ (vecB ((y.bes j ρ h).lev (a.x j).vol).o ((y.bes j ρ h).lev (a.x j).vol).ζ)) ∈ latO ((y.bes j ρ h).lev (a.x j).vol).V₀ ((y.jac j ρ h).lev (a.x (j + 1)).vol).W (M j ρ h : Set _) (N (j + 1) : Set _) (· = ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) ↔ t ∈ GlobalTheory.FinPl.intAt D (· = ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP))) := by
  first | exact @GlobalTheory.SplitLastPt.normalFr_incAdj_yZero_mem_latO_iff | exact GlobalTheory.SplitLastPt.normalFr_incAdj_yZero_mem_latO_iff | (intros; apply GlobalTheory.SplitLastPt.normalFr_incAdj_yZero_mem_latO_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLatticeSplitsAlongWittNormalFrames
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLatticeSplitsAlongWittNormalFrames
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.MonoBes

open GlobalTheory.FinPl GlobalTheory.SeeSaw.SplitLat

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem mul_mem_iff {c : k} (hc : valuation k c = 1) (y : k) : c * y ∈ 𝒪[k] ↔ y ∈ 𝒪[k] := by
  rw [Valuation.mem_integer_iff, Valuation.mem_integer_iff, map_mul, hc, one_mul]

theorem ne_zero_of_val {x : k} (h : valuation k x = 1) : x ≠ 0 := by
  rintro rfl
  rw [map_zero] at h
  exact zero_ne_one h

theorem sec_mem_intAt_iff (q : SplitPt D k) (c : k) : q.sec c ∈ intAt D (· = q.v) ↔ c ∈ 𝒪[k] :=
  ⟨fun h => (q.int_iff c).2 h.2, FrameLat.sec_mem_intAt q c⟩

theorem sec_pr_eq (q : SplitPt D k) (x : D.host.E) : q.sec ((ofSplit q).pr x) = incA D x * q.e := by
  rw [show (ofSplit q).pr x = q.pr (incA D x) from rfl, q.sec_pr, mul_comm]

theorem val_xi (q : SplitPt D k) (hU : q.UnitAA) : valuation k (ofSplit q).xi = 1 := by
  have h1 := (hU.1 q.e (FrameLat.e_mem_intAt q)).1
  have h2 := (hU.1 q.e (FrameLat.e_mem_intAt q)).2
  rw [← sec_pr_eq, sec_mem_intAt_iff] at h1 h2
  have e : (ofSplit q).pr D.host.xi0⁻¹ = ((ofSplit q).xi)⁻¹ := by
    rw [← GlobalTheory.SliceModel.prH_apply, map_inv₀]; rfl
  rw [e, Valuation.mem_integer_iff, map_inv₀] at h2
  rw [Valuation.mem_integer_iff] at h1
  have hne : valuation k (ofSplit q).xi ≠ 0 := by
    rw [Ne, Valuation.zero_iff]; exact GlobalTheory.LocMod.Witness.xi_ne (ofSplit q)
  exact le_antisymm h1 (by
    by_contra hlt
    push_neg at hlt
    have := (one_lt_inv₀ (zero_lt_iff.2 hne)).2 hlt
    exact absurd h2 (not_le.2 this))

end GlobalTheory.MonoBes

namespace GlobalTheory.MonoBes

open GlobalTheory.FinPl GlobalTheory.SeeSaw.SplitLat

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem eq_sec_add_csec (q : SplitPt D k) {n : ℕ} {y : Fin n → AE D} (hy : ∀ i, y i ∈ idAt D (· = q.v)) :
    y = (fun i => q.sec (q.pr (y i))) + (fun i => cA D (q.sec (q.pr (cA D (y i))))) := by
  funext i
  have h := (FrameLat.idem_iff q (y i)).1 (hy i)
  simp only [Pi.add_apply, q.sec_pr, map_mul, Formalism.L2.Theta.cA_cA]
  rw [← add_mul, h]

theorem mem_of_sec_iff (q : SplitPt D k) {S : HSp D} {L L' : Lat S} (hL : IsSelfDualC S L) (hL' : IsSelfDualC S L')
    (h : ∀ u : Fin S.rank → k, (fun i => q.sec (u i)) ∈ latV S L (· = q.v) ↔ (fun i => q.sec (u i)) ∈ latV S L' (· = q.v))
    {y : Fin S.rank → AE D} (hy : y ∈ latV S L (· = q.v)) : y ∈ latV S L' (· = q.v) := by
  have hs : ∀ i, y i ∈ idAt D (· = q.v) := fun i => FrameLat.latV_supp hy i
  rw [eq_sec_add_csec q hs] at hy ⊢
  have hy' := (FrameLat.decomp hL (fun i => q.pr (y i)) (fun i => q.pr (cA D (y i)))).1 hy
  refine (FrameLat.decomp hL' (fun i => q.pr (y i)) (fun i => q.pr (cA D (y i)))).2 ⟨(h _).1 hy'.1, ?_⟩
  have hd := (FrameLat.csec_mem_iff hL (fun i => q.pr (cA D (y i)))).1 hy'.2
  exact (FrameLat.csec_mem_iff hL' (fun i => q.pr (cA D (y i)))).2 fun x hx => hd x ((h x).2 hx)

theorem latV_eq_of_frame (q : SplitPt D k) {S : HSp D} {L L' : Lat S} (hL : IsSelfDualC S L) (hL' : IsSelfDualC S L')
    {Y : Type} [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k S.rank Y) (h1 : IntIn q S F L) (h2 : IntIn q S F L') :
    latV S L (· = q.v) = latV S L' (· = q.v) := by
  have h : ∀ u : Fin S.rank → k,
      (fun i => q.sec (u i)) ∈ latV S L (· = q.v) ↔ (fun i => q.sec (u i)) ∈ latV S L' (· = q.v) := by
    intro u
    have e : F.β *ᵥ (F.γ *ᵥ u) = u := by rw [Matrix.mulVec_mulVec, F.βγ, Matrix.one_mulVec]
    have := (h1 (F.γ *ᵥ u)).symm.trans (h2 (F.γ *ᵥ u))
    rwa [e] at this
  exact AddSubgroup.ext fun _ => ⟨mem_of_sec_iff q hL hL' h, mem_of_sec_iff q hL' hL fun u => (h u).symm⟩

def besselNormalFrameAuxiliaryColumnIndex (ρ : ℕ) : Fin ρ ⊕ (Unit ⊕ Fin ρ) → Fin (2 * ρ + 1) :=
  Sum.elim (fun i => ⟨i.val, by omega⟩) (Sum.elim (fun _ => ⟨ρ, by omega⟩) fun i => ⟨2 * ρ - i.val, by omega⟩)

theorem besselNormalFrameAuxiliaryColumnIndex_bijective (ρ : ℕ) : Function.Bijective (besselNormalFrameAuxiliaryColumnIndex ρ) := by
  refine (Fintype.bijective_iff_injective_and_card _).2 ⟨?_, by simp; ring⟩
  rintro (a | a | a) (b | b | b) h <;> simp [besselNormalFrameAuxiliaryColumnIndex, Fin.ext_iff] at h ⊢ <;> first | exact h | omega

theorem sum_divisible_eq_sum_mul {M : Type} [AddCommMonoid M] (ρ : ℕ) (f : Fin (2 * ρ + 1) → M) :
    ∑ j, f j = ∑ i : Fin ρ, f ⟨i.val, by omega⟩ + f ⟨ρ, by omega⟩ + ∑ i : Fin ρ, f ⟨2 * ρ - i.val, by omega⟩ := by
  rw [← (Equiv.ofBijective _ (besselNormalFrameAuxiliaryColumnIndex_bijective ρ)).sum_comp, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp [besselNormalFrameAuxiliaryColumnIndex, add_assoc]

theorem forall_fin_odd_iff_lower_middle_upperReversed (ρ : ℕ) (p : Fin (2 * ρ + 1) → Prop) :
    (∀ j, p j) ↔ (∀ i : Fin ρ, p ⟨i.val, by omega⟩) ∧ p ⟨ρ, by omega⟩ ∧ ∀ i : Fin ρ, p ⟨2 * ρ - i.val, by omega⟩ := by
  refine ⟨fun h => ⟨fun i => h _, h _, fun i => h _⟩, fun ⟨h1, h2, h3⟩ j => ?_⟩
  obtain ⟨x, rfl⟩ := (besselNormalFrameAuxiliaryColumnIndex_bijective ρ).2 j
  rcases x with (a | a | a)
  · exact h1 a
  · exact h2
  · exact h3 a

end GlobalTheory.MonoBes

namespace GlobalTheory.MonoBes

open GlobalTheory.FinPl GlobalTheory.SeeSaw.SplitLat

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem proj_sec (q : SplitPt D k) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (w : Fin S₀.rank → k) (a b : Fin ρ → k) :
    (d.pX *ᵥ fun i => q.sec ((d.i₀.map (GlobalTheory.SliceModel.prH (ofSplit q)) *ᵥ w +
        d.e.map (GlobalTheory.SliceModel.prH (ofSplit q)) *ᵥ a + d.e'.map (GlobalTheory.SliceModel.prH (ofSplit q)) *ᵥ b) i)) =
        (fun i => q.sec (a i)) ∧
    (d.pY *ᵥ fun i => q.sec ((d.i₀.map (GlobalTheory.SliceModel.prH (ofSplit q)) *ᵥ w +
        d.e.map (GlobalTheory.SliceModel.prH (ofSplit q)) *ᵥ a + d.e'.map (GlobalTheory.SliceModel.prH (ofSplit q)) *ᵥ b) i)) =
        (fun i => q.sec (b i)) ∧
    (d.p0 *ᵥ fun i => q.sec ((d.i₀.map (GlobalTheory.SliceModel.prH (ofSplit q)) *ᵥ w +
        d.e.map (GlobalTheory.SliceModel.prH (ofSplit q)) *ᵥ a + d.e'.map (GlobalTheory.SliceModel.prH (ofSplit q)) *ᵥ b) i)) =
        (fun i => q.sec (w i)) := by
  set P := GlobalTheory.SliceModel.prH (ofSplit q) with hP
  have m : ∀ {a b c : ℕ} (X : Matrix (Fin a) (Fin b) D.host.E) (Y : Matrix (Fin b) (Fin c) D.host.E),
      X.map P * Y.map P = (X * Y).map P := fun X Y => Matrix.map_mul.symm
  have z : ∀ {a b : ℕ}, (0 : Matrix (Fin a) (Fin b) D.host.E).map P = 0 := Matrix.map_zero _ (map_zero P)
  have o : ∀ {a : ℕ}, (1 : Matrix (Fin a) (Fin a) D.host.E).map P = 1 := Matrix.map_one _ (map_zero P) (map_one P)
  refine ⟨?_, ?_, ?_⟩
  · change rat d.qX *ᵥ _ = _
    rw [GlobalTheory.CoreFrameLat.rat_mulVec_sec, ← hP, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, m, m, m, GlobalTheory.SeeSaw.SplitLat.qX_i₀, GlobalTheory.SeeSaw.SplitLat.qX_e, GlobalTheory.SeeSaw.SplitLat.qX_e']
    simp only [z, o, Matrix.zero_mulVec, Matrix.one_mulVec, zero_add, add_zero]
  · change rat d.qY *ᵥ _ = _
    rw [GlobalTheory.CoreFrameLat.rat_mulVec_sec, ← hP, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, m, m, m, GlobalTheory.SeeSaw.SplitLat.qY_i₀, GlobalTheory.SeeSaw.SplitLat.qY_e, GlobalTheory.SeeSaw.SplitLat.qY_e']
    simp only [z, o, Matrix.zero_mulVec, Matrix.one_mulVec, zero_add, add_zero]
  · change rat d.q0 *ᵥ _ = _
    rw [GlobalTheory.CoreFrameLat.rat_mulVec_sec, ← hP, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, m, m, m, GlobalTheory.SeeSaw.SplitLat.wittDecomposition_coreProj_mul_core_eq_one, GlobalTheory.SeeSaw.SplitLat.wittDecomposition_coreProj_mul_e_eq_zero, GlobalTheory.SeeSaw.SplitLat.wittZeroProjection_mul_dualBasis_eq_zero]
    simp only [z, o, Matrix.zero_mulVec, Matrix.one_mulVec, zero_add, add_zero]

end GlobalTheory.MonoBes

namespace GlobalTheory.MonoBes

open GlobalTheory.FinPl GlobalTheory.SeeSaw.SplitLat

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem lineX_sec (q : SplitPt D k) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (M : Lat S₀) (i : Fin ρ) (c : k) :
    colMul d.jX i (q.sec c) ∈ latV S (splitL d M fun _ => 1) (· = q.v) ↔ c ∈ 𝒪[k] := by
  rw [line_splitL, GlobalTheory.SeeSaw.idV_one_eq_intAt, sec_mem_intAt_iff]

theorem lineY_sec (q : SplitPt D k) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (M : Lat S₀) (i : Fin ρ) (c : k) :
    colMul d.jY i (q.sec c) ∈ latV S (splitL d M fun _ => 1) (· = q.v) ↔ c ∈ 𝒪[k] := by
  rw [GlobalTheory.FinPl.MonoIdele.line_splitL_jY, GlobalTheory.SeeSaw.idV_one_eq_intAt, sec_mem_intAt_iff]

end GlobalTheory.MonoBes

namespace GlobalTheory.MonoBes

open GlobalTheory.FinPl GlobalTheory.SeeSaw.SplitLat

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]


set_option maxHeartbeats 1000000 in
theorem intIn_splitL (q : SplitPt D k) {ρ : ℕ} (B : BesLev D ρ) {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} (s : k)
    (FA : GlobalTheory.LocMod.Frame k B.A.rank n) (F₀ : GlobalTheory.LocMod.Frame k B.V₀.rank (n ⊕ Unit))
    (FV : GlobalTheory.LocMod.Frame k B.V.rank (n ⊕ Fin c)) (M : Lat B.V₀)
    (hs : valuation k s = 1) (hxi : valuation k (ofSplit q).xi = 1) (hz : valuation k ((ofSplit q).hz B) = 1)
    (hC : (ofSplit q).IsCoreFrame B s FA F₀) (hB : (ofSplit q).IsBesFrame B s FA FV) (hM : IntIn q B.V₀ F₀ M) :
    IntIn q B.V FV (splitL B.d M fun _ => 1) := by
  obtain ⟨rfl, h1, h2, h3, h4⟩ := hB
  intro y
  have hPa : ∀ x, GlobalTheory.SliceModel.prH (ofSplit q) x = (ofSplit q).pr x := fun x => GlobalTheory.SliceModel.prH_apply _ x
  set P := GlobalTheory.SliceModel.prH (ofSplit q) with hP
  let ca : Fin ρ → k := fun i => s * (ofSplit q).xi ^ (ρ - i.val)
  let cb : Fin ρ → k := fun i => s * (-(ofSplit q).hz B / (ofSplit q).xi) * (-1 / (ofSplit q).xi) ^ (ρ - 1 - i.val)
  let a : Fin ρ → k := fun i => ca i * y (Sum.inr ⟨i.val, by omega⟩)
  let b : Fin ρ → k := fun i => cb i * y (Sum.inr ⟨2 * ρ - i.val, by omega⟩)
  let y₀ : n ⊕ Unit → k := Sum.elim (fun x => y (Sum.inl x)) fun _ => y (Sum.inr ⟨ρ, by omega⟩)
  have hca : ∀ i, valuation k (ca i) = 1 := fun i => by simp [ca, hs, hxi]
  have hcb : ∀ i, valuation k (cb i) = 1 := fun i => by simp [cb, hs, hxi, hz, map_div₀]
  have c1 : ∀ r x, FV.β r (Sum.inl x) = (B.d.i₀.map P * F₀.β) r (Sum.inl x) := by
    intro r x
    rw [h1]
    change ((B.d.i₀ * B.o.iA).map P * FA.β) r x = _
    rw [Matrix.map_mul, Matrix.mul_assoc, Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [hC.1]
    rfl
  have c2 : ∀ r, FV.β r (Sum.inr ⟨ρ, by omega⟩) = (B.d.i₀.map P * F₀.β) r (Sum.inr ()) := by
    intro r
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h3 _ rfl, Matrix.mul_apply, ← hPa, Matrix.mulVec, dotProduct, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [hC.2, map_mul, Matrix.map_apply]
    simp only [hPa]
    ring
  have c3 : ∀ r (i : Fin ρ), FV.β r (Sum.inr ⟨i.val, by omega⟩) = ca i * (B.d.e.map P) r i := by
    intro r i; rw [h2 i _ rfl]; simp [ca, hPa]
  have c4 : ∀ r (i : Fin ρ), FV.β r (Sum.inr ⟨2 * ρ - i.val, by omega⟩) = cb i * (B.d.e'.map P) r i := by
    intro r i; rw [h4 i _ (by simp; omega)]; simp [cb, hPa]
  have hdec : FV.β *ᵥ y = B.d.i₀.map P *ᵥ (F₀.β *ᵥ y₀) + B.d.e.map P *ᵥ a + B.d.e'.map P *ᵥ b := by
    rw [Matrix.mulVec_mulVec]
    funext r
    simp only [Pi.add_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fintype.sum_unique]
    rw [sum_divisible_eq_sum_mul ρ]
    have ea : ∑ i : Fin ρ, B.d.e.map P r i * a i =
        ∑ i : Fin ρ, FV.β r (Sum.inr ⟨i.val, by omega⟩) * y (Sum.inr ⟨i.val, by omega⟩) :=
      Finset.sum_congr rfl fun i _ => by rw [c3]; simp only [a]; ring
    have eb : ∑ i : Fin ρ, B.d.e'.map P r i * b i =
        ∑ i : Fin ρ, FV.β r (Sum.inr ⟨2 * ρ - i.val, by omega⟩) * y (Sum.inr ⟨2 * ρ - i.val, by omega⟩) :=
      Finset.sum_congr rfl fun i _ => by rw [c4]; simp only [b]; ring
    rw [ea, eb]
    simp only [c1, c2, y₀, Sum.elim_inl, Sum.elim_inr]
    ring
  have hpr := proj_sec q B.d (F₀.β *ᵥ y₀) a b
  have hpX : B.d.pX *ᵥ (fun i => q.sec ((FV.β *ᵥ y) i)) = fun i => q.sec (a i) := by rw [hdec]; exact hpr.1
  have hpY : B.d.pY *ᵥ (fun i => q.sec ((FV.β *ᵥ y) i)) = fun i => q.sec (b i) := by rw [hdec]; exact hpr.2.1
  have hp0 : B.d.p0 *ᵥ (fun i => q.sec ((FV.β *ᵥ y) i)) = fun i => q.sec ((F₀.β *ᵥ y₀) i) := by rw [hdec]; exact hpr.2.2
  have lX : ∀ i, colMul B.d.jX i (q.sec (a i)) ∈ latV B.V (splitL B.d M fun _ => 1) (· = q.v) ↔
      y (Sum.inr ⟨i.val, by omega⟩) ∈ 𝒪[k] := fun i =>
    (lineX_sec q B.d M i (a i)).trans (mul_mem_iff (hca i) _)
  have lY : ∀ i, colMul B.d.jY i (q.sec (b i)) ∈ latV B.V (splitL B.d M fun _ => 1) (· = q.v) ↔
      y (Sum.inr ⟨2 * ρ - i.val, by omega⟩) ∈ 𝒪[k] := fun i =>
    (lineY_sec q B.d M i (b i)).trans (mul_mem_iff (hcb i) _)
  have hf := forall_fin_odd_iff_lower_middle_upperReversed ρ (fun j => y (Sum.inr j) ∈ 𝒪[k])
  rw [monoAt_splitL B.d M _ q.v, hpX, hpY, hp0, ← hM y₀]
  have e1 : (∀ i, colMul B.d.jX i ((fun i => q.sec (a i)) i) ∈ latV B.V (splitL B.d M fun _ => 1) (· = q.v)) ↔
      ∀ i : Fin ρ, y (Sum.inr ⟨i.val, by omega⟩) ∈ 𝒪[k] := forall_congr' lX
  have e2 : (∀ i, colMul B.d.jY i ((fun i => q.sec (b i)) i) ∈ latV B.V (splitL B.d M fun _ => 1) (· = q.v)) ↔
      ∀ i : Fin ρ, y (Sum.inr ⟨2 * ρ - i.val, by omega⟩) ∈ 𝒪[k] := forall_congr' lY
  have e3 : (∀ i, y₀ i ∈ 𝒪[k]) ↔ (∀ x, y (Sum.inl x) ∈ 𝒪[k]) ∧ y (Sum.inr ⟨ρ, by omega⟩) ∈ 𝒪[k] :=
    ⟨fun h => ⟨fun x => h (Sum.inl x), h (Sum.inr ())⟩, fun h m => by
      rcases m with x | u
      · exact h.1 x
      · exact h.2⟩
  rw [e1, e2, e3, Sum.forall, hf]
  constructor
  · rintro ⟨hl, ha, hr, hb⟩; exact ⟨ha, hb, hl, hr⟩
  · rintro ⟨ha, hb, hl, hr⟩; exact ⟨hl, ha, hr, hb⟩

end GlobalTheory.MonoBes

theorem GlobalTheory.MonoBes.besLat_monoAt : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ {a : XGeo D} (y : YRat a) {βT : GL (Fin D.sp.X'.rank) (Lev.EAf D)} {PP : Pl D.host.E} (l : LocX a βT PP) (FY : FYFam l) (sc : ℕ → l.k), IsNormalFr l y FY sc → (∀ j, j ≤ D.R.m → (a.x j).Is) → ∀ (N : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)) (M : ∀ j ρ (h : j + 2 * ρ + 2 = D.R.m), GlobalTheory.FinPl.Lat (y.bes j ρ h).V₀), (∀ j, j < D.R.m → IsSelfDualC (Yc D j) (N j)) → (∀ j c (hc : j + c = l.s + 1), IntIn l.q (Yc D j) (FY j c hc) (N j)) → (∀ j ρ h, IsSelfDualC (y.bes j ρ h).V₀ (M j ρ h)) → (∀ j ρ h (hj : j ≤ l.s + 1) (F₀ : Frame l.k ((y.bes j ρ h).lev (a.x j).vol).V₀.rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Unit)), (ofSplit l.q).IsCoreFrame ((y.bes j ρ h).lev (a.x j).vol) (sc j) (l.FX j hj) F₀ → IntIn l.q _ F₀ (M j ρ h)) → ∀ j ρ (h : j + 2 * ρ + 2 = D.R.m), GlobalTheory.FinPl.MonoAt ((y.bes j ρ h).lev (a.x j).vol).d (N j) (M j ρ h) ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) := by
  intro D ψ hψ a y βT PP l FY sc hN hx N M hsdN hIntN hsdM hIntM j ρ h
  have hs := l.hs
  have hj : j ≤ l.s + 1 := by omega
  have hc : j + (2 * ρ + 1) = l.s + 1 := by omega
  have hjm : j < D.R.m := by omega
  have hsc := hN.1 j
  have hxi := GlobalTheory.MonoBes.val_xi l.q l.unit
  have hhz := hN.2.2.1 j ρ h
  have hB := hN.2.2.2.1 j ρ h (2 * ρ + 1) hc
  obtain ⟨F₀, hF₀⟩ := GlobalTheory.LocMod.Witness.exists_core (ofSplit l.q) ((y.bes j ρ h).lev (a.x j).vol)
    (GlobalTheory.MonoBes.ne_zero_of_val hsc) (l.FX j hj)
  have hM₀ := hIntM j ρ h hj F₀ hF₀
  have hL' := GlobalTheory.SeeSaw.SplitLat.isSelfDualC_splitL ((y.bes j ρ h).lev (a.x j).vol).d (fun _ => one_ne_zero) (hsdM j ρ h)
  have hint := GlobalTheory.MonoBes.intIn_splitL l.q ((y.bes j ρ h).lev (a.x j).vol) (sc j) (l.FX j hj) F₀ (FY j (2 * ρ + 1) hc)
    (M j ρ h) hsc hxi hhz hF₀ hB hM₀
  have heq := GlobalTheory.MonoBes.latV_eq_of_frame l.q (hsdN j hjm) hL' (FY j _ hc) (hIntN j _ hc) hint
  rw [← l.under]
  exact GlobalTheory.LocCongr.monoAt_congr heq.symm rfl
    (GlobalTheory.SeeSaw.SplitLat.monoAt_splitL ((y.bes j ρ h).lev (a.x j).vol).d (M j ρ h) _ l.q.v)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLatticeSplitsAlongWittNormalFramesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselLattice_splits_along_witt_normalFrames : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ {a : XGeo D} (y : YRat a) {βT : GL (Fin D.sp.X'.rank) (Lev.EAf D)} {PP : Pl D.host.E} (l : LocX a βT PP) (FY : FYFam l) (sc : ℕ → l.k), IsNormalFr l y FY sc → (∀ j, j ≤ D.R.m → (a.x j).Is) → ∀ (N : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)) (M : ∀ j ρ (h : j + 2 * ρ + 2 = D.R.m), GlobalTheory.FinPl.Lat (y.bes j ρ h).V₀), (∀ j, j < D.R.m → IsSelfDualC (Yc D j) (N j)) → (∀ j c (hc : j + c = l.s + 1), IntIn l.q (Yc D j) (FY j c hc) (N j)) → (∀ j ρ h, IsSelfDualC (y.bes j ρ h).V₀ (M j ρ h)) → (∀ j ρ h (hj : j ≤ l.s + 1) (F₀ : Frame l.k ((y.bes j ρ h).lev (a.x j).vol).V₀.rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Unit)), (ofSplit l.q).IsCoreFrame ((y.bes j ρ h).lev (a.x j).vol) (sc j) (l.FX j hj) F₀ → IntIn l.q _ F₀ (M j ρ h)) → ∀ j ρ (h : j + 2 * ρ + 2 = D.R.m), GlobalTheory.FinPl.MonoAt ((y.bes j ρ h).lev (a.x j).vol).d (N j) (M j ρ h) ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) := by
  first | exact @GlobalTheory.MonoBes.besLat_monoAt | exact GlobalTheory.MonoBes.besLat_monoAt | (intros; apply GlobalTheory.MonoBes.besLat_monoAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureBound
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Fam.goodBF_of_normalFrames : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (a : XGeo D) (y : YRat a) (m : YMeas y) (b₀ : ∀ j, GA D (Yc D j)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (v : VCom (commOf (pk W) u (mkGeo m b₀))) (o : TDat (commOf (pk W) u (mkGeo m b₀)) k ι) (l : ∀ PP, PP ∈ (pk W).Pg ∨ QAll W PP → LocX a (pk W).βX PP) (bas : ∀ PP h j c, j + c = (l PP h).s + 1 → GL (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c) (l PP h).k), (commOf (pk W) u (mkGeo m b₀)).Is → y.Tau (-D.host.xi0 ^ (D.R.m / 2)) → star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀ = (((D.mem u).A.T : ℕ) : D.host.E) → v.τ = y.τ → v.NT = a.LT → o.ζ₀ = a.ζ₀ → IsSelfDualC D.sp.X' a.LT → (∀ p, p ∈ v.gP ↔ ∃ PP ∈ (pk W).Pg, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) → (∀ p, p ∈ v.tP ↔ (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ (_root_.IsDedekindDomain.HeightOneSpectrum.asIdeal p)) → Disjoint v.gP v.tP → PreT v o → (∀ n (h : n = D.R.m) x, x ∉ v.tP → ∃ LZ : GlobalTheory.FinPl.Lat a.Lz, IsSelfDualC _ LZ ∧ GlobalTheory.FinPl.OrthAt (a.oT n h) (a.x n).L a.LT LZ x) → (∀ PP h, PP ∉ (pk W).Pg → ∀ j c hc, bas PP h j c hc = 1) → ∀ (FY : ∀ PP h, FYFam (l PP h)) (sc : ∀ PP h, ℕ → (l PP h).k), (∀ PP h, IsNormalFr (l PP h) y (FY PP h) (sc PP h)) → ∀ (N₁ : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)) (M₁ : ∀ j ρ h, GlobalTheory.FinPl.Lat (y.bes j ρ h).V₀), (∀ j, j < D.R.m → IsSelfDualC (Yc D j) (N₁ j)) → (∀ PP h j c hc, IntIn (l PP h).q (Yc D j) (FY PP h j c hc) (N₁ j)) → (∀ j ρ h, IsSelfDualC (y.bes j ρ h).V₀ (M₁ j ρ h)) → (∀ PP hP j ρ h (hj : j ≤ (l PP hP).s + 1) (F₀ : Frame (l PP hP).k ((y.bes j ρ h).lev (a.x j).vol).V₀.rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Unit)), (ofSplit (l PP hP).q).IsCoreFrame ((y.bes j ρ h).lev (a.x j).vol) (sc PP hP j) ((l PP hP).FX j hj) F₀ → IntIn (l PP hP).q _ F₀ (M₁ j ρ h)) → ∀ PP (hP : PP ∈ (pk W).Pg ∨ QAll W PP), ∀ j ρ h, GlobalTheory.FinPl.GoodBF (commOf (pk W) u (mkGeo m b₀)).ψ ((commOf (pk W) u (mkGeo m b₀)).B j ρ h) ((commOf (pk W) u (mkGeo m b₀)).J j ρ h) (N₁ j) (M₁ j ρ h) (N₁ (j + 1)) ((commOf (pk W) u (mkGeo m b₀)).x (j + 1)).L ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) := by
  intro D L hT Gi Gl Kc Yd cX ex W u hW a y m b₀ k _ _ _ _ ι v o l bas hIs hTau hgram hτ hNT hζ hSD hgP htP hdisj hPre hOrth hbas FY sc hNF N₁ M₁ hN₁ hFY hM₁ hcore PP hP j ρ h
  have hx : ∀ j, j ≤ D.R.m → (a.x j).Is := fun j hj => hIs.x j hj
  exact ⟨GlobalTheory.FinPl.TamePlaces.tame D _, hN₁ j (by omega), hM₁ j ρ h, hN₁ (j + 1) (by omega), (hIs.x (j + 1) (by omega)).sd,
    GlobalTheory.T.besselLattice_splits_along_witt_normalFrames _ hIs.std y (l PP hP) (FY PP hP) (sc PP hP) (hNF PP hP) hx N₁ M₁ hN₁ (hFY PP hP) hM₁ (hcore PP hP) j ρ h, GlobalTheory.T.fourierJacobiLattice_splits_at_normalFrame_place _ hIs.std y (l PP hP) (FY PP hP) (sc PP hP) (hNF PP hP) hx N₁ M₁ hN₁ (hFY PP hP) hM₁ (hcore PP hP) j ρ h, GlobalTheory.T.besselPeriodCharacter_primitive_normalFrames _ hIs.std y (l PP hP) (FY PP hP) (sc PP hP) (hNF PP hP) hx N₁ M₁ hN₁ (hFY PP hP) hM₁ (hcore PP hP) j ρ h, GlobalTheory.T.besselToJacobiMap_carries_normalFrameLines _ hIs.std y (l PP hP) (FY PP hP) (sc PP hP) (hNF PP hP) hx N₁ M₁ hN₁ (hFY PP hP) hM₁ (hcore PP hP) j ρ h, GlobalTheory.T.normalFrame_place_yZero_primitive_in_hom_lattice _ hIs.std y (l PP hP) (FY PP hP) (sc PP hP) (hNF PP hP) hx N₁ M₁ hN₁ (hFY PP hP) hM₁ (hcore PP hP) j ρ h⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentMeasureBoundStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_component_measure_bound : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (a : XGeo D) (y : YRat a) (m : YMeas y) (b₀ : ∀ j, GA D (Yc D j)) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (v : VCom (commOf (pk W) u (mkGeo m b₀))) (o : TDat (commOf (pk W) u (mkGeo m b₀)) k ι) (l : ∀ PP, PP ∈ (pk W).Pg ∨ QAll W PP → LocX a (pk W).βX PP) (bas : ∀ PP h j c, j + c = (l PP h).s + 1 → GL (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c) (l PP h).k), (commOf (pk W) u (mkGeo m b₀)).Is → y.Tau (-D.host.xi0 ^ (D.R.m / 2)) → star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀ = (((D.mem u).A.T : ℕ) : D.host.E) → v.τ = y.τ → v.NT = a.LT → o.ζ₀ = a.ζ₀ → IsSelfDualC D.sp.X' a.LT → (∀ p, p ∈ v.gP ↔ ∃ PP ∈ (pk W).Pg, p = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) → (∀ p, p ∈ v.tP ↔ (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ (_root_.IsDedekindDomain.HeightOneSpectrum.asIdeal p)) → Disjoint v.gP v.tP → PreT v o → (∀ n (h : n = D.R.m) x, x ∉ v.tP → ∃ LZ : GlobalTheory.FinPl.Lat a.Lz, IsSelfDualC _ LZ ∧ GlobalTheory.FinPl.OrthAt (a.oT n h) (a.x n).L a.LT LZ x) → (∀ PP h, PP ∉ (pk W).Pg → ∀ j c hc, bas PP h j c hc = 1) → ∀ (FY : ∀ PP h, FYFam (l PP h)) (sc : ∀ PP h, ℕ → (l PP h).k), (∀ PP h, IsNormalFr (l PP h) y (FY PP h) (sc PP h)) → ∀ (N₁ : ∀ j, GlobalTheory.FinPl.Lat (Yc D j)) (M₁ : ∀ j ρ h, GlobalTheory.FinPl.Lat (y.bes j ρ h).V₀), (∀ j, j < D.R.m → IsSelfDualC (Yc D j) (N₁ j)) → (∀ PP h j c hc, IntIn (l PP h).q (Yc D j) (FY PP h j c hc) (N₁ j)) → (∀ j ρ h, IsSelfDualC (y.bes j ρ h).V₀ (M₁ j ρ h)) → (∀ PP hP j ρ h (hj : j ≤ (l PP hP).s + 1) (F₀ : Frame (l PP hP).k ((y.bes j ρ h).lev (a.x j).vol).V₀.rank (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Unit)), (ofSplit (l PP hP).q).IsCoreFrame ((y.bes j ρ h).lev (a.x j).vol) (sc PP hP j) ((l PP hP).FX j hj) F₀ → IntIn (l PP hP).q _ F₀ (M₁ j ρ h)) → ∀ PP (hP : PP ∈ (pk W).Pg ∨ QAll W PP), ∀ j ρ h, GlobalTheory.FinPl.GoodBF (commOf (pk W) u (mkGeo m b₀)).ψ ((commOf (pk W) u (mkGeo m b₀)).B j ρ h) ((commOf (pk W) u (mkGeo m b₀)).J j ρ h) (N₁ j) (M₁ j ρ h) (N₁ (j + 1)) ((commOf (pk W) u (mkGeo m b₀)).x (j + 1)).L ((_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP)) := by
  first | exact @GlobalTheory.Fam.goodBF_of_normalFrames | exact GlobalTheory.Fam.goodBF_of_normalFrames | (intros; apply GlobalTheory.Fam.goodBF_of_normalFrames <;> assumption)
end
