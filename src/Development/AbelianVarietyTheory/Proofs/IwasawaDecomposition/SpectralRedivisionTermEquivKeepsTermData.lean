module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ECure
public import Lean
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicityMapExtremalVectorHolomorphicType
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpectralRedivisionTermEquivKeepsTermData
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpectralRedivisionTermEquivKeepsTermData
open scoped Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2 Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.SG.RowDict Formalism.L2.Forms Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.ConcreteSettingExists GlobalTheory.Mem GlobalTheory.Mem.SRe

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.SRe

variable (D : D7) (Z : New D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (t : RT Y u u')

set_option maxHeartbeats 4000000 in
theorem re_termIsId : Formalism.L2.SG.FourParts.termIsId t ↔ Formalism.L2.SG.FourParts.termIsId (eRT Z Y u u' t) := (by with_unfolding_all exact (Iff.rfl (a := Formalism.L2.SG.FourParts.termIsId t) :))

set_option maxHeartbeats 4000000 in
theorem re_termInS : Formalism.L2.SG.FourParts.termInS t ↔ Formalism.L2.SG.FourParts.termInS (eRT Z Y u u' t) := (by with_unfolding_all exact (Iff.rfl (a := Formalism.L2.SG.FourParts.termInS t) :))

set_option maxHeartbeats 4000000 in
theorem re_relevant : t.relevant ↔ (eRT Z Y u u' t).relevant := (by with_unfolding_all exact (Iff.rfl (a := t.relevant) :))

set_option maxHeartbeats 4000000 in
theorem re_FeqF : t.FeqF ↔ (eRT Z Y u u' t).FeqF := (by with_unfolding_all exact (Iff.rfl (a := t.FeqF) :))

set_option maxHeartbeats 4000000 in
theorem re_generic : t.generic ↔ (eRT Z Y u u' t).generic := (by with_unfolding_all exact (Iff.rfl (a := t.generic) :))

set_option maxHeartbeats 4000000 in
theorem re_G : t.G = (eRT Z Y u u' t).G := (by with_unfolding_all exact (Eq.refl t.G :))

set_option maxHeartbeats 4000000 in
theorem re_termBBne : ∀ p, Formalism.L2.SG.Saturated.termBBne t p ↔ Formalism.L2.SG.Saturated.termBBne (eRT Z Y u u' t) p := (by with_unfolding_all exact (fun p => Iff.rfl (a := Formalism.L2.SG.Saturated.termBBne t p) :))

set_option maxHeartbeats 4000000 in
theorem re_ptOf : Formalism.L2.SG.PairVal.ptOf t = Formalism.L2.SG.PairVal.ptOf (eRT Z Y u u' t) := (by with_unfolding_all exact (Eq.refl (Formalism.L2.SG.PairVal.ptOf t) :))

set_option maxHeartbeats 4000000 in
theorem re_massTerm : Formalism.L2.SG.PairVal.massTerm t = Formalism.L2.SG.PairVal.massTerm (eRT Z Y u u' t) := (by with_unfolding_all exact (Eq.refl (Formalism.L2.SG.PairVal.massTerm t) :))

set_option maxHeartbeats 4000000 in
theorem re_cTerm : Formalism.L2.SG.PairVal.cTerm (Formalism.L2.SG.PairVal.vRdef D u u' (X.Fu u) (Y.what₂ u) Y.δ Y.M) t = Formalism.L2.SG.PairVal.cTerm (Formalism.L2.SG.PairVal.vRdef (reD D Z) (wd Z u) (wd Z u') ((reX Z X).Fu (wd Z u)) ((reY Z Y).what₂ (wd Z u)) (reY Z Y).δ (reY Z Y).M) (eRT Z Y u u' t) := by
  with_unfolding_all exact (Eq.refl (Formalism.L2.SG.PairVal.cTerm (Formalism.L2.SG.PairVal.vRdef D u u' (X.Fu u) (Y.what₂ u) Y.δ Y.M) t) :)

omit t in
set_option maxHeartbeats 4000000 in
theorem re_meanCount : ∀ w, Formalism.L2.SG.PairVal.meanCount D u u' (X.Fu u) (Y.what₂ u) w = Formalism.L2.SG.PairVal.meanCount (reD D Z) (wd Z u) (wd Z u') ((reX Z X).Fu (wd Z u)) ((reY Z Y).what₂ (wd Z u)) w := (by with_unfolding_all exact (fun w => Eq.refl (Formalism.L2.SG.PairVal.meanCount D u u' (X.Fu u) (Y.what₂ u) w) :))


omit t in
set_option maxHeartbeats 4000000 in
theorem eRT_keeps_term_data : ∀ (D : D7) (Z : New D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), (∀ t : RT Y u u', (Formalism.L2.SG.FourParts.termIsId t ↔ Formalism.L2.SG.FourParts.termIsId (eRT Z Y u u' t)) ∧ (Formalism.L2.SG.FourParts.termInS t ↔ Formalism.L2.SG.FourParts.termInS (eRT Z Y u u' t)) ∧ (t.relevant ↔ (eRT Z Y u u' t).relevant) ∧ (t.FeqF ↔ (eRT Z Y u u' t).FeqF) ∧ (t.generic ↔ (eRT Z Y u u' t).generic) ∧ t.G = (eRT Z Y u u' t).G ∧ (∀ p, Formalism.L2.SG.Saturated.termBBne t p ↔ Formalism.L2.SG.Saturated.termBBne (eRT Z Y u u' t) p) ∧ Formalism.L2.SG.PairVal.ptOf t = Formalism.L2.SG.PairVal.ptOf (eRT Z Y u u' t) ∧ Formalism.L2.SG.PairVal.massTerm t = Formalism.L2.SG.PairVal.massTerm (eRT Z Y u u' t) ∧ Formalism.L2.SG.PairVal.cTerm (Formalism.L2.SG.PairVal.vRdef D u u' (X.Fu u) (Y.what₂ u) Y.δ Y.M) t = Formalism.L2.SG.PairVal.cTerm (Formalism.L2.SG.PairVal.vRdef (reD D Z) (wd Z u) (wd Z u') ((reX Z X).Fu (wd Z u)) ((reY Z Y).what₂ (wd Z u)) (reY Z Y).δ (reY Z Y).M) (eRT Z Y u u' t)) ∧ ∀ w, Formalism.L2.SG.PairVal.meanCount D u u' (X.Fu u) (Y.what₂ u) w = Formalism.L2.SG.PairVal.meanCount (reD D Z) (wd Z u) (wd Z u') ((reX Z X).Fu (wd Z u)) ((reY Z Y).what₂ (wd Z u)) w :=
  fun D Z X Y u u' => ⟨fun t => ⟨re_termIsId D Z X Y u u' t, re_termInS D Z X Y u u' t,
    re_relevant D Z X Y u u' t, re_FeqF D Z X Y u u' t, re_generic D Z X Y u u' t, re_G D Z X Y u u' t,
    re_termBBne D Z X Y u u' t, re_ptOf D Z X Y u u' t, re_massTerm D Z X Y u u' t,
    re_cTerm D Z X Y u u' t⟩, re_meanCount D Z X Y u u'⟩

end GlobalTheory.Mem.SRe
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpectralRedivisionTermEquivKeepsTermDataStatement
open scoped Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2 Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.Forms Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.ConcreteSettingExists GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spectralRedivisionTermEquiv_keeps_term_data : ∀ (D : D7) (Z : New D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), (∀ t : RT Y u u', (Formalism.L2.SG.FourParts.termIsId t ↔ Formalism.L2.SG.FourParts.termIsId (eRT Z Y u u' t)) ∧ (Formalism.L2.SG.FourParts.termInS t ↔ Formalism.L2.SG.FourParts.termInS (eRT Z Y u u' t)) ∧ (t.relevant ↔ (eRT Z Y u u' t).relevant) ∧ (t.FeqF ↔ (eRT Z Y u u' t).FeqF) ∧ (t.generic ↔ (eRT Z Y u u' t).generic) ∧ t.G = (eRT Z Y u u' t).G ∧ (∀ p, Formalism.L2.SG.Saturated.termBBne t p ↔ Formalism.L2.SG.Saturated.termBBne (eRT Z Y u u' t) p) ∧ Formalism.L2.SG.PairVal.ptOf t = Formalism.L2.SG.PairVal.ptOf (eRT Z Y u u' t) ∧ Formalism.L2.SG.PairVal.massTerm t = Formalism.L2.SG.PairVal.massTerm (eRT Z Y u u' t) ∧ Formalism.L2.SG.PairVal.cTerm (Formalism.L2.SG.PairVal.vRdef D u u' (X.Fu u) (Y.what₂ u) Y.δ Y.M) t = Formalism.L2.SG.PairVal.cTerm (Formalism.L2.SG.PairVal.vRdef (reD D Z) (wd Z u) (wd Z u') ((reX Z X).Fu (wd Z u)) ((reY Z Y).what₂ (wd Z u)) (reY Z Y).δ (reY Z Y).M) (eRT Z Y u u' t)) ∧ ∀ w, Formalism.L2.SG.PairVal.meanCount D u u' (X.Fu u) (Y.what₂ u) w = Formalism.L2.SG.PairVal.meanCount (reD D Z) (wd Z u) (wd Z u') ((reX Z X).Fu (wd Z u)) ((reY Z Y).what₂ (wd Z u)) w := by
  first | exact @GlobalTheory.Mem.SRe.eRT_keeps_term_data | exact GlobalTheory.Mem.SRe.eRT_keeps_term_data | (intros; apply GlobalTheory.Mem.SRe.eRT_keeps_term_data <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsoPairToTermSymm
noncomputable section

open scoped Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2 Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.SG.RowDict Formalism.L2.Forms Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.ConcreteSettingExists GlobalTheory.Mem GlobalTheory.Mem.SRe

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SRe

variable {D : D7} (Z : New D) {X : HidaSetting D} (Y : Full X) (u u' : D.what₂.Word)


set_option maxHeartbeats 4000000 in
theorem isoPair_toTerm (s : TT Y u u') : (eTT Z Y u u' s).toTerm = eRT Z Y u u' s.toTerm := (by with_unfolding_all exact ((Eq.refl (eRT Z Y u u' s.toTerm)) :))


set_option maxHeartbeats 4000000 in
theorem isoPair_toTerm_symm (s : TT (reY Z Y) (wd Z u) (wd Z u')) :
    ((eTT Z Y u u').symm s).toTerm = (eRT Z Y u u').symm s.toTerm := (by with_unfolding_all exact ((Eq.refl ((eTT Z Y u u').symm s).toTerm) :))


set_option maxHeartbeats 4000000 in
theorem isoPair_row (a b : TT Y u u') :
    rowOf (reY Z Y).TR ((reY Z Y).cs (wd Z u)) ((reY Z Y).cs (wd Z u')) (eTT Z Y u u' a) =
        rowOf (reY Z Y).TR ((reY Z Y).cs (wd Z u)) ((reY Z Y).cs (wd Z u')) (eTT Z Y u u' b) ↔
      rowOf Y.TR (Y.cs u) (Y.cs u') a = rowOf Y.TR (Y.cs u) (Y.cs u') b := (by with_unfolding_all exact ((Iff.rfl : rowOf Y.TR (Y.cs u) (Y.cs u') a = rowOf Y.TR (Y.cs u) (Y.cs u') b ↔ _) :))


set_option maxHeartbeats 4000000 in
theorem isoPair_row_symm (a b : TT (reY Z Y) (wd Z u) (wd Z u')) :
    rowOf Y.TR (Y.cs u) (Y.cs u') ((eTT Z Y u u').symm a) = rowOf Y.TR (Y.cs u) (Y.cs u') ((eTT Z Y u u').symm b) ↔
      rowOf (reY Z Y).TR ((reY Z Y).cs (wd Z u)) ((reY Z Y).cs (wd Z u')) a =
        rowOf (reY Z Y).TR ((reY Z Y).cs (wd Z u)) ((reY Z Y).cs (wd Z u')) b := by
  have := isoPair_row Z Y u u' ((eTT Z Y u u').symm a) ((eTT Z Y u u').symm b)
  simpa only [Equiv.apply_symm_apply] using this.symm


set_option maxHeartbeats 4000000 in
theorem isoPair_s0T (a b : TT Y u u') : s0T (eTT Z Y u u' a) (eTT Z Y u u' b) = s0T a b := (by with_unfolding_all exact (
  (Eq.refl (s0T a b)) :))


set_option maxHeartbeats 4000000 in
theorem isoPair_lift (a b : TT Y u u') : liftScalar (eTT Z Y u u' a) (eTT Z Y u u' b) ↔ liftScalar a b := (by exact (Iff.rfl : liftScalar a b ↔ liftScalar a b))

def isoPairFib (t : RT Y u u') : fib Y t ≃ fib (reY Z Y) (eRT Z Y u u' t) where
  toFun s := ⟨eTT Z Y u u' s.1, by rw [isoPair_toTerm, s.2]⟩
  invFun s := ⟨(eTT Z Y u u').symm s.1, by rw [isoPair_toTerm_symm, s.2, Equiv.symm_apply_apply]⟩
  left_inv s := Subtype.ext (Equiv.symm_apply_apply _ _)
  right_inv s := Subtype.ext (Equiv.apply_symm_apply _ _)

def isoPairE : RP Y u u' ≃ RP (reY Z Y) (wd Z u) (wd Z u') where
  toFun q := ⟨(eRT Z Y u u' q.1.1, eRT Z Y u u' q.1.2), by
    obtain ⟨s₁, s₂, hs⟩ := q.2
    exact ⟨isoPairFib Z Y u u' _ s₁, isoPairFib Z Y u u' _ s₂, (isoPair_row Z Y u u' _ _).2 hs⟩⟩
  invFun q := ⟨((eRT Z Y u u').symm q.1.1, (eRT Z Y u u').symm q.1.2), by
    obtain ⟨s₁, s₂, hs⟩ := q.2
    refine ⟨⟨(eTT Z Y u u').symm s₁.1, by rw [isoPair_toTerm_symm, s₁.2]⟩,
      ⟨(eTT Z Y u u').symm s₂.1, by rw [isoPair_toTerm_symm, s₂.2]⟩, (isoPair_row_symm Z Y u u' _ _).2 hs⟩⟩
  left_inv q := Subtype.ext (by simp)
  right_inv q := Subtype.ext (by simp)


set_option maxHeartbeats 4000000 in
theorem rp_iso_pair : ∀ (D : D7) (Z : New D) (X : HidaSetting D) (Y : Full X) (h : FinX Y) (h' : FinX (reY Z Y))
    (u u' : D.what₂.Word), ∃ e : RP Y u u' ≃ RP (reY Z Y) (wd Z u) (wd Z u'), ∀ q, eRT Z Y u u' q.1.1 = (e q).1.1 ∧
      eRT Z Y u u' q.1.2 = (e q).1.2 ∧ s0T q.l1 q.l2 = s0T (e q).l1 (e q).l2 ∧
      (liftScalar q.l1 q.l2 ↔ liftScalar (e q).l1 (e q).l2) ∧
      pvR h u u' q = pvR h' (wd Z u) (wd Z u') (e q) := by
  intro D Z X Y h h' u u'
  refine ⟨isoPairE Z Y u u', fun q => ⟨rfl, rfl, ?_⟩⟩

  set a := (eTT Z Y u u').symm (isoPairE Z Y u u' q).l1 with ha
  set b := (eTT Z Y u u').symm (isoPairE Z Y u u' q).l2 with hb
  have hA : (isoPairE Z Y u u' q).l1 = eTT Z Y u u' a := by simp [a]
  have hB : (isoPairE Z Y u u' q).l2 = eTT Z Y u u' b := by simp [b]
  have h1 : q.l1.toTerm = q.1.1 := q.2.choose.2
  have h2 : q.l2.toTerm = q.1.2 := q.2.choose_spec.choose.2
  have hr : rowOf Y.TR (Y.cs u) (Y.cs u') q.l1 = rowOf Y.TR (Y.cs u) (Y.cs u') q.l2 := q.2.choose_spec.choose_spec
  have e1 : (isoPairE Z Y u u' q).l1.toTerm = eRT Z Y u u' q.1.1 := (isoPairE Z Y u u' q).2.choose.2
  have e2 : (isoPairE Z Y u u' q).l2.toTerm = eRT Z Y u u' q.1.2 := (isoPairE Z Y u u' q).2.choose_spec.choose.2
  have er := (isoPairE Z Y u u' q).2.choose_spec.choose_spec
  have ha1 : a.toTerm = q.1.1 := by rw [isoPair_toTerm_symm]; erw [e1]; simp
  have hb1 : b.toTerm = q.1.2 := by rw [isoPair_toTerm_symm]; erw [e2]; simp
  have hab : rowOf Y.TR (Y.cs u) (Y.cs u') a = rowOf Y.TR (Y.cs u) (Y.cs u') b :=
    (isoPair_row_symm Z Y u u' _ _).2 er
  obtain ⟨hs, hl⟩ := h.pairIndep u u' q.l1 q.l2 a b (h1.trans ha1.symm) (h2.trans hb1.symm) hr hab
  refine ⟨?_, ?_, ?_⟩
  · rw [hA, hB, isoPair_s0T]; exact hs
  · rw [hA, hB, isoPair_lift]; exact hl
  · letI := h.fibFT q.1.1
    letI := h.fibFT q.1.2
    letI := h'.fibFT (eRT Z Y u u' q.1.1)
    letI := h'.fibFT (eRT Z Y u u' q.1.2)
    unfold pvR
    refine Fintype.sum_equiv ((isoPairFib Z Y u u' q.1.1).prodCongr (isoPairFib Z Y u u' q.1.2)) _ _
      fun r => ?_
    exact (by with_unfolding_all exact ((Eq.refl (if rowOf Y.TR (Y.cs u) (Y.cs u') r.1.1 = rowOf Y.TR (Y.cs u) (Y.cs u') r.2.1
        then inner ℂ (vT Y u u' r.2.1) (vT Y u u' r.1.1) else (0 : ℂ))) :))

end GlobalTheory.Mem.SRe
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolomorphicTypeAtExtremalOfKEquivariantLoweringK
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolomorphicTypeAtExtremalOfKEquivariantLoweringK
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift

namespace GlobalTheory.KMapHol

theorem exp_mem_kset {n : ℕ} (ε : Fin n → Bool) {X : Mt n} (hX : X ∈ lieH (Formalism.REAL.Jm ε))
    (hc : Commute X (Formalism.REAL.Jm ε)) (t : ℝ) : NormedSpace.exp (t • X) ∈ Formalism.REAL.Kset ε := by
  have hd : IsUnit (Formalism.REAL.Jm ε).det := isUnit_iff_ne_zero.2 (VKill.jm_det ε)
  have h0 : Xᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * X = 0 := hX
  have h1 : X ∈ lieH (1 : Mt n) := by
    show Xᴴ * 1 + 1 * X = 0
    rw [← hc.eq, ← Matrix.add_mul] at h0
    have := congrArg (· * (Formalism.REAL.Jm ε)⁻¹) h0
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one, Matrix.zero_mul] at this
    simpa using this
  have h2 : (NormedSpace.exp (t • X))ᴴ * 1 * NormedSpace.exp (t • X) = 1 := GlobalTheory.SmVec.exp_mem_UH isUnit_one h1 t
  refine ⟨Matrix.mem_unitaryGroup_iff'.2 (by simpa [star_eq_conjTranspose] using h2), ?_⟩
  exact ((hc.smul_left t).exp_left).eq

theorem commute_conjH {n : ℕ} (ε : Fin n → Bool) {E : Mt n} (hc : Commute E (Formalism.REAL.Jm ε)) :
    Commute (conjH (Formalism.REAL.Jm ε) E) (Formalism.REAL.Jm ε) := by
  have hd : IsUnit (Formalism.REAL.Jm ε).det := isUnit_iff_ne_zero.2 (VKill.jm_det ε)
  have h1 : Formalism.REAL.Jm ε * Eᴴ = Eᴴ * Formalism.REAL.Jm ε := by
    have := congrArg conjTranspose hc.eq
    simpa only [conjTranspose_mul, (VKill.jm_herm ε).eq] using this
  have h2 : conjH (Formalism.REAL.Jm ε) E = -Eᴴ := by
    rw [conjH, Matrix.mul_assoc, ← h1, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.one_mul]
  rw [h2]
  exact Commute.neg_left h1.symm

theorem commute_single {n : ℕ} (ε : Fin n → Bool) {a c : Fin n} (h : ε a = ε c) :
    Commute (Matrix.single a c (1 : ℂ)) (Formalism.REAL.Jm ε) := by
  show _ * _ = _ * _
  unfold Formalism.REAL.Jm
  ext i j
  rw [mul_diagonal, diagonal_mul, Matrix.single_apply]
  split_ifs with h1 h2 h3 <;> simp_all

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S}


open Classical in
theorem exists_form (h1 : LowSm M) (h2 : GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.LowIrr M) (U : GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.KMap M) (e : ∀ τ, lowT M τ)
    (τ : D.what₂.Tau) (x : GA D V) :
    ∃ ℓ : M.H τ →L[ℂ] ℂ, ∀ u : lowT M τ, ℓ ((u : M.sm τ) : M.H τ) = U (Function.update e τ u) x := by
  let P := lowKSub (M.ε τ) (M.lam τ) (M.σ τ)
  haveI : FiniteDimensional ℂ P := (h2 τ).1
  haveI : CompleteSpace P := FiniteDimensional.complete ℂ P
  let ℓ₀ : P →ₗ[ℂ] ℂ :=
    { toFun := fun y => U (Function.update e τ ⟨⟨y, h1 τ y.2⟩, y.2⟩) x
      map_add' := fun y z => congrFun (U.map_update_add e τ ⟨⟨y, h1 τ y.2⟩, y.2⟩ ⟨⟨z, h1 τ z.2⟩, z.2⟩) x
      map_smul' := fun a y => congrFun (U.map_update_smul e τ a ⟨⟨y, h1 τ y.2⟩, y.2⟩) x }
  refine ⟨(LinearMap.toContinuousLinearMap ℓ₀).comp P.orthogonalProjection, fun u => ?_⟩
  have : P.orthogonalProjection ((u : M.sm τ) : M.H τ) = ⟨_, u.2⟩ :=
    Submodule.orthogonalProjection_mem_subspace_eq_self (K := P) ⟨_, u.2⟩
  rw [ContinuousLinearMap.comp_apply, this]
  rfl


open Classical in
theorem rder_eq (θ : InfFam D) (h1 : LowSm M) (h2 : GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.LowIrr M) (U : GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.KMap M)
    (hK : KEquiv θ M U) (e : ∀ τ, lowT M τ) (τ : D.what₂.Tau) (x : GA D V) (ℓ : M.H τ →L[ℂ] ℂ)
    (hℓ : ∀ u : lowT M τ, ℓ ((u : M.sm τ) : M.H τ) = U (Function.update e τ u) x)
    {X Y : Mt V.rank} (hY : Y ∈ lieH (Formalism.REAL.Jm (M.ε τ))) (hc : Commute Y (Formalism.REAL.Jm (M.ε τ)))
    (hXY : X = (M.fr τ)⁻¹ * Y * M.fr τ)
    (hd : HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) ((e τ : M.sm τ) : M.H τ))
      (dRep (M.rep τ) X ((e τ : M.sm τ) : M.H τ)) 0) :
    Rder θ V τ X (U e) x = ℓ (dRep (M.rep τ) X ((e τ : M.sm τ) : M.H τ)) := by
  have hP := M.fr_unit τ
  have hPd := (Matrix.isUnit_iff_isUnit_det _).1 hP
  have e1 : M.fr τ * X * (M.fr τ)⁻¹ = Y := by
    rw [hXY, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hPd, Matrix.one_mul, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hPd, Matrix.mul_one]
  have key : ∀ t : ℝ, U e (x * oneP θ V τ X t) = ℓ (M.rep τ (NormedSpace.exp (t • X)) ((e τ : M.sm τ) : M.H τ)) := by
    intro t
    have hk : M.fr τ * NormedSpace.exp (t • X) * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) := by
      rw [VKill.conj_exp hP, e1]; exact exp_mem_kset _ hY hc t
    have hm := (h2 τ).2.1 _ hk _ (e τ).2
    have h := hK τ _ hk e ⟨⟨_, h1 τ hm⟩, hm⟩ rfl
    have e2 : (M.fr τ)⁻¹ * (M.fr τ * NormedSpace.exp (t • X) * (M.fr τ)⁻¹) * M.fr τ = NormedSpace.exp (t • X) := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hPd, Matrix.one_mul, Matrix.mul_assoc,
        Matrix.nonsing_inv_mul _ hPd, Matrix.mul_one]
    rw [e2] at h
    exact ((hℓ ⟨⟨_, h1 τ hm⟩, hm⟩).trans (congrFun h x)).symm
  unfold Rder
  simp only [key]
  exact ((ℓ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 hd).deriv

theorem holAd_of_kEquiv : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ), IsInfFam θ → HolShape M → WtIs M w → LowSm M → GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.LowIrr M → ∀ U : GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.KMap M, (∀ e, GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.IsSmoothFn V θ (U e)) → KEquiv θ M U → (∀ τ, ∀ Z ∈ GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.pMinus M τ, ∀ e, RderC θ V τ Z (U e) = 0) → ∀ e : ∀ τ, lowT M τ, IsExtVec M (fun τ => (e τ : M.sm τ)) → HolAd θ M w (U e) := by
  classical
  intro D θ V S M w hθ hS hw h1 h2 U hsm hK hp e hv g
  obtain ⟨L, -, hmul, -, -, hinv, hat, -, -, hG⟩ := GlobalTheory.RealLift.exists_real_lift D θ V hθ
  have hexp : ∀ τ, ∀ X ∈ lieH (gramAt D V τ), ∀ t : ℝ, NormedSpace.exp (t • X) ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) :=
    fun τ X hX t => GlobalTheory.SmVec.exp_mem_UH ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 (hG τ).2)) hX t
  have hone : ∀ τ, ∀ X ∈ lieH (gramAt D V τ), ∀ t : ℝ,
      L (Pi.mulSingle τ (NormedSpace.exp (t • X))) = oneP θ V τ X t :=
    fun τ X hX t => (hat τ _ (hexp τ X hX t)).symm
  refine ⟨fun u => U e (g * L u), ?_, fun u hu => by simp only [hinv u hu]⟩
  refine GlobalTheory.HolDict.holFn_of_killed _ _ _ _ _ _ (fun τ => ((ModelRep.model_rep D V S M τ).2.2.2 hS).1) _ ?_ ?_
  · intro k τs Xs hX u hu
    have h := hsm e k τs Xs hX (g * L u)
    convert h using 2 with t
    obtain ⟨h1, h2⟩ := GlobalTheory.MultHol.lift_prod L hmul
      (List.ofFn fun i => (Pi.mulSingle (τs i) (NormedSpace.exp (t i • Xs i)) : D.what₂.Tau → Mt V.rank)) (by
        intro x hx
        obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hx
        exact GlobalTheory.MultHol.mulSingle_mem_UG _ (hexp _ _ (hX i) _))
    show U e (g * L (u * _)) = _
    rw [hmul u hu _ h1, h2, List.map_ofFn, mul_assoc]
    exact congrArg (fun F : Fin k → GA D V => U e (g * (L u * (List.ofFn F).prod))) (funext fun i => hone _ _ (hX i) _)
  · intro τ a c hac u hu
    have hder : ∀ X ∈ lieH (gramAt D V τ), der τ X (fun u => U e (g * L u)) u = Rder θ V τ X (U e) (g * L u) := by
      intro X hX
      unfold der Rder
      congr 1
      funext t
      show U e (g * L (u * _)) = _
      rw [hmul u hu _ (GlobalTheory.MultHol.mulSingle_mem_UG _ (hexp _ _ hX _)), hone τ X hX, mul_assoc]
    obtain ⟨hc, hU, -, hx⟩ := ModelRep.model_rep D V S M τ
    obtain ⟨-, hx⟩ := hx hS
    obtain ⟨hs, hk⟩ := VKill.borel_extVec D θ V S M w _ hθ hS hw hv τ
    have hk := hk a c hac
    rw [hx a c] at hk ⊢
    set a' := arr (nNeg (M.ε τ)) a with ha'
    set c' := arr (nNeg (M.ε τ)) c with hc'
    obtain ⟨p1, p2⟩ := GlobalTheory.MultHol.parts_mem_lieH (hG τ).1 (hG τ).2 ((M.fr τ)⁻¹ * Matrix.single a' c' 1 * M.fr τ)
    by_cases hε : M.ε τ a' = M.ε τ c'
    · obtain ⟨ℓ, hℓ⟩ := exists_form h1 h2 U e τ (g * L u)
      obtain ⟨q1, q2⟩ := GlobalTheory.MultHol.parts_mem_lieH (VKill.jm_herm (M.ε τ)) (VKill.jm_det (M.ε τ)) (Matrix.single a' c' 1)
      have c1 := commute_single (M.ε τ) hε
      have c2 := commute_conjH (M.ε τ) c1
      have hcj : conjH (gramAt D V τ) ((M.fr τ)⁻¹ * Matrix.single a' c' 1 * M.fr τ) =
          (M.fr τ)⁻¹ * conjH (Formalism.REAL.Jm (M.ε τ)) (Matrix.single a' c' 1) * M.fr τ := by
        rw [← M.fr_gram τ]; exact VKill.conjH_conj (M.fr_unit τ) _ _
      have hD := ((GlobalTheory.UnitarySmVec.smoothVec_basic _ _ _ _ (hG τ).1 (hG τ).2 hU).2 _ hs).2.1
      have r1 := rder_eq θ h1 h2 U hK e τ (g * L u) ℓ hℓ q1 ((c1.add_left c2).smul_left _)
        (by rw [hcj, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul]) (hD _ p1).2
      have r2 := rder_eq θ h1 h2 U hK e τ (g * L u) ℓ hℓ q2 ((c1.sub_left c2).smul_left _)
        (by rw [hcj, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul]) (hD _ p2).2
      have hk' := congrArg ℓ hk
      unfold dRepC at hk'
      rw [map_add (f := _), map_smul, smul_eq_mul] at hk'
      unfold derC
      rw [hder _ p1, hder _ p2, r1, r2, hk']
      split_ifs
      · rw [map_smul, hℓ (e τ), Function.update_eq_self, smul_eq_mul]
      · rw [map_zero]
    · obtain ⟨-, p, hpn, hεp⟩ := hS τ
      have hq := nNeg_shape hpn hεp
      have hsg : ∀ b : Fin V.rank, M.ε τ (arr (nNeg (M.ε τ)) b) = decide (¬ (b : ℕ) < V.rank - p) := by
        intro b
        have := b.2
        rw [hεp, hq]
        unfold arr
        split_ifs with hb
        · simp only [hb, not_true_eq_false, decide_false, decide_eq_false_iff_not]; omega
        · simp only [hb, not_false_eq_true, decide_true, decide_eq_true_eq]; omega
      have hac' : (a : ℕ) ≤ c := hac
      have hne : a ≠ c := fun h => hε (by rw [ha', hc', h])
      rw [ha', hc', hsg, hsg, decide_eq_decide] at hε
      have ha : M.ε τ a' = false := by rw [ha', hsg]; simp only [decide_eq_false_iff_not]; omega
      have hb : M.ε τ c' = true := by rw [hc', hsg]; simp only [decide_eq_true_eq]; omega
      have h0 := congrFun (hp τ _ (GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.single_mem_pMinus M τ ha hb) e) (g * L u)
      rw [if_neg hne]
      unfold derC
      rw [hder _ p1, hder _ p2]
      exact h0

end GlobalTheory.KMapHol
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolomorphicTypeAtExtremalOfKEquivariantLoweringKStatement
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphicType_at_extremal_of_kEquivariant_loweringKilled : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ), IsInfFam θ → HolShape M → WtIs M w → LowSm M → GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.LowIrr M → ∀ U : GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.KMap M, (∀ e, GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.IsSmoothFn V θ (U e)) → KEquiv θ M U → (∀ τ, ∀ Z ∈ GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.pMinus M τ, ∀ e, RderC θ V τ Z (U e) = 0) → ∀ e : ∀ τ, lowT M τ, IsExtVec M (fun τ => (e τ : M.sm τ)) → HolAd θ M w (U e) := by
  first | exact @GlobalTheory.KMapHol.holAd_of_kEquiv | exact GlobalTheory.KMapHol.holAd_of_kEquiv | (intros; apply GlobalTheory.KMapHol.holAd_of_kEquiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtMCastSuccLast
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col GlobalTheory.Mem.Col2 Matrix

namespace GlobalTheory.Mem.Col2.TilX

section Ext

variable {A : Type} [CommRing A] {N n : ℕ} (hN : N = n + 1)

def extM (_hN : N = n + 1) (g : Matrix (Fin n) (Fin n) A) : Matrix (Fin N) (Fin N) A := fun a b =>
  if ha : a.1 < n then (if hb : b.1 < n then g ⟨a.1, ha⟩ ⟨b.1, hb⟩ else 0) else if b.1 < n then 0 else 1

theorem extM_castSucc (g : Matrix (Fin n) (Fin n) A) (i j : Fin n) :
    extM (rfl : n + 1 = n + 1) g i.castSucc j.castSucc = g i j := by
  simp [extM]

theorem extM_castSucc_last (g : Matrix (Fin n) (Fin n) A) (i : Fin n) :
    extM (rfl : n + 1 = n + 1) g i.castSucc (Fin.last n) = 0 := by
  simp [extM]

theorem extM_last_castSucc (g : Matrix (Fin n) (Fin n) A) (j : Fin n) :
    extM (rfl : n + 1 = n + 1) g (Fin.last n) j.castSucc = 0 := by
  simp [extM]

theorem extM_last_last (g : Matrix (Fin n) (Fin n) A) :
    extM (rfl : n + 1 = n + 1) g (Fin.last n) (Fin.last n) = 1 := by
  simp [extM]

theorem extM_mulVec_iC (g : Matrix (Fin n) (Fin n) A) (x : Fin N → A) (i : Fin n) :
    (extM hN g *ᵥ x) (Br.iC hN i) = (g *ᵥ iniH hN x) i := by
  subst hN
  have e : Br.iC (rfl : n + 1 = n + 1) i = i.castSucc := rfl
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, e, extM_castSucc, extM_castSucc_last, zero_mul, add_zero]
  rfl

theorem extM_mulVec_iL (g : Matrix (Fin n) (Fin n) A) (x : Fin N → A) :
    (extM hN g *ᵥ x) (Br.iL hN) = x (Br.iL hN) := by
  subst hN
  have e : Br.iL (rfl : n + 1 = n + 1) = Fin.last n := rfl
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, e, extM_last_castSucc, extM_last_last, zero_mul,
    Finset.sum_const_zero, zero_add, one_mul]

theorem extM_one : extM hN (1 : Matrix (Fin n) (Fin n) A) = 1 := by
  subst hN
  ext a b
  refine Fin.lastCases ?_ (fun i => ?_) a <;> refine Fin.lastCases ?_ (fun j => ?_) b
  · simp [extM_last_last]
  · rw [extM_last_castSucc, Matrix.one_apply_ne (Fin.castSucc_lt_last j).ne']
  · rw [extM_castSucc_last, Matrix.one_apply_ne (Fin.castSucc_lt_last i).ne]
  · rw [extM_castSucc, Matrix.one_apply, Matrix.one_apply]
    simp [Fin.castSucc_inj]

theorem extM_mul (g h : Matrix (Fin n) (Fin n) A) : extM hN (g * h) = extM hN g * extM hN h := by
  subst hN
  ext a b
  rw [Matrix.mul_apply, Fin.sum_univ_castSucc]
  refine Fin.lastCases ?_ (fun i => ?_) a <;> refine Fin.lastCases ?_ (fun j => ?_) b
  · simp [extM_last_last, extM_last_castSucc]
  · simp [extM_last_last, extM_last_castSucc]
  · simp [extM_castSucc_last]
  · simp [extM_castSucc, extM_castSucc_last, Matrix.mul_apply]

def extGL : GL (Fin n) A →* GL (Fin N) A :=
  Units.map { toFun := extM hN, map_one' := extM_one hN, map_mul' := extM_mul hN }

theorem extGL_val (g : GL (Fin n) A) : (extGL hN g : Matrix (Fin N) (Fin N) A) = extM hN g := rfl

theorem extGL_inv_val (g : GL (Fin n) A) :
    ((extGL hN g)⁻¹ : GL (Fin N) A).1 = extM hN ((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) := by
  rw [← map_inv, extGL_val]

theorem eq_extM {M : Matrix (Fin N) (Fin N) A} {g : Matrix (Fin n) (Fin n) A}
    (h1 : ∀ (a : Fin N) (j : Fin n), M a (Br.iC hN j) = extM hN g a (Br.iC hN j))
    (h2 : ∀ a : Fin N, M a (Br.iL hN) = extM hN g a (Br.iL hN)) : M = extM hN g := by
  subst hN
  ext a b
  refine Fin.lastCases ?_ (fun j => ?_) b
  · exact h2 a
  · exact h1 a j

end Ext

end GlobalTheory.Mem.Col2.TilX

end
end
