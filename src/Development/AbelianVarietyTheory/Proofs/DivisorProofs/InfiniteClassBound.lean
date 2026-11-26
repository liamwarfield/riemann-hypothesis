module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameConjugatePrincipalCongruenceMemLatticeCongr
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestSupportFamiliesStaircaseCosets

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteVertexClassesCardLePrincipalCongruence
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealTrivialPointFiniteAdelicHomEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealTrivialPointFiniteAdelicHomEq
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport

namespace GlobalTheory.FrameTransport

theorem exists_finG_eq : ∀ {D : D7} (V : HSp D) (M : GL (Fin V.rank) (Lev.EAf D)), M ∈ UA D.sp.cm V.gram →
    ∃ g : GfC V, finG V g = M := by
  intro D V M hM
  obtain ⟨g0, hg0⟩ := GlobalTheory.FunObj.UA_le_range_finE V hM
  obtain ⟨k, k1, k2⟩ := GlobalTheory.UnitarySplit.ga_glue V 1 (finHom V g0) (one_mem _) (GlobalTheory.UnitarySplit.finHom_mem V g0)
  refine ⟨⟨k, MonoidHom.mem_ker.2 k1⟩, ?_⟩
  rw [← hg0]
  change Formalism.UG.bc (Lev.swapAE D) (finHom V k) = Formalism.UG.bc (Lev.swapAE D) (finHom V g0)
  rw [k2]

end GlobalTheory.FrameTransport

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealTrivialPointFiniteAdelicHomEqStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_realTrivial_point_finiteAdelicHom_eq : ∀ {D : D7} (V : HSp D) (M : GL (Fin V.rank) (Lev.EAf D)), M ∈ UA D.sp.cm V.gram → ∃ g : GfC V, finG V g = M := by
  first | exact @GlobalTheory.FrameTransport.exists_finG_eq | exact GlobalTheory.FrameTransport.exists_finG_eq | (intros; apply GlobalTheory.FrameTransport.exists_finG_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameConjStandardUnitaryMemUnitaryFiniteAdelic
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameConjStandardUnitaryMemUnitaryFiniteAdelic
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport

noncomputable section

namespace GlobalTheory.FrameTransport

theorem cT_map' {A B : Type} [CommRing A] [CommRing B] {m p : Type} (s : A →+* A) (t : B →+* B) (ι : A →+* B)
    (h : ∀ a, t (ι a) = ι (s a)) (M : Matrix m p A) :
    Formalism.UG.cT t (M.map ι) = (Formalism.UG.cT s M).map ι := by
  ext i j
  simp [Formalism.UG.cT, h]

theorem conj_unitary {A B C : Type} [CommRing A] [CommRing B] [CommRing C] {n : Type} [Fintype n] [DecidableEq n]
    (s : A →+* A) (t : C →+* C) (u : B →+* B) (ι : A →+* B) (φ : C →+* B)
    (hι : ∀ a, u (ι a) = ι (s a)) (hφ : ∀ c, u (φ c) = φ (t c))
    (P Q J : Matrix n n A) (H : Matrix n n C) (hPQ : P * Q = 1) (hQP : Q * P = 1)
    (hfr : Formalism.UG.cT s P * J * P = 1) (hH : Formalism.UG.cT t H * H = 1) :
    Formalism.UG.cT u (P.map ι * H.map φ * Q.map ι) * J.map ι * (P.map ι * H.map φ * Q.map ι) = J.map ι := by
  have hJ : J = Formalism.UG.cT s Q * Q := by
    calc J = Formalism.UG.cT s (P * Q) * J * (P * Q) := by
            rw [hPQ, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]
      _ = Formalism.UG.cT s Q * (Formalism.UG.cT s P * J * P) * Q := by
            rw [Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
      _ = Formalism.UG.cT s Q * Q := by rw [hfr, Matrix.mul_one]
  have hHu : Formalism.UG.cT u (H.map φ) * H.map φ = 1 := by
    rw [cT_map' t u φ hφ, ← Matrix.map_mul, hH, Matrix.map_one _ (map_zero _) (map_one _)]
  have hQP' : Q.map ι * P.map ι = 1 := by
    rw [← Matrix.map_mul, hQP, Matrix.map_one _ (map_zero _) (map_one _)]
  have hPQc : Formalism.UG.cT u (P.map ι) * Formalism.UG.cT u (Q.map ι) = 1 := by
    rw [← Formalism.UG.cT_mul, hQP', Formalism.UG.cT_one]
  have hJ' : J.map ι = Formalism.UG.cT u (Q.map ι) * Q.map ι := by
    rw [hJ, Matrix.map_mul, cT_map' s u ι hι]
  rw [hJ']
  calc Formalism.UG.cT u (P.map ι * H.map φ * Q.map ι) * (Formalism.UG.cT u (Q.map ι) * Q.map ι) * (P.map ι * H.map φ * Q.map ι)
      = Formalism.UG.cT u (Q.map ι) * (Formalism.UG.cT u (H.map φ) * (Formalism.UG.cT u (P.map ι) * Formalism.UG.cT u (Q.map ι))
          * (Q.map ι * P.map ι) * H.map φ) * Q.map ι := by
        rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
    _ = Formalism.UG.cT u (Q.map ι) * Q.map ι := by
        rw [hPQc, hQP', Matrix.mul_one, Matrix.mul_one, hHu, Matrix.mul_one]

theorem adSwap_sgA (D : D7) (y : StandardLatticesGL3.AE D) :
    adSwap D (StandardLatticesGL3.sgA D y) = Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) (adSwap D y) := by
  unfold adSwap
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
  rw [GlobalTheory.BotFormula.toAfE_sgA]
  generalize (GlobalTheory.BotFormula.toAfE D) y = x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    simp [Lev.swapAE, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Formalism.UG.sigR, Algebra.TensorProduct.map_tmul]
  | add x y hx hy => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), RingHom.map_add (f := _), hx, hy, RingHom.map_add (f := _)]

theorem sigR_inclEAf (D : D7) (a : D.host.E) :
    Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) (inclEAf D a) = inclEAf D (D.sp.cm.sig a) := by
  simp only [inclEAf, Formalism.UG.sigR, Formalism.UG.inclE, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq]

theorem frConj_mem_UA {D : D7} (V : HSp D) (fr : GL (Fin V.rank) D.host.E)
    (hfr : Formalism.UG.cT (↑D.sp.cm.sig) (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * V.gram
      * (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = 1)
    (h : StandardLatticesGL3.GA D V.rank) : GlobalTheory.FrameTransport.frConj fr h.1 ∈ UA D.sp.cm V.gram := by
  have h2 : Formalism.UG.cT (StandardLatticesGL3.sgA D) (h.1 : Matrix (Fin V.rank) (Fin V.rank) (StandardLatticesGL3.AE D))
      * (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (StandardLatticesGL3.inc D) * (h.1 : Matrix (Fin V.rank) (Fin V.rank) (StandardLatticesGL3.AE D)) =
      (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (StandardLatticesGL3.inc D) := h.2
  rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one] at h2
  have key := conj_unitary (D.sp.cm.sig : D.host.E →+* D.host.E) (StandardLatticesGL3.sgA D) (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F))
    (inclEAf D) (adSwap D) (sigR_inclEAf D) (fun y => (adSwap_sgA D y).symm)
    (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) ((fr⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E)
    V.gram (h.1 : Matrix (Fin V.rank) (Fin V.rank) (StandardLatticesGL3.AE D))
    (by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]) (by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]) hfr h2
  exact key

end GlobalTheory.FrameTransport

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameConjStandardUnitaryMemUnitaryFiniteAdelicStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameConj_standardUnitary_mem_unitaryFiniteAdelic : ∀ {D : D7} (V : HSp D) (fr : GL (Fin V.rank) D.host.E), Formalism.UG.cT (↑D.sp.cm.sig) (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * V.gram * (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = 1 → ∀ h : StandardLatticesGL3.GA D V.rank, GlobalTheory.FrameTransport.frConj fr h.1 ∈ UA D.sp.cm V.gram := by
  first | exact @GlobalTheory.FrameTransport.frConj_mem_UA | exact GlobalTheory.FrameTransport.frConj_mem_UA | (intros; apply GlobalTheory.FrameTransport.frConj_mem_UA <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStandardUnitaryFrameConjEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStandardUnitaryFrameConjEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport

noncomputable section

namespace GlobalTheory.FrameTransport.Onto

open scoped TensorProduct

theorem swapAE_sigR (D : D7) (z : TensorProduct D.host.F (Af D.host.F) D.host.E) :
    Lev.swapAE D (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (Af D.host.F) D.sp.cm.sig z) =
      Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) (Lev.swapAE D z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero, RingHom.map_zero]
  | add a b ha hb => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), ha, hb, RingHom.map_add (f := _), RingHom.map_add (f := _)]
  | tmul a e => rfl

theorem adSwap_sgA (D : D7) (y : StandardLatticesGL3.AE D) :
    adSwap D (StandardLatticesGL3.sgA D y) = Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) (adSwap D y) := by
  show Lev.swapAE D (GlobalTheory.BotFormula.toAfE D (StandardLatticesGL3.sgA D y)) = _
  rw [GlobalTheory.BotFormula.toAfE_sgA]
  exact swapAE_sigR D _

def adSwapEquiv (D : D7) : StandardLatticesGL3.AE D ≃+* Lev.EAf D :=
  (GlobalTheory.BotFormula.toAfE D).trans (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).toRingEquiv

theorem adSwapEquiv_apply (D : D7) (y : StandardLatticesGL3.AE D) : adSwapEquiv D y = adSwap D y := rfl

theorem sigR_inclEAf (D : D7) (e : D.host.E) :
    Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) (inclEAf D e) = inclEAf D (D.sp.cm.sig e) := rfl

end GlobalTheory.FrameTransport.Onto

namespace GlobalTheory.FrameTransport.Onto

theorem cT_map_inclEAf (D : D7) {n : ℕ} (A : Matrix (Fin n) (Fin n) D.host.E) :
    (Formalism.UG.cT (↑D.sp.cm.sig) A).map (inclEAf D) =
      Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) (A.map (inclEAf D)) := by
  ext i j
  exact (sigR_inclEAf D (A j i)).symm

theorem cT_map_adSwap (D : D7) {n : ℕ} (A : Matrix (Fin n) (Fin n) (StandardLatticesGL3.AE D)) :
    (Formalism.UG.cT (StandardLatticesGL3.sgA D) A).map (adSwap D) =
      Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) (A.map (adSwap D)) := by
  ext i j
  exact adSwap_sgA D (A j i)

theorem conj_unitary {R : Type} [CommRing R] (s : R →+* R) {n : ℕ} (J P Pi M : Matrix (Fin n) (Fin n) R)
    (hPPi : P * Pi = 1) (hP : Formalism.UG.cT s P * J * P = 1) (hM : Formalism.UG.cT s M * J * M = J) :
    Formalism.UG.cT s (Pi * M * P) * (Pi * M * P) = 1 := by
  have h2 : Formalism.UG.cT s Pi * Formalism.UG.cT s P = 1 := by rw [← Formalism.UG.cT_mul, hPPi, Formalism.UG.cT_one]
  have hJ : J = Formalism.UG.cT s Pi * Pi := by
    calc J = (Formalism.UG.cT s Pi * Formalism.UG.cT s P) * J * (P * Pi) := by rw [h2, hPPi, Matrix.one_mul, Matrix.mul_one]
      _ = Formalism.UG.cT s Pi * (Formalism.UG.cT s P * J * P) * Pi := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hP, Matrix.mul_one]
  rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul, ← hP]
  calc _ = Formalism.UG.cT s P * (Formalism.UG.cT s M * (Formalism.UG.cT s Pi * Pi) * M) * P := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [← hJ, hM]

theorem _root_.GlobalTheory.FrameTransport.exists_frConj_eq : ∀ {D : D7} (V : HSp D) (fr : GL (Fin V.rank) D.host.E), Formalism.UG.cT (↑D.sp.cm.sig) (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * V.gram * (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = 1 → ∀ M : GL (Fin V.rank) (Lev.EAf D), M ∈ UA D.sp.cm V.gram → ∃ h : StandardLatticesGL3.GA D V.rank, GlobalTheory.FrameTransport.frConj fr h.1 = M := by
  intro D V fr hfr M hM
  let P : GL (Fin V.rank) (Lev.EAf D) := Formalism.UG.bc (inclEAf D) fr
  let N : GL (Fin V.rank) (Lev.EAf D) := P⁻¹ * M * P
  let h0 : GL (Fin V.rank) (StandardLatticesGL3.AE D) := Formalism.UG.bc (adSwapEquiv D).symm.toRingHom N
  have hbc : Formalism.UG.bc (adSwap D) h0 = N := by
    ext i j
    show adSwap D ((adSwapEquiv D).symm _) = _
    rw [← adSwapEquiv_apply, RingEquiv.apply_symm_apply]
  have hbcm : h0.val.map (adSwap D) = N.val := congrArg Units.val hbc
  have hPPi : P.val * (P⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hfr' : Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) P.val * V.gram.map (inclEAf D) * P.val = 1 := by
    have := congrArg (fun X => X.map (inclEAf D)) hfr
    simp only [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at this
    rw [cT_map_inclEAf] at this
    exact this
  have hN : Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) N.val * N.val = 1 := by
    have hNv : N.val = (P⁻¹).val * M.val * P.val := by simp only [N, Units.val_mul]
    rw [hNv]
    exact conj_unitary _ _ _ _ _ hPPi hfr' hM
  refine ⟨⟨h0, ?_⟩, ?_⟩
  · show Formalism.UG.cT (StandardLatticesGL3.sgA D) h0.val *
        (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (Formalism.UG.inclE (F := ℚ) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) *
        h0.val = (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (Formalism.UG.inclE (F := ℚ) (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ))
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one]
    apply Matrix.map_injective (adSwapEquiv D).injective
    change (Formalism.UG.cT (StandardLatticesGL3.sgA D) h0.val * h0.val).map (adSwap D) =
      (1 : Matrix (Fin V.rank) (Fin V.rank) (StandardLatticesGL3.AE D)).map (adSwap D)
    rw [Matrix.map_mul, cT_map_adSwap, hbcm, hN, Matrix.map_one _ (map_zero _) (map_one _)]
  · show frConj fr h0 = M
    rw [frConj_apply, hbc]
    show P * (P⁻¹ * M * P) * P⁻¹ = M
    group

end GlobalTheory.FrameTransport.Onto
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStandardUnitaryFrameConjEqStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_standardUnitary_frameConj_eq : ∀ {D : D7} (V : HSp D) (fr : GL (Fin V.rank) D.host.E), Formalism.UG.cT (↑D.sp.cm.sig) (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * V.gram * (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = 1 → ∀ M : GL (Fin V.rank) (Lev.EAf D), M ∈ UA D.sp.cm V.gram → ∃ h : StandardLatticesGL3.GA D V.rank, GlobalTheory.FrameTransport.frConj fr h.1 = M := by
  first | exact @GlobalTheory.FrameTransport.exists_frConj_eq | exact GlobalTheory.FrameTransport.exists_frConj_eq | (intros; apply GlobalTheory.FrameTransport.exists_frConj_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameConjStandardRationalMemUnitaryRational
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameConjStandardRationalMemUnitaryRational
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport

noncomputable section

namespace GlobalTheory.FrameTransport

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem toAfE_inc (D : D7) (x : D.host.E) :
    GlobalTheory.BotFormula.toAfE D (StandardLatticesGL3.inc D x) = (1 : Af D.host.F) ⊗ₜ[D.host.F] x := by
  have h1 : GlobalTheory.LFun.finAdEquiv D.host.F D.host.E ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) =
      algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x :=
    (GlobalTheory.LFun.toFinAd_tmul (1 : Af D.host.F) x).trans (by rw [map_one, one_mul])
  have h2 : GlobalTheory.BotFormula.toFinE D (StandardLatticesGL3.inc D x) = algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x :=
    (GlobalTheory.LFun.toFinAd_tmul (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) x).trans (by rw [map_one, one_mul])
  show (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).symm (GlobalTheory.BotFormula.toFinE D (StandardLatticesGL3.inc D x)) = _
  rw [h2, ← h1, RingEquiv.symm_apply_apply]

theorem adSwap_inc (D : D7) (x : D.host.E) : adSwap D (StandardLatticesGL3.inc D x) = inclEAf D x := by
  show Lev.swapAE D (GlobalTheory.BotFormula.toAfE D (StandardLatticesGL3.inc D x)) = _
  rw [toAfE_inc]
  rfl

theorem finE_val_of_isRat {D : D7} {V : HSp D} {g : GA D V} {a : Matrix (Fin V.rank) (Fin V.rank) D.host.E}
    (h : GlobalTheory.RatAut.IsRat V g a) :
    (Lev.finE V g).val = a.map (inclEAf D) := by
  have e : (Lev.finE V g).val =
      (Formalism.L2.Theta.mt V g).map (fun y => Lev.swapAE D
        (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) y)) := rfl
  rw [e, show Formalism.L2.Theta.mt V g = _ from h]
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.map_apply]
  show Lev.swapAE D (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)
    ((1 : AF D.host.F) ⊗ₜ[D.host.F] a i j)) = _
  rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply]
  rfl

theorem frConj_ratG : ∀ {D : D7} (V : HSp D) (fr : GL (Fin V.rank) D.host.E),
    Formalism.UG.cT (↑D.sp.cm.sig) (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * V.gram *
      (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = 1 →
    ∀ γ ∈ GlobalTheory.NormSum.ratG D V.rank, ∃ q ∈ ratFin V, finG V q = GlobalTheory.FrameTransport.frConj fr γ.1 := by
  intro D V fr hfr
  let S : Subgroup (StandardLatticesGL3.GA D V.rank) :=
    ((ratFin V).map (finG V)).comap ((frConj fr).comp (StandardLatticesGL3.GA D V.rank).subtype)
  suffices hS : GlobalTheory.NormSum.ratG D V.rank ≤ S by
    intro γ hγ
    obtain ⟨q, hq, e⟩ := hS hγ
    exact ⟨q, hq, e⟩
  rw [GlobalTheory.NormSum.ratG, Subgroup.closure_le]
  rintro g ⟨γ₀, hγ₀⟩

  have h1 : (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (StandardLatticesGL3.inc D) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  have hg : ((g.1 : Matrix (Fin V.rank) (Fin V.rank) (StandardLatticesGL3.AE D)).map (StandardLatticesGL3.sgA D)).transpose *
      (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (StandardLatticesGL3.inc D) * (g.1 : Matrix (Fin V.rank) (Fin V.rank) (StandardLatticesGL3.AE D)) =
      (1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (StandardLatticesGL3.inc D) := g.2
  have hc : ((γ₀.map D.host.conj).transpose).map (StandardLatticesGL3.inc D) = ((γ₀.map (StandardLatticesGL3.inc D)).map (StandardLatticesGL3.sgA D)).transpose := by
    ext i j
    simp [StandardLatticesGL3.sgA, StandardLatticesGL3.inc, Formalism.UG.sigR, Formalism.UG.inclE]
  have hu : (γ₀.map D.host.conj).transpose * γ₀ = 1 := by
    apply Matrix.map_injective (GlobalTheory.NormSum.inc_inj D)
    unfold StandardLatticesGL3.IsRat at hγ₀
    rw [hγ₀, h1, Matrix.mul_one, ← hc, ← Matrix.map_mul] at hg
    exact hg.trans h1.symm
  have hu' : γ₀ᴴ * γ₀ = 1 := by
    have : γ₀ᴴ = (γ₀.map D.host.conj).transpose := Matrix.ext fun i j => by
      show star (γ₀ j i) = D.host.conj (γ₀ j i)
      exact Formalism.MainNotions.GlobalTheoryTheory.jnt_sig_eq_conj D (γ₀ j i)
    rw [this, hu]

  set F : Matrix (Fin V.rank) (Fin V.rank) D.host.E := (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) with hF
  set Fi : Matrix (Fin V.rank) (Fin V.rank) D.host.E := (fr⁻¹ : GL (Fin V.rank) D.host.E).val with hFi
  have hFFi : F * Fi = 1 := by rw [hF, hFi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hfr' : Fᴴ * V.gram * F = 1 := hfr
  have hJ : V.gram = Fiᴴ * Fi := by
    have := congrArg (fun M => Fiᴴ * M * Fi) hfr'
    simp only [Matrix.mul_one] at this
    rw [← this, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, hFFi, Matrix.conjTranspose_one,
      Matrix.one_mul, Matrix.mul_assoc, hFFi, Matrix.mul_one]
  set a : Matrix (Fin V.rank) (Fin V.rank) D.host.E := F * γ₀ * Fi with ha
  have hau : aᴴ * V.gram * a = V.gram := by
    have e1 : aᴴ * V.gram * a = Fiᴴ * γ₀ᴴ * (Fᴴ * V.gram * F) * γ₀ * Fi := by
      rw [ha, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    rw [e1, hfr', Matrix.mul_one, Matrix.mul_assoc Fiᴴ, hu', Matrix.mul_one, hJ]
  obtain ⟨g', hg'Q, hg'⟩ := GlobalTheory.RatAut.exists_of_unitary V hau
  obtain ⟨k, k1, k2⟩ := GlobalTheory.UnitarySplit.ga_glue V 1 (finHom V g') (one_mem _) (GlobalTheory.UnitarySplit.finHom_mem V g')
  have hkC : k ∈ GfC V := MonoidHom.mem_ker.2 k1
  have hfin : finG V ⟨k, hkC⟩ = Lev.finE V g' := by
    show Formalism.UG.bc (Lev.swapAE D) (finHom V k) = Formalism.UG.bc (Lev.swapAE D) (finHom V g')
    rw [k2]
  refine ⟨⟨k, hkC⟩, ⟨g', hg'Q, hfin.symm⟩, ?_⟩
  show finG V ⟨k, hkC⟩ = frConj fr g.1
  rw [hfin, frConj_apply]
  apply Units.ext
  rw [finE_val_of_isRat hg', ← map_inv, Units.val_mul, Units.val_mul]
  have eb : ∀ (M : GL (Fin V.rank) D.host.E),
      (Formalism.UG.bc (inclEAf D) M).val = M.val.map (inclEAf D) := fun M => rfl
  have eg : (Formalism.UG.bc (adSwap D) g.1).val =
      γ₀.map (inclEAf D) := by
    show g.1.val.map (adSwap D) = _
    unfold StandardLatticesGL3.IsRat at hγ₀
    rw [hγ₀, Matrix.map_map]
    exact Matrix.ext fun i j => adSwap_inc D (γ₀ i j)
  rw [eb, eb, eg, ha, Matrix.map_mul, Matrix.map_mul]

end GlobalTheory.FrameTransport
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameConjStandardRationalMemUnitaryRationalStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
open GlobalTheory.FrameTransport
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameConj_standardRational_mem_unitaryRational : ∀ {D : D7} (V : HSp D) (fr : GL (Fin V.rank) D.host.E), Formalism.UG.cT (↑D.sp.cm.sig) (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * V.gram * (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = 1 → ∀ γ ∈ GlobalTheory.NormSum.ratG D V.rank, ∃ q ∈ ratFin V, finG V q = GlobalTheory.FrameTransport.frConj fr γ.1 := by
  first | exact @GlobalTheory.FrameTransport.frConj_ratG | exact GlobalTheory.FrameTransport.frConj_ratG | (intros; apply GlobalTheory.FrameTransport.frConj_ratG <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteVertexClassesCardLePrincipalCongruence
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount

namespace GlobalTheory.FrameTransport


open GlobalTheory.FrameTransport in
theorem exists_surj_cls {D : D7} (V : HSp D) (fr : GL (Fin V.rank) D.host.E)
    (hfr : Formalism.UG.cT (↑D.sp.cm.sig) (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) * V.gram *
      (fr : Matrix (Fin V.rank) (Fin V.rank) D.host.E) = 1)
    (u : GfC V) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hu : ∀ v, v ∈ Formalism.L2.Herm.hatL (colLat fr) ↔ (finG V u).val *ᵥ v ∈ Formalism.L2.Herm.hatL Λ)
    (𝔪 : Ideal (𝓞 D.host.E)) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D)))
    (hK : congLev D.sp.cm V.gram Λ 𝔪 ≤ K) :
    ∃ f : GlobalTheory.NormSum.Cls D V.rank (GlobalTheory.FunObj.StdDatum.congLev D 𝔪 V.rank) → FinCl V K, Function.Surjective f := by
  classical
  obtain ⟨uf, huf_def⟩ : ∃ uf, uf = finG V u := ⟨_, rfl⟩
  rw [← huf_def] at hu
  have hufU : uf ∈ UA D.sp.cm V.gram := by rw [huf_def]; exact GlobalTheory.LevSplit.finE_mem_UA V u.1
  have lift : ∀ h : StandardLatticesGL3.GA D V.rank, ∃ g : GfC V, finG V g = frConj fr h.1 * uf⁻¹ := fun h =>
    GlobalTheory.T.exists_realTrivial_point_finiteAdelicHom_eq V _ (mul_mem (GlobalTheory.T.frameConj_standardUnitary_mem_unitaryFiniteAdelic V fr hfr h) (inv_mem hufU))
  choose φ hφ using lift

  have hC : ∀ c ∈ GlobalTheory.FunObj.StdDatum.congLev D 𝔪 V.rank, uf * frConj fr c.1 * uf⁻¹ ∈ K := by
    let ρ : StandardLatticesGL3.GA D V.rank →* GL (Fin V.rank) (Lev.EAf D) :=
      (MulAut.conj uf).toMonoidHom.comp ((frConj fr).comp (StandardLatticesGL3.GA D V.rank).subtype)
    have hle : GlobalTheory.FunObj.StdDatum.congLev D 𝔪 V.rank ≤ K.comap ρ := by
      refine (Subgroup.closure_le _).2 fun k hk => ?_
      have hU : uf * frConj fr k.1 * uf⁻¹ ∈ UA D.sp.cm V.gram :=
        mul_mem (mul_mem hufU (GlobalTheory.T.frameConj_standardUnitary_mem_unitaryFiniteAdelic V fr hfr k)) (inv_mem hufU)
      exact hK (GlobalTheory.T.frameConjugate_principalCongruence_mem_latticeCongruence V fr uf Λ hu 𝔪 k hk.1 hk.2 hU)
    intro c hc
    exact hle hc
  refine ⟨fun q => DoubleCoset.mk (ratFin V) (K.comap (finG V)) (φ (Quotient.out q)), ?_⟩
  intro p
  obtain ⟨x, rfl⟩ : ∃ x, DoubleCoset.mk (ratFin V) (K.comap (finG V)) x = p := ⟨Quotient.out p, DoubleCoset.out_eq' p⟩
  obtain ⟨h, hh⟩ := GlobalTheory.T.exists_standardUnitary_frameConj_eq V fr hfr (finG V x * uf) (mul_mem (GlobalTheory.LevSplit.finE_mem_UA V x.1) hufU)
  refine ⟨DoubleCoset.mk (GlobalTheory.NormSum.ratG D V.rank) (GlobalTheory.FunObj.StdDatum.congLev D 𝔪 V.rank) h, ?_⟩
  show DoubleCoset.mk (ratFin V) (K.comap (finG V)) (φ (Quotient.out (DoubleCoset.mk (GlobalTheory.NormSum.ratG D V.rank) (GlobalTheory.FunObj.StdDatum.congLev D 𝔪 V.rank) h))) = _
  obtain ⟨γ, hγ, c, hc, e⟩ := (@DoubleCoset.eq _ _ _ _ _ _).1
    (DoubleCoset.out_eq'
      (DoubleCoset.mk (GlobalTheory.NormSum.ratG D V.rank) (GlobalTheory.FunObj.StdDatum.congLev D 𝔪 V.rank) h))
  generalize Quotient.out (DoubleCoset.mk (GlobalTheory.NormSum.ratG D V.rank) (GlobalTheory.FunObj.StdDatum.congLev D 𝔪 V.rank) h) = h' at e ⊢
  obtain ⟨q, hq, hqe⟩ := GlobalTheory.T.frameConj_standardRational_mem_unitaryRational V fr hfr γ hγ
  obtain ⟨k, hk⟩ := GlobalTheory.T.exists_realTrivial_point_finiteAdelicHom_eq V (uf * frConj fr c.1 * uf⁻¹)
    (mul_mem (mul_mem hufU (GlobalTheory.T.frameConj_standardUnitary_mem_unitaryFiniteAdelic V fr hfr c)) (inv_mem hufU))
  refine (@DoubleCoset.eq _ _ _ _ _ _).2 ⟨q, hq, k, ?_, ?_⟩
  · show finG V k ∈ K
    rw [hk]; exact hC c hc
  · apply finG_injective V
    have e1 : finG V x = frConj fr h.1 * uf⁻¹ := by rw [hh]; group
    have e2 : frConj fr h.1 = frConj fr γ.1 * frConj fr h'.1 * frConj fr c.1 := by
      rw [e]; simp only [Subgroup.coe_mul, map_mul]
    have e3 := hφ h'
    simp only [map_mul, hqe, e3, hk, e1, e2]
    group

theorem finCl_card_le : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {U : Set T}, Std G U → ∀ X : Node, DefNode D.R.m X → ∀ 𝔪 : Ideal (𝓞 D.host.E), 𝔪 ≠ ⊥ → ∀ K : Subgroup (GL (Fin (G.V X).rank) (Lev.EAf D)), congLev D.sp.cm (G.V X).gram (G.Λ X) 𝔪 ≤ K → (Nat.card (FinCl (G.V X) K) : ℝ) ≤ hBd D (G.V X).rank * (Ideal.absNorm 𝔪 : ℝ) ^ ((G.V X).rank ^ 2) := by
  intro D T L sc G U hS X hX 𝔪 h𝔪 K hK
  obtain ⟨f, hf⟩ := exists_surj_cls (G.V X) (hS.fr X) (hS.fr_on X hX) (hS.u X) (G.Λ X) (hS.u_lat X hX) 𝔪 K hK
  obtain ⟨-, hI, hJ⟩ := GlobalTheory.NormSum.cls_finite_card_le D (G.V X).rank
  obtain ⟨hne, hle⟩ := GlobalTheory.congLev_relIndex_le D 𝔪 h𝔪 (G.V X).rank
  obtain ⟨hfin, hcard⟩ := hJ _ (GlobalTheory.FunObj.StdDatum.congLev_le 𝔪 _) hne
  have h1 := Nat.card_le_card_of_surjective f hf
  have hI' : (Nat.card (GlobalTheory.NormSum.Cls D (G.V X).rank (GlobalTheory.NormSum.intG D (G.V X).rank)) : ℝ) ≤ hBd D (G.V X).rank := hI
  calc (Nat.card (FinCl (G.V X) K) : ℝ)
      ≤ (Nat.card (GlobalTheory.NormSum.Cls D (G.V X).rank (GlobalTheory.FunObj.StdDatum.congLev D 𝔪 (G.V X).rank)) : ℝ) := by
        exact_mod_cast h1
    _ ≤ (Nat.card (GlobalTheory.NormSum.Cls D (G.V X).rank (GlobalTheory.NormSum.intG D (G.V X).rank)) : ℝ) *
          ((GlobalTheory.FunObj.StdDatum.congLev D 𝔪 (G.V X).rank).relIndex (GlobalTheory.NormSum.intG D (G.V X).rank) : ℝ) := by
        exact_mod_cast hcard
    _ ≤ hBd D (G.V X).rank * (Ideal.absNorm 𝔪 : ℝ) ^ ((G.V X).rank ^ 2) := by
        apply mul_le_mul hI' (by exact_mod_cast hle) (by positivity)
        exact le_trans (Nat.cast_nonneg _) hI'

end GlobalTheory.FrameTransport

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteVertexClassesCardLePrincipalCongruenceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteVertexClasses_card_le_principalCongruence : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {U : Set T}, Std G U → ∀ X : Node, DefNode D.R.m X → ∀ 𝔪 : Ideal (𝓞 D.host.E), 𝔪 ≠ ⊥ → ∀ K : Subgroup (GL (Fin (G.V X).rank) (Lev.EAf D)), congLev D.sp.cm (G.V X).gram (G.Λ X) 𝔪 ≤ K → (Nat.card (FinCl (G.V X) K) : ℝ) ≤ hBd D (G.V X).rank * (Ideal.absNorm 𝔪 : ℝ) ^ ((G.V X).rank ^ 2) := by
  first | exact @GlobalTheory.FrameTransport.finCl_card_le | exact GlobalTheory.FrameTransport.finCl_card_le | (intros; apply GlobalTheory.FrameTransport.finCl_card_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalCongruenceLeTopLevelClassSum
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalCongruenceLeTopLevelClassSum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.LevTopCong

open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx

theorem KO_le_symPr {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {G : Grid k} (hs : 1 ≤ G.s) (J : G.Level) (g : G.VertexGroup) {j : ℕ} (hj : j < G.m)
    (hJ : J (G.m, j) = KO k _)
    (hc : ∀ x : GL (Fin (topRank G j)) k, toFrame hs hj (g (G.m, j)) * embX (G.m - 1 - j) x =
      embX (G.m - 1 - j) x * toFrame hs hj (g (G.m, j))) :
    KO k (Fin (topRank G j)) ≤ symPr (conjLevel hs J g hj) := by
  intro x hx
  refine ⟨1, one_mem _, ?_⟩
  rw [one_mul, conjLevel, Subgroup.map_equiv_eq_comap_symm', Subgroup.mem_comap]
  refine ⟨(g (G.m, j))⁻¹ * (toFrame hs hj).symm (embX _ x) * g (G.m, j), ?_, ?_⟩
  · rw [hJ]
    have e : toFrame hs hj ((g (G.m, j))⁻¹ * (toFrame hs hj).symm (embX _ x) * g (G.m, j)) = embX _ x := by
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, mul_assoc, ← hc, ← mul_assoc, inv_mul_cancel, one_mul]
    exact OneCosetProof.mem_KO_of_frameGL _ (by
      have := GlobalTheory.TwistVertex.embX_mem_KO (c := G.m - 1 - j) hx
      rw [← e] at this
      exact this)
  · simp [mul_assoc]

end GlobalTheory.LevTopCong

namespace GlobalTheory.LevTopCong

open GlobalTheory.SplitWeil GlobalTheory.RootEx

theorem diag_comm_embX {k : Type} [Field k] {n : ℕ} {c : ℕ} (d : Fin c → kˣ) (x : GL (Fin n) k) :
    GlobalTheory.SplitFlip.diagGL (Sum.elim (fun _ => (1 : kˣ)) d) * embX c x =
      embX c x * GlobalTheory.SplitFlip.diagGL (Sum.elim (fun _ => (1 : kˣ)) d) := by
  refine Units.ext ?_
  have e : (diagonal fun i => ((Sum.elim (fun _ => (1 : kˣ)) d i : kˣ) : k)) =
      fromBlocks (1 : Matrix (Fin n) (Fin n) k) 0 0 (diagonal fun p => (d p : k)) := by
    ext (i | i) (j | j) <;> simp [Matrix.diagonal_apply, Matrix.one_apply]
  have hx : (embX c x).val = fromBlocks x.val 0 0 1 := rfl
  rw [Units.val_mul, Units.val_mul, GlobalTheory.SplitFlip.diagGL_val, e, hx, fromBlocks_multiply, fromBlocks_multiply]
  simp

end GlobalTheory.LevTopCong

namespace GlobalTheory.LevTopCong

open GlobalTheory.SplitWeil GlobalTheory.RootEx

theorem KO_le_pr_stair {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] {G : GlobalTheory.SplitFlip.Grid k} (hs : 1 ≤ G.s) (J : G.Level)
    (hJ : ∀ j, 0 < j → j < G.m → J (G.m, j) = KO k _) (ϖ : kˣ) (e : ℕ) (β : Cosets hs J)
    (hβ : ∀ i, β i = DoubleCoset.mk _ _ (stair G ϖ e (i + 1))) {j : ℕ} (hj0 : 0 < j) (hj : j < G.m) :
    KO k (Fin (topRank G j)) ≤ symPr (conjLevel hs J ((Reps.through hs J (stair G ϖ e)).elt β) hj) := by
  refine KO_le_symPr hs J _ hj (hJ j hj0 hj) fun x => ?_
  obtain rfl : β = fun i : Fin (G.m - 2) => DoubleCoset.mk _ _ (stair G ϖ e (i + 1)) := funext hβ
  by_cases h2 : j + 2 ≤ G.m
  · rw [through_elt _ h2, toFrame_stair]
    exact diag_comm_embX _ _
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have e1 : (Reps.through hs J (stair G ϖ e)).elt (fun i : Fin (G.m - 2) => DoubleCoset.mk _ _ (stair G ϖ e (i + 1))) (G.m, i + 1) = 1 := by
      rw [Reps.elt, onColumn_apply]
      simp [show ¬ i < G.m - 2 by omega]
    rw [e1, map_one, one_mul, mul_one]

end GlobalTheory.LevTopCong


open GlobalTheory.SplitWeil in
theorem GlobalTheory.LevTopCong.congLev_le_levTop : ∃ CF0 : ℝ, ∀ CF : ℝ, CF0 ≤ CF → ∀ ε : ℝ, ∃ x₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε → x₀ ≤ large₂.sc.x → ∀ (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), HidaSetting large₂ R F → ∀ ch : Choice R, ch.Is → ch.AtScale CF large₂.sc.b → ch.FieldOK → ∀ (Φ : ch.G.Datum), ∀ β ∈ ch.S.supp A.μ0 Φ, ∀ j : Fin D.R.m, congLev D.sp.cm (ch.G.V (.top j)).gram (ch.G.Λ (.top j)) ch.G.modul ≤ ch.S.levTop A.μ0 Φ β j j.2 := by
  obtain ⟨CF0, hB⟩ := GlobalTheory.RowVal.oneAt
  refine ⟨CF0, fun CF hCF ε => ?_⟩
  obtain ⟨x₀, hx⟩ := hB ε CF hCF
  refine ⟨x₀, fun D large₂ hε hx0 Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch hsc _ Φ β hβ j => ?_⟩
  have hone := hx D large₂ hε hx0 Γ Pl0 T A Ks R F s ch hch hsc A.μ0 Φ β hβ
  have hL : R.toLevCh.Is A.μ0 := s.core.lev
  have hQ : R.Q A.μ0 = ∅ := Formalism.IndefR.FWT.Q_base_empty R hL
  obtain ⟨j, hj⟩ := j
  cases j with
  | zero => exact le_rfl
  | succ j =>
    intro g hg
    have hfr := ch.S.βp_is (j + 1) hj.le
    have hSt : g ∈ St (ch.S.βp (j + 1)) :=
      (GlobalTheory.LevSplit.mem_St_iff _ _ hfr g).2 (GlobalTheory.CongMember.stab_of_mem_congLev hg)
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_iInf.2 fun w => ?_,
      Subgroup.mem_iInf.2 fun w' => Subgroup.mem_iInf.2 fun _ => LevRowSucc.KO_of_St rfl _ _ hSt⟩
    have hw0 : w.1 ∈ ch.G.pl.W0 := by
      have h2 := w.2
      simp only [locPl, Finset.mem_union] at h2
      rcases h2 with h2 | h2
      · exact h2
      · have h4 : (w : Pl D.host.E) ∈ R.Q A.μ0 := h2
        rw [hQ] at h4
        exact absurd h4 (Finset.notMem_empty _)
    refine GlobalTheory.LevTopCong.KO_le_pr_stair one_le_sLen _
      (fun i hi0 hi => GlobalTheory.RowVal.givenLevel_inner _ _ _ _ (by change 1 ≤ D.R.m; omega) hi0) _ _ (β w) (hone w hw0)
      j.succ_pos hj ?_
    exact LevRowSucc.KO_of_St _ _ _ hSt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalCongruenceLeTopLevelClassSumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principalCongruence_le_topLevel_classSum : ∃ CF0 : ℝ, ∀ CF : ℝ, CF0 ≤ CF → ∀ ε : ℝ, ∃ x₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε → x₀ ≤ large₂.sc.x → ∀ (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), HidaSetting large₂ R F → ∀ ch : Choice R, ch.Is → ch.AtScale CF large₂.sc.b → ch.FieldOK → ∀ (Φ : ch.G.Datum), ∀ β ∈ ch.S.supp A.μ0 Φ, ∀ j : Fin D.R.m, congLev D.sp.cm (ch.G.V (.top j)).gram (ch.G.Λ (.top j)) ch.G.modul ≤ ch.S.levTop A.μ0 Φ β j j.2 := by
  first | exact @GlobalTheory.LevTopCong.congLev_le_levTop | exact GlobalTheory.LevTopCong.congLev_le_levTop | (intros; apply GlobalTheory.LevTopCong.congLev_le_levTop <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassSumVertexLevelsContainPrincipalCongruence
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassSumVertexLevelsContainPrincipalCongruence
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowLevelCong

variable {D : D7} {T : Type}

theorem gridModulus_le_of_mem_chosenPlaces {L : LevCh D T} {sc : Consts} (G : GridData L sc) {PP : Pl D.host.E} (h : PP ∈ G.pl.W0) :
    G.modul ≤ PP.asIdeal := by
  classical
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h
  calc G.modul = ∏ u ∈ G.pl.S0, (G.pl.w u).asIdeal ^ G.pl.depth sc u := rfl
    _ ≤ (G.pl.w v).asIdeal ^ G.pl.depth sc v := by
        exact Ideal.le_of_dvd (Finset.dvd_prod_of_mem _ hv)
    _ ≤ _ := Ideal.pow_le_self (G.pl.depth_pos sc v).ne'


set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in
theorem congLev_le_lev {L : LevCh D T} {sc : Consts} (G : GridData L sc) {μ₀ : T} (hL : L.Is μ₀) :
    congLev D.sp.cm D.sp.X'.gram L.ΛX G.modul ≤ lev D.sp.cm D.sp.X'.gram L.βX (L.datXt μ₀) := by
  intro x hx
  obtain ⟨c, hc⟩ := hL.βX
  rw [one_pow] at hc
  have hβ : IsFrame L.βX L.ΛX := hc.1
  have hS : x ∈ St L.βX := (GlobalTheory.LevSplit.mem_St_iff _ _ hβ x).2 (GlobalTheory.CongMember.stab_of_mem_congLev hx)
  refine GlobalTheory.LevSplit.mem_lev_of_red _ _ _ _ x hx.1 hS fun PP hP => ?_
  have hPg : PP ∈ L.Pg := by
    rcases hP with h | h
    · exact h
    · exfalso
      refine (hL.Q_ram μ₀ PP).2 (Or.inl h) ?_
      rw [hL.xi_base]
      exact fun _ _ => rfl
  have hle : G.modul ≤ PP.asIdeal := gridModulus_le_of_mem_chosenPlaces G (levelChainTypePlaces_subset_chosenPlaces G hL μ₀ hPg)
  refine GlobalTheory.LevRedTriv.redFn_eq_one_of_cols hβ PP x hS 1 ((Ideal.ne_top_iff_one _).1 PP.isPrime.ne_top) fun j => ?_
  have hz := (hβ (L.βX.1 *ᵥ Pi.single j 1)).2 fun k => by
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Pi.single_apply]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  have h1 := hx.2.2 _ hz
  rw [map_one, Subring.coe_one, one_smul, Matrix.sub_mulVec, Matrix.one_mulVec]
  exact Submodule.span_mono (Set.image_mono (Submodule.smul_mono_left hle)) h1

end GlobalTheory.RowLevelCong

namespace GlobalTheory.ClassCount

open GlobalTheory.RowLevelCong


set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 2000000 in
theorem levRow_congLev_le : ∃ CF0 : ℝ, ∀ CF : ℝ, CF0 ≤ CF → ∀ ε : ℝ, ∃ x₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε →
    x₀ ≤ large₂.sc.x → ∀ (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m) (Ks : Type) [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), HidaSetting large₂ R F → ∀ ch : Choice R, ch.Is →
    ch.AtScale CF large₂.sc.b → ch.FieldOK → ∀ i : Fin (D.R.m + 1),
    congLev D.sp.cm (ch.G.V (.grid i D.R.m)).gram (ch.G.Λ (.grid i D.R.m)) ch.G.modul ≤
      ch.S.levRow A.μ0 i (Nat.le_of_lt_succ i.2) := by
  refine ⟨0, fun CF _ ε => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch _ _ _ i => ?_⟩⟩
  have hL := hS.core.lev
  rcases i with ⟨_ | i, hi⟩
  · show congLev D.sp.cm (ch.G.V (.grid 0 D.R.m)).gram (ch.G.Λ (.grid 0 D.R.m)) ch.G.modul ≤
      ch.S.toGridChoice.levRow A.μ0 0 (Nat.zero_le _)
    have e := GlobalTheory.FunObj.levRow_zero_eq_lev ch.W ch.S.toGridChoice hL A.μ0 (Nat.zero_le _)
    have key : ∀ (Y : LSp D) (K : Subgroup (GL (Fin Y.sp.rank) (Lev.EAf D))), Y = ⟨D.sp.X', R.toLevCh.ΛX⟩ →
        HEq K (lev D.sp.cm D.sp.X'.gram R.toLevCh.βX (R.toLevCh.datXt A.μ0)) →
        congLev D.sp.cm Y.sp.gram Y.lat ch.G.modul ≤ K := by
      rintro _ K rfl e'
      obtain rfl := eq_of_heq e'
      exact congLev_le_lev ch.G hL
    exact (key (ch.G.node (.grid 0 D.R.m)) _ (colY_m _) e).trans inf_le_left
  · show congLev D.sp.cm (ch.G.V (.grid (i + 1) D.R.m)).gram (ch.G.Λ (.grid (i + 1) D.R.m)) ch.G.modul ≤
      ch.S.toGridChoice.levRow A.μ0 (i + 1) (Nat.le_of_lt_succ hi)
    have e := GlobalTheory.FunObj.GridChoice.levRow_succ_inf_UA ch.W ch.S.toGridChoice A.μ0 i (Nat.le_of_lt_succ hi)
    calc congLev D.sp.cm (ch.G.V (.grid (i + 1) D.R.m)).gram (ch.G.Λ (.grid (i + 1) D.R.m)) ch.G.modul
        ≤ ch.G.levMax (.grid (i + 1) D.R.m) := congLev_mono le_top
      _ = ch.S.toGridChoice.levRow A.μ0 (i + 1) (Nat.le_of_lt_succ hi) ⊓ UA D.sp.cm (ch.G.V (.grid (i + 1) D.R.m)).gram := e.symm
      _ ≤ _ := inf_le_left

end GlobalTheory.ClassCount

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassSumVertexLevelsContainPrincipalCongruenceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classSum_vertexLevels_contain_principalCongruence : ∃ CF0 : ℝ, ∀ CF : ℝ, CF0 ≤ CF → ∀ ε : ℝ, ∃ x₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε → x₀ ≤ large₂.sc.x → ∀ (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), HidaSetting large₂ R F → ∀ ch : Choice R, ch.Is → ch.AtScale CF large₂.sc.b → ch.FieldOK → ∀ i : Fin (D.R.m + 1), congLev D.sp.cm (ch.G.V (.grid i D.R.m)).gram (ch.G.Λ (.grid i D.R.m)) ch.G.modul ≤ ch.S.levRow A.μ0 i (Nat.le_of_lt_succ i.2) := by
  first | exact @GlobalTheory.ClassCount.levRow_congLev_le | exact GlobalTheory.ClassCount.levRow_congLev_le | (intros; apply GlobalTheory.ClassCount.levRow_congLev_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTopVertexClassesLeClassNumberBoundNormPow
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTopVertexClassesLeClassNumberBoundNormPow
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount

namespace GlobalTheory.ClassCount

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}


set_option maxHeartbeats 2000000 in
theorem finCl_mk_eq_iff (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (a b : GfC V) :
    DoubleCoset.mk (ratFin V) (K.comap (finG V)) a = DoubleCoset.mk (ratFin V) (K.comap (finG V)) b ↔
      (DoubleCoset.mk (UQ D.sp.cm V.gram) (K.subgroupOf (UA D.sp.cm V.gram)) (GlobalTheory.DefFree.finU V a.1) :
        Cl D.sp.cm V.gram K) = DoubleCoset.mk _ _ (GlobalTheory.DefFree.finU V b.1) := by
  rw [DoubleCoset.eq, DoubleCoset.eq]
  constructor
  · rintro ⟨γ, hγ, k, hk, rfl⟩
    have hγ' : finG V γ ∈ (GQ V).map (Lev.finE V) := hγ
    obtain ⟨γ0, hγ0, e0⟩ := hγ'
    refine ⟨GlobalTheory.DefFree.finU V γ.1, ?_, GlobalTheory.DefFree.finU V k.1, ?_, ?_⟩
    · have : GlobalTheory.DefFree.finU V γ.1 = GlobalTheory.DefFree.finU V γ0 := Subtype.ext e0.symm
      rw [this]
      exact GlobalTheory.DefFree.AdelCls.rat_mem V γ0 hγ0
    · exact Subgroup.mem_subgroupOf.2 hk
    · simp only [Subgroup.coe_mul, map_mul]
  · rintro ⟨q, hq, k, hk, e⟩
    have hq' : q ∈ (GQ V).map (GlobalTheory.DefFree.finU V) := by rw [GlobalTheory.DefFree.AdelCls.map_rat]; exact hq
    obtain ⟨γ0, hγ0, rfl⟩ := hq'
    obtain ⟨γ1, hγ1, e1⟩ := GlobalTheory.DefFree.AdelCls.exists_fin V (GlobalTheory.DefFree.finU V γ0)
    obtain ⟨κ, hκ, e2⟩ := GlobalTheory.DefFree.AdelCls.exists_fin V k
    refine ⟨⟨γ1, hγ1⟩, ?_, ⟨κ, hκ⟩, ?_, ?_⟩
    · refine Subgroup.mem_comap.2 (Subgroup.mem_map.2 ⟨γ0, hγ0, ?_⟩)
      exact (congrArg Subtype.val e1).symm
    · refine Subgroup.mem_comap.2 ?_
      have := Subgroup.mem_subgroupOf.1 hk
      rw [← e2] at this
      exact this
    · apply Subtype.ext
      have hx : (b.1)⁻¹ * (γ1 * a.1 * κ) ∈ GinfC V := by
        rw [← GlobalTheory.DefFree.AdelCls.finU_eq_one_iff, MonoidHom.map_mul, MonoidHom.map_inv, MonoidHom.map_mul, MonoidHom.map_mul,
          e1, e2, e]
        exact inv_mul_cancel _
      have hy : (b.1)⁻¹ * (γ1 * a.1 * κ) ∈ GfC V :=
        (GfC V).mul_mem ((GfC V).inv_mem b.2) ((GfC V).mul_mem ((GfC V).mul_mem hγ1 a.2) hκ)
      exact inv_mul_eq_one.1 (GlobalTheory.AutFunCounterexample.GfC_inf_GinfC V hy hx)

theorem card_finCl_eq (V : HSp D) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) :
    Nat.card (FinCl V K) = Nat.card (Cl D.sp.cm V.gram K) := by
  let f : FinCl V K → Cl D.sp.cm V.gram K := Quotient.lift
    (fun x : GfC V => (DoubleCoset.mk (UQ D.sp.cm V.gram) (K.subgroupOf (UA D.sp.cm V.gram)) (GlobalTheory.DefFree.finU V x.1) :
      Cl D.sp.cm V.gram K))
    (fun a b h => (finCl_mk_eq_iff V K a b).1 ((DoubleCoset.eq'').2 h))
  refine Nat.card_eq_of_bijective f ⟨fun c c' h => ?_, fun c => ?_⟩
  · induction c using Quotient.inductionOn with | h a => ?_
    induction c' using Quotient.inductionOn with | h b => ?_
    exact (finCl_mk_eq_iff V K a b).2 h
  · induction c using Quotient.inductionOn with | h x => ?_
    obtain ⟨h, hh, e⟩ := GlobalTheory.DefFree.AdelCls.exists_fin V x
    exact ⟨DoubleCoset.mk _ _ (⟨h, hh⟩ : GfC V), by
      show (DoubleCoset.mk _ _ (GlobalTheory.DefFree.finU V h) : Cl D.sp.cm V.gram K) = _
      rw [e]⟩

theorem card_clPlus_le : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {U : Set T}, Std G U →
    (Nat.card G.ClPlus : ℝ) ≤ hBd D (G.V (.top 0)).rank * (Ideal.absNorm G.modul : ℝ) ^ ((G.V (.top 0)).rank ^ 2) := by
  intro D T L sc G U hS
  have h := GlobalTheory.T.definiteVertexClasses_card_le_principalCongruence G hS (.top 0) (Nat.zero_le _) G.modul (G.pl.modul_ne_bot sc) G.Kplus le_rfl
  rw [card_finCl_eq] at h
  exact h

end GlobalTheory.ClassCount

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTopVertexClassesLeClassNumberBoundNormPowStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_topVertexClasses_le_classNumberBound_norm_pow : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) {U : Set T}, Std G U → (Nat.card G.ClPlus : ℝ) ≤ hBd D (G.V (.top 0)).rank * (Ideal.absNorm G.modul : ℝ) ^ ((G.V (.top 0)).rank ^ 2) := by
  first | exact @GlobalTheory.ClassCount.card_clPlus_le | exact GlobalTheory.ClassCount.card_clPlus_le | (intros; apply GlobalTheory.ClassCount.card_clPlus_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsNormGridModulusLeExpDepthLogNormSum
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsNormGridModulusLeExpDepthLogNormSum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount

noncomputable section

namespace GlobalTheory.ModulNorm

open GlobalTheory.SumSize

theorem absNorm_map_of_finrank_two {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (h2 : Module.finrank F E = 2) (I : Ideal (𝓞 F)) :
    Ideal.absNorm (Ideal.map (algebraMap (𝓞 F) (𝓞 E)) I) = Ideal.absNorm I ^ 2 := by
  rw [Ideal.absNorm_algebraMap, ← h2]
  congr 1
  exact (IsFractionRing.finrank_eq (𝓞 F) F (𝓞 E) E).symm

theorem absNorm_le_sq_of_under {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (h2 : Module.finrank F E = 2) (P : HeightOneSpectrum (𝓞 E)) :
    Ideal.absNorm P.asIdeal ≤ Ideal.absNorm (P.under (𝓞 F)).asIdeal ^ 2 := by
  have hle : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (P.under (𝓞 F)).asIdeal ≤ P.asIdeal :=
    Ideal.map_le_iff_le_comap.2 le_rfl
  have hd := Ideal.absNorm_dvd_absNorm_of_le hle
  rw [absNorm_map_of_finrank_two h2] at hd
  refine Nat.le_of_dvd (pow_pos (Nat.pos_of_ne_zero ?_) 2) hd
  rw [Ne, Ideal.absNorm_eq_zero_iff]
  exact (P.under (𝓞 F)).ne_bot

theorem absNorm_modul_le : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc), D.host.F = maximalRealSubfield D.host.E → (Ideal.absNorm G.modul : ℝ) ≤ Real.exp (2 * sig G) := by
  intro D T L sc G hF
  have h2 : Module.finrank D.host.F D.host.E = 2 := by
    rw [hF]; exact Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have hmod : G.modul = ∏ v ∈ G.pl.S0, (G.pl.w v).asIdeal ^ G.pl.depth sc v := rfl
  rw [hmod, map_prod, Nat.cast_prod, sig, Finset.mul_sum, Real.exp_sum]
  refine Finset.prod_le_prod₀ (fun v _ => by positivity) fun v hv => ?_
  have hw : Ideal.absNorm (G.pl.w v).asIdeal ≤ Ideal.absNorm v.asIdeal ^ 2 := by
    have := absNorm_le_sq_of_under h2 (G.pl.w v)
    rwa [G.pl.under_w hv] at this
  have hpos : (0 : ℝ) < Ideal.absNorm v.asIdeal := by
    have : Ideal.absNorm v.asIdeal ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
    exact_mod_cast Nat.pos_of_ne_zero this
  rw [map_pow, Nat.cast_pow]
  calc ((Ideal.absNorm (G.pl.w v).asIdeal : ℕ) : ℝ) ^ G.pl.depth sc v
      ≤ ((Ideal.absNorm v.asIdeal : ℝ) ^ 2) ^ G.pl.depth sc v := by
        gcongr
        exact_mod_cast hw
    _ = Real.exp (2 * ((G.pl.depth sc v : ℝ) * Real.log (Ideal.absNorm v.asIdeal))) := by
        rw [← pow_mul, ← Real.rpow_natCast, Real.rpow_def_of_pos hpos]
        congr 1
        push_cast
        ring

end GlobalTheory.ModulNorm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsNormGridModulusLeExpDepthLogNormSumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.ClassCount
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absNorm_gridModulus_le_exp_depthLogNormSum : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc), D.host.F = maximalRealSubfield D.host.E → (Ideal.absNorm G.modul : ℝ) ≤ Real.exp (2 * sig G) := by
  first | exact @GlobalTheory.ModulNorm.absNorm_modul_le | exact GlobalTheory.ModulNorm.absNorm_modul_le | (intros; apply GlobalTheory.ModulNorm.absNorm_modul_le <;> assumption)
end
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.TestLat GlobalTheory.SumSize GlobalTheory.RowClaim

namespace GlobalTheory.ClassCount


end GlobalTheory.ClassCount

end
