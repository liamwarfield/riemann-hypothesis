module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartFunctionalEqOfAgreeBadPlacesAllSteps
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColumnLastStepLocalFactorTwistPrimeLaw
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MuCharacterDetLevelEqLocalTameProduct

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepCharacterAtLevelDetMulLocalCharacters
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepCharacterAtLevelDetMulLocalCharacters
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TopMuDet

open Matrix
open scoped TensorProduct

section Cong

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
  {P : HeightOneSpectrum (𝓞 E)}

theorem intAtA_add {a b : E ⊗[F] FiniteAdeleRing (𝓞 F) F} (ha : IntAtA (F := F) P a) (hb : IntAtA (F := F) P b) :
    IntAtA (F := F) P (a + b) := by
  obtain ⟨s, hs, h1⟩ := ha
  obtain ⟨r, hr, h2⟩ := hb
  have hi : ∀ x : 𝓞 E, iA F E (algebraMap (𝓞 E) E x) ∈ Formalism.L2.Herm.intAf F E := fun x => (toRInt F E x).2
  refine ⟨s * r, fun h => (P.isPrime.mem_or_mem h).elim hs hr, ?_⟩
  have e : iA F E (algebraMap (𝓞 E) E (s * r)) * (a + b) =
      iA F E (algebraMap (𝓞 E) E r) * (iA F E (algebraMap (𝓞 E) E s) * a) +
        iA F E (algebraMap (𝓞 E) E s) * (iA F E (algebraMap (𝓞 E) E r) * b) := by
    rw [map_mul, map_mul]; ring
  rw [e]
  exact add_mem (mul_mem (hi r) h1) (mul_mem (hi s) h2)

theorem intAtA_mul {a b : E ⊗[F] FiniteAdeleRing (𝓞 F) F} (ha : IntAtA (F := F) P a) (hb : IntAtA (F := F) P b) :
    IntAtA (F := F) P (a * b) := by
  obtain ⟨s, hs, h1⟩ := ha
  obtain ⟨r, hr, h2⟩ := hb
  refine ⟨s * r, fun h => (P.isPrime.mem_or_mem h).elim hs hr, ?_⟩
  have e : iA F E (algebraMap (𝓞 E) E (s * r)) * (a * b) =
      (iA F E (algebraMap (𝓞 E) E s) * a) * (iA F E (algebraMap (𝓞 E) E r) * b) := by
    rw [map_mul, map_mul]; ring
  rw [e]
  exact mul_mem h1 h2

theorem intAtA_int (x : 𝓞 E) : IntAtA (F := F) P (iA F E (algebraMap (𝓞 E) E x)) :=
  ⟨1, fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by
    rw [map_one, map_one, one_mul]; exact (toRInt F E x).2⟩

def intAtSub (P : HeightOneSpectrum (𝓞 E)) :
    Subring (E ⊗[F] FiniteAdeleRing (𝓞 F) F) where
  carrier := {a | IntAtA (F := F) P a}
  mul_mem' := intAtA_mul
  one_mem' := by simpa using intAtA_int (F := F) (P := P) 1
  add_mem' := intAtA_add
  zero_mem' := by simpa using intAtA_int (F := F) (P := P) 0
  neg_mem' := by
    intro a ha
    have := intAtA_mul (intAtA_int (F := F) (P := P) (-1)) ha
    simpa using this

theorem det_congAt {d : ℕ} (hd : 1 ≤ d) {k : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)} (h : CongAt P d k) :
    IntAtA (F := F) P (iA F E ((qOf P : ℕ) : E)⁻¹ *
      (((Matrix.GeneralLinearGroup.det k : (E ⊗[F] FiniteAdeleRing (𝓞 F) F)ˣ) : E ⊗[F] FiniteAdeleRing (𝓞 F) F) - 1)) := by
  classical
  set S := intAtSub (F := F) P with hS
  have hq : ((qOf P : ℕ) : E) ≠ 0 := by
    have : qOf P ≠ 0 := fun h0 => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    exact_mod_cast this
  set Q := iA F E ((qOf P : ℕ) : E) with hQ
  have hcQ : iA F E ((qOf P : ℕ) : E)⁻¹ * Q = 1 := by rw [hQ, ← map_mul, inv_mul_cancel₀ hq, map_one]
  have hQS : Q ∈ S := by
    have := intAtA_int (F := F) (P := P) ((qOf P : ℕ) : 𝓞 E)
    simpa [hQ] using this
  have hZ : ∀ a b, Q ^ (d - 1) * (iA F E (((qOf P : ℕ) : E) ^ d)⁻¹ *
      ((k : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1) a b) ∈ S :=
    fun a b => S.mul_mem (S.pow_mem hQS _) (h a b)
  have hZe : ∀ a b, Q * (Q ^ (d - 1) * (iA F E (((qOf P : ℕ) : E) ^ d)⁻¹ *
      ((k : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1) a b)) =
      ((k : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) - 1) a b := by
    intro a b
    have e : Q * Q ^ (d - 1) * iA F E (((qOf P : ℕ) : E) ^ d)⁻¹ = 1 := by
      rw [← pow_succ', Nat.sub_add_cancel hd, hQ, ← map_pow, ← map_mul, mul_inv_cancel₀ (pow_ne_zero _ hq), map_one]
    rw [← mul_assoc, ← mul_assoc, e, one_mul]
  let Z : Matrix (Fin N) (Fin N) S := fun a b => ⟨_, hZ a b⟩
  let q' : S := ⟨Q, hQS⟩
  let M : Matrix (Fin N) (Fin N) S := 1 + q' • Z
  have hM : M.map S.subtype = (k : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) := by
    ext a b
    have e1 : S.subtype ((1 : Matrix (Fin N) (Fin N) S) a b) = (1 : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) a b := by
      rw [Matrix.one_apply, Matrix.one_apply]; split_ifs <;> simp
    rw [Matrix.map_apply]
    simp only [M]
    rw [Matrix.add_apply, map_add (f := _), e1, Matrix.smul_apply, smul_eq_mul, map_mul]
    show _ + Q * (Q ^ (d - 1) * _) = _
    rw [hZe, Matrix.sub_apply]
    ring_nf
  set I : Ideal S := Ideal.span {q'}
  have hMI : M.map (Ideal.Quotient.mk I) = 1 := by
    ext a b
    have hq0 : Ideal.Quotient.mk I q' = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
    rw [Matrix.map_apply]
    simp only [M]
    rw [Matrix.add_apply, map_add (f := _), Matrix.smul_apply, smul_eq_mul, map_mul, hq0, zero_mul, add_zero,
      Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hdet : Ideal.Quotient.mk I M.det = Ideal.Quotient.mk I 1 := by
    rw [RingHom.map_det, map_one]
    show (M.map (Ideal.Quotient.mk I)).det = 1
    rw [hMI, Matrix.det_one]
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 hdet)
  have hk : ((Matrix.GeneralLinearGroup.det k : (E ⊗[F] FiniteAdeleRing (𝓞 F) F)ˣ) : E ⊗[F] FiniteAdeleRing (𝓞 F) F) =
      S.subtype M.det := by
    rw [RingHom.map_det, Matrix.GeneralLinearGroup.val_det_apply]
    exact congrArg Matrix.det hM.symm
  have e2 : iA F E ((qOf P : ℕ) : E)⁻¹ *
      (((Matrix.GeneralLinearGroup.det k : (E ⊗[F] FiniteAdeleRing (𝓞 F) F)ˣ) : E ⊗[F] FiniteAdeleRing (𝓞 F) F) - 1) = (w : _) := by
    rw [hk, show S.subtype M.det - 1 = S.subtype (M.det - 1) by simp, ← hw, map_mul]
    show iA F E ((qOf P : ℕ) : E)⁻¹ * ((w : _) * Q) = _
    rw [mul_comm (w : E ⊗[F] FiniteAdeleRing (𝓞 F) F), ← mul_assoc, hcQ, one_mul]
  rw [e2]
  exact w.2

end Cong

section Rat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem det_ratA (g : GL (Fin n) E) :
    ((Matrix.GeneralLinearGroup.det (ratA F g) : (E ⊗[F] FiniteAdeleRing (𝓞 F) F)ˣ) : E ⊗[F] FiniteAdeleRing (𝓞 F) F) =
      iA F E ((Matrix.GeneralLinearGroup.det g : Eˣ) : E) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]
  rfl

end Rat

section Frame

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Fields} (s : Seam D X)

theorem det_seamGL {n : ℕ} (g : Sp X.E n ≃ₗ[X.E] Sp X.E n) :
    ((Matrix.GeneralLinearGroup.det (seamGL s g) : D.host.Eˣ) : D.host.E) = s.iE ((LinearEquiv.det g : X.Eˣ) : X.E) := by
  have h : ((seamGL s g : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E) =
      (LinearMap.toMatrix' g.toLinearMap).map (s.iE : X.E →+* D.host.E) := rfl
  rw [Matrix.GeneralLinearGroup.val_det_apply, h, ← RingHom.mapMatrix_apply, ← RingHom.map_det, LinearMap.det_toMatrix',
    LinearEquiv.coe_det]
  rfl

variable {i : ℕ} {SB : Finset (HeightOneSpectrum (𝓞 X.E))} (fb : SB → GL (Fin (D.R.N i)) D.host.E) (dep : SB → ℕ)

theorem det_inFrame {P : SB} {κ : GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)}
    {g : Sp X.E (D.R.N i) ≃ₗ[X.E] Sp X.E (D.R.N i)} (hd : 1 ≤ dep P) (h : InFrame s fb dep P κ g) :
    IntAtA (F := D.host.F) (seamP s P.1) (iA D.host.F D.host.E ((qOf (seamP s P.1) : D.host.E))⁻¹ *
      ((((Matrix.GeneralLinearGroup.det κ)⁻¹ : (AfE D.host.F D.host.E)ˣ) : AfE D.host.F D.host.E) *
        iA D.host.F D.host.E (s.iE ((LinearEquiv.det g : X.Eˣ) : X.E)) - 1)) := by
  have H := det_congAt hd h
  have e : ((Matrix.GeneralLinearGroup.det (((ratA D.host.F (fb P))⁻¹ * κ * ratA D.host.F (fb P))⁻¹ *
      ratA D.host.F (seamGL s g)) : (AfE D.host.F D.host.E)ˣ) : AfE D.host.F D.host.E) =
      (((Matrix.GeneralLinearGroup.det κ)⁻¹ : (AfE D.host.F D.host.E)ˣ) : AfE D.host.F D.host.E) *
        iA D.host.F D.host.E (s.iE ((LinearEquiv.det g : X.Eˣ) : X.E)) := by
    rw [map_mul, map_inv, map_mul, map_mul, map_inv, Units.val_mul, det_ratA, det_seamGL]
    congr 2
    rw [mul_comm, mul_inv_cancel_left]
  rw [← e]
  exact H

end Frame

end GlobalTheory.TopMuDet

end

theorem GlobalTheory.TwTop.muOf_det_top : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => MuLaw t u μ dtU →
  ∀ (hi : t.m2 + 1 + 1 ≤ D.R.m) (β : (St (t.m2 + 1) (Nat.le_of_succ_le hi)).Ch) (β' : (St (t.m2 + 1 + 1) hi).Ch)
    (κ : ((St (t.m2 + 1) (Nat.le_of_succ_le hi)).K β).lev.U) (κ' : ((St (t.m2 + 1 + 1) hi).K β').lev.U)
    (g : SB t μ → (Sp t.X.E (D.R.N (t.m2 + 1)) ≃ₗ[t.X.E] Sp t.X.E (D.R.N (t.m2 + 1)))) (z : SB t μ → t.X.K)
    (g' : SB t μ → (Sp t.X.E (D.R.N (t.m2 + 1 + 1)) ≃ₗ[t.X.E] Sp t.X.E (D.R.N (t.m2 + 1 + 1)))) (z' : SB t μ → t.X.K),
    (∀ P, A.cplRel β P (g P) (z P) ∧ InFrame t.seam (A.fb (t.m2 + 1) (Nat.le_of_succ_le hi) β) (t.cst μ).D P κ.1 (g P)) →
    (∀ P, TopLev t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1 + 1) P (g' P) (z' P) ∧
      InFrame t.seam (A.fb (t.m2 + 1 + 1) hi β') (topDep t.sel (t.tup μ) (t.cst μ)) P κ'.1 (g' P)) →
    muOf t u μ dtU (t.m2 + 1 + 1) (Matrix.GeneralLinearGroup.det κ.1) *
        t.seam.σ₀ (∏ P, rhoS t.Ch t.sel (t.tup μ) (t.m2 + 1) P ((LinearEquiv.det (g P) : t.X.Eˣ) : t.X.E) *
          rhoT t.Ch t.sel (t.tup μ) (t.m2 + 1) P ((LinearEquiv.det (g' P) : t.X.Eˣ) : t.X.E)) =
      muOf t u μ dtU (t.m2 + 1 + 1) (Matrix.GeneralLinearGroup.det κ'.1)) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin hTie hMu hi β β' κ κ' g z g' z' hg hg'
  have hlt : t.m2 + 1 < D.R.m := by omega
  have hok := (t.idx_ok μ).cst_ok
  obtain ⟨h1, -⟩ := GlobalTheory.T.muCharacter_det_level_eq_local_tame_product A dtU a hPin hTie hMu (t.m2 + 1) hlt (t.m2 + 1) (Nat.le_of_succ_le hi) β κ
    (fun P => ((LinearEquiv.det (g P) : t.X.Eˣ) : t.X.E))
    (fun P => GlobalTheory.TopMuDet.det_inFrame t.seam _ _ (hok.D_pos P) (hg P).2)
  have hdep : ∀ P : SB t μ, 1 ≤ topDep t.sel (t.tup μ) (t.cst μ) P := by
    intro P
    unfold topDep
    split_ifs
    · exact le_rfl
    · have := hok.M_pos
      omega
  obtain ⟨-, h2⟩ := GlobalTheory.T.muCharacter_det_level_eq_local_tame_product A dtU a hPin hTie hMu (t.m2 + 1) hlt (t.m2 + 1 + 1) hi β' κ'
    (fun P => ((LinearEquiv.det (g' P) : t.X.Eˣ) : t.X.E))
    (fun P => GlobalTheory.TopMuDet.det_inFrame t.seam _ _ (hdep P) (hg' P).2)
  rw [Finset.prod_mul_distrib, map_mul, ← mul_assoc, h1, one_mul, h2]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepCharacterAtLevelDetMulLocalCharactersStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastStepCharacter_at_levelDet_mul_localCharacters : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => MuLaw t u μ dtU →
  ∀ (hi : t.m2 + 1 + 1 ≤ D.R.m) (β : (St (t.m2 + 1) (Nat.le_of_succ_le hi)).Ch) (β' : (St (t.m2 + 1 + 1) hi).Ch)
    (κ : ((St (t.m2 + 1) (Nat.le_of_succ_le hi)).K β).lev.U) (κ' : ((St (t.m2 + 1 + 1) hi).K β').lev.U)
    (g : SB t μ → (Sp t.X.E (D.R.N (t.m2 + 1)) ≃ₗ[t.X.E] Sp t.X.E (D.R.N (t.m2 + 1)))) (z : SB t μ → t.X.K)
    (g' : SB t μ → (Sp t.X.E (D.R.N (t.m2 + 1 + 1)) ≃ₗ[t.X.E] Sp t.X.E (D.R.N (t.m2 + 1 + 1)))) (z' : SB t μ → t.X.K),
    (∀ P, A.cplRel β P (g P) (z P) ∧ InFrame t.seam (A.fb (t.m2 + 1) (Nat.le_of_succ_le hi) β) (t.cst μ).D P κ.1 (g P)) →
    (∀ P, TopLev t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1 + 1) P (g' P) (z' P) ∧
      InFrame t.seam (A.fb (t.m2 + 1 + 1) hi β') (topDep t.sel (t.tup μ) (t.cst μ)) P κ'.1 (g' P)) →
    muOf t u μ dtU (t.m2 + 1 + 1) (Matrix.GeneralLinearGroup.det κ.1) *
        t.seam.σ₀ (∏ P, rhoS t.Ch t.sel (t.tup μ) (t.m2 + 1) P ((LinearEquiv.det (g P) : t.X.Eˣ) : t.X.E) *
          rhoT t.Ch t.sel (t.tup μ) (t.m2 + 1) P ((LinearEquiv.det (g' P) : t.X.Eˣ) : t.X.E)) =
      muOf t u μ dtU (t.m2 + 1 + 1) (Matrix.GeneralLinearGroup.det κ'.1)) := by
  first | exact @GlobalTheory.TwTop.muOf_det_top | exact GlobalTheory.TwTop.muOf_det_top | (intros; apply GlobalTheory.TwTop.muOf_det_top <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartDatumLevelPrimeInvariantMulLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartDatumLevelPrimeInvariantMulLevel
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwV.PhiTLev


set_option maxHeartbeats 2000000 in
theorem deco_mul_lev : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
    ∀ (j : ℕ) (hj : j ≤ D.R.m) (β : (St j hj).Ch) (x x₁ : UA D j hj) (κ : ((St j hj).K β).lev.U) p p₁,
      x₁.1 = x.1 * κ.1 → IsPtAd A a j hj β x p → IsPtAd A a j hj β x₁ p₁ →
      p₁.deco.1.N = p.deco.1.N ∧ ∀ P : t.Pr.vT (t.word u), ∀ y ∈ p.deco.1.at P.1, p₁.deco.1.f P y = p.deco.1.f P y) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _hPins hTie j hj β x x₁ κ p p₁ hx hp hp₁
  have hL : latCo D.sp (gramN D j hj) (A.crd j hj) a x₁.1 ((St j hj).K β).lev.Lb =
      latCo D.sp (gramN D j hj) (A.crd j hj) a x.1 ((St j hj).K β).lev.Lb := by
    unfold latCo
    rw [hx, Formalism.MainNotions.G.KAat.latAd_stab _ _ _ (hatStab_of_lev _ κ)]
  have hN : p₁.deco.1.N = p.deco.1.N := by
    have h := congrArg (latBack t.seam) ((hp₁.lat.trans hL).trans hp.lat.symm)
    rwa [latBack_seam_lat, latBack_seam_lat] at h
  refine ⟨hN, fun P => ?_⟩
  obtain ⟨v, hov, hTv, -⟩ := FnlAwayCpl.exists_place hTie P
  have hat : p₁.deco.1.at P.1 = p.deco.1.at P.1 := by
    show Formalism.HermitianLatticesTheory.localization₂ _ p₁.deco.1.N = Formalism.HermitianLatticesTheory.localization₂ _ p.deco.1.N
    rw [hN]
  refine FnlAwayCpl.f_eq_on_at p.deco.2 p₁.deco.2 P hat fun w hw hw₁ => ?_
  have H := GlobalTheory.CplPt.funMoved_mul_lev t.seam _ P v (hTv j hj) _ _ _ κ (hp.fnl P v (hTv j hj) hov)
  have e : ratA D.host.F (A.crd j hj) * x₁.1 = ratA D.host.F (A.crd j hj) * x.1 * κ.1 := by
    rw [hx, mul_assoc]
  rw [← e] at H
  have hu₁ : (fun l => t.seam.iE (w l)) ∈ latCo D.sp (gramN D j hj) (A.crd j hj) a x₁.1 ((St j hj).K β).lev.Lb := by
    rw [← hp₁.lat]
    exact Submodule.subset_span ⟨w, hw₁, rfl⟩
  obtain ⟨z, hz⟩ := FnlAwayCpl.exists_latS_pullV D.sp (gramN D j hj) (A.crd j hj) a x₁.1 x₁.2
    (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_gramN_det D j hj) ((St j hj).K β).lev.Lb ((St j hj).K β).lev.Lb_fin
    ((St j hj).K β).lev.Lb_span ((St j hj).K β).lev.Lb_int v _ hu₁
  rw [hp₁.fnl P v (hTv j hj) hov w hw₁ z hz, H w hw z hz]


set_option maxHeartbeats 2000000 in
theorem phiT_mul_lev : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (i : ℕ) (hi : i + 1 ≤ D.R.m) (β : (St i (Nat.le_of_succ_le hi)).Ch) (β' : (St (i + 1) hi).Ch)
    (x x₁ : UA D i (Nat.le_of_succ_le hi)) (x' x₁' : UA D (i + 1) hi)
    (κ : ((St i (Nat.le_of_succ_le hi)).K β).lev.U) (κ' : ((St (i + 1) hi).K β').lev.U),
    x₁.1 = x.1 * κ.1 → x₁'.1 = x'.1 * κ'.1 →
    ∀ p p' p₁ p₁', IsPtAd A a i (Nat.le_of_succ_le hi) β x p → IsPtAd A a (i + 1) hi β' x' p' →
      IsPtAd A a i (Nat.le_of_succ_le hi) β x₁ p₁ → IsPtAd A a (i + 1) hi β' x₁' p₁' →
      ∀ z, phiT t.X.K p₁.deco.1 p₁'.deco.1 z = phiT t.X.K p.deco.1 p'.deco.1 z) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPins hTie i hi β β' x x₁ x' x₁' κ κ' hx hx' p p' p₁ p₁' hp hp' hp₁ hp₁' z
  obtain ⟨hN, hf⟩ := deco_mul_lev A dtU a hPins hTie i (Nat.le_of_succ_le hi) β x x₁ κ p p₁ hx hp hp₁
  obtain ⟨hN', hf'⟩ := deco_mul_lev A dtU a hPins hTie (i + 1) hi β' x' x₁' κ' p' p₁' hx' hp' hp₁'
  unfold phiT
  refine @if_congr _ _ _ (_) (_) _ _ _ _ ?_ rfl rfl
  refine forall_congr' fun P => ?_
  simp only [Deco.at, hN, hN']
  refine forall₂_congr fun y hy => and_congr_right fun hzy => ?_
  rw [hf P y hy, hf' P (z y) hzy]

end GlobalTheory.TwV.PhiTLev
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartDatumLevelPrimeInvariantMulLevelStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartDatum_levelPrime_invariant_mul_level : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (i : ℕ) (hi : i + 1 ≤ D.R.m) (β : (St i (Nat.le_of_succ_le hi)).Ch) (β' : (St (i + 1) hi).Ch)
    (x x₁ : UA D i (Nat.le_of_succ_le hi)) (x' x₁' : UA D (i + 1) hi)
    (κ : ((St i (Nat.le_of_succ_le hi)).K β).lev.U) (κ' : ((St (i + 1) hi).K β').lev.U),
    x₁.1 = x.1 * κ.1 → x₁'.1 = x'.1 * κ'.1 →
    ∀ p p' p₁ p₁', IsPtAd A a i (Nat.le_of_succ_le hi) β x p → IsPtAd A a (i + 1) hi β' x' p' →
      IsPtAd A a i (Nat.le_of_succ_le hi) β x₁ p₁ → IsPtAd A a (i + 1) hi β' x₁' p₁' →
      ∀ z, phiT t.X.K p₁.deco.1 p₁'.deco.1 z = phiT t.X.K p.deco.1 p'.deco.1 z) := by
  first | exact @GlobalTheory.TwV.PhiTLev.phiT_mul_lev | exact GlobalTheory.TwV.PhiTLev.phiT_mul_lev | (intros; apply GlobalTheory.TwV.PhiTLev.phiT_mul_lev <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepLocalFactorLevelValuesTypePrime
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepLocalFactorSourceLawCoupledLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepLocalFactorSourceLawCoupledLevel
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop GlobalTheory.TopStep
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TopLawG

theorem locTopG_source : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}
  {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))}
  {G : ChGlob X R.m} {m2 : ℕ}, X.Ok → Pr.Ok → IsSel X sel → L.Ok Ch sel mu cst G m2 → ∀ (b : L.β (m2 + 1)) (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs →
  ∀ (g : Sp X.E (R.N (m2 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1))) (z : X.K), MidLev Ch sel mu cst (m2 + 1) P (L.h (m2 + 1) b P) g z →
  ∃ Gg : GLint X.E (R.N (m2 + 1)) P.1, Gg.1 = g ∧ ∀ (k : GLint X.E (R.N (m2 + 1)) P.1), redGL _ P.1 k = redGL _ P.1 Gg →
  ∀ (y : HomE X.E (R.N (m2 + 1)) (R.N (m2 + 1 + 1))) (y' y'' : Sp X.E (R.N (m2 + 1))),
    (∀ i, IntAt P.1 ((qOf P.1 : X.E) * y' i)) → k.1 y'' - y' ∈ stdAt X.E _ P.1 →
    (PhiTopG Ch mu cst.sharp (m2 + 1) (m2 + 1 + 1) (R.N (m2 + 1 + 1)) P.1
        (prXpG X.E (R.N (m2 + 1 + 1)) ∘ₗ (y ∘ₗ k.1.toLinearMap) ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) *
      ftY sel mu cst P (atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ (y ∘ₗ k.1.toLinearMap)) y'') * rhoS Ch sel mu (m2 + 1) P ((LinearEquiv.det g : X.Eˣ) : X.E) =
      z * (PhiTopG Ch mu cst.sharp (m2 + 1) (m2 + 1 + 1) (R.N (m2 + 1 + 1)) P.1
        (prXpG X.E (R.N (m2 + 1 + 1)) ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) *
      ftY sel mu cst P (atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ y) y') := by
  intro X Pr R Ch sel S mu cst L G m2 hX hPr _hsel hL b P hP g z hmid
  have hgC : g ∈ prCat (Pr := Pr) cst.sharp (m2 + 1) P.1 (L.h (m2 + 1) b P) :=
    (exists_midLev_iff Ch sel mu cst (m2 + 1) P (L.h (m2 + 1) b P) g).1 ⟨z, hmid⟩
  have hgI : g ∈ GLint X.E (R.N (m2 + 1)) P.1 := hL.int (m2 + 1) b P hgC
  refine ⟨⟨g, hgI⟩, rfl, ?_⟩
  intro k hk y y' y'' hy' hky
  obtain ⟨r, hr, hrg, hz⟩ := hmid
  have hred : ∀ x ∈ stdAt X.E (R.N (m2 + 1)) P.1, redV P.1 (g x) = (redGL _ P.1 k).1.mulVec (redV P.1 x) := by
    intro x hx
    rw [hk]
    exact redV_redGL (⟨g, hgI⟩ : GLint X.E (R.N (m2 + 1)) P.1) hx
  have hmem : redGL _ P.1 k ∈ (L.levG (m2 + 1) b ⟨P.1, hP⟩).H :=
    (hL.grpG (m2 + 1) b ⟨P.1, hP⟩ (redGL _ P.1 k)).2 ⟨g, hgC, hred⟩
  set c : X.Kˣ := (L.levG (m2 + 1) b ⟨P.1, hP⟩).lam ⟨redGL _ P.1 k, hmem⟩ with hcdef
  have hcz : (c : X.K) = z := by
    rw [hz]
    exact hL.chrG (m2 + 1) b ⟨P.1, hP⟩ ⟨redGL _ P.1 k, hmem⟩ g r hr hrg hred
  have hlev : GlobalTheory.TopLaw.LevAt (L.levG (m2 + 1) b) (L.levQ (m2 + 1) b) P k c :=
    ⟨fun _ => ⟨hmem, rfl⟩, fun _ h => absurd hP h⟩
  have hrho : rhoS Ch sel mu (m2 + 1) P ((LinearEquiv.det g : X.Eˣ) : X.E) =
      rhoS Ch sel mu (m2 + 1) P ((LinearEquiv.det k.1 : X.Eˣ) : X.E) := by
    unfold rhoS
    refine unitV_congr _ ?_
    rw [(det_glint k).2, ← redGL_val, hk, redGL_val]
    exact (det_glint (⟨g, hgI⟩ : GLint X.E (R.N (m2 + 1)) P.1)).2
  rw [hrho, ← hcz]
  have hm := hL.hm
  have key := GlobalTheory.TopLaw.locTop_source hX hPr hL hlev
  clear_value c
  clear hcdef hcz hrho hred hz hrg hr hmem
  revert key y
  cases R with
  | mk e k0 m t h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
    change m = m2 + 2 at hm
    subst hm
    intro y key
    have := key y (fun _ => hy') (fun h => absurd hP h) (fun _ => hky) (fun h => absurd hP h)
    unfold locTop at this
    rw [PhiTopG_eq]
    exact this

end GlobalTheory.TopLawG
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepLocalFactorSourceLawCoupledLevelStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop GlobalTheory.TopStep
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.last_step_local_factor_source_law_coupled_level : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}
  {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))}
  {G : ChGlob X R.m} {m2 : ℕ}, X.Ok → Pr.Ok → IsSel X sel → L.Ok Ch sel mu cst G m2 → ∀ (b : L.β (m2 + 1)) (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs →
  ∀ (g : Sp X.E (R.N (m2 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1))) (z : X.K), MidLev Ch sel mu cst (m2 + 1) P (L.h (m2 + 1) b P) g z →
  ∃ Gg : GLint X.E (R.N (m2 + 1)) P.1, Gg.1 = g ∧ ∀ (k : GLint X.E (R.N (m2 + 1)) P.1), redGL _ P.1 k = redGL _ P.1 Gg →
  ∀ (y : HomE X.E (R.N (m2 + 1)) (R.N (m2 + 1 + 1))) (y' y'' : Sp X.E (R.N (m2 + 1))),
    (∀ i, IntAt P.1 ((qOf P.1 : X.E) * y' i)) → k.1 y'' - y' ∈ stdAt X.E _ P.1 →
    (PhiTopG Ch mu cst.sharp (m2 + 1) (m2 + 1 + 1) (R.N (m2 + 1 + 1)) P.1
        (prXpG X.E (R.N (m2 + 1 + 1)) ∘ₗ (y ∘ₗ k.1.toLinearMap) ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) *
      ftY sel mu cst P (atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ (y ∘ₗ k.1.toLinearMap)) y'') * rhoS Ch sel mu (m2 + 1) P ((LinearEquiv.det g : X.Eˣ) : X.E) =
      z * (PhiTopG Ch mu cst.sharp (m2 + 1) (m2 + 1 + 1) (R.N (m2 + 1 + 1)) P.1
        (prXpG X.E (R.N (m2 + 1 + 1)) ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) *
      ftY sel mu cst P (atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ y) y') := by
  first | exact @GlobalTheory.TopLawG.locTopG_source | exact GlobalTheory.TopLawG.locTopG_source | (intros; apply GlobalTheory.TopLawG.locTopG_source <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepLocalFactorTargetLawTopLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepLocalFactorTargetLawTopLevel
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop GlobalTheory.TopStep
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwTop

open GlobalTheory.DatumLaw GlobalTheory.TopLaw

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {cst : LocCst X (rowSG Pr sel mu)} {m2 : ℕ}

theorem rowLevTop_glint {sharp : Bool} {n : ℕ} {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ Pr.vGs)
    {g : Sp X.E ((n - 1) + 0) ≃ₗ[X.E] Sp X.E ((n - 1) + 0)} (hg : g ∈ rowLevTop Pr R sharp n P) : g ∈ GLint X.E (n - 1) P := by
  unfold rowLevTop at hg
  rw [if_pos hP] at hg
  have h : g ∈ stabL X.E ((n - 1) + 0) (LocE.lamY P (qOf P) (n - 1) 0 fun i => i + 1) := by
    split_ifs at hg
    · exact hg.1
    · exact hg.1
  rw [GlobalTheory.TopLawSym.lamY_eq] at h
  exact h

theorem phiTop_rowLevTop (hm : R.m = m2 + 2) (sharp : Bool) {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ Pr.vGs)
    {g : Sp X.E ((R.N R.m - 1) + 0) ≃ₗ[X.E] Sp X.E ((R.N R.m - 1) + 0)} (hg : g ∈ rowLevTop Pr R sharp (R.N R.m) P)
    (x : HomE X.E (R.N (m2 + 1) + cOf R (m2 + 1)) ((R.N R.m - 1) + 0)) :
    PhiTop Ch mu sharp m2 P (g.toLinearMap ∘ₗ x) * LocE.unitV (chiP Ch P (m2 + 1)) ((LinearEquiv.det g : X.Eˣ) : X.E) =
      rowChrTop Ch mu sharp R.m (R.N R.m) P g.toLinearMap * PhiTop Ch mu sharp m2 P x := by
  obtain ⟨-, -, -, a4⟩ := ranks R (j := 0) (by omega)
  have a5 := r_le_X' R
  have b1 : R.N R.m - 1 + 0 = R.r + (m2 + 1) * R.t + R.t := by
    rw [add_zero, rank_X'_eq R, hm]; ring
  unfold rowLevTop at hg
  unfold PhiTop rowChrTop
  rw [if_pos hP] at hg
  rw [if_pos hP, if_pos hP]
  generalize R.N R.m - 1 = n at *
  generalize psi0P Ch P = ψ
  generalize chiP Ch P = χ
  rw [hm]
  split_ifs at hg ⊢
  · rw [DatumLaw.phiGS_eq]
    exact phiM_target _ _ (by omega) (by omega) b1 _ inf_le_left
      (fun g hg => levG_of_JGsym (by omega) a4 (by omega) hg) hg x
  · rw [phiG_eq, LocE.lamGB, lamGv_eq]
    exact phiM_target _ _ (by omega) (by omega) b1 _ inf_le_left
      (fun g hg => levG_of_JG (by omega) (by omega) hg) hg x

theorem locTop_topLev (hm : R.m = m2 + 2) (hc : cst.Ok) {P : rowSG Pr sel mu} (hq : ((qOf P.1 : ℕ) : 𝓞 X.E) ∉ P.1.asIdeal ^ 2)
    (hP : P.1 ∈ Pr.vGs) (g : Sp X.E (R.N R.m) ≃ₗ[X.E] Sp X.E (R.N R.m)) (z : X.K) (hg : TopLev Ch sel mu cst R.m P g z) :
    ∃ Gg : GLint X.E (R.N R.m) P.1, Gg.1 = g ∧ ∀ (k : GLint X.E (R.N R.m) P.1), redGL _ P.1 k = redGL _ P.1 Gg →
      ∀ (y : HomE X.E (R.N (m2 + 1)) (R.N R.m)) (y' : Sp X.E (R.N (m2 + 1))), (∀ i, IntAt P.1 ((qOf P.1 : X.E) * y' i)) →
        z * locTop Ch sel mu cst m2 P ((k⁻¹).1.toLinearMap ∘ₗ y) y' * rhoT Ch sel mu (m2 + 1) P ((LinearEquiv.det g : X.Eˣ) : X.E) =
          locTop Ch sel mu cst m2 P y y' := by
  classical
  obtain ⟨g', hg', h1, h2, rfl⟩ := hg
  let j : GLint X.E (R.N R.m - 1) P.1 := ⟨g', rowLevTop_glint hP hg'⟩
  have eg : (extI (N_m_succ R) P.1 j).1 = g := by
    refine LinearEquiv.ext fun v => ext_prH (N_m_succ R) ?_ ?_
    · exact (prH_sumE (N_m_succ R) _ _ _).trans (LinearMap.congr_fun h1 v).symm
    · refine (sumE_last (N_m_succ R) _ _ _).trans ?_
      rw [Units.val_one, one_mul]
      exact (atNL_last v).symm.trans ((LinearMap.congr_fun h2 v).symm.trans (atNL_last _))
  refine ⟨extI (N_m_succ R) P.1 j, eg, fun k hk y y' hy' => ?_⟩
  have e3 : (k⁻¹).1.toLinearMap ∘ₗ y = (k⁻¹ * extI (N_m_succ R) P.1 j).1.toLinearMap ∘ₗ
      ((extI (N_m_succ R) P.1 j⁻¹).1.toLinearMap ∘ₗ y) := by
    rw [map_inv]
    exact LinearMap.ext fun v => congrArg (k⁻¹).1 (LinearEquiv.apply_symm_apply (extI (N_m_succ R) P.1 j).1 (y v)).symm
  rw [e3, locTop_inv hm hc hP hq _ (by rw [map_mul, map_inv, hk, inv_mul_cancel]) _ hy', locTop_extI, ← eg]
  unfold rhoT
  rw [if_pos hP, unitV_det_ext _ (N_m_succ R) j _ rfl]
  have h3 := phiTop_rowLevTop (Ch := Ch) (mu := mu) hm cst.sharp hP hg' ((j⁻¹).1.toLinearMap ∘ₗ
    (prXp X.E R ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))))
  have e4 : g'.toLinearMap ∘ₗ ((j⁻¹).1.toLinearMap ∘ₗ
      (prXp X.E R ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1))))) =
      prXp X.E R ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1))) :=
    LinearMap.ext fun v => g'.apply_symm_apply _
  rw [e4] at h3
  have hu : IsUnit (redP P.1 ((LinearEquiv.det j.1 : X.Eˣ) : X.E)) := by
    rw [(det_glint j).2, ← redGL_val, ← Matrix.isUnit_iff_isUnit_det]
    exact Units.isUnit _
  have h4 : LocE.unitV (chiP Ch P.1 (m2 + 1)) ((LinearEquiv.det g' : X.Eˣ) : X.E) *
      LocE.unitV (chiP Ch P.1 (m2 + 1))⁻¹ ((LinearEquiv.det j.1 : X.Eˣ) : X.E) = 1 := by
    rw [DatumLaw.unitV_eq, DatumLaw.unitV_eq, extendByZeroOffSubset_mul_left_of_mem_lattice]
    exact mul_inv_cancel₀ (unitCharacterExtendByZero_ne_zero_of_isUnit _ hu)
  unfold locTop
  rw [← mul_assoc, mul_right_comm]
  congr 1
  refine (congrArg (· * _) h3.symm).trans ?_
  rw [mul_assoc, h4, mul_one]

theorem topF_target_vG : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}
  {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))}
  {G : ChGlob X R.m} {m2 : ℕ}, X.Ok → Pr.Ok → IsSel X sel → L.Ok Ch sel mu cst G m2 → ∀ (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs →
  ∀ (g : Sp X.E (R.N (m2 + 1 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1 + 1))) (z : X.K), TopLev Ch sel mu cst (m2 + 1 + 1) P g z →
  ∃ Gg : GLint X.E (R.N (m2 + 1 + 1)) P.1, Gg.1 = g ∧ ∀ (k : GLint X.E (R.N (m2 + 1 + 1)) P.1), redGL _ P.1 k = redGL _ P.1 Gg →
  ∀ (y : HomE X.E (R.N (m2 + 1)) (R.N (m2 + 1 + 1))) (y' : Sp X.E (R.N (m2 + 1))),
    (∀ i, IntAt P.1 ((qOf P.1 : X.E) * y' i)) →
    z * (PhiTopG Ch mu cst.sharp (m2 + 1) (m2 + 1 + 1) (R.N (m2 + 1 + 1)) P.1
        (prXpG X.E (R.N (m2 + 1 + 1)) ∘ₗ ((k⁻¹).1.toLinearMap ∘ₗ y) ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) *
      ftY sel mu cst P (atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ ((k⁻¹).1.toLinearMap ∘ₗ y)) y') * rhoT Ch sel mu (m2 + 1) P ((LinearEquiv.det g : X.Eˣ) : X.E) =
      (PhiTopG Ch mu cst.sharp (m2 + 1) (m2 + 1 + 1) (R.N (m2 + 1 + 1)) P.1
        (prXpG X.E (R.N (m2 + 1 + 1)) ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) *
      ftY sel mu cst P (atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ y) y') := by
  intro X Pr R Ch sel S mu cst L G m2 hX hPr hsel hL P hP
  have hm : R.m = m2 + 1 + 1 := hL.hm
  generalize m2 + 1 + 1 = j at hm ⊢
  subst hm
  intro g z hg
  exact locTop_topLev hL.hm hL.cst_ok (GlobalTheory.ColPeriod.levelPrimes X Pr sel S mu hX hPr hsel P).1.2 hP g z hg

end GlobalTheory.TwTop

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepLocalFactorTargetLawTopLevelStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop GlobalTheory.TopStep
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.last_step_local_factor_target_law_top_level : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}
  {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))}
  {G : ChGlob X R.m} {m2 : ℕ}, X.Ok → Pr.Ok → IsSel X sel → L.Ok Ch sel mu cst G m2 → ∀ (P : rowSG Pr sel mu), P.1 ∈ Pr.vGs →
  ∀ (g : Sp X.E (R.N (m2 + 1 + 1)) ≃ₗ[X.E] Sp X.E (R.N (m2 + 1 + 1))) (z : X.K), TopLev Ch sel mu cst (m2 + 1 + 1) P g z →
  ∃ Gg : GLint X.E (R.N (m2 + 1 + 1)) P.1, Gg.1 = g ∧ ∀ (k : GLint X.E (R.N (m2 + 1 + 1)) P.1), redGL _ P.1 k = redGL _ P.1 Gg →
  ∀ (y : HomE X.E (R.N (m2 + 1)) (R.N (m2 + 1 + 1))) (y' : Sp X.E (R.N (m2 + 1))),
    (∀ i, IntAt P.1 ((qOf P.1 : X.E) * y' i)) →
    z * (PhiTopG Ch mu cst.sharp (m2 + 1) (m2 + 1 + 1) (R.N (m2 + 1 + 1)) P.1
        (prXpG X.E (R.N (m2 + 1 + 1)) ∘ₗ ((k⁻¹).1.toLinearMap ∘ₗ y) ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) *
      ftY sel mu cst P (atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ ((k⁻¹).1.toLinearMap ∘ₗ y)) y') * rhoT Ch sel mu (m2 + 1) P ((LinearEquiv.det g : X.Eˣ) : X.E) =
      (PhiTopG Ch mu cst.sharp (m2 + 1) (m2 + 1 + 1) (R.N (m2 + 1 + 1)) P.1
        (prXpG X.E (R.N (m2 + 1 + 1)) ∘ₗ y ∘ₗ LinearMap.funLeft X.E X.E (Fin.castAdd (cOf R (m2 + 1)))) *
      ftY sel mu cst P (atNL X.E (R.N (m2 + 1 + 1)) (R.N (m2 + 1 + 1) - 1) ∘ₗ y) y') := by
  first | exact @GlobalTheory.TwTop.topF_target_vG | exact GlobalTheory.TwTop.topF_target_vG | (intros; apply GlobalTheory.TwTop.topF_target_vG <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepLocalFactorLevelValuesTypePrime
noncomputable section

namespace GlobalTheory.TwTop

open NumberField IsDedekindDomain Formalism.BasicNotions _root_.Formalism.L2.DIV _root_.Formalism.L2.Col Formalism.MainNotions _root_.Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop GlobalTheory.TopStep
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem locAt_vG : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (hi : t.m2 + 1 + 1 ≤ D.R.m) (β : (St (t.m2 + 1) (Nat.le_of_succ_le hi)).Ch) (β' : (St (t.m2 + 1 + 1) hi).Ch)
    (x x₁ : UA D (t.m2 + 1) (Nat.le_of_succ_le hi)) (x' x₁' : UA D (t.m2 + 1 + 1) hi)
    (κ : ((St (t.m2 + 1) (Nat.le_of_succ_le hi)).K β).lev.U) (κ' : ((St (t.m2 + 1 + 1) hi).K β').lev.U),
    x₁.1 = x.1 * κ.1 → x₁'.1 = x'.1 * κ'.1 →
    ∀ p p' p₁ p₁', IsPtAd A a (t.m2 + 1) (Nat.le_of_succ_le hi) β x p → IsPtAd A a (t.m2 + 1 + 1) hi β' x' p' →
      IsPtAd A a (t.m2 + 1) (Nat.le_of_succ_le hi) β x₁ p₁ → IsPtAd A a (t.m2 + 1 + 1) hi β' x₁' p₁' →
    ∀ (P : SB t μ), P.1 ∈ t.Pr.vGs → ∀ g z g' z', A.cplRel β P g z →
      InFrame t.seam (A.fb (t.m2 + 1) (Nat.le_of_succ_le hi) β) (t.cst μ).D P κ.1 g →
      TopLev t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1 + 1) P g' z' →
      InFrame t.seam (A.fb (t.m2 + 1 + 1) hi β') (topDep t.sel (t.tup μ) (t.cst μ)) P κ'.1 g' →
    ∀ Z, z' * topF t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P p₁ (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p₁) p₁' Z *
        rhoS t.Ch t.sel (t.tup μ) (t.m2 + 1) P ((LinearEquiv.det g : t.X.Eˣ) : t.X.E) *
        rhoT t.Ch t.sel (t.tup μ) (t.m2 + 1) P ((LinearEquiv.det g' : t.X.Eˣ) : t.X.E) =
      z * topF t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P p (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p) p' Z) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin hTie hi β β' x x₁ x' x₁' κ κ' hx hx' p p' p₁ p₁' hp hp' hp₁ hp₁' P hP g z g' z' hC hF hT hF' Z
  have hD : (t.cst μ).D P = 1 := (t.idx_ok μ).depthG P hP
  have hDt : topDep t.sel (t.tup μ) (t.cst μ) P = 1 := by unfold topDep; simp [hP]
  obtain ⟨Gg, rfl, hsrc⟩ := GlobalTheory.T.last_step_local_factor_source_law_coupled_level hPin.fields.ok t.pr_ok hPin.sel (t.idx_ok μ) _ P hP g z hC.1
  obtain ⟨Gt, rfl, htgt⟩ := GlobalTheory.T.last_step_local_factor_target_law_top_level hPin.fields.ok t.pr_ok hPin.sel (t.idx_ok μ) P hP g' z' hT
  obtain ⟨k, hk, hkr⟩ := GlobalTheory.T.type_prime_frames_right_translate_differ_integral_GL A dtU a hPin hTie (t.m2 + 1) (Nat.le_of_succ_le hi) β x x₁ κ hx p p₁ hp hp₁ P hP (t.cst μ).D hD Gg hF
  obtain ⟨k', hk', hkr'⟩ := GlobalTheory.T.type_prime_frames_right_translate_differ_integral_GL A dtU a hPin hTie (t.m2 + 1 + 1) hi β' x' x₁' κ' hx' p' p₁' hp' hp₁' P hP _ hDt Gt hF'
  obtain ⟨i0, i1, hdiff⟩ := GlobalTheory.T.coupling_cosets_right_translate_in_frames_type_prime A dtU a hPin hTie (Nat.le_of_succ_le hi) β p p₁ P hP Gg k z hC hkr hk
  have e1 : inFr (frsF t.sel (t.tup μ) p₁ P) (frsG t.sel (t.tup μ) p₁' P) Z =
      (k'⁻¹).1.toLinearMap ∘ₗ (inFr (frsF t.sel (t.tup μ) p P) (frsG t.sel (t.tup μ) p' P) Z ∘ₗ k.1.toLinearMap) := by
    rw [frsG_eq, frsG_eq, hk, hk']
    rfl
  have hs := hsrc k hkr (inFr (frsF t.sel (t.tup μ) p P) (frsG t.sel (t.tup μ) p' P) Z) _ _ i0 hdiff
  have ht := htgt k' hkr' (inFr (frsF t.sel (t.tup μ) p P) (frsG t.sel (t.tup μ) p' P) Z ∘ₗ k.1.toLinearMap) _ i1
  unfold topF
  rw [e1]
  linear_combination rhoS t.Ch t.sel (t.tup μ) (t.m2 + 1) P ((LinearEquiv.det Gg.1 : t.X.Eˣ) : t.X.E) * ht + hs

end GlobalTheory.TwTop

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepLocalFactorLevelValuesTypePrimeStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastStep_localFactor_levelValues_typePrime : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (hi : t.m2 + 1 + 1 ≤ D.R.m) (β : (St (t.m2 + 1) (Nat.le_of_succ_le hi)).Ch) (β' : (St (t.m2 + 1 + 1) hi).Ch)
    (x x₁ : UA D (t.m2 + 1) (Nat.le_of_succ_le hi)) (x' x₁' : UA D (t.m2 + 1 + 1) hi)
    (κ : ((St (t.m2 + 1) (Nat.le_of_succ_le hi)).K β).lev.U) (κ' : ((St (t.m2 + 1 + 1) hi).K β').lev.U),
    x₁.1 = x.1 * κ.1 → x₁'.1 = x'.1 * κ'.1 →
    ∀ p p' p₁ p₁', IsPtAd A a (t.m2 + 1) (Nat.le_of_succ_le hi) β x p → IsPtAd A a (t.m2 + 1 + 1) hi β' x' p' →
      IsPtAd A a (t.m2 + 1) (Nat.le_of_succ_le hi) β x₁ p₁ → IsPtAd A a (t.m2 + 1 + 1) hi β' x₁' p₁' →
    ∀ (P : SB t μ), P.1 ∈ t.Pr.vGs → ∀ g z g' z', A.cplRel β P g z →
      InFrame t.seam (A.fb (t.m2 + 1) (Nat.le_of_succ_le hi) β) (t.cst μ).D P κ.1 g →
      TopLev t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1 + 1) P g' z' →
      InFrame t.seam (A.fb (t.m2 + 1 + 1) hi β') (topDep t.sel (t.tup μ) (t.cst μ)) P κ'.1 g' →
    ∀ Z, z' * topF t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P p₁ (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p₁) p₁' Z *
        rhoS t.Ch t.sel (t.tup μ) (t.m2 + 1) P ((LinearEquiv.det g : t.X.Eˣ) : t.X.E) *
        rhoT t.Ch t.sel (t.tup μ) (t.m2 + 1) P ((LinearEquiv.det g' : t.X.Eˣ) : t.X.E) =
      z * topF t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P p (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p) p' Z) := by
  first | exact @GlobalTheory.TwTop.locAt_vG | exact GlobalTheory.TwTop.locAt_vG | (intros; apply GlobalTheory.TwTop.locAt_vG <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepAdelicDatumLevelEquivariance
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV

namespace GlobalTheory.TwTop

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem locAt : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (hi : t.m2 + 1 + 1 ≤ D.R.m) (β : (St (t.m2 + 1) (Nat.le_of_succ_le hi)).Ch) (β' : (St (t.m2 + 1 + 1) hi).Ch)
    (x x₁ : UA D (t.m2 + 1) (Nat.le_of_succ_le hi)) (x' x₁' : UA D (t.m2 + 1 + 1) hi)
    (κ : ((St (t.m2 + 1) (Nat.le_of_succ_le hi)).K β).lev.U) (κ' : ((St (t.m2 + 1 + 1) hi).K β').lev.U),
    x₁.1 = x.1 * κ.1 → x₁'.1 = x'.1 * κ'.1 →
    ∀ p p' p₁ p₁', IsPtAd A a (t.m2 + 1) (Nat.le_of_succ_le hi) β x p → IsPtAd A a (t.m2 + 1 + 1) hi β' x' p' →
      IsPtAd A a (t.m2 + 1) (Nat.le_of_succ_le hi) β x₁ p₁ → IsPtAd A a (t.m2 + 1 + 1) hi β' x₁' p₁' →
    ∀ (P : SB t μ) g z g' z', A.cplRel β P g z →
      InFrame t.seam (A.fb (t.m2 + 1) (Nat.le_of_succ_le hi) β) (t.cst μ).D P κ.1 g →
      TopLev t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1 + 1) P g' z' →
      InFrame t.seam (A.fb (t.m2 + 1 + 1) hi β') (topDep t.sel (t.tup μ) (t.cst μ)) P κ'.1 g' →
    ∀ Z, z' * topF t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P p₁ (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p₁) p₁' Z *
        rhoS t.Ch t.sel (t.tup μ) (t.m2 + 1) P ((LinearEquiv.det g : t.X.Eˣ) : t.X.E) *
        rhoT t.Ch t.sel (t.tup μ) (t.m2 + 1) P ((LinearEquiv.det g' : t.X.Eˣ) : t.X.E) =
      z * topF t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P p (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p) p' Z) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin hTie hi β β' x x₁ x' x₁' κ κ' hx hx' p p' p₁ p₁' hp hp' hp₁ hp₁' P
  by_cases hP : P.1 ∈ t.Pr.vGs
  · exact GlobalTheory.T.lastStep_localFactor_levelValues_typePrime A dtU a hPin hTie hi β β' x x₁ x' x₁' κ κ' hx hx' p p' p₁ p₁' hp hp' hp₁ hp₁' P hP
  · exact GlobalTheory.T.columnLastStep_localFactor_twist_prime_law A dtU a hPin hTie hi β β' x x₁ x' x₁' κ κ' hx hx' p p' p₁ p₁' hp hp' hp₁ hp₁' P hP

end GlobalTheory.TwTop

namespace GlobalTheory.TwTop

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem levAt_top : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => PtEx A a → MuLaw t u μ dtU →
    ∀ i hi, i = t.m2 + 1 → PtAway A a i hi → LevAt A dtU a i hi) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin hTie hEx hMu i hi hieq _hAway
  subst hieq
  intro β β' x x' x₁ x₁' κ κ' hx hx' z
  have key : ∀ p p' p₁ p₁', IsPtAd A a (t.m2 + 1) (Nat.le_of_succ_le hi) β x p → IsPtAd A a (t.m2 + 1 + 1) hi β' x' p' →
      IsPtAd A a (t.m2 + 1) (Nat.le_of_succ_le hi) β x₁ p₁ → IsPtAd A a (t.m2 + 1 + 1) hi β' x₁' p₁' → ∀ Z,
      muOf t u μ dtU (t.m2 + 1 + 1) (Matrix.GeneralLinearGroup.det κ'.1) * ((((St (t.m2 + 1) _).K β).lev.chi κ : ℂˣ) : ℂ) *
          t.seam.σ₀ (xiPt A (t.m2 + 1) hi β β' p₁ p₁' Z) =
        muOf t u μ dtU (t.m2 + 1 + 1) (Matrix.GeneralLinearGroup.det κ.1) * ((((St (t.m2 + 1 + 1) hi).K β').lev.chi κ' : ℂˣ) : ℂ) *
          t.seam.σ₀ (xiPt A (t.m2 + 1) hi β β' p p' Z) := by
    intro p p' p₁ p₁' hp hp' hp₁ hp₁' Z
    have hxi : ∀ q q', xiPt A (t.m2 + 1) hi β β' q q' Z =
        _root_.Formalism.L2.Col.XiTop t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) q (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β q) q' Z := by
      intro q q'
      unfold xiPt
      rw [dite_eq_right (by omega), if_neg (by omega)]
    have e1 := hxi p₁ p₁'
    have e2 := hxi p p'
    have e3 := GlobalTheory.T.chartDatum_levelPrime_invariant_mul_level A dtU a hPin hTie (t.m2 + 1) hi β β' x x₁ x' x₁' κ κ' hx hx' p p' p₁ p₁' hp hp' hp₁ hp₁' Z
    simp only [e1, e2, xiTop_eq_prod, e3]
    have hC := hTie.levCpl β
    have hT2 := hTie.levTop β'
    have hLe := hC.1
    have hChi := hC.2.2
    have hLe' := hT2.1
    have hChi' := hT2.2
    have hU := (((St (t.m2 + 1) (Nat.le_of_succ_le hi)).K β).lev.U_eq κ.1).1 κ.2
    have hU' := (((St (t.m2 + 1 + 1) hi).K β').lev.U_eq κ'.1).1 κ'.2
    have hov : ∀ P : SB t μ, IsOver (HeightOneSpectrum.under (𝓞 D.host.F) (seamP t.seam P.1)) (seamP t.seam P.1) := by
      intro P
      unfold IsOver
      rw [HeightOneSpectrum.under_asIdeal]
    choose g zz hg using fun P : SB t μ => hLe P _ (hov P) κ.1 hU.1 (hU.2 _)
    choose g' zz' hg' using fun P : SB t μ => hLe' P _ (hov P) κ'.1 hU'.1 (hU'.2 _)
    have c1 := hChi κ g zz hg
    have c2 := hChi' κ' g' zz' hg'
    have hm := GlobalTheory.T.lastStepCharacter_at_levelDet_mul_localCharacters A dtU a hPin hTie hMu hi β β' κ κ' g zz g' zz' hg hg'
    have hprod : (∏ P, zz' P) * (∏ P, topF t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P p₁
          (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p₁) p₁' Z) *
        (∏ P, rhoS t.Ch t.sel (t.tup μ) (t.m2 + 1) P ((LinearEquiv.det (g P) : t.X.Eˣ) : t.X.E) *
          rhoT t.Ch t.sel (t.tup μ) (t.m2 + 1) P ((LinearEquiv.det (g' P) : t.X.Eˣ) : t.X.E)) =
        (∏ P, zz P) * ∏ P, topF t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P p
          (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p) p' Z := by
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun P _ => ?_
      rw [← locAt A dtU a hPin hTie hi β β' x x₁ x' x₁' κ κ' hx hx' p p' p₁ p₁' hp hp' hp₁ hp₁' P (g P) (zz P) (g' P) (zz' P)
        (hg P).1 (hg P).2 (hg' P).1 (hg' P).2 Z]
      ring
    have e := congrArg t.seam.σ₀ hprod
    simp only [map_mul] at e ⊢
    have hA : t.seam.σ₀ (∏ P, zz P) ≠ 0 := right_ne_zero_of_mul_eq_one c1
    have hB : t.seam.σ₀ (∏ P, zz' P) ≠ 0 := right_ne_zero_of_mul_eq_one c2
    apply mul_right_cancel₀ (mul_ne_zero hA hB)
    linear_combination
      (-(((((St (t.m2 + 1) _).K β).lev.chi κ : ℂˣ) : ℂ) * t.seam.σ₀ (phiT t.X.K p.deco.1 p'.deco.1 Z) *
        t.seam.σ₀ (∏ P, topF t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P p₁ (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p₁) p₁' Z) *
        t.seam.σ₀ (∏ P, zz P) * t.seam.σ₀ (∏ P, zz' P))) * hm +
      (muOf t u μ dtU (t.m2 + 1 + 1) (Matrix.GeneralLinearGroup.det κ.1) * t.seam.σ₀ (phiT t.X.K p.deco.1 p'.deco.1 Z) *
        t.seam.σ₀ (∏ P, zz' P) *
        t.seam.σ₀ (∏ P, topF t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P p₁ (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p₁) p₁' Z) *
        t.seam.σ₀ (∏ P, rhoS t.Ch t.sel (t.tup μ) (t.m2 + 1) P ((LinearEquiv.det (g P) : t.X.Eˣ) : t.X.E) *
          rhoT t.Ch t.sel (t.tup μ) (t.m2 + 1) P ((LinearEquiv.det (g' P) : t.X.Eˣ) : t.X.E))) * c1 +
      (muOf t u μ dtU (t.m2 + 1 + 1) (Matrix.GeneralLinearGroup.det κ.1) * t.seam.σ₀ (phiT t.X.K p.deco.1 p'.deco.1 Z)) * e -
      (muOf t u μ dtU (t.m2 + 1 + 1) (Matrix.GeneralLinearGroup.det κ.1) * t.seam.σ₀ (phiT t.X.K p.deco.1 p'.deco.1 Z) *
        t.seam.σ₀ (∏ P, topF t.Ch t.sel (t.tup μ) (t.cst μ) (t.m2 + 1) P p (cosetOf A (t.m2 + 1) (Nat.le_of_succ_le hi) β p) p' Z) *
        t.seam.σ₀ (∏ P, zz P)) * c2
  have h₁ : (∃ p, IsPtAd A a (t.m2 + 1) (Nat.le_of_succ_le hi) β x₁ p) ∧ ∃ p', IsPtAd A a (t.m2 + 1 + 1) hi β' x₁' p' :=
    ⟨hEx _ _ β x₁, hEx _ _ β' x₁'⟩
  have h₀ : (∃ p, IsPtAd A a (t.m2 + 1) (Nat.le_of_succ_le hi) β x p) ∧ ∃ p', IsPtAd A a (t.m2 + 1 + 1) hi β' x' p' :=
    ⟨hEx _ _ β x, hEx _ _ β' x'⟩
  unfold xiAd
  rw [dite_eq_left h₁, dite_eq_left h₀]
  exact key _ _ _ _ h₀.1.choose_spec h₀.2.choose_spec h₁.1.choose_spec h₁.2.choose_spec _

end GlobalTheory.TwTop

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LastStepAdelicDatumLevelEquivarianceStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lastStep_adelicDatum_level_equivariance : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => PtEx A a → MuLaw t u μ dtU → ∀ i hi, i = t.m2 + 1 → PtAway A a i hi → LevAt A dtU a i hi) := by
  first | exact @GlobalTheory.TwTop.levAt_top | exact GlobalTheory.TwTop.levAt_top | (intros; apply GlobalTheory.TwTop.levAt_top <;> assumption)
end
