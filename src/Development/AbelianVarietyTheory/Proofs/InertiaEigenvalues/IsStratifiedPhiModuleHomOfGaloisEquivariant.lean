module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemMaximalIdealIff

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StratifiedHomComparisonCompatibleEnvelope
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StratifiedHomDefectFrobeniusEquation
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StratifiedHomDefectFrobeniusEquation
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.HomDefect

theorem smul_cancel {R : Type} [CommRing R] {m n : Type} {r : R} (hr : r ∈ nonZeroDivisors R)
    {M N : Matrix m n R} (h : r • M = r • N) : M = N := by
  ext i j
  have := congrFun (congrFun h i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  exact (mul_cancel_left_mem_nonZeroDivisors hr).1 this

theorem map_smul' {R R' : Type} [CommRing R] [CommRing R'] {m n : Type} (φ : R →+* R') (c : R)
    (M : Matrix m n R) : (c • M).map φ = φ c • M.map φ := by
  ext i j; simp

theorem map_frob {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {B : Obj l ↥(OL K)} (f : Hom bk.prism B)
    {m n : Type} (M : Matrix m n bk.S) : (M.map (frobS l bk.a)).map (BK.hf f) = (M.map (BK.hf f)).map B.D.φ := by
  ext i j
  exact f.f_φ (M i j)

end GlobalTheory.BSP.HomDefect


set_option maxHeartbeats 800000 in
open GlobalTheory.BSP.HomDefect in
theorem GlobalTheory.BSP.strat_homDefect_φ : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' : ℕ) (S : Strat bk d) (S' : Strat bk d') (Y : Matrix (Fin d') (Fin d) bk.S), bk.E ^ S.a • (S'.A * Y.map (frobS l bk.a)) = bk.E ^ S'.a • (Y * S.A) → ∀ (B : Obj l ↥(OL K)) (f g : Hom bk.prism B), BK.hf g bk.E ^ S.a • (S'.A.map (BK.hf f) * (S'.ε f g * Y.map (BK.hf g) - Y.map (BK.hf f) * S.ε f g).map B.D.φ) = BK.hf f bk.E ^ S'.a • ((S'.ε f g * Y.map (BK.hf g) - Y.map (BK.hf f) * S.ε f g) * S.A.map (BK.hf g)) := by
  intro l _ K bk d d' S S' Y hY B f g
  obtain ⟨hfE, -, -⟩ := GlobalTheory.T.breuilKisin_two_homs_E_regular_associated l K bk B f g
  obtain ⟨hgE, -, -⟩ := GlobalTheory.T.breuilKisin_two_homs_E_regular_associated l K bk B g f
  have hYf := congrArg (fun M => M.map (BK.hf f)) hY
  have hYg := congrArg (fun M => M.map (BK.hf g)) hY
  simp only [map_smul', Matrix.map_mul, map_pow, map_frob] at hYf hYg
  have e1 := S.ε_φ f g
  have e2 := S'.ε_φ f g
  have T1 : BK.hf g bk.E ^ S.a • (S'.A.map (BK.hf f) * ((S'.ε f g).map B.D.φ * (Y.map (BK.hf g)).map B.D.φ)) =
      BK.hf f bk.E ^ S'.a • (S'.ε f g * Y.map (BK.hf g) * S.A.map (BK.hf g)) := by
    apply smul_cancel (pow_mem hgE S'.a)
    calc BK.hf g bk.E ^ S'.a • BK.hf g bk.E ^ S.a • (S'.A.map (BK.hf f) * ((S'.ε f g).map B.D.φ * (Y.map (BK.hf g)).map B.D.φ))
        = BK.hf g bk.E ^ S.a • ((BK.hf g bk.E ^ S'.a • (S'.A.map (BK.hf f) * (S'.ε f g).map B.D.φ)) * (Y.map (BK.hf g)).map B.D.φ) := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc, mul_comm]
      _ = BK.hf g bk.E ^ S.a • ((BK.hf f bk.E ^ S'.a • (S'.ε f g * S'.A.map (BK.hf g))) * (Y.map (BK.hf g)).map B.D.φ) := congrArg (fun M => BK.hf g bk.E ^ S.a • (M * (Y.map (BK.hf g)).map B.D.φ)) e2
      _ = BK.hf f bk.E ^ S'.a • (S'.ε f g * (BK.hf g bk.E ^ S.a • (S'.A.map (BK.hf g) * (Y.map (BK.hf g)).map B.D.φ))) := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc, mul_comm]
      _ = BK.hf f bk.E ^ S'.a • (S'.ε f g * (BK.hf g bk.E ^ S'.a • (Y.map (BK.hf g) * S.A.map (BK.hf g)))) := congrArg (fun M => BK.hf f bk.E ^ S'.a • (S'.ε f g * M)) hYg
      _ = BK.hf g bk.E ^ S'.a • BK.hf f bk.E ^ S'.a • (S'.ε f g * Y.map (BK.hf g) * S.A.map (BK.hf g)) := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc, mul_comm]
  have T2 : BK.hf g bk.E ^ S.a • (S'.A.map (BK.hf f) * ((Y.map (BK.hf f)).map B.D.φ * (S.ε f g).map B.D.φ)) =
      BK.hf f bk.E ^ S'.a • (Y.map (BK.hf f) * S.ε f g * S.A.map (BK.hf g)) := by
    apply smul_cancel (pow_mem hfE S.a)
    calc BK.hf f bk.E ^ S.a • BK.hf g bk.E ^ S.a • (S'.A.map (BK.hf f) * ((Y.map (BK.hf f)).map B.D.φ * (S.ε f g).map B.D.φ))
        = BK.hf g bk.E ^ S.a • ((BK.hf f bk.E ^ S.a • (S'.A.map (BK.hf f) * (Y.map (BK.hf f)).map B.D.φ)) * (S.ε f g).map B.D.φ) := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc, mul_comm]
      _ = BK.hf g bk.E ^ S.a • ((BK.hf f bk.E ^ S'.a • (Y.map (BK.hf f) * S.A.map (BK.hf f))) * (S.ε f g).map B.D.φ) := congrArg (fun M => BK.hf g bk.E ^ S.a • (M * (S.ε f g).map B.D.φ)) hYf
      _ = BK.hf f bk.E ^ S'.a • (Y.map (BK.hf f) * (BK.hf g bk.E ^ S.a • (S.A.map (BK.hf f) * (S.ε f g).map B.D.φ))) := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc, mul_comm]
      _ = BK.hf f bk.E ^ S'.a • (Y.map (BK.hf f) * (BK.hf f bk.E ^ S.a • (S.ε f g * S.A.map (BK.hf g)))) := congrArg (fun M => BK.hf f bk.E ^ S'.a • (Y.map (BK.hf f) * M)) e1
      _ = BK.hf f bk.E ^ S.a • BK.hf f bk.E ^ S'.a • (Y.map (BK.hf f) * S.ε f g * S.A.map (BK.hf g)) := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc, mul_comm]
  rw [Matrix.map_sub, Matrix.map_mul, Matrix.map_mul, Matrix.mul_sub, Matrix.sub_mul, smul_sub, smul_sub]
  · exact congrArg₂ (· - ·) T1 T2
  · exact fun a b => map_sub _ a b
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StratifiedHomDefectFrobeniusEquationStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stratifiedHom_defect_frobenius_equation : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' : ℕ) (S : Strat bk d) (S' : Strat bk d') (Y : Matrix (Fin d') (Fin d) bk.S), bk.E ^ S.a • (S'.A * Y.map (frobS l bk.a)) = bk.E ^ S'.a • (Y * S.A) → ∀ (B : Obj l ↥(OL K)) (f g : Hom bk.prism B), BK.hf g bk.E ^ S.a • (S'.A.map (BK.hf f) * (S'.ε f g * Y.map (BK.hf g) - Y.map (BK.hf f) * S.ε f g).map B.D.φ) = BK.hf f bk.E ^ S'.a • ((S'.ε f g * Y.map (BK.hf g) - Y.map (BK.hf f) * S.ε f g) * S.A.map (BK.hf g)) := by
  first | exact @GlobalTheory.BSP.strat_homDefect_φ | exact GlobalTheory.BSP.strat_homDefect_φ | (intros; apply GlobalTheory.BSP.strat_homDefect_φ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StratifiedHomComparisonCompatibleEnvelope
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem strat_defect_map {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {d d' : ℕ} (S : Strat bk d)
    (S' : Strat bk d') (Y : Matrix (Fin d') (Fin d) bk.S) {B C : Obj l ↥(OL K)} (σ : Hom B C)
    (f g : Hom bk.prism B) :
    (S'.ε f g * Y.map (BK.hf g) - Y.map (BK.hf f) * S.ε f g).map σ.f =
      S'.ε (σ.comp f) (σ.comp g) * Y.map (BK.hf (σ.comp g)) -
        Y.map (BK.hf (σ.comp f)) * S.ε (σ.comp f) (σ.comp g) := by
  have e1 : (Y.map (BK.hf g)).map σ.f = Y.map (BK.hf (σ.comp g)) := rfl
  have e2 : (Y.map (BK.hf f)).map σ.f = Y.map (BK.hf (σ.comp f)) := rfl
  have m1 := Matrix.map_mul (L := S'.ε f g) (M := Y.map (BK.hf g)) (f := σ.f)
  have m2 := Matrix.map_mul (L := Y.map (BK.hf f)) (M := S.ε f g) (f := σ.f)
  rw [Matrix.map_sub _ (map_sub σ.f), m1, m2, S'.ε_nat, S.ε_nat, e1, e2]

theorem matrix_phi_eq_family_self (C : Type) [CommRing C] (φ : C → C) (e e' : C) (he : Associated e e')
    (d d' a a' b : ℕ) (P : Matrix (Fin d') (Fin d') C) (Q Q' : Matrix (Fin d) (Fin d) C)
    (hQ : Q * Q' = e' ^ b • (1 : Matrix (Fin d) (Fin d) C)) (Δ : Matrix (Fin d') (Fin d) C)
    (h : e' ^ a • (P * Δ.map φ) = e ^ a' • (Δ * Q)) :
    ∃ (h : ℕ) (c : Fin d' × Fin d → Fin d' × Fin d → C), ∀ j : Fin d' × Fin d,
      e ^ h * Δ j.1 j.2 = ∑ k : Fin d' × Fin d, φ (Δ k.1 k.2) * c k j :=
  GlobalTheory.T.matrix_phi_equation_to_family_equation C C (RingHom.id C) φ e e' he d d' a a' b P Q Q' hQ Δ h

theorem obj_eq_zero_of_pow_dvd {l : ℕ} [Fact l.Prime] {K : FinExt l} (B : Obj l ↥(OL K)) (x : B.A)
    (hk : ∀ k : ℕ, ((l : ℕ) : B.A) ^ k ∣ x) : x = 0 := by
  refine B.complete.toIsHausdorff.haus _ fun n => ?_
  obtain ⟨y, hy⟩ := hk n
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, hy]
  exact Ideal.mul_mem_right _ _
    (Ideal.pow_mem_pow (Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)) n)

theorem strat_map_A_mul {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {d : ℕ} (S : Strat bk d)
    {B : Obj l ↥(OL K)} (g : Hom bk.prism B) :
    S.A.map (BK.hf g) * S.A'.map (BK.hf g) = BK.hf g bk.E ^ S.b • (1 : Matrix (Fin d) (Fin d) B.A) := by
  rw [← Matrix.map_mul, S.A_mul]
  ext i j
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

theorem env_matrix_eq_zero {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K}
    (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)) {d d' : ℕ} (S : Strat bk d) (S' : Strat bk d')
    (Δ : Matrix (Fin d') (Fin d) En.Q.A)
    (h1 : BK.hf En.inr bk.E ^ S.a • (S'.A.map (BK.hf En.inl) * Δ.map En.Q.D.φ) =
      BK.hf En.inl bk.E ^ S'.a • (Δ * S.A.map (BK.hf En.inr)))
    (hσ : ∀ (g : ↥(GK K)) (σ : Hom En.Q (ainfObj K)), σ.comp En.inl = bk.ι →
      σ.comp En.inr = (ainfHom K g).comp bk.ι → Δ.map σ.f = 0) : Δ = 0 := by
  have hass := (GlobalTheory.T.breuilKisin_two_homs_E_regular_associated l K bk En.Q En.inl En.inr).2.1
  obtain ⟨h, c, hc⟩ := matrix_phi_eq_family_self En.Q.A En.Q.D.φ _ _ hass d d' S.a S'.a S.b
    (S'.A.map (BK.hf En.inl)) _ _ (strat_map_A_mul S En.inr) Δ h1
  refine Matrix.ext fun i j => obj_eq_zero_of_pow_dvd En.Q (Δ i j) fun k => ?_
  refine GlobalTheory.T.breuilKisin_envelope_frobenius_solutions_pow_dvd l K bk En (Fin d' × Fin d) c h k (fun p => Δ p.1 p.2) hc ?_ (i, j)
  intro g σ ha hb p
  have h0 : σ.f (Δ p.1 p.2) = 0 := congrFun (congrFun (hσ g σ ha hb) p.1) p.2
  exact ⟨0, h0.trans (mul_zero _).symm⟩

theorem strat_eps_compat_env (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K)
    (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)) (d d' : ℕ) (S : Strat bk d) (S' : Strat bk d')
    (Y : Matrix (Fin d') (Fin d) bk.S)
    (hφ : bk.E ^ S.a • (S'.A * Y.map (frobS l bk.a)) = bk.E ^ S'.a • (Y * S.A))
    (hg : ∀ g : ↥(GK K), S'.ε bk.ι ((ainfHom K g).comp bk.ι) * Y.map (BK.hf ((ainfHom K g).comp bk.ι)) =
      Y.map (BK.hf bk.ι) * S.ε bk.ι ((ainfHom K g).comp bk.ι)) :
    S'.ε En.inl En.inr * Y.map (BK.hf En.inr) = Y.map (BK.hf En.inl) * S.ε En.inl En.inr := by
  have h1 := GlobalTheory.T.stratifiedHom_defect_frobenius_equation l K bk d d' S S' Y hφ En.Q En.inl En.inr
  have hσ : ∀ (g : ↥(GK K)) (σ : Hom En.Q (ainfObj K)), σ.comp En.inl = bk.ι →
      σ.comp En.inr = (ainfHom K g).comp bk.ι →
      (S'.ε En.inl En.inr * Y.map (BK.hf En.inr) - Y.map (BK.hf En.inl) * S.ε En.inl En.inr).map σ.f = 0 := by
    intro g σ ha hb
    rw [strat_defect_map, ha, hb, hg g, sub_self]
  exact sub_eq_zero.1 (env_matrix_eq_zero En S S' _ h1 hσ)

end GlobalTheory.BSP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StratifiedHomComparisonCompatibleEnvelopeStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stratifiedHom_comparison_compatible_envelope : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)) (d d' : ℕ) (S : Strat bk d) (S' : Strat bk d') (Y : Matrix (Fin d') (Fin d) bk.S), bk.E ^ S.a • (S'.A * Y.map (frobS l bk.a)) = bk.E ^ S'.a • (Y * S.A) → (∀ g : ↥(GK K), S'.ε bk.ι ((ainfHom K g).comp bk.ι) * Y.map (BK.hf ((ainfHom K g).comp bk.ι)) = Y.map (BK.hf bk.ι) * S.ε bk.ι ((ainfHom K g).comp bk.ι)) → S'.ε En.inl En.inr * Y.map (BK.hf En.inr) = Y.map (BK.hf En.inl) * S.ε En.inl En.inr := by
  first | exact @GlobalTheory.BSP.strat_eps_compat_env | exact GlobalTheory.BSP.strat_eps_compat_env | (intros; apply GlobalTheory.BSP.strat_eps_compat_env <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StratPeriodMatrixEquivariantHomCommFrobenius
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StratPeriodMatrixEquivariantHomCommFrobenius
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem mreal_hom_frob : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' : ℕ) (S : Strat bk d) (S' : Strat bk d') (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (ρ' : ↥(GK K) → Matrix (Fin d') (Fin d') ℤ_[l]) (T : Matrix (Fin d) (Fin d) (WCb l)) (T' : Matrix (Fin d') (Fin d') (WCb l)), MReal S ρ T → MReal S' ρ' T' → ∀ f : Matrix (Fin d') (Fin d) ℤ_[l], (∀ g, f * ρ g = ρ' g * f) → ∀ Y : Matrix (Fin d') (Fin d) bk.S, T' * Y.map bk.evW = zW f * T → bk.E ^ S.a • (S'.A * Y.map (frobS l bk.a)) = bk.E ^ S'.a • (Y * S.A) := by
  intro l _ K bk d d' S S' ρ ρ' T T' hT hT' f _ Y hY
  set L := bk.evW with hL
  set Φ : WCb l →+* WCb l := (frobW l).toRingHom with hΦ
  have hc : ∀ x, L (frobS l bk.a x) = Φ (L x) := by
    intro x
    simp only [hL, hΦ, BK.evW, RingHom.comp_apply, bk.ev_frob, AlgHom.coe_toRingHom]
    exact (frobW_inclW _).symm
  have hsm : ∀ {m n : Type} (c : bk.S) (M : Matrix m n bk.S), (c • M).map L = L c • M.map L := by
    intro m n c M; ext i j; simp [Matrix.map_apply, Matrix.smul_apply]
  have hTΦ : ∀ {m n : Type} (M : Matrix m n (WCb l)), M.map (frobW l) = M.map Φ := fun _ => rfl
  have hz : (zW f).map Φ = zW f := by
    ext i j; simp [zW, hΦ, Matrix.map_apply]
  have hYΦ : (Y.map (frobS l bk.a)).map L = (Y.map L).map Φ := by
    refine Matrix.ext fun i j => ?_; simp only [Matrix.map_apply]; exact hc _
  have φT := hT.φ
  have φT' := hT'.φ
  rw [hTΦ] at φT φT'
  have hYf : T'.map Φ * (Y.map L).map Φ = zW f * T.map Φ := by
    rw [← Matrix.map_mul, hY, Matrix.map_mul, hz]
  have key : T' * (bk.E ^ S.a • (S'.A * Y.map (frobS l bk.a))).map L =
      T' * (bk.E ^ S'.a • (Y * S.A)).map L := by
    rw [hsm, hsm, Matrix.map_mul, Matrix.map_mul, hYΦ, Matrix.mul_smul, Matrix.mul_smul, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, ← φT', map_pow, map_pow, Matrix.smul_mul, smul_smul, hYf, hY, Matrix.mul_assoc,
      ← φT, Matrix.mul_smul, smul_smul, mul_comm]
  obtain ⟨u, hu⟩ := hT'.unit
  have key2 : (bk.E ^ S.a • (S'.A * Y.map (frobS l bk.a))).map L = (bk.E ^ S'.a • (Y * S.A)).map L := by
    have := congrArg (fun M => (↑u⁻¹ : Matrix (Fin d') (Fin d') (WCb l)) * M) key
    simp only [← hu, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul] at this
    exact this
  have hinj := (GlobalTheory.T.breuilKisin_evW_isUnit_injective_dvd l K bk).2.1
  refine Matrix.ext fun i j => ?_
  exact hinj (congrFun (congrFun key2 i) j)

end GlobalTheory.BSP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StratPeriodMatrixEquivariantHomCommFrobeniusStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stratPeriodMatrix_equivariant_hom_comm_frobenius : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' : ℕ) (S : Strat bk d) (S' : Strat bk d') (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (ρ' : ↥(GK K) → Matrix (Fin d') (Fin d') ℤ_[l]) (T : Matrix (Fin d) (Fin d) (WCb l)) (T' : Matrix (Fin d') (Fin d') (WCb l)), MReal S ρ T → MReal S' ρ' T' → ∀ f : Matrix (Fin d') (Fin d) ℤ_[l], (∀ g, f * ρ g = ρ' g * f) → ∀ Y : Matrix (Fin d') (Fin d) bk.S, T' * Y.map bk.evW = zW f * T → bk.E ^ S.a • (S'.A * Y.map (frobS l bk.a)) = bk.E ^ S'.a • (Y * S.A) := by
  first | exact @GlobalTheory.BSP.mreal_hom_frob | exact GlobalTheory.BSP.mreal_hom_frob | (intros; apply GlobalTheory.BSP.mreal_hom_frob <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StratifiedPhiModuleEquivariantMatrixCommute
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StratifiedPhiModuleEquivariantMatrixCommute
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory

theorem strat_homGal : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' : ℕ) (S : Strat bk d) (S' : Strat bk d') (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (ρ' : ↥(GK K) → Matrix (Fin d') (Fin d') ℤ_[l]) (T : Matrix (Fin d) (Fin d) (WCb l)) (T' : Matrix (Fin d') (Fin d') (WCb l)), MReal S ρ T → MReal S' ρ' T' → ∀ f : Matrix (Fin d') (Fin d) ℤ_[l], (∀ g, f * ρ g = ρ' g * f) → ∀ Y : Matrix (Fin d') (Fin d) bk.S, T' * Y.map bk.evW = zW f * T → ∀ g : ↥(GK K), S'.ε bk.ι ((ainfHom K g).comp bk.ι) * Y.map (BK.hf ((ainfHom K g).comp bk.ι)) = Y.map (BK.hf bk.ι) * S.ε bk.ι ((ainfHom K g).comp bk.ι) := by
  intro l _ K bk d d' S S' ρ ρ' T T' hT hT' f hf Y hY g
  let G : WCb l →+* WCb l := (galW l (g : GQ l)).toRingEquiv.toRingHom
  have hG : ∀ z : ℤ_[l], G (algebraMap ℤ_[l] (WCb l) z) = algebraMap ℤ_[l] (WCb l) z :=
    fun z => (galW l (g : GQ l)).commutes z
  have hzG : ∀ {m n : Type} (M : Matrix m n ℤ_[l]), (zW M).map G = zW M := by
    intro m n M; exact Matrix.ext fun i j => hG _
  have hYG : (Y.map bk.evW).map G = (Y.map (BK.hf ((ainfHom K g).comp bk.ι))).map (inclW l) := by
    exact Matrix.ext fun i j => galW_inclW (g : GQ l) (bk.ev (Y i j))
  have hzmul : ∀ {m n o : Type} [Fintype n] (A : Matrix m n ℤ_[l]) (B : Matrix n o ℤ_[l]),
      zW (A * B) = zW A * zW B := fun A B => Matrix.map_mul
  have h1 := congrArg (fun M => M.map G) hY
  simp only [Matrix.map_mul, hzG, hYG] at h1

  have e1 : T' * ((S'.ε bk.ι ((ainfHom K g).comp bk.ι)).map (inclW l) *
      (Y.map (BK.hf ((ainfHom K g).comp bk.ι))).map (inclW l)) =
      T' * ((Y.map (BK.hf bk.ι)).map (inclW l) * (S.ε bk.ι ((ainfHom K g).comp bk.ι)).map (inclW l)) := by
    have a1 := hT'.gal g
    have a2 := hT.gal g
    have a3 : T'.map (galW l (g : GQ l)) = T'.map G := rfl
    have a4 : T.map (galW l (g : GQ l)) = T.map G := rfl
    have a5 : (Y.map (BK.hf bk.ι)).map (inclW l) = Y.map bk.evW := Matrix.map_map
    rw [a3] at a1
    rw [a4] at a2
    rw [a5]
    calc _ = (T' * (S'.ε bk.ι ((ainfHom K g).comp bk.ι)).map (inclW l)) *
          (Y.map (BK.hf ((ainfHom K g).comp bk.ι))).map (inclW l) := (Matrix.mul_assoc _ _ _).symm
      _ = zW (ρ' g) * (T'.map G * (Y.map (BK.hf ((ainfHom K g).comp bk.ι))).map (inclW l)) := by
          rw [← a1, Matrix.mul_assoc]
      _ = zW (ρ' g * f) * T.map G := by rw [h1, hzmul, Matrix.mul_assoc]
      _ = zW f * (zW (ρ g) * T.map G) := by rw [← hf g, hzmul, Matrix.mul_assoc]
      _ = (T' * Y.map bk.evW) * (S.ε bk.ι ((ainfHom K g).comp bk.ι)).map (inclW l) := by
          rw [a2, hY, Matrix.mul_assoc]
      _ = _ := Matrix.mul_assoc _ _ _
  obtain ⟨u, hu⟩ := hT'.unit
  rw [← hu] at e1
  have e2 := congrArg (fun M => (↑u⁻¹ : Matrix (Fin d') (Fin d') (WCb l)) * M) e1
  simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul] at e2
  apply Matrix.map_injective (f := inclW l) inclW_injective
  exact (Matrix.map_mul (f := inclW l)).trans (e2.trans (Matrix.map_mul (f := inclW l)).symm)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StratifiedPhiModuleEquivariantMatrixCommuteStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stratifiedPhiModule_equivariant_matrix_commute : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' : ℕ) (S : Strat bk d) (S' : Strat bk d') (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (ρ' : ↥(GK K) → Matrix (Fin d') (Fin d') ℤ_[l]) (T : Matrix (Fin d) (Fin d) (WCb l)) (T' : Matrix (Fin d') (Fin d') (WCb l)), MReal S ρ T → MReal S' ρ' T' → ∀ f : Matrix (Fin d') (Fin d) ℤ_[l], (∀ g, f * ρ g = ρ' g * f) → ∀ Y : Matrix (Fin d') (Fin d) bk.S, T' * Y.map bk.evW = zW f * T → ∀ g : ↥(GK K), S'.ε bk.ι ((ainfHom K g).comp bk.ι) * Y.map (BK.hf ((ainfHom K g).comp bk.ι)) = Y.map (BK.hf bk.ι) * S.ε bk.ι ((ainfHom K g).comp bk.ι) := by
  first | exact @GlobalTheory.strat_homGal | exact GlobalTheory.strat_homGal | (intros; apply GlobalTheory.strat_homGal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsStratifiedPhiModuleHomOfGaloisEquivariant
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory

theorem isStratHom_of_equivariant : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' : ℕ) (S : Strat bk d)
    (S' : Strat bk d') (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l])
    (ρ' : ↥(GK K) → Matrix (Fin d') (Fin d') ℤ_[l]) (T : Matrix (Fin d) (Fin d) (WCb l))
    (T' : Matrix (Fin d') (Fin d') (WCb l)), MReal S ρ T → MReal S' ρ' T' →
    ∀ f : Matrix (Fin d') (Fin d) ℤ_[l], (∀ g, f * ρ g = ρ' g * f) →
    ∀ Y : Matrix (Fin d') (Fin d) bk.S, T' * Y.map bk.evW = zW f * T → IsStratHom S S' Y := by
  intro l _ K bk d d' S S' ρ ρ' T T' hT hT' f hf Y hY
  have hφ := GlobalTheory.T.stratPeriodMatrix_equivariant_hom_comm_frobenius l K bk d d' S S' ρ ρ' T T' hT hT' f hf Y hY
  have hgal := GlobalTheory.T.stratifiedPhiModule_equivariant_matrix_commute l K bk d d' S S' ρ ρ' T T' hT hT' f hf Y hY
  have hfr : IsFrame bk bk.prism (bk.toP bk.E) (bk.toP X) := GlobalTheory.T.isOrientedPrismUniformizerFrame_breuilKisinHom l K bk bk.prism (Hom.id _)
  obtain ⟨En⟩ := GlobalTheory.T.nonempty_breuilKisinPrismCoproduct l K bk bk.prism _ _ hfr
  have h1 := GlobalTheory.T.stratifiedHom_comparison_compatible_envelope l K bk En d d' S S' Y hφ hgal
  refine ⟨hφ, ?_⟩
  intro B f₁ g₁
  obtain ⟨k, ⟨hk1, hk2⟩, -⟩ := En.univ B f₁ g₁
  subst hk1 hk2
  have e : ∀ {m n : Type} (M : Matrix m n bk.S) (h : Hom bk.prism En.Q),
      (M.map (BK.hf h)).map k.f = M.map (BK.hf (k.comp h)) := fun M h => rfl
  have h2 : (S'.ε En.inl En.inr * Y.map (BK.hf En.inr)).map k.f =
      (Y.map (BK.hf En.inl) * S.ε En.inl En.inr).map k.f := congrArg (fun M => M.map k.f) h1
  have m1 := Matrix.map_mul (f := k.f) (L := S'.ε En.inl En.inr) (M := Y.map (BK.hf En.inr))
  have m2 := Matrix.map_mul (f := k.f) (L := Y.map (BK.hf En.inl)) (M := S.ε En.inl En.inr)
  have n1 := S'.ε_nat k En.inl En.inr
  have n2 := S.ε_nat k En.inl En.inr
  exact (congrArg₂ (· * ·) n1.symm (e Y En.inr).symm).trans
    (m1.symm.trans (h2.trans (m2.trans (congrArg₂ (· * ·) (e Y En.inl) n2))))

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsStratifiedPhiModuleHomOfGaloisEquivariantStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isStratifiedPhiModuleHom_of_galois_equivariant : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' : ℕ) (S : Strat bk d) (S' : Strat bk d') (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (ρ' : ↥(GK K) → Matrix (Fin d') (Fin d') ℤ_[l]) (T : Matrix (Fin d) (Fin d) (WCb l)) (T' : Matrix (Fin d') (Fin d') (WCb l)), MReal S ρ T → MReal S' ρ' T' → ∀ f : Matrix (Fin d') (Fin d) ℤ_[l], (∀ g, f * ρ g = ρ' g * f) → ∀ Y : Matrix (Fin d') (Fin d) bk.S, T' * Y.map bk.evW = zW f * T → IsStratHom S S' Y := by
  first | exact @GlobalTheory.isStratHom_of_equivariant | exact GlobalTheory.isStratHom_of_equivariant | (intros; apply GlobalTheory.isStratHom_of_equivariant <;> assumption)
end
