module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBoundedOfPhiEquationDisc

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinDiscCocycleFrobeniusEquation
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinDiscCocycleFrobeniusEquation
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP.CocycleFrob

theorem σA_frob {l : ℕ} [Fact l.Prime] (g : GQ l) (x : Ainf l) :
    Per.σA g (WittVector.frobenius x) = WittVector.frobenius (Per.σA g x) := by
  rw [WittVector.frobenius_eq_map_frobenius]
  refine WittVector.ext fun n => ?_
  rw [GlobalTheory.RingIface.sigA_coeff l g, WittVector.map_coeff, WittVector.map_coeff,
    GlobalTheory.RingIface.sigA_coeff l g, frobenius_def, frobenius_def, map_pow]

theorem cancel_left {R : Type} [CommRing R] [IsDomain R] {n : Type} [Fintype n] [DecidableEq n]
    (Y X₁ X₂ : Matrix n n R) (c : R) (hc : c ≠ 0) (hY : Y.det ≠ 0) (h : c • (Y * X₁) = c • (Y * X₂)) :
    X₁ = X₂ := by
  have h1 : Y * X₁ = Y * X₂ := by
    ext i j
    have := congrFun (congrFun h i) j
    simp only [Matrix.smul_apply, smul_eq_mul] at this
    exact mul_left_cancel₀ hc this
  have h2 := congrArg (fun Z => Y.adjugate * Z) h1
  simp only [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul] at h2
  ext i j
  have := congrFun (congrFun h2 i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  exact mul_left_cancel₀ hY this

theorem frob_eq : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d M N : ℕ) (Y : Matrix (Fin d) (Fin d) (Ainf l)) (A A' : Matrix (Fin d) (Fin d) bk.S), A * A' = bk.E ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) bk.S) → bk.ev bk.E ^ N • Y.map WittVector.frobenius = bk.ev bk.E ^ M • (Y * A.map bk.ev) → (Y.map bk.iA).det ≠ 0 → ∀ (g : GQ l) (G Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA g) G → IsDiscMap (l := _) (u := _) (ρ := _) WittVector.frobenius Φ → ∀ (w : (Ainf l)ˣ), Per.σA g (bk.ev bk.E) = bk.ev bk.E * w → ∀ (P : Matrix (Fin d) (Fin d) (Ainf l)), P.map WittVector.frobenius = P → ∀ (e : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)), bk.iA (Per.σA g τ) ^ M • (Y.map bk.iA * e) = bk.iA τ ^ M • (P.map bk.iA * (Y.map (Per.σA g)).map bk.iA) → bk.iS bk.E ^ (2 * N) • e = (((↑w⁻¹ : Ainf l) ^ N) • A.map bk.ev).map bk.iA * e.map Φ * ((A'.map bk.ev).map (Per.σA g)).map bk.iA := by
  intro l _ K bk τ hτ d M N Y A A' hAA hφ hdet g G Φ _ hΦ w hw P hP e he
  obtain ⟨-, -, -, h0, h1, -⟩ := GlobalTheory.BSP.exists_discMaps l K bk
  haveI : IsDomain (bk.DA bk.ρ₀) := (GlobalTheory.BSP.discAinf_isDomain l K bk bk.ρ₀ h0 h1).1
  obtain ⟨ι, ⟨tb⟩⟩ := GlobalTheory.BSP.AinfTopBasis.main l K bk
  have hinj : Function.Injective bk.iA := (GlobalTheory.BSP.toDisc_injective_of_topBasis l K bk (Ainf l) bk.ev ι tb bk.ρ₀ h0 h1).1
  obtain ⟨-, -, -, hστ⟩ := GlobalTheory.BSP.isUnit_inclW_of_isPer l K bk τ hτ
  have ht' : bk.iA (Per.σA g τ) ≠ 0 := by
    rw [← map_zero bk.iA]
    intro h
    have h2 := hστ g
    rw [hinj h, map_zero] at h2
    exact not_isUnit_zero h2
  have hE : bk.iA (bk.ev bk.E) ≠ 0 := by
    rw [← map_zero bk.iA]
    intro h
    exact bk.E_ne_zero (bk.ev_injective ((hinj h).trans (map_zero _).symm))
  have hu : bk.iA (w : Ainf l) ≠ 0 := fun h => by
    have := congrArg bk.iA w.mul_inv
    rw [map_mul, h, zero_mul, map_one] at this
    exact zero_ne_one this

  have hΦA : ∀ x, Φ (bk.iA x) = bk.iA (WittVector.frobenius x) := hΦ.ext
  have hσE : ∀ k : ℕ, bk.iA (Per.σA g (bk.ev bk.E ^ k)) = (bk.iA (bk.ev bk.E) * bk.iA w) ^ k := fun k => by
    rw [map_pow, hw, map_pow, map_mul]

  have hφ1 : bk.iA (bk.ev bk.E) ^ N • (Y.map WittVector.frobenius).map bk.iA =
      bk.iA (bk.ev bk.E) ^ M • (Y.map bk.iA * (A.map bk.ev).map bk.iA) := by
    have := congrArg (fun X => X.map bk.iA) hφ
    simp only [Matrix.map_smul' _ _ _ (map_mul bk.iA), Matrix.map_mul, map_pow] at this
    exact this

  have hφ2 : (bk.iA (bk.ev bk.E) * bk.iA w) ^ N • ((Y.map (Per.σA g)).map WittVector.frobenius).map bk.iA =
      (bk.iA (bk.ev bk.E) * bk.iA w) ^ M • ((Y.map (Per.σA g)).map bk.iA * ((A.map bk.ev).map (Per.σA g)).map bk.iA) := by
    have := congrArg (fun X => (X.map (Per.σA g)).map bk.iA) hφ
    simp only [Matrix.map_smul' _ _ _ (map_mul bk.iA), Matrix.map_smul' _ _ _ (map_mul (Per.σA g)),
      Matrix.map_mul] at this
    rw [hσE, hσE] at this
    have hc : ((Y.map WittVector.frobenius).map (Per.σA g)) = ((Y.map (Per.σA g)).map WittVector.frobenius) := by
      exact Matrix.ext fun i j => σA_frob g (Y i j)
    rw [hc] at this
    exact this

  have he1 : (bk.iA (bk.ev bk.E) * bk.iA w * bk.iA (Per.σA g τ)) ^ M • ((Y.map WittVector.frobenius).map bk.iA * e.map Φ) =
      (bk.iA (bk.ev bk.E) * bk.iA τ) ^ M • (P.map bk.iA * ((Y.map (Per.σA g)).map WittVector.frobenius).map bk.iA) := by
    have := congrArg (fun X => X.map Φ) he
    simp only [Matrix.map_smul' _ _ _ (map_mul Φ), Matrix.map_mul, map_pow, hΦA] at this
    have m1 : ∀ Z : Matrix (Fin d) (Fin d) (Ainf l), (Z.map bk.iA).map Φ = (Z.map WittVector.frobenius).map bk.iA :=
      fun Z => Matrix.ext fun i j => hΦA (Z i j)
    rw [m1, m1, m1, hP, ← σA_frob, hτ.1, map_mul, hw, map_mul, map_mul, map_mul] at this
    exact this
  have hA2 : ((A.map bk.ev).map (Per.σA g)).map bk.iA * ((A'.map bk.ev).map (Per.σA g)).map bk.iA =
      (bk.iA (bk.ev bk.E) * bk.iA w) ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) := by
    have := congrArg (fun X => ((X.map bk.ev).map (Per.σA g)).map bk.iA) hAA
    simp only [Matrix.map_smul' _ _ _ (map_mul bk.iA), Matrix.map_smul' _ _ _ (map_mul (Per.σA g)),
      Matrix.map_smul' _ _ _ (map_mul bk.ev), Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] at this
    rw [map_pow bk.ev, hσE] at this
    exact this
  have hv : bk.iA ((w⁻¹ : (Ainf l)ˣ) : Ainf l) * bk.iA w = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have hiS : bk.iS bk.E = bk.iA (bk.ev bk.E) := rfl
  rw [hiS, Matrix.map_smul' _ _ _ (map_mul bk.iA), map_pow]
  generalize (Y.map WittVector.frobenius).map bk.iA = ΦY at hφ1 he1
  generalize ((Y.map (Per.σA g)).map WittVector.frobenius).map bk.iA = ΦGY at hφ2 he1
  generalize (Y.map (Per.σA g)).map bk.iA = GY at hφ2 he
  generalize Y.map bk.iA = YY at hφ1 he hdet
  generalize (A.map bk.ev).map bk.iA = AA at hφ1 ⊢
  generalize ((A.map bk.ev).map (Per.σA g)).map bk.iA = GA at hφ2 hA2
  generalize ((A'.map bk.ev).map (Per.σA g)).map bk.iA = GA' at hA2 ⊢
  generalize P.map bk.iA = PP at he he1
  generalize e.map Φ = Φe at he1 ⊢
  generalize bk.iA (bk.ev bk.E) = E' at *
  generalize bk.iA ((w⁻¹ : (Ainf l)ˣ) : Ainf l) = v at *
  generalize bk.iA (w : Ainf l) = u at *
  generalize bk.iA (Per.σA g τ) = t' at *
  generalize bk.iA τ = t at *
  have key : (E' ^ (2 * M) * u ^ M * t' ^ M) • (YY * (u ^ N • (AA * Φe))) =
      (E' ^ (2 * M) * u ^ M * t' ^ M) • (YY * (e * GA)) :=
    calc (E' ^ (2 * M) * u ^ M * t' ^ M) • (YY * (u ^ N • (AA * Φe)))
        = (u ^ N * (E' * u * t') ^ M) • ((E' ^ M • (YY * AA)) * Φe) := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]; congr 1; ring
      _ = (u ^ N * (E' * u * t') ^ M) • ((E' ^ N • ΦY) * Φe) := by rw [hφ1]
      _ = (E' * u) ^ N • ((E' * u * t') ^ M • (ΦY * Φe)) := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]; congr 1; ring
      _ = (E' * u) ^ N • ((E' * t) ^ M • (PP * ΦGY)) := by rw [he1]
      _ = (E' * t) ^ M • (PP * ((E' * u) ^ N • ΦGY)) := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]; congr 1; ring
      _ = (E' * t) ^ M • (PP * ((E' * u) ^ M • (GY * GA))) := by rw [hφ2]
      _ = (E' ^ M * (E' * u) ^ M) • ((t ^ M • (PP * GY)) * GA) := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]; congr 1; ring
      _ = (E' ^ M * (E' * u) ^ M) • ((t' ^ M • (YY * e)) * GA) := by rw [he]
      _ = (E' ^ (2 * M) * u ^ M * t' ^ M) • (YY * (e * GA)) := by
          simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]; congr 1; ring
  have hu' : u ≠ 0 := fun h => by rw [h, mul_zero] at hv; exact zero_ne_one hv
  have hc : E' ^ (2 * M) * u ^ M * t' ^ M ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ hE) (pow_ne_zero _ hu')) (pow_ne_zero _ ht')
  have hX := cancel_left YY _ _ _ hc hdet key
  calc E' ^ (2 * N) • e = (v ^ (2 * N) * (E' * u) ^ (2 * N)) • e := by
        congr 1
        rw [show v ^ (2 * N) * (E' * u) ^ (2 * N) = E' ^ (2 * N) * (v * u) ^ (2 * N) by ring, hv, one_pow, mul_one]
    _ = v ^ (2 * N) • (e * ((E' * u) ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)))) := by
        rw [Matrix.mul_smul, Matrix.mul_one, smul_smul]
    _ = v ^ (2 * N) • ((e * GA) * GA') := by rw [← hA2, Matrix.mul_assoc]
    _ = v ^ (2 * N) • ((u ^ N • (AA * Φe)) * GA') := by rw [hX]
    _ = (v ^ N • AA) * Φe * GA' := by
        simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
        congr 1
        rw [show v ^ (2 * N) * u ^ N = v ^ N * (v * u) ^ N by ring, hv, one_pow, mul_one]

end GlobalTheory.BSP.CocycleFrob
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinDiscCocycleFrobeniusEquationStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_disc_cocycle_frobenius_equation : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d M N : ℕ) (Y : Matrix (Fin d) (Fin d) (Ainf l)) (A A' : Matrix (Fin d) (Fin d) bk.S), A * A' = bk.E ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) bk.S) → bk.ev bk.E ^ N • Y.map WittVector.frobenius = bk.ev bk.E ^ M • (Y * A.map bk.ev) → (Y.map bk.iA).det ≠ 0 → ∀ (g : GQ l) (G Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA g) G → IsDiscMap (l := _) (u := _) (ρ := _) WittVector.frobenius Φ → ∀ (w : (Ainf l)ˣ), Per.σA g (bk.ev bk.E) = bk.ev bk.E * w → ∀ (P : Matrix (Fin d) (Fin d) (Ainf l)), P.map WittVector.frobenius = P → ∀ (e : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)), bk.iA (Per.σA g τ) ^ M • (Y.map bk.iA * e) = bk.iA τ ^ M • (P.map bk.iA * (Y.map (Per.σA g)).map bk.iA) → bk.iS bk.E ^ (2 * N) • e = (((↑w⁻¹ : Ainf l) ^ N) • A.map bk.ev).map bk.iA * e.map Φ * ((A'.map bk.ev).map (Per.σA g)).map bk.iA := by
  first | (exact @GlobalTheory.BSP.CocycleFrob.frob_eq) | (exact GlobalTheory.BSP.CocycleFrob.frob_eq) | (intros; apply GlobalTheory.BSP.CocycleFrob.frob_eq  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSemistableDiscCocycle
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSemistableDiscCocycle
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim

theorem exists_gal_ev_E_unit {l : ℕ} [Fact l.Prime] {K : FinExt l} (bk : BK K) (g : GQ l) :
    ∃ w : (Ainf l)ˣ, Per.σA g (bk.ev bk.E) = bk.ev bk.E * w := by
  have key : ∀ h : GQ l, bk.ev bk.E ∣ Per.σA h (bk.ev bk.E) := fun h => by
    rw [← Ideal.mem_span_singleton, bk.span_ev, RingHom.mem_ker, GlobalTheory.RingBasics.θ_σA]
    have : Per.θ l (bk.ev bk.E) = 0 := by
      rw [← RingHom.mem_ker, ← bk.span_ev]; exact Ideal.mem_span_singleton_self _
    rw [this, map_zero]
  haveI : IsDomain (Ainf l) := inclW_injective.isDomain (inclW l)
  have h2 : Per.σA g (bk.ev bk.E) ∣ bk.ev bk.E := by
    have := map_dvd (Per.σA g) (key g⁻¹)
    rwa [← GlobalTheory.RingBasics.σA_mul, mul_inv_cancel, GlobalTheory.RingBasics.σA_one] at this
  obtain ⟨w, hw⟩ := associated_of_dvd_dvd (key g) h2
  exact ⟨w, hw.symm⟩

theorem WSeed.exists_disc_cocycle : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (s : WSeed bk d ρ τ) (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Z : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)) (i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀), IsUnit Z → IsDiscMap (l := _) (u := _) (ρ := _) bk.ev i → s.W * Z.map i = Y.map bk.iA → ∀ (g : ↥(GK K)) (G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA (g : GQ l)) G → ∃ e : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀), G (bk.iS bk.E) ^ s.N • (s.X.map bk.iS * Z.map i * e) = bk.iS bk.E ^ s.N • (s.κ g * (s.X.map bk.iS * Z.map i).map G) ∧ bk.iA (Per.σA (g : GQ l) τ) ^ s.N • (Y.map bk.iA * e) = bk.iA τ ^ s.N • (((ρ g).map (algebraMap ℤ_[l] (Ainf l))).map bk.iA * (Y.map (Per.σA (g : GQ l))).map bk.iA) := by
  intro l _ K bk τ hτ d ρ s Y Z i hZ hi hWZ g G hG
  obtain ⟨h0, h1⟩ := bk.ρ₀_pos_lt_one
  haveI : IsDomain (bk.DA bk.ρ₀) := (GlobalTheory.BSP.discAinf_isDomain l K bk bk.ρ₀ h0 h1).1
  obtain ⟨ι, ⟨tb⟩⟩ := GlobalTheory.BSP.AinfTopBasis.main l K bk
  have hinj : Function.Injective bk.iA :=
    (GlobalTheory.BSP.toDisc_injective_of_topBasis l K bk (Ainf l) bk.ev ι tb bk.ρ₀ h0 h1).1
  have hGA : ∀ y, G (bk.iA y) = bk.iA (Per.σA (g : GQ l) y) := hG.ext
  have hevE : bk.ev bk.E ≠ 0 := fun h => bk.frobenius_ev_E_ne_zero hτ (by rw [h, map_zero])
  have hE : bk.iS bk.E ≠ 0 := fun h => hevE (hinj (h.trans (map_zero _).symm))
  have hL0 : (l : bk.DA bk.ρ₀) ≠ 0 := fun h =>
    WittVector.p_nonzero l (OCb l) (hinj (by rw [map_natCast, map_zero]; exact h))
  obtain ⟨w, hw⟩ := exists_gal_ev_E_unit bk (g : GQ l)
  have hvu : bk.iA (w : Ainf l) * bk.iA ((w⁻¹ : (Ainf l)ˣ) : Ainf l) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hv0 : bk.iA (w : Ainf l) ≠ 0 := left_ne_zero_of_mul_eq_one hvu
  have hGE : G (bk.iS bk.E) = bk.iS bk.E * bk.iA (w : Ainf l) := by
    change G (bk.iA (bk.ev bk.E)) = _
    rw [hGA, hw, map_mul]
    rfl
  obtain ⟨li, hli⟩ : ∃ li : bk.DA bk.ρ₀, li * (l : bk.DA bk.ρ₀) = 1 := by
    obtain ⟨x, hx⟩ := (isUnit_l_disc l (bk.ev (PowerSeries.X : bk.S)) bk.ρ₀).exists_left_inv
    exact ⟨x, hx⟩
  have hnp : ∀ a b, ∃ c, (s.X'.map bk.iS * s.κ g * (s.X.map bk.iS).map G) a b = bk.iS bk.E ^ (2 * s.N) * c :=
    fun a b => s.nopole g G hG a b
  choose Q hQ using hnp
  have hQm : s.X'.map bk.iS * s.κ g * (s.X.map bk.iS).map G = bk.iS bk.E ^ (2 * s.N) • Matrix.of Q := by
    ext a b; rw [hQ a b]; rfl
  have hXX : s.X.map bk.iS * s.X'.map bk.iS =
      ((l : bk.DA bk.ρ₀) ^ s.c₂ * bk.iS bk.E ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) := by
    rw [← Matrix.map_mul, s.X_mul, Matrix.map_smul' _ _ _ (map_mul _), Matrix.map_one _ (map_zero _) (map_one _)]
    simp only [map_mul, map_pow, map_natCast]
  have hc : (l : bk.DA bk.ρ₀) ^ s.c₂ * bk.iS bk.E ^ (2 * s.N) ≠ 0 := mul_ne_zero (pow_ne_zero _ hL0) (pow_ne_zero _ hE)
  have hX'X := GlobalTheory.BSP.mul_comm_of_mul_eq_smul_one _ _ _ hc hXX

  have hC1 : s.X.map bk.iS * Matrix.of Q = (l : bk.DA bk.ρ₀) ^ s.c₂ • (s.κ g * (s.X.map bk.iS).map G) := by
    refine smul_right_injective (Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) (pow_ne_zero (2 * s.N) hE) ?_
    dsimp only
    rw [← Matrix.mul_smul, ← hQm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hXX, Matrix.smul_mul, Matrix.smul_mul,
      Matrix.one_mul, smul_smul, mul_comm ((l : bk.DA bk.ρ₀) ^ s.c₂)]
  have hZi : IsUnit (Z.map i) := hZ.map (RingHom.mapMatrix i)
  have hZZ : Z.map i * (Z.map i)⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hZi)
  refine ⟨(li ^ s.c₂ * bk.iA ((w⁻¹ : (Ainf l)ˣ) : Ainf l) ^ s.N) • ((Z.map i)⁻¹ * Matrix.of Q * (Z.map i).map G), ?_, ?_⟩
  · have h3 : s.X.map bk.iS * Z.map i * ((li ^ s.c₂ * bk.iA ((w⁻¹ : (Ainf l)ˣ) : Ainf l) ^ s.N) •
        ((Z.map i)⁻¹ * Matrix.of Q * (Z.map i).map G)) =
        (li ^ s.c₂ * bk.iA ((w⁻¹ : (Ainf l)ˣ) : Ainf l) ^ s.N) • (s.X.map bk.iS * Matrix.of Q * (Z.map i).map G) := by
      rw [Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc (s.X.map bk.iS) (Z.map i), hZZ,
        Matrix.mul_one]
    have hs : G (bk.iS bk.E) ^ s.N * (li ^ s.c₂ * bk.iA ((w⁻¹ : (Ainf l)ˣ) : Ainf l) ^ s.N) * (l : bk.DA bk.ρ₀) ^ s.c₂ =
        bk.iS bk.E ^ s.N := by
      rw [hGE]
      calc (bk.iS bk.E * bk.iA (w : Ainf l)) ^ s.N * (li ^ s.c₂ * bk.iA ((w⁻¹ : (Ainf l)ˣ) : Ainf l) ^ s.N) *
            (l : bk.DA bk.ρ₀) ^ s.c₂
          = bk.iS bk.E ^ s.N * (bk.iA (w : Ainf l) * bk.iA ((w⁻¹ : (Ainf l)ˣ) : Ainf l)) ^ s.N *
            (li * (l : bk.DA bk.ρ₀)) ^ s.c₂ := by ring
        _ = _ := by rw [hvu, hli, one_pow, one_pow, mul_one, mul_one]
    rw [h3, hC1, Matrix.smul_mul, smul_smul, smul_smul, hs, Matrix.map_mul, ← Matrix.mul_assoc]
  · have hGXX : (s.X'.map bk.iS).map G * (s.X.map bk.iS).map G =
        G ((l : bk.DA bk.ρ₀) ^ s.c₂ * bk.iS bk.E ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) := by
      rw [← Matrix.map_mul, hX'X, Matrix.map_smul' _ _ _ (map_mul _), Matrix.map_one _ (map_zero _) (map_one _)]
    have hYG : (Y.map (Per.σA (g : GQ l))).map bk.iA = s.W.map G * (Z.map i).map G := by
      rw [← Matrix.map_mul, hWZ, Matrix.map_map, Matrix.map_map]
      congr 1
      funext y
      exact (hGA y).symm
    have hρ : (ρ g).map (bk.iA.comp (algebraMap ℤ_[l] (Ainf l))) =
        ((ρ g).map (algebraMap ℤ_[l] (Ainf l))).map bk.iA := by
      rw [Matrix.map_map]; rfl
    have hL : (ρ g).map (bk.iA.comp (algebraMap ℤ_[l] (Ainf l))) * (s.W * s.X'.map bk.iS).map G *
        ((s.X.map bk.iS).map G * (Z.map i).map G) =
        G ((l : bk.DA bk.ρ₀) ^ s.c₂ * bk.iS bk.E ^ (2 * s.N)) •
          ((ρ g).map (bk.iA.comp (algebraMap ℤ_[l] (Ainf l))) * s.W.map G * (Z.map i).map G) := by
      rw [Matrix.map_mul]
      calc _ = (ρ g).map (bk.iA.comp (algebraMap ℤ_[l] (Ainf l))) * s.W.map G *
            ((s.X'.map bk.iS).map G * (s.X.map bk.iS).map G) * (Z.map i).map G := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hGXX, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
    have hR : s.W * s.X'.map bk.iS * s.κ g * ((s.X.map bk.iS).map G * (Z.map i).map G) =
        bk.iS bk.E ^ (2 * s.N) • (s.W * Matrix.of Q * (Z.map i).map G) := by
      calc _ = s.W * (s.X'.map bk.iS * s.κ g * (s.X.map bk.iS).map G) * (Z.map i).map G := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hQm, Matrix.mul_smul, Matrix.smul_mul]
    have h5 := congrArg (· * ((s.X.map bk.iS).map G * (Z.map i).map G)) (s.gal g G hG)
    rw [Matrix.smul_mul, Matrix.smul_mul, hL, hR, smul_smul, smul_smul] at h5
    have h6 : s.W * Z.map i * ((li ^ s.c₂ * bk.iA ((w⁻¹ : (Ainf l)ˣ) : Ainf l) ^ s.N) •
        ((Z.map i)⁻¹ * Matrix.of Q * (Z.map i).map G)) =
        (li ^ s.c₂ * bk.iA ((w⁻¹ : (Ainf l)ˣ) : Ainf l) ^ s.N) • (s.W * Matrix.of Q * (Z.map i).map G) := by
      rw [Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc s.W (Z.map i), hZZ, Matrix.mul_one]
    rw [hYG, ← hρ, ← hWZ, h6, smul_smul, ← Matrix.mul_assoc]
    have hk : bk.iS bk.E ^ (3 * s.N) * bk.iA (w : Ainf l) ^ (2 * s.N) * (l : bk.DA bk.ρ₀) ^ s.c₂ ≠ 0 :=
      mul_ne_zero (mul_ne_zero (pow_ne_zero _ hE) (pow_ne_zero _ hv0)) (pow_ne_zero _ hL0)
    refine smul_right_injective (Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) hk ?_
    dsimp only
    have hσE : bk.iA (Per.σA (g : GQ l) (bk.ev bk.E * τ)) =
        bk.iS bk.E * bk.iA (w : Ainf l) * bk.iA (Per.σA (g : GQ l) τ) := by
      rw [map_mul, hw, map_mul, map_mul]; rfl
    have hE2 : bk.iA (bk.ev bk.E * τ) = bk.iS bk.E * bk.iA τ := by rw [map_mul]; rfl
    have hGc : G ((l : bk.DA bk.ρ₀) ^ s.c₂ * bk.iS bk.E ^ (2 * s.N)) =
        (l : bk.DA bk.ρ₀) ^ s.c₂ * (bk.iS bk.E * bk.iA (w : Ainf l)) ^ (2 * s.N) := by
      rw [map_mul, map_pow, map_pow, map_natCast, hGE]
    rw [hσE, hE2, hGc] at h5
    rw [smul_smul, smul_smul]
    have hs1 : bk.iS bk.E ^ (3 * s.N) * bk.iA (w : Ainf l) ^ (2 * s.N) * (l : bk.DA bk.ρ₀) ^ s.c₂ *
        (bk.iA (Per.σA (g : GQ l) τ) ^ s.N * (li ^ s.c₂ * bk.iA ((w⁻¹ : (Ainf l)ˣ) : Ainf l) ^ s.N)) =
        (bk.iS bk.E * bk.iA (w : Ainf l) * bk.iA (Per.σA (g : GQ l) τ)) ^ s.N * bk.iS bk.E ^ (2 * s.N) := by
      calc _ = bk.iS bk.E ^ (3 * s.N) * bk.iA (w : Ainf l) ^ s.N * bk.iA (Per.σA (g : GQ l) τ) ^ s.N *
            (bk.iA (w : Ainf l) * bk.iA ((w⁻¹ : (Ainf l)ˣ) : Ainf l)) ^ s.N * (li * (l : bk.DA bk.ρ₀)) ^ s.c₂ := by ring
        _ = _ := by rw [hvu, hli]; ring
    have hs2 : bk.iS bk.E ^ (3 * s.N) * bk.iA (w : Ainf l) ^ (2 * s.N) * (l : bk.DA bk.ρ₀) ^ s.c₂ * bk.iA τ ^ s.N =
        (bk.iS bk.E * bk.iA τ) ^ s.N * ((l : bk.DA bk.ρ₀) ^ s.c₂ * (bk.iS bk.E * bk.iA (w : Ainf l)) ^ (2 * s.N)) := by
      ring
    rw [hs1, hs2]
    exact h5.symm

end GlobalTheory.BKLim
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSemistableDiscCocycleStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_semistable_disc_cocycle : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (s : WSeed bk d ρ τ) (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Z : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)) (i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀), IsUnit Z → IsDiscMap (l := _) (u := _) (ρ := _) bk.ev i → s.W * Z.map i = Y.map bk.iA → ∀ (g : ↥(GK K)) (G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA (g : GQ l)) G → ∃ e : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀), G (bk.iS bk.E) ^ s.N • (s.X.map bk.iS * Z.map i * e) = bk.iS bk.E ^ s.N • (s.κ g * (s.X.map bk.iS * Z.map i).map G) ∧ bk.iA (Per.σA (g : GQ l) τ) ^ s.N • (Y.map bk.iA * e) = bk.iA τ ^ s.N • (((ρ g).map (algebraMap ℤ_[l] (Ainf l))).map bk.iA * (Y.map (Per.σA (g : GQ l))).map bk.iA) := by
  first | (exact @GlobalTheory.BKLim.WSeed.exists_disc_cocycle) | (exact GlobalTheory.BKLim.WSeed.exists_disc_cocycle) | (intros; apply GlobalTheory.BKLim.WSeed.exists_disc_cocycle  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodsBreuilKisinGaloisStable
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim.GalStab

section Alg
variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

theorem det_ne_zero_of_mul_eq_smul [IsDomain R] {A B : Matrix n n R} {c : R} (hc : c ≠ 0) (h : A * B = c • 1) :
    A.det ≠ 0 := by
  have hd : A.det * B.det = c ^ Fintype.card n := by
    rw [← Matrix.det_mul, h, Matrix.det_smul, Matrix.det_one, mul_one]
  intro h0
  rw [h0, zero_mul] at hd
  exact pow_ne_zero _ hc hd.symm

omit [Fintype n] [DecidableEq n] in
theorem map_smul_hom {R' : Type} [CommRing R'] (f : R →+* R') (c : R) (M : Matrix n n R) :
    (c • M).map f = f c • M.map f := by
  ext i j; simp

end Alg

theorem smul_cancel_of_isUnit {R : Type} [CommRing R] {n : Type} {c : R} (hc : IsUnit c) {M M' : Matrix n n R}
    (h : c • M = c • M') : M = M' := by
  ext i j
  have := congrFun (congrFun h i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  exact hc.mul_left_cancel this

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l}

theorem gal_E (bk : BK K) (g : GQ l) : ∃ w : (Ainf l)ˣ, Per.σA g (bk.ev bk.E) = bk.ev bk.E * w := by
  have key : ∀ h : GQ l, bk.ev bk.E ∣ Per.σA h (bk.ev bk.E) := fun h => by
    rw [← Ideal.mem_span_singleton, bk.span_ev, RingHom.mem_ker, GlobalTheory.RingBasics.θ_σA]
    have : Per.θ l (bk.ev bk.E) = 0 := by
      rw [← RingHom.mem_ker, ← bk.span_ev]; exact Ideal.mem_span_singleton_self _
    rw [this, map_zero]
  haveI : IsDomain (Ainf l) := inclW_injective.isDomain (inclW l)
  have h2 : Per.σA g (bk.ev bk.E) ∣ bk.ev bk.E := by
    have := map_dvd (Per.σA g) (key g⁻¹)
    rwa [← GlobalTheory.RingBasics.σA_mul, mul_inv_cancel, GlobalTheory.RingBasics.σA_one] at this
  obtain ⟨w, hw⟩ := associated_of_dvd_dvd (key g) h2
  exact ⟨w, hw.symm⟩

theorem frob_zl (z : ℤ_[l]) :
    WittVector.frobenius (algebraMap ℤ_[l] (Ainf l) z) = algebraMap ℤ_[l] (Ainf l) z := by
  rw [WittVector.frobenius_eq_map_frobenius]
  exact map_zlW l _ z

theorem frob_Y (bk : BK K) {τ : Ainf l} (hτ : bk.IsPer τ) {d N : ℕ} {ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]}
    (F : Pre bk N d ρ) (M : ℕ) (Y : Matrix (Fin d) (Fin d) (Ainf l)) (hY : Y.map (inclW l) = inclW l τ ^ M • F.T) :
    bk.ev bk.E ^ N • Y.map WittVector.frobenius = bk.ev bk.E ^ M • (Y * F.A.map bk.ev) := by
  apply Matrix.map_injective inclW_injective
  beta_reduce
  have hfτ : frobW l (inclW l τ) = inclW l (bk.ev bk.E) * inclW l τ := by rw [frobW_inclW, hτ.1, map_mul]
  have h1 : (Y.map WittVector.frobenius).map (inclW l) = (Y.map (inclW l)).map (frobW l) := by
    ext i j; simp only [Matrix.map_apply, frobW_inclW]
  have hA : (F.A.map bk.ev).map (inclW l) = F.A.map bk.evW := by rw [Matrix.map_map]; rfl
  have hφ : inclW l (bk.ev bk.E) ^ N • F.T.map (frobW l) = F.T * F.A.map bk.evW := F.φ
  have h2 : (inclW l τ ^ M • F.T).map (frobW l) = (inclW l (bk.ev bk.E) * inclW l τ) ^ M • F.T.map (frobW l) := by
    ext i j; simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, hfτ]
  rw [map_smul_hom, map_smul_hom, h1, Matrix.map_mul, hY, h2, hA, Matrix.smul_mul,
    ← hφ, smul_smul, smul_smul, smul_smul, map_pow, map_pow]
  congr 1
  ring

theorem disc_cocycle (bk : BK K) {τ : Ainf l} (hτ : bk.IsPer τ) {d : ℕ} {ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]}
    (s : WSeed bk d ρ τ) (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Z : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀))
    (i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀) (hZ : IsUnit Z) (hi : IsDiscMap (l := _) (u := _) (ρ := _) bk.ev i) (hWZ : s.W * Z.map i = Y.map bk.iA)
    (g : ↥(GK K)) (G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀) (hG : IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA (g : GQ l)) G) :
    ∃ e : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀),
      G (bk.iS bk.E) ^ s.N • (s.X.map bk.iS * Z.map i * e) =
        bk.iS bk.E ^ s.N • (s.κ g * (s.X.map bk.iS * Z.map i).map G) ∧
      bk.iA (Per.σA (g : GQ l) τ) ^ s.N • (Y.map bk.iA * e) =
        bk.iA τ ^ s.N • (((ρ g).map (algebraMap ℤ_[l] (Ainf l))).map bk.iA * (Y.map (Per.σA (g : GQ l))).map bk.iA) :=
  GlobalTheory.T.exists_semistable_disc_cocycle l K bk τ hτ d ρ s Y Z i hZ hi hWZ g G hG

theorem frob_eq (bk : BK K) {τ : Ainf l} (hτ : bk.IsPer τ) {d : ℕ} (M N : ℕ) (Y : Matrix (Fin d) (Fin d) (Ainf l))
    (A A' : Matrix (Fin d) (Fin d) bk.S) (hA : A * A' = bk.E ^ (2 * N) • (1 : Matrix (Fin d) (Fin d) bk.S))
    (hφ : bk.ev bk.E ^ N • Y.map WittVector.frobenius = bk.ev bk.E ^ M • (Y * A.map bk.ev))
    (hdet : (Y.map bk.iA).det ≠ 0) (g : GQ l) (G Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀) (hG : IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA g) G)
    (hΦ : IsDiscMap (l := _) (u := _) (ρ := _) WittVector.frobenius Φ) (w : (Ainf l)ˣ) (hw : Per.σA g (bk.ev bk.E) = bk.ev bk.E * w)
    (P : Matrix (Fin d) (Fin d) (Ainf l)) (hP : P.map WittVector.frobenius = P)
    (e : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀))
    (he : bk.iA (Per.σA g τ) ^ M • (Y.map bk.iA * e) = bk.iA τ ^ M • (P.map bk.iA * (Y.map (Per.σA g)).map bk.iA)) :
    bk.iS bk.E ^ (2 * N) • e =
      (((↑w⁻¹ : Ainf l) ^ N) • A.map bk.ev).map bk.iA * e.map Φ * ((A'.map bk.ev).map (Per.σA g)).map bk.iA :=
  GlobalTheory.T.breuilKisin_disc_cocycle_frobenius_equation l K bk τ hτ d M N Y A A' hA hφ hdet g G Φ hG hΦ w hw P hP e he

theorem bounded (bk : BK K) {d : ℕ} (h : ℕ) (C B : Matrix (Fin d) (Fin d) (Ainf l))
    (Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀) (hΦ : IsDiscMap (l := _) (u := _) (ρ := _) WittVector.frobenius Φ) (e : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀))
    (he : bk.iS bk.E ^ h • e = C.map bk.iA * e.map Φ * B.map bk.iA) :
    ∃ (k : ℕ) (v : Matrix (Fin d) (Fin d) (Ainf l)), v.map bk.iA = (l : bk.DA bk.ρ₀) ^ k • e := by
  obtain ⟨ι, ⟨tb⟩⟩ := GlobalTheory.BSP.AinfTopBasis.main l K bk
  have hφX : WittVector.frobenius (bk.ev X) = bk.ev X ^ l := by rw [← bk.ev_frob, frobS_X, map_pow]
  have hj : ∀ j : Fin d × Fin d, HasSum (fun x : Fin d × Fin d => Φ (e x.1 x.2) * bk.iA (C j.1 x.1 * B x.2 j.2))
      (bk.iS bk.E ^ h * e j.1 j.2) := by
    intro j
    convert hasSum_fintype _ using 1
    have := congrFun (congrFun he j.1) j.2
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.map_apply] at this
    rw [this, Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [map_mul]; ring
  obtain ⟨k, v, hv, -⟩ := GlobalTheory.BSP.exists_bounded_of_phi_equation l K bk (Ainf l) bk.ev ι tb WittVector.frobenius hφX
    Φ hΦ (Fin d × Fin d) (fun x j => C j.1 x.1 * B x.2 j.2) (fun _ _ => Set.toFinite _) h
    (fun x => e x.1 x.2) (by rw [Filter.cofinite_eq_bot]; exact Filter.tendsto_bot) hj
  refine ⟨k, Matrix.of fun a b => v (a, b), ?_⟩
  ext a b
  simp only [Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  exact hv (a, b)

theorem descend (bk : BK K) {τ : Ainf l} (hτ : bk.IsPer τ) {d : ℕ} (M k : ℕ) (Y v : Matrix (Fin d) (Fin d) (Ainf l))
    (T : Matrix (Fin d) (Fin d) (WCb l)) (hT : IsUnit T) (hY : Y.map (inclW l) = inclW l τ ^ M • T) (g : GQ l)
    (P : Matrix (Fin d) (Fin d) ℤ_[l])
    (hv : Per.σA g τ ^ M • (Y * v) =
      (l : Ainf l) ^ k • τ ^ M • (P.map (algebraMap ℤ_[l] (Ainf l)) * Y.map (Per.σA g))) :
    ∃ a : Matrix (Fin d) (Fin d) (Ainf l), P.map (algebraMap ℤ_[l] (WCb l)) * T.map (galW l g) = T * a.map (inclW l) ∧
      (l : Ainf l) ^ k • a = v := by
  have hτu := GlobalTheory.BSP.isUnit_inclW_of_isPer l K bk τ hτ
  have hTd : IsUnit T.det := (Matrix.isUnit_iff_isUnit_det T).1 hT
  set P' := P.map (algebraMap ℤ_[l] (WCb l)) with hP'
  have hPA : (P.map (algebraMap ℤ_[l] (Ainf l))).map (inclW l) = P' := by
    exact Matrix.ext fun i j => (inclWA l).commutes (P i j)
  have hgY : (Y.map (Per.σA g)).map (inclW l) = inclW l (Per.σA g τ) ^ M • T.map (galW l g) := by
    have : (Y.map (Per.σA g)).map (inclW l) = (Y.map (inclW l)).map (galW l g) := by
      ext i j; simp only [Matrix.map_apply, galW_inclW]
    rw [this, hY]
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, galW_inclW]
  have hW := congrArg (fun M => M.map (inclW l)) hv
  beta_reduce at hW
  rw [map_smul_hom, map_smul_hom, map_smul_hom, Matrix.map_mul, Matrix.map_mul, hY, hPA, hgY, map_pow, map_pow, map_pow,
    map_natCast] at hW
  have hu : IsUnit (inclW l (Per.σA g τ) ^ M * inclW l τ ^ M) := ((hτu.2.2.2 g).pow M).mul (hτu.1.pow M)
  have hW2 : T * v.map (inclW l) = T * ((l : WCb l) ^ k • (T⁻¹ * (P' * T.map (galW l g)))) := by
    apply smul_cancel_of_isUnit hu
    rw [Matrix.mul_smul, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hTd, Matrix.one_mul]
    refine Matrix.ext fun i j => ?_
    have := congrFun (congrFun hW i) j
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.smul_mul, Matrix.mul_smul] at this ⊢
    linear_combination this
  have hW3 : v.map (inclW l) = (l : WCb l) ^ k • (T⁻¹ * (P' * T.map (galW l g))) := by
    have := congrArg (fun M => T⁻¹ * M) hW2
    beta_reduce at this
    rwa [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hTd, Matrix.one_mul, Matrix.one_mul] at this
  have hx : ∀ i j, ∃ a : Ainf l, (T⁻¹ * (P' * T.map (galW l g))) i j = inclW l (1 * a) ∧ (l : Ainf l) ^ k * a = v i j := by
    intro i j
    have hij : (l : WCb l) ^ k * (T⁻¹ * (P' * T.map (galW l g))) i j = inclW l (v i j) := by
      have := congrFun (congrFun hW3 i) j
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul] at this
      exact this.symm
    obtain ⟨a, ha⟩ := GlobalTheory.T.ainf_principal_ideal_saturated_closed l 1 (by rw [map_one]; exact isUnit_one) k _
      (fun n => ⟨v i j, by rw [hij, one_mul, sub_self]; exact dvd_zero _⟩)
    refine ⟨a, ha, inclW_injective ?_⟩
    rw [map_mul, map_pow, map_natCast, ← hij, ha, one_mul]
  choose a ha1 ha2 using hx
  refine ⟨Matrix.of a, ?_, ?_⟩
  · have : (Matrix.of a).map (inclW l) = T⁻¹ * (P' * T.map (galW l g)) := by
      exact Matrix.ext fun i j => by simp only [Matrix.map_apply, Matrix.of_apply, ha1, one_mul]
    rw [this, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hTd, Matrix.one_mul]
  · exact Matrix.ext fun i j => by simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, ha2]

theorem galois_stable : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])), (∀ g, IsUnit (ρ g)) → ∀ (s : WSeed bk d ρ τ) (N : ℕ) (F : Pre bk N d ρ) (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Z : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)), Y.map (inclW l) = inclW l τ ^ s.N • F.T → IsUnit Z → (∀ i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev i → s.W * Z.map i = Y.map bk.iA) → ∃ F₀ : Frame bk N d ρ, F₀.toPre = F ∧ ∀ (g : ↥(GK K)) (G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀) (i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA (g : GQ l)) G → IsDiscMap (l := _) (u := _) (ρ := _) bk.ev i → G (bk.iS bk.E) ^ s.N • (s.X.map bk.iS * Z.map i * (F₀.ε g).map bk.iA) = bk.iS bk.E ^ s.N • (s.κ g * (s.X.map bk.iS * Z.map i).map G) := by
  intro l _ K bk τ hτ d ρ hρ s N F Y Z hY hZ hWZ
  obtain ⟨ι, ⟨tb⟩⟩ := GlobalTheory.BSP.AinfTopBasis.main l K bk
  obtain ⟨hmaps, hgal, -, hρ0, hρ1, -⟩ := GlobalTheory.BSP.exists_discMaps l K bk
  have hinj : Function.Injective bk.iA :=
    (GlobalTheory.BSP.toDisc_injective_of_topBasis l K bk (Ainf l) bk.ev ι tb bk.ρ₀ hρ0 hρ1).1
  haveI : IsDomain (bk.DA bk.ρ₀) := (GlobalTheory.BSP.discAinf_isDomain l K bk bk.ρ₀ hρ0 hρ1).1
  obtain ⟨i₀, hi₀⟩ := hmaps bk.S (Ainf l) bk.ev X (bk.ev X) bk.ρ₀ bk.ρ₀ 1 hρ0 (by rw [pow_one]) (by rw [pow_one])
  obtain ⟨Φ, hΦ⟩ := hmaps (Ainf l) (Ainf l) WittVector.frobenius (bk.ev X) (bk.ev X) bk.ρ₀ bk.ρ₀ 1 hρ0
    (by rw [pow_one, ← bk.ev_frob, frobS_X, map_pow]; exact dvd_pow_self _ (Fact.out : l.Prime).ne_zero) (by rw [pow_one])
  have hτu := GlobalTheory.BSP.isUnit_inclW_of_isPer l K bk τ hτ
  have hYφ := frob_Y bk hτ F s.N Y hY
  have hdet : (Y.map bk.iA).det ≠ 0 := by
    rw [← hWZ i₀ hi₀, Matrix.det_mul]
    refine mul_ne_zero (det_ne_zero_of_mul_eq_smul (pow_ne_zero _ hτu.2.1) s.W_mul) ?_
    exact ((Matrix.isUnit_iff_isUnit_det _).1 (hZ.map (RingHom.mapMatrix i₀))).ne_zero
  have key : ∀ g : ↥(GK K), ∃ a : Matrix (Fin d) (Fin d) (Ainf l),
      zW (ρ g) * F.T.map (galW l (g : GQ l)) = F.T * a.map (inclW l) ∧
      ∀ (G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀) (i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA (g : GQ l)) G →
        IsDiscMap (l := _) (u := _) (ρ := _) bk.ev i → G (bk.iS bk.E) ^ s.N • (s.X.map bk.iS * Z.map i * a.map bk.iA) =
          bk.iS bk.E ^ s.N • (s.κ g * (s.X.map bk.iS * Z.map i).map G) := by
    intro g
    obtain ⟨G, hG⟩ := hgal bk.ρ₀ hρ0 (g : GQ l)
    obtain ⟨e, heA, heD⟩ := disc_cocycle bk hτ s Y Z i₀ hZ hi₀ (hWZ i₀ hi₀) g G hG
    obtain ⟨w, hw⟩ := gal_E bk (g : GQ l)
    have hP : ((ρ g).map (algebraMap ℤ_[l] (Ainf l))).map WittVector.frobenius =
        (ρ g).map (algebraMap ℤ_[l] (Ainf l)) := by
      ext i j; simp only [Matrix.map_apply, frob_zl]
    have hφe := frob_eq bk hτ s.N N Y F.A F.A' F.A_mul hYφ hdet (g : GQ l) G Φ hG hΦ w hw _ hP e heD
    obtain ⟨k, v, hv⟩ := bounded bk (2 * N) _ _ Φ hΦ e hφe
    have hvA : Per.σA (g : GQ l) τ ^ s.N • (Y * v) = (l : Ainf l) ^ k • τ ^ s.N •
        ((ρ g).map (algebraMap ℤ_[l] (Ainf l)) * Y.map (Per.σA (g : GQ l))) := by
      apply Matrix.map_injective hinj
      beta_reduce
      simp only [map_smul_hom, Matrix.map_mul, hv, map_pow, map_natCast]
      rw [Matrix.mul_smul, smul_smul, mul_comm, ← smul_smul, heD, smul_comm]
    obtain ⟨a, ha1, ha2⟩ := descend bk hτ s.N k Y v F.T F.unit hY (g : GQ l) (ρ g) hvA
    have hae : a.map bk.iA = e := by
      refine smul_cancel_of_isUnit ((isUnit_l_disc l (bk.ev X) bk.ρ₀).pow k) ?_
      rw [← hv, ← ha2, map_smul_hom, map_pow, map_natCast]
    refine ⟨a, ha1, fun G' i hG' hi => ?_⟩
    rw [hG'.unique hG, hi.unique hi₀, hae]
    exact heA
  choose ε hε using key
  exact ⟨{ F with ε := ε, gal := fun g => (hε g).1 }, rfl, fun g G i hG hi => (hε g).2 G i hG hi⟩

end GlobalTheory.BKLim.GalStab
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemistablePeriodsBreuilKisinGaloisStableStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semistablePeriods_breuilKisin_galoisStable : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) (ℤ_[l])), (∀ g, IsUnit (ρ g)) → ∀ (s : WSeed bk d ρ τ) (N : ℕ) (F : Pre bk N d ρ) (Y : Matrix (Fin d) (Fin d) (Ainf l)) (Z : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀)), Y.map (inclW l) = inclW l τ ^ s.N • F.T → IsUnit Z → (∀ i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev i → s.W * Z.map i = Y.map bk.iA) → ∃ F₀ : Frame bk N d ρ, F₀.toPre = F ∧ ∀ (g : ↥(GK K)) (G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀) (i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA (g : GQ l)) G → IsDiscMap (l := _) (u := _) (ρ := _) bk.ev i → G (bk.iS bk.E) ^ s.N • (s.X.map bk.iS * Z.map i * (F₀.ε g).map bk.iA) = bk.iS bk.E ^ s.N • (s.κ g * (s.X.map bk.iS * Z.map i).map G) := by
  first | (exact @GlobalTheory.BKLim.GalStab.galois_stable) | (exact GlobalTheory.BKLim.GalStab.galois_stable) | (intros; apply GlobalTheory.BKLim.GalStab.galois_stable  <;> assumption)
end
