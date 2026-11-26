module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JumpDictCrysAtOfWeights
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsReadsAtOfCover
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachExpansionBasisDivisibility
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachExpansionsSpanFullLattice
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachExpansionLatticeGradedOfLevelLe
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachWeierstrassTestAndDensity

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusMatrixRelationDiscrete
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusMatrixRelationDiscrete
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BKLim

theorem WSeed.crystallineDiscPeriods_frobenius_eq_mul : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ)
    (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : WSeed bk d ρ τ),
    ∀ Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) WittVector.frobenius Φ →
      ((l : bk.DA bk.ρ₀) ^ (s.c₁ + s.c₂) * bk.iS (frobS l bk.a bk.E) ^ s.N) • s.W.map Φ =
        s.W * (s.X' * s.F.map (C : Wq l bk.a →+* bk.S) * s.X.map (frobS l bk.a)).map bk.iS := by
  intro l _ K bk τ hτ d ρ _ s Φ hΦ
  obtain ⟨h0, h1⟩ := bk.ρ₀_pos_lt_one
  haveI : IsDomain (bk.DA bk.ρ₀) := (GlobalTheory.BSP.discAinf_isDomain l K bk bk.ρ₀ h0 h1).1
  obtain ⟨ι, ⟨tb⟩⟩ := GlobalTheory.BSP.AinfTopBasis.main l K bk
  have hinj : Function.Injective bk.iA := (GlobalTheory.BSP.toDisc_injective_of_topBasis l K bk (Ainf l) bk.ev ι tb bk.ρ₀ h0 h1).1
  have hΦS : ∀ x, Φ (bk.iS x) = bk.iS (frobS l bk.a x) := fun x => by
    change Φ (bk.iA (bk.ev x)) = bk.iA (bk.ev (frobS l bk.a x))
    rw [hΦ.ext, bk.ev_frob]
  have he : bk.iS (frobS l bk.a bk.E) ≠ 0 := by
    change bk.iA (bk.ev (frobS l bk.a bk.E)) ≠ 0
    rw [bk.ev_frob, ← map_zero bk.iA]
    exact fun h => bk.frobenius_ev_E_ne_zero hτ (hinj h)
  have hL0 : (l : bk.DA bk.ρ₀) ≠ 0 := fun h =>
    WittVector.p_nonzero l (OCb l) (hinj (by rw [map_natCast, map_zero]; exact h))
  have hQP : s.X.map (bk.iS.comp (frobS l bk.a)) * s.X'.map (bk.iS.comp (frobS l bk.a)) =
      ((l : bk.DA bk.ρ₀) ^ s.c₂ * bk.iS (frobS l bk.a bk.E) ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) := by
    rw [← Matrix.map_mul, s.X_mul, Matrix.map_smul' _ _ _ (map_mul _), Matrix.map_one _ (map_zero _) (map_one _)]
    simp only [RingHom.comp_apply, map_mul, map_pow, map_natCast]
  have hc : (l : bk.DA bk.ρ₀) ^ s.c₂ * bk.iS (frobS l bk.a bk.E) ^ (2 * s.N) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hL0) (pow_ne_zero _ he)
  have hPQ := GlobalTheory.BSP.mul_comm_of_mul_eq_smul_one _ _ _ hc hQP
  have hA : (s.X'.map bk.iS).map Φ = s.X'.map (bk.iS.comp (frobS l bk.a)) := by
    rw [Matrix.map_map]; congr 1; funext x; exact hΦS x
  have hF : (s.F.map (C : Wq l bk.a →+* bk.S)).map bk.iS = s.F.map (bk.iS.comp C) := by
    rw [Matrix.map_map]; rfl
  have hX : (s.X.map (frobS l bk.a)).map bk.iS = s.X.map (bk.iS.comp (frobS l bk.a)) := by
    rw [Matrix.map_map]; rfl
  have h2 := congrArg (· * s.X.map (bk.iS.comp (frobS l bk.a))) (s.φ Φ hΦ)
  simp only [Matrix.map_mul, hA] at h2
  rw [Matrix.smul_mul, Matrix.mul_assoc (s.W.map Φ), hPQ, Matrix.mul_smul, Matrix.mul_one, smul_smul] at h2
  rw [Matrix.map_mul, Matrix.map_mul, hF, hX]
  refine smul_right_injective (Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) (pow_ne_zero s.N he) ?_
  dsimp only
  calc bk.iS (frobS l bk.a bk.E) ^ s.N • (((l : bk.DA bk.ρ₀) ^ (s.c₁ + s.c₂) * bk.iS (frobS l bk.a bk.E) ^ s.N) •
        s.W.map Φ)
      = ((l : bk.DA bk.ρ₀) ^ s.c₁ * ((l : bk.DA bk.ρ₀) ^ s.c₂ * bk.iS (frobS l bk.a bk.E) ^ (2 * s.N))) •
        s.W.map Φ := by rw [smul_smul]; congr 1; ring
    _ = _ := h2
    _ = _ := by rw [Matrix.smul_mul]; simp only [Matrix.mul_assoc]

end GlobalTheory.BKLim
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusMatrixRelationDiscreteStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_matrix_relation_discrete : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : WSeed bk d ρ τ), ∀ Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) WittVector.frobenius Φ → ((l : bk.DA bk.ρ₀) ^ (s.c₁ + s.c₂) * bk.iS (frobS l bk.a bk.E) ^ s.N) • s.W.map Φ = s.W * (s.X' * s.F.map (C : Wq l bk.a →+* bk.S) * s.X.map (frobS l bk.a)).map bk.iS := by
  first | exact @GlobalTheory.BKLim.WSeed.crystallineDiscPeriods_frobenius_eq_mul | exact GlobalTheory.BKLim.WSeed.crystallineDiscPeriods_frobenius_eq_mul | (intros; apply GlobalTheory.BKLim.WSeed.crystallineDiscPeriods_frobenius_eq_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeFrobeniusInverseMatrix
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeFrobeniusInverseMatrix
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.BSP.crystallineLattice_frobenius_inverse_matrix

theorem frob_inverse {R : Type} [CommRing R] [IsDomain R] {d : ℕ} (Φ : R →+* R)
    (W W' B : Matrix (Fin d) (Fin d) R) (t e lam : R) (ht : t ≠ 0)
    (hW : W * W' = t • (1 : Matrix (Fin d) (Fin d) R)) (hB : lam • W.map Φ = W * B) (hΦ : Φ t = e * t) :
    B * W'.map Φ = (lam * e) • W' := by
  have hdet : W.det ≠ 0 := by
    intro h
    have h1 := congrArg Matrix.det hW
    rw [Matrix.det_mul, h, zero_mul, Matrix.det_smul, Matrix.det_one, mul_one] at h1
    exact pow_ne_zero _ ht h1.symm
  have h2 : W.map Φ * W'.map Φ = (e * t) • (1 : Matrix (Fin d) (Fin d) R) := by
    rw [← Matrix.map_mul, hW, ← hΦ]
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.one_apply_ne hij]
  have h3 : W * (B * W'.map Φ - (lam * e) • W') = 0 := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc, ← hB, Matrix.smul_mul, h2, Matrix.mul_smul, hW, smul_smul, smul_smul,
      mul_assoc, sub_self]
  have h4 : W.det • (B * W'.map Φ - (lam * e) • W') = 0 := by
    rw [← Matrix.one_mul (B * W'.map Φ - (lam * e) • W'), ← Matrix.smul_mul, ← Matrix.adjugate_mul,
      Matrix.mul_assoc, h3, Matrix.mul_zero]
  rw [← sub_eq_zero]
  ext i j
  have h5 := congrFun (congrFun h4 i) j
  rw [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at h5
  exact (mul_eq_zero.1 h5).resolve_left hdet

theorem radius_mem (l : ℕ) [hl : Fact l.Prime] (K : FinExt l) (bk : BK K) : 0 < bk.ρ₀ ∧ bk.ρ₀ < 1 := by
  have h1 : (1 : ℝ≥0) < (l : ℝ≥0) := by exact_mod_cast hl.out.one_lt
  have h2 : (0 : ℝ) < (bk.Ep.natDegree : ℝ) := by exact_mod_cast bk.deg_pos
  refine ⟨NNReal.rpow_pos (lt_trans zero_lt_one h1), ?_⟩
  exact NNReal.rpow_lt_one_of_one_lt_of_neg h1 (neg_lt_zero.2 (one_div_pos.2 h2))

end GlobalTheory.BSP.crystallineLattice_frobenius_inverse_matrix

theorem GlobalTheory.BSP.seed_frob_inverse : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ), ∀ Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) WittVector.frobenius Φ → (s.X' * s.F.map (C : Wq l bk.a →+* bk.S) * s.X.map (frobS l bk.a)).map bk.iS * s.W'.map Φ = (((l : bk.DA bk.ρ₀) ^ (s.c₁ + s.c₂) * bk.iS (frobS l bk.a bk.E) ^ s.N) * bk.iS bk.E ^ (2 * s.N)) • s.W' := by
  intro l _ K bk τ hτ d ρ hρ s Φ hΦ
  obtain ⟨h0, h1⟩ := GlobalTheory.BSP.crystallineLattice_frobenius_inverse_matrix.radius_mem l K bk
  haveI := (GlobalTheory.T.breuilKisin_ainfDisc_isDomain_norm_bounds l K bk bk.ρ₀ h0 h1).1
  have hτ0 := (GlobalTheory.T.breuilKisin_period_isUnit_wittTilt_and_ne_zero l K bk τ hτ).2.1
  refine GlobalTheory.BSP.crystallineLattice_frobenius_inverse_matrix.frob_inverse Φ s.W s.W' _ (bk.iA τ ^ (2 * s.N)) _ _ (pow_ne_zero _ hτ0) s.W_mul
    (GlobalTheory.T.discPeriods_map_frobenius_eq_mul l K bk τ hτ d ρ hρ s Φ hΦ) ?_
  have h2 : Φ (bk.iA τ) = bk.iS bk.E * bk.iA τ := by
    have h3 := hΦ.ext τ
    rw [hτ.1, map_mul] at h3
    exact h3
  rw [map_pow, h2, mul_pow]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeFrobeniusInverseMatrixStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystallineLattice_frobenius_inverse_matrix : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ), ∀ Φ : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) WittVector.frobenius Φ → (s.X' * s.F.map (C : Wq l bk.a →+* bk.S) * s.X.map (frobS l bk.a)).map bk.iS * s.W'.map Φ = (((l : bk.DA bk.ρ₀) ^ (s.c₁ + s.c₂) * bk.iS (frobS l bk.a bk.E) ^ s.N) * bk.iS bk.E ^ (2 * s.N)) • s.W' := by
  first | exact @GlobalTheory.BSP.seed_frob_inverse | exact GlobalTheory.BSP.seed_frob_inverse | (intros; apply GlobalTheory.BSP.seed_frob_inverse <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraicCharacterOfAdm
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GaloisAdmissibleIffRepPureAvatar
noncomputable section

namespace GlobalTheory.GaloisInputCompare

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Formalism.MainNotions.SumRepresentations.At

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem norm_le_one_of_isIntegral {K : Type} [NormedField K] [IsUltrametricDist K] {x : K} (hx : IsIntegral ℤ x) :
    ‖x‖ ≤ 1 := by
  have h : x ∈ (NormedField.valuation (K := K)).integer :=
    (Valuation.integer.integers (NormedField.valuation (K := K))).mem_of_integral hx.tower_top
  rw [Valuation.mem_integer_iff] at h
  exact_mod_cast h

theorem exists_inducesW (i : N.Loc) (τ : H.E →+* Qbar (N.l i)) :
    ∃ w ∈ placesOver H.E (N.l i), InducesW N i τ w := by
  have hle : ∀ x : 𝓞 H.E, ‖τ (x : H.E)‖ ≤ 1 := fun x =>
    norm_le_one_of_isIntegral (map_isIntegral_int τ (RingOfIntegers.isIntegral_coe x))
  let I : Ideal (𝓞 H.E) :=
    { carrier := {x | ‖τ (x : H.E)‖ < 1}
      zero_mem' := by simp
      add_mem' := fun {x y} hx hy => by
        change ‖τ ((x + y : 𝓞 H.E) : H.E)‖ < 1
        rw [show ((x + y : 𝓞 H.E) : H.E) = x + y from rfl, map_add (f := _)]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hx hy)
      smul_mem' := fun c x hx => by
        change ‖τ ((c * x : 𝓞 H.E) : H.E)‖ < 1
        rw [show ((c * x : 𝓞 H.E) : H.E) = c * x from rfl, map_mul, norm_mul]
        exact (mul_le_of_le_one_left (norm_nonneg _) (hle c)).trans_lt hx }
  have hI : ∀ x : 𝓞 H.E, x ∈ I ↔ ‖τ (x : H.E)‖ < 1 := fun x => Iff.rfl
  have hl : ((N.l i : ℕ) : 𝓞 H.E) ∈ I := by
    rw [hI, show (((N.l i : ℕ) : 𝓞 H.E) : H.E) = (N.l i : ℕ) by simp, map_natCast,
      ← map_natCast (algebraMap ℚ_[N.l i] (PadicAlgCl (N.l i))), PadicAlgCl.norm_extends]
    exact Padic.norm_p_lt_one
  have hP : I.IsPrime := by
    refine ⟨fun h => ?_, fun {x y} h => ?_⟩
    · have := (hI 1).1 (h ▸ Submodule.mem_top)
      simp at this
    · rw [hI, show ((x * y : 𝓞 H.E) : H.E) = x * y from rfl, map_mul, norm_mul] at h
      by_contra hn
      rw [not_or, hI, hI, not_lt, not_lt] at hn
      exact absurd h (not_lt.2 (one_le_mul_of_one_le_of_one_le hn.1 hn.2))
  refine ⟨⟨I, hP, fun h => ?_⟩, hl, fun x => (hI x).symm⟩
  rw [h, Ideal.mem_bot] at hl
  exact (N.lPrime i).out.ne_zero (by exact_mod_cast hl)


end GlobalTheory.GaloisInputCompare
end
end

noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

namespace GlobalTheory.AlgCharFromGal

theorem charpoly_fin_one {K : Type*} [CommRing K] (M : Matrix (Fin 1) (Fin 1) K) :
    M.charpoly = X - C (M 0 0) := by
  simp [Matrix.charpoly, Matrix.det_fin_one, Matrix.charmatrix_apply]

end GlobalTheory.AlgCharFromGal

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeDiscSpanFrobeniusStable
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeDiscSpanFrobeniusStable
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.BSP

theorem mulVec_frob_of_unit {R D : Type} [CommRing R] [CommRing D] {d : ℕ} (j : R →+* D) (Φ : D →+* D)
    (Ψ : R →+* R) (h : ∀ r, j (Ψ r) = Φ (j r)) (c : Rˣ) (W : Matrix (Fin d) (Fin d) D)
    (B : Matrix (Fin d) (Fin d) R) (hW : j c • W.map Φ = W * B.map j) (x : Fin d → R) :
    W *ᵥ (fun a => j (((c⁻¹ : Rˣ) : R) * (B *ᵥ fun b => Ψ (x b)) a)) =
      fun a => Φ ((W *ᵥ fun b => j (x b)) a) := by
  have e1 : (fun a => j (((c⁻¹ : Rˣ) : R) * (B *ᵥ fun b => Ψ (x b)) a)) =
      j ((c⁻¹ : Rˣ) : R) • (B.map j *ᵥ fun b => Φ (j (x b))) := by
    funext a
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.mulVec, dotProduct, map_sum, h]
  have e2 : (fun a => Φ ((W *ᵥ fun b => j (x b)) a)) = W.map Φ *ᵥ fun b => Φ (j (x b)) := by
    funext a
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Matrix.mulVec, dotProduct, map_sum]
  rw [e1, e2, Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← hW, Matrix.smul_mulVec, smul_smul, ← map_mul,
    Units.inv_mul, map_one, one_smul]

theorem seed_span_frobenius_stable : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ), ∀ y, (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a)) y → (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a)) (fun a => WittVector.frobenius (y a)) := by
  intro l hl K bk τ hτ d ρ hρ s y ⟨x, hx⟩
  obtain ⟨-, -, ⟨h0, h1, -⟩, -⟩ := GlobalTheory.T.breuilKisin_flat_radius_ideal_facts l K bk
  have hpow : bk.ρ₀ ^ l ≤ bk.ρ₀ := pow_le_of_le_one h0.le h1.le hl.out.ne_zero
  obtain ⟨Ψ, hΨ⟩ := exists_discMap_of_pow_dvd l bk.S bk.S (frobS l bk.a) X X bk.ρ₀ bk.ρ₀ l h0
    (by rw [frobS_X]) hpow
  obtain ⟨Φ, hΦ⟩ := exists_discMap_of_pow_dvd l (Ainf l) (Ainf l) WittVector.frobenius (bk.ev X) (bk.ev X)
    bk.ρ₀ bk.ρ₀ l h0 (by rw [← bk.ev_frob, frobS_X, map_pow]) hpow
  have hu : IsUnit (((l : ℕ) : bk.DS bk.ρ₀) ^ (s.c₁ + s.c₂) *
      toDisc l (X : bk.S) bk.ρ₀ (frobS l bk.a bk.E) ^ s.N) :=
    ((isUnit_l_disc l (X : bk.S) bk.ρ₀).pow _).mul ((isUnit_toDisc_frobS_E l K bk).pow _)
  obtain ⟨c, hc⟩ := hu
  refine ⟨fun a => ((c⁻¹ : (bk.DS bk.ρ₀)ˣ) : bk.DS bk.ρ₀) *
    ((s.X' * s.F.map (C : Wq l bk.a →+* bk.S) * s.X.map (frobS l bk.a)).map (toDisc l (X : bk.S) bk.ρ₀) *ᵥ
      fun b => Ψ (x b)) a, fun j hj => ?_⟩
  have hcomm : j.comp Ψ = Φ.comp j := by
    refine IsDiscMap.unique (DiscBasic.isDiscMap_comp l _ _ hΨ hj) ?_
    have e : bk.ev.comp (frobS l bk.a) = (WittVector.frobenius : Ainf l →+* Ainf l).comp bk.ev :=
      RingHom.ext bk.ev_frob
    rw [e]
    exact DiscBasic.isDiscMap_comp l _ _ hj hΦ
  have hW := GlobalTheory.T.discPeriods_map_frobenius_eq_mul l K bk τ hτ d ρ hρ s Φ hΦ
  rw [mulVec_frob_of_unit j Φ Ψ (RingHom.congr_fun hcomm) c s.W _ ?_ x, hx j hj]
  · funext a
    exact hΦ.ext _
  · rw [hc, map_mul, map_pow, map_pow, map_natCast, hj.ext, Matrix.map_map]
    refine hW.trans ?_
    congr 2
    funext a
    exact (hj.ext a).symm

end GlobalTheory.BSP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeDiscSpanFrobeniusStableStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystallineLattice_discSpan_frobenius_stable : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ), ∀ y, (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a)) y → (fun y : Fin d → Ainf l => ∃ x : Fin d → bk.DS bk.ρ₀, ∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → s.W *ᵥ (fun a => j (x a)) = fun a => bk.iA (y a)) (fun a => WittVector.frobenius (y a)) := by
  first | exact @GlobalTheory.BSP.seed_span_frobenius_stable | exact GlobalTheory.BSP.seed_span_frobenius_stable | (intros; apply GlobalTheory.BSP.seed_span_frobenius_stable <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SmulMemFilTOfZero
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.BKReal GlobalTheory.BKGal
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.XiFil

variable {l : ℕ} [Fact l.Prime]

theorem mem_FilD_zero_iff (x : Per.BdR l) :
    x ∈ Per.FilD l 0 ↔ ∃ z : Per.BdRp l, x = algebraMap (Per.BdRp l) (Per.BdR l) z := by
  have h := GlobalTheory.BdRQuot.mem_FilD_nat (l := l) 0 x
  rw [Nat.cast_zero] at h
  rw [h]
  constructor
  · rintro ⟨z, -, rfl⟩
    exact ⟨z, rfl⟩
  · rintro ⟨z, rfl⟩
    exact ⟨z, GlobalTheory.BdRQuot.mem_filtration_zero z, rfl⟩

theorem mul_mem_FilD_of_zero {x y : Per.BdR l} {n : ℤ} (hx : x ∈ Per.FilD l 0) (hy : y ∈ Per.FilD l n) :
    x * y ∈ Per.FilD l n := by
  obtain ⟨z, rfl⟩ := (mem_FilD_zero_iff x).1 hx
  rw [← Algebra.smul_def]
  exact Submodule.smul_mem _ z hy

theorem mul_mem_FilD_neg {x y : Per.BdR l} {m : ℕ} (hx : x ∈ Per.FilD l m) (hy : y ∈ Per.FilD l (-(m : ℤ))) :
    x * y ∈ Per.FilD l 0 := by
  obtain ⟨e, he⟩ := GlobalTheory.MemLoc.BdRField.exists_isEps l
  obtain ⟨w, rfl⟩ := (GlobalTheory.MemLoc.TiedUnif.mem_FilD_iff he _ x).1 hx
  obtain ⟨w', rfl⟩ := (GlobalTheory.MemLoc.TiedUnif.mem_FilD_iff he _ y).1 hy
  rw [mul_mul_mul_comm, ← Units.val_mul, ← zpow_add, add_neg_cancel, zpow_zero, Units.val_one, one_mul,
    ← map_mul]
  exact GlobalTheory.MemLoc.TiedUnif.alg_mem_FilD_zero _

variable (O : Type) [CommRing O] [Algebra ℤ_[l] O]

def filO (C : GlobalTheory.MemLoc.Core l) (n : ℤ) : Submodule O (OB l O) :=
  Submodule.span O {x | ∃ β : Per.Bcris l, C.ι β ∈ Per.FilD l n ∧ x = (1 : O) ⊗ₜ[ℤ_[l]] β}

variable {O} {K : Type} [NormedField K] [NormedAlgebra ℚ_[l] K] [Algebra O K]
  {G : Type} [Group G] [TopologicalSpace G]

def filT (C : GlobalTheory.MemLoc.Core l) (T : LocLat G ℚ_[l] K O) (n : ℤ) : Submodule O (TW (OB l O) T) :=
  Submodule.span O {w | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l n ∧
    w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x}

theorem smul_mem_filT {C : GlobalTheory.MemLoc.Core l} {T : LocLat G ℚ_[l] K O} {a b c : ℤ}
    (hmul : ∀ β β' : Per.Bcris l, C.ι β ∈ Per.FilD l a → C.ι β' ∈ Per.FilD l b → C.ι (β * β') ∈ Per.FilD l c)
    {r : OB l O} (hr : r ∈ filO O C a) {v : TW (OB l O) T} (hv : v ∈ filT C T b) : r • v ∈ filT C T c := by
  induction hr using Submodule.span_induction with
  | mem r hr =>
    obtain ⟨β, hβ, rfl⟩ := hr
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨β', x, hβ', rfl⟩ := hv
      rw [smul_tmul', smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      exact Submodule.subset_span ⟨β * β', x, hmul β β' hβ hβ', rfl⟩
    | zero => rw [smul_zero]; exact zero_mem _
    | add v v' _ _ h h' => rw [smul_add]; exact add_mem h h'
    | smul o v _ h => rw [smul_comm]; exact Submodule.smul_mem _ o h
  | zero => rw [zero_smul]; exact zero_mem _
  | add r r' _ _ h h' => rw [add_smul]; exact add_mem h h'
  | smul o r _ h => rw [smul_assoc]; exact Submodule.smul_mem _ o h

theorem smul_mem_filT_of_zero {C : GlobalTheory.MemLoc.Core l} {T : LocLat G ℚ_[l] K O} {n : ℤ} {r : OB l O}
    (hr : r ∈ filO O C 0) {v : TW (OB l O) T} (hv : v ∈ filT C T n) : r • v ∈ filT C T n :=
  smul_mem_filT (fun β β' h h' => by rw [map_mul]; exact mul_mem_FilD_of_zero h h') hr hv

theorem smul_mem_filT_neg {C : GlobalTheory.MemLoc.Core l} {T : LocLat G ℚ_[l] K O} {m : ℕ} {r : OB l O}
    (hr : r ∈ filO O C m) {v : TW (OB l O) T} (hv : v ∈ filT C T (-(m : ℤ))) : r • v ∈ filT C T 0 :=
  smul_mem_filT (fun β β' h h' => by rw [map_mul]; exact mul_mem_FilD_neg h h') hr hv

end GlobalTheory.BKGal.XiFil
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableAndCoverPrismHomOfPushout
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableAndCoverPrismHomOfPushout
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

open CategoryTheory

namespace GlobalTheory.BSP.CoverBC

variable {l : ℕ} {R : Type} [CommRing R]

theorem hom_ext {P P' : Obj l R} {a b : Hom P P'} (h : a.f = b.f) : a = b := by
  cases a; cases b; cases h; rfl

theorem comp_assoc {P₁ P₂ P₃ P₄ : Obj l R} (c : Hom P₃ P₄) (b : Hom P₂ P₃) (a : Hom P₁ P₂) :
    (c.comp b).comp a = c.comp (b.comp a) := hom_ext rfl

theorem qmap_comp {P₁ P₂ P₃ : Obj l R} (g : Hom P₂ P₃) (f : Hom P₁ P₂) (m : ℕ) :
    qmap (g.comp f) m = (qmap g m).comp (qmap f m) :=
  Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)

theorem of_isPushout {P : ∀ {A B : Type} [CommRing A] [CommRing B], (A →+* B) → Prop}
    (hP : RingHom.IsStableUnderBaseChange @P)
    {A B A' B' : Type} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    {φ : A →+* B} {α : A →+* A'} {β : B →+* B'} {φ' : A' →+* B'}
    (H : IsPushout (CommRingCat.ofHom φ) (CommRingCat.ofHom α) (CommRingCat.ofHom β) (CommRingCat.ofHom φ'))
    (h : P φ) : P φ' := by
  algebraize [φ, α, β, φ', φ'.comp α]
  have : IsScalarTower A B B' := IsScalarTower.of_algebraMap_eq' (congrArg CommRingCat.Hom.hom H.w).symm
  have : Algebra.IsPushout A B A' B' := CommRingCat.isPushout_iff_isPushout.1 H
  exact hP A B A' B' h

end GlobalTheory.BSP.CoverBC

namespace GlobalTheory.BSP.CoverBC

variable {l : ℕ} {R : Type} [CommRing R]

theorem flat_of_isPO {B C B' C' : Obj l R} {h : Hom B C} {k : Hom B B'} {k' : Hom C C'} {h' : Hom B' C'}
    (H : IsPO h k k' h') (hf : ∀ m : ℕ, (qmap h m).Flat) (m : ℕ) : (qmap h' m).Flat :=
  of_isPushout RingHom.Flat.isStableUnderBaseChange (H.po m) (hf m)

theorem faithfullyFlat_of_isPO {B C B' C' : Obj l R} {h : Hom B C} {k : Hom B B'} {k' : Hom C C'}
    {h' : Hom B' C'} (H : IsPO h k k' h') (hf : ∀ m : ℕ, (qmap h m).FaithfullyFlat) (m : ℕ) :
    (qmap h' m).FaithfullyFlat :=
  of_isPushout RingHom.FaithfullyFlat.isStableUnderBaseChange (H.po m) (hf m)

end GlobalTheory.BSP.CoverBC


open GlobalTheory.BSP.CoverBC in
theorem GlobalTheory.BSP.stable_cover_of_isPO : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B C B' C' : Obj l R)
    (h : Hom B C) (k : Hom B B') (k' : Hom C C') (h' : Hom B' C'),
    IsPO h k k' h' → (Stable h → Stable h') ∧ (Cover h → Cover h') := by
  intro l _ R _ B C B' C' h k k' h' H
  have st : Stable h → Stable h' := by
    intro hs
    refine ⟨flat_of_isPO H hs.flat, fun B'' k₂ => ?_⟩
    obtain ⟨C'', k₀, h'', H₂⟩ := hs.po B'' (k₂.comp k)
    have e : k₀.comp h = (h''.comp k₂).comp k := by rw [H₂.comm, comp_assoc]
    obtain ⟨c, ⟨hc₁, hc₂⟩, -⟩ := GlobalTheory.T.prismPushoutModAdicPow_universal l R B C B' C' h k k' h' H C'' k₀ (h''.comp k₂) e
    refine ⟨C'', c, h'', ⟨hc₂, fun m => ?_⟩⟩
    have s := H₂.po m
    rw [← hc₁, qmap_comp, qmap_comp, CommRingCat.ofHom_comp, CommRingCat.ofHom_comp] at s
    refine IsPushout.of_top s ?_ (H.po m)
    rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, ← qmap_comp, ← qmap_comp, hc₂]
  exact ⟨st, fun hc => ⟨st hc.stable, faithfullyFlat_of_isPO H hc.ff⟩⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableAndCoverPrismHomOfPushoutStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stable_and_cover_prismHom_of_pushout : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B C B' C' : Obj l R) (h : Hom B C) (k : Hom B B') (k' : Hom C C') (h' : Hom B' C'), IsPO h k k' h' → (Stable h → Stable h') ∧ (Cover h → Cover h') := by
  first | exact @GlobalTheory.BSP.stable_cover_of_isPO | exact GlobalTheory.BSP.stable_cover_of_isPO | (intros; apply GlobalTheory.BSP.stable_cover_of_isPO <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankIdempotentBlockCharPolyOfProjection
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankIdempotentBlockCharPolyOfProjection
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory.CharBlock

open Polynomial Matrix

theorem rank_blockPol_of_factor {K : Type} [Field K] {n t : ℕ} (a : Matrix (Fin n) (Fin t) K)
    (b : Matrix (Fin t) (Fin n) K) (d : Fin t → K) (hba : b * a = 1) :
    (a * b).rank = t ∧
      blockPol (a * b) (a * Matrix.diagonal d * b) = ∏ c, (Polynomial.X - Polynomial.C (d c)) := by
  constructor
  · apply le_antisymm
    · exact (Matrix.rank_mul_le_left a b).trans (by simpa using Matrix.rank_le_width a)
    · have h1 : b * (a * b) * a = 1 := by
        rw [← Matrix.mul_assoc b a b, hba, Matrix.one_mul, hba]
      have h2 : (b * (a * b) * a).rank ≤ (a * b).rank :=
        (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
      rw [h1, Matrix.rank_one] at h2
      simpa using h2
  · unfold blockPol
    have hba' : b.map (C (R := K)) * a.map (C (R := K)) = 1 := by
      rw [← Matrix.map_mul, hba]
      simp
    set D : Matrix (Fin t) (Fin t) K[X] := Matrix.diagonal (fun c => (X : K[X]) - C (d c)) with hD
    have hD' : D = (X : K[X]) • (1 : Matrix (Fin t) (Fin t) K[X]) - (Matrix.diagonal d).map (C (R := K)) := by
      ext1 i j
      by_cases h : i = j
      · subst h; simp [hD]
      · simp [hD, h, Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
    have key : (X : K[X]) • (a * b).map (C (R := K)) - (a * Matrix.diagonal d * b).map (C (R := K)) + 1
        - (a * b).map (C (R := K)) = 1 + a.map (C (R := K)) * ((D - 1) * b.map (C (R := K))) := by
      rw [hD', Matrix.map_mul, Matrix.map_mul, Matrix.map_mul]
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
        Matrix.mul_assoc]
      abel
    rw [key, Matrix.det_one_add_mul_comm, Matrix.mul_assoc, hba', Matrix.mul_one, add_sub_cancel, hD,
      Matrix.det_diagonal]

theorem rank_blockPol_proj : ∀ {K : Type} [Field K] {n r t : ℕ} (e : (Fin n → K) ≃ₗ[K] ((Fin r → K) × (Fin t → K))) (E M : Matrix (Fin n) (Fin n) K) (d : Fin t → K), (∀ u, e (E.mulVec u) = (0, (e u).2)) → (∀ u, e (M.mulVec u) = (0, fun c => d c * (e u).2 c)) → E.rank = t ∧ blockPol E M = ∏ c, (Polynomial.X - Polynomial.C (d c)) := by
  intro K _ n r t e E M d hE hM
  let a : Matrix (Fin n) (Fin t) K :=
    LinearMap.toMatrix' (e.symm.toLinearMap ∘ₗ LinearMap.inr K (Fin r → K) (Fin t → K))
  let b : Matrix (Fin t) (Fin n) K :=
    LinearMap.toMatrix' (LinearMap.snd K (Fin r → K) (Fin t → K) ∘ₗ e.toLinearMap)
  have ha : ∀ w, a.mulVec w = e.symm (0, w) := by
    intro w
    simp [a, LinearMap.toMatrix'_mulVec]
  have hb : ∀ u, b.mulVec u = (e u).2 := by
    intro u
    simp [b, LinearMap.toMatrix'_mulVec]
  have hba : b * a = 1 := by
    apply Matrix.toLin'.injective
    ext1 w
    ext1
    simp only [LinearMap.comp_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ha, hb,
      LinearEquiv.apply_symm_apply, Matrix.one_mulVec]
  have hE' : E = a * b := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun u => ?_
    simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ha, hb]
    rw [← hE, LinearEquiv.symm_apply_apply]
  have hM' : M = a * Matrix.diagonal d * b := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun u => ?_
    simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ha, hb]
    apply e.injective
    rw [hM, LinearEquiv.apply_symm_apply]
    congr 1
    funext c
    rw [Matrix.mulVec_diagonal]
  rw [hE', hM']
  exact rank_blockPol_of_factor a b d hba

end GlobalTheory.CharBlock
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankIdempotentBlockCharPolyOfProjectionStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_idempotentBlockCharPoly_of_projection : ∀ {K : Type} [Field K] {n r t : ℕ} (e : (Fin n → K) ≃ₗ[K] ((Fin r → K) × (Fin t → K))) (E M : Matrix (Fin n) (Fin n) K) (d : Fin t → K), (∀ u, e (E.mulVec u) = (0, (e u).2)) → (∀ u, e (M.mulVec u) = (0, fun c => d c * (e u).2 c)) → E.rank = t ∧ blockPol E M = ∏ c, (Polynomial.X - Polynomial.C (d c)) := by
  first | exact @GlobalTheory.CharBlock.rank_blockPol_proj | exact GlobalTheory.CharBlock.rank_blockPol_proj | (intros; apply GlobalTheory.CharBlock.rank_blockPol_proj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachNInvQPowGammaStable
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachNInvQPowGammaStable
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.GamQ

theorem isUnit_one_add {O : Type} [CommRing O] (f : PowerSeries O)
    (hf : PowerSeries.constantCoeff f = 0) : IsUnit (1 + f) := by
  rw [PowerSeries.isUnit_iff_constantCoeff]; simp [hf]


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in
theorem gam_Q_pow : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let C := Cm l; let u : ↥LL.1 := algebraMap ↥(OL LL) ↥LL.1 (W.χΓ W.gam : ↥(OL LL)); ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ k : ℕ, (∀ x : W.DD T, W.Q ^ k • x ∈ W.N T → W.Q ^ k • W.γ T x ∈ W.N T) ∧ ∀ (i : Let K) (ζ : ↥LL.1), IsPrimitiveRoot ζ (l ^ s) → ∃ w : PowerSeries ↥LL.1, PowerSeries.constantCoeff w = u ^ (-(k : ℤ)) ∧ ∀ (x : W.DD T) (hx : W.Q ^ k • x ∈ W.N T) (hγ : W.Q ^ k • W.γ T x ∈ W.N T) (j : ℤ), ex C h T i ζ ⟨W.Q ^ k • W.γ T x, hγ⟩ j = conv w (fun m => u ^ m • ex C h T i ζ ⟨W.Q ^ k • x, hx⟩ m) j := by
  intro D HW F Cm l _ K s LL h W C u T hT k
  obtain ⟨χ, -, -, hγ₀, -, hQ, -, -⟩ := GlobalTheory.NL.CycRing.rings_cyclotomic D HW l K s LL h
  obtain ⟨b, hb⟩ := ((GlobalTheory.Cyc.XX_QQ_properties l ↥(OL LL) s h.1).2.2.2.2.2.1 (χ W.gam)).2
  let U : AA K LL := fun _ => 1 + GlobalTheory.Cyc.XX l ↥(OL LL) s * b
  have hγQ : W.γA W.gam W.Q = W.Q * U := by
    funext i
    show W.γ₀ W.gam (W.Q i) = W.Q i * U i
    rw [hγ₀, hQ]
    exact hb
  have hUu : IsUnit U := Pi.isUnit_iff.2 fun _ => isUnit_one_add _ (by simp [GlobalTheory.Cyc.XX])
  have hγs : ∀ (a : AA K LL) (y : W.DD T), W.γ T (a • y) = W.γA W.gam a • W.γ T y := by
    intro a y
    have := W.γD_smul T W.gam (algebraMap (AA K LL) W.EE a) y
    rw [algebraMap_smul, W.γE_ext, algebraMap_smul] at this
    exact this
  let v : AA K LL := ((hUu.unit ^ k)⁻¹ : (AA K LL)ˣ)
  have hvU : v * U ^ k = 1 := by
    show (((hUu.unit ^ k)⁻¹ : (AA K LL)ˣ) : AA K LL) * U ^ k = 1
    have e : U ^ k = ((hUu.unit ^ k : (AA K LL)ˣ) : AA K LL) := by
      rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec]
    rw [e, Units.inv_mul]
  have key : ∀ y : W.DD T, W.Q ^ k • W.γ T y = v • W.γ T (W.Q ^ k • y) := by
    intro y
    rw [hγs, map_pow, hγQ, mul_pow, smul_smul, mul_left_comm, hvU, mul_one]
  refine ⟨fun x hx => ?_, fun i ζ hζ => ?_⟩
  · rw [key]
    exact (W.N T).smul_mem v (W.N_Γ T W.gam _ hx)
  have hfull := GlobalTheory.NL.FullLevel.full_lat D HW F Cm l K s LL h T hT i ζ hζ
  have hlev := (GlobalTheory.NL.LevInj.expansion_basis D HW F Cm l K s LL h T hT i ζ ⟨s, hζ⟩ hfull).1
  refine ⟨W.lev i ζ v, ?_, fun x hx hγ j => ?_⟩
  · have hg := W.gam_gen
    rw [(HW l).W_s] at hg
    have hΓ := ((Cm l).C K s LL h).tie.lev_Γ W.gam i ζ ζ s 1
      (by rw [(D.loc l).PD_p]; exact hζ) (by rw [Nat.cast_one]; exact hg.ge) (pow_one ζ).symm W.Q
    have hΓ' : W.lev i ζ W.Q * W.lev i ζ U = PowerSeries.rescale u (W.lev i ζ W.Q) := by
      rw [← map_mul, ← hγQ]; exact hΓ
    obtain ⟨w0, hw0, hQw⟩ := ((GlobalTheory.NL.lev_at_root_of_unity D HW l K s LL h i ζ ⟨s, hζ⟩).2.2.2.1 hζ).1
    rw [hQw, map_mul, PowerSeries.rescale_X] at hΓ'
    have h1 : w0 * W.lev i ζ U = PowerSeries.C u * PowerSeries.rescale u w0 := by
      apply mul_left_cancel₀ (PowerSeries.X_ne_zero (R := ↥LL.1))
      linear_combination hΓ'
    have h2 := congrArg (PowerSeries.coeff 0) h1
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale, pow_zero, one_mul,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_zero_eq_constantCoeff_apply,
      map_mul] at h2
    have hw0c : PowerSeries.constantCoeff w0 ≠ 0 := (hw0.map PowerSeries.constantCoeff).ne_zero
    have hUc : PowerSeries.constantCoeff (W.lev i ζ U) = u := by
      apply mul_left_cancel₀ hw0c
      rw [h2, mul_comm]
    have h3 := congrArg PowerSeries.constantCoeff (congrArg (W.lev i ζ) hvU)
    rw [map_mul, map_pow, map_one, map_mul, map_pow, map_one, hUc] at h3
    rw [zpow_neg, zpow_natCast]
    exact eq_inv_of_mul_eq_one_left h3
  · have e1 : (⟨W.Q ^ k • W.γ T x, hγ⟩ : ↥(W.N T)) =
        v • (⟨W.γD T W.gam (W.Q ^ k • x), W.N_Γ T W.gam _ hx⟩ : ↥(W.N T)) :=
      Subtype.ext (key x)
    have e2 : ex C h T i ζ ⟨W.γD T W.gam (W.Q ^ k • x), W.N_Γ T W.gam _ hx⟩ =
        fun m => u ^ m • ex C h T i ζ ⟨W.Q ^ k • x, hx⟩ m :=
      funext fun m => GlobalTheory.NL.GradedLat.ex_gam C h T hT i ζ hζ.pow_eq_one ⟨W.Q ^ k • x, hx⟩ m
    rw [e1, hlev, e2]

end GlobalTheory.NL.GamQ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachNInvQPowGammaStableStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachN_invQPow_gamma_stable : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let C := Cm l; let u : ↥LL.1 := algebraMap ↥(OL LL) ↥LL.1 (W.χΓ W.gam : ↥(OL LL)); ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ k : ℕ, (∀ x : W.DD T, W.Q ^ k • x ∈ W.N T → W.Q ^ k • W.γ T x ∈ W.N T) ∧ ∀ (i : Let K) (ζ : ↥LL.1), IsPrimitiveRoot ζ (l ^ s) → ∃ w : PowerSeries ↥LL.1, PowerSeries.constantCoeff w = u ^ (-(k : ℤ)) ∧ ∀ (x : W.DD T) (hx : W.Q ^ k • x ∈ W.N T) (hγ : W.Q ^ k • W.γ T x ∈ W.N T) (j : ℤ), ex C h T i ζ ⟨W.Q ^ k • W.γ T x, hγ⟩ j = conv w (fun m => u ^ m • ex C h T i ζ ⟨W.Q ^ k • x, hx⟩ m) j := by
  first | exact @GlobalTheory.NL.GamQ.gam_Q_pow | exact GlobalTheory.NL.GamQ.gam_Q_pow | (intros; apply GlobalTheory.NL.GamQ.gam_Q_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemWachNIffExpansion
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemWachNIffExpansion
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.WachModulePoleQuotient

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem mem_N_iff_of_points (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) {ι : Type} [Fintype ι]
    (nb : Module.Basis ι (LetA O n) ↥(W.N T)) (P : ZMod n → LL → Prop) (Φ : ZMod n → LL → Prop)
    (k : ℕ) (x : W.DD T) (hx : W.Q ^ k • x ∈ W.N T)
    (hkey : ∀ i ζ, P i ζ → (Φ i ζ ↔ ∀ j, nb.repr ⟨W.Q ^ k • x, hx⟩ j ∈ van W i ζ k))
    (hQ : ∀ i ζ, P i ζ → ∃ w : PowerSeries LL, W.lev i ζ W.Q = PowerSeries.X * w)
    (hdiv : ∀ a : LetA O n, (∀ i ζ, P i ζ → a ∈ van W i ζ k) → W.Q ^ k ∣ a)
    (hunit : IsUnit (algebraMap (LetA O n) W.EE W.Q)) :
    x ∈ W.N T ↔ ∀ i ζ, P i ζ → Φ i ζ := by
  constructor
  · intro hxN i ζ hζ
    rw [hkey i ζ hζ]
    intro j
    have e : (⟨W.Q ^ k • x, hx⟩ : ↥(W.N T)) = W.Q ^ k • (⟨x, hxN⟩ : ↥(W.N T)) := rfl
    rw [e, map_smul, Finsupp.smul_apply, smul_eq_mul]
    obtain ⟨w, hw⟩ := hQ i ζ hζ
    refine Ideal.mem_comap.2 (Ideal.mem_span_singleton.2 ?_)
    rw [map_mul, map_pow, hw]
    exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd (dvd_mul_right _ _) k) _
  · intro H
    have hd : ∀ j, W.Q ^ k ∣ nb.repr ⟨W.Q ^ k • x, hx⟩ j := fun j =>
      hdiv _ (fun i ζ hζ => (hkey i ζ hζ).1 (H i ζ hζ) j)
    choose b hb using hd
    let z : ↥(W.N T) := ∑ j, b j • nb j
    have hz : W.Q ^ k • ((z : ↥(W.N T)) : W.DD T) = W.Q ^ k • x := by
      have e : (⟨W.Q ^ k • x, hx⟩ : ↥(W.N T)) = W.Q ^ k • z := by
        conv_lhs => rw [← nb.sum_repr ⟨W.Q ^ k • x, hx⟩]
        simp only [z, Finset.smul_sum, hb, mul_smul]
      exact (congrArg Subtype.val e).symm
    have hu : IsUnit (algebraMap (LetA O n) W.EE (W.Q ^ k)) := by
      rw [map_pow]
      exact hunit.pow k
    obtain ⟨u, hu'⟩ := hu
    have h1 : ∀ y : W.DD T, W.Q ^ k • y = (u : W.EE) • y := fun y => by
      rw [hu', algebraMap_smul]
    rw [h1, h1] at hz
    have hx' : x = (z : W.DD T) := by
      have := congrArg (fun y => ((u⁻¹ : W.EEˣ) : W.EE) • y) hz
      simp only [smul_smul, Units.inv_mul, one_smul] at this
      exact this.symm
    rw [hx']
    exact z.2

end Generic


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem mem_N_iff_expansion : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (k : ℕ) (x : W.DD T) (hx : W.Q ^ k • x ∈ W.N T), x ∈ W.N T ↔ ∀ (i : Let K) (ζ : ↥LL.1), IsPrimitiveRoot ζ (l ^ s) → ∃ f ∈ Lat C h T i ζ, ∀ j : ℤ, ex C h T i ζ ⟨W.Q ^ k • x, hx⟩ j = f (j - k) := by
  intro D HW F Cm l _ K s LL h W C T hT k x hx
  obtain ⟨nb⟩ := GlobalTheory.NL.N_basis D HW F l K s LL h T hT
  refine mem_N_iff_of_points W T nb (fun i ζ => IsPrimitiveRoot ζ (l ^ s)) _ k x hx ?_ ?_ ?_ ?_
  · intro i ζ hζ
    exact ((GlobalTheory.NL.LevInj.expansion_basis D HW F Cm l K s LL h T hT i ζ ⟨s, hζ⟩
      (GlobalTheory.NL.FullLevel.full_lat D HW F Cm l K s LL h T hT i ζ hζ)).2 _ nb).2.2 _ k
  · intro i ζ hζ
    obtain ⟨⟨w, _, hw⟩, -⟩ := (GlobalTheory.NL.lev_at_root_of_unity D HW l K s LL h i ζ ⟨s, hζ⟩).2.2.2.1 hζ
    exact ⟨w, hw⟩
  · exact (GlobalTheory.NL.WDiv.weierstrass_dense D HW l K s LL h).1 k
  · have h0 := ((GlobalTheory.NL.IoXQ.main D HW F l K s LL h).2.2.2.2.2.2 0).2
    simpa using h0

end GlobalTheory.NL.WachModulePoleQuotient
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemWachNIffExpansionStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_wachN_iff_expansion : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (k : ℕ) (x : W.DD T) (hx : W.Q ^ k • x ∈ W.N T), x ∈ W.N T ↔ ∀ (i : Let K) (ζ : ↥LL.1), IsPrimitiveRoot ζ (l ^ s) → ∃ f ∈ Lat C h T i ζ, ∀ j : ℤ, ex C h T i ζ ⟨W.Q ^ k • x, hx⟩ j = f (j - k) := by
  first | exact @GlobalTheory.NL.WachModulePoleQuotient.mem_N_iff_expansion | exact GlobalTheory.NL.WachModulePoleQuotient.mem_N_iff_expansion | (intros; apply GlobalTheory.NL.WachModulePoleQuotient.mem_N_iff_expansion <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitToBFrobEis
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitToBFrobEis
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal.FrobEis

theorem factorial_pow_dvd (r : ℕ) : ∀ k : ℕ, r.factorial ^ k ∣ (k * r).factorial
  | 0 => by simp
  | k + 1 => by
    rw [pow_succ, add_mul, one_mul]
    exact (Nat.mul_dvd_mul_right (factorial_pow_dvd r k) _).trans
      (Nat.factorial_mul_factorial_dvd_factorial_add _ _)

theorem factorial_pow_mul_dvd {l : ℕ} (hl : 1 ≤ l) : l.factorial ^ l * l ∣ (l * l).factorial := by
  obtain ⟨k, rfl⟩ : ∃ k, l = k + 1 := ⟨l - 1, by omega⟩
  have h1 : (k + 1) * (k + 1) = (k * (k + 1) + k) + 1 := by ring
  have h3 := (Nat.mul_dvd_mul_right (factorial_pow_dvd (k + 1) k) k.factorial).trans
    (Nat.factorial_mul_factorial_dvd_factorial_add (k * (k + 1)) k)
  have h4 : (k + 1).factorial ^ (k + 1) * (k + 1) =
      (k + 1).factorial ^ k * k.factorial * (k * (k + 1) + k + 1) := by
    rw [Nat.factorial_succ k, pow_succ]; ring
  rw [h1, Nat.factorial_succ (k * (k + 1) + k), h4, mul_comm (k * (k + 1) + k + 1)]
  exact Nat.mul_dvd_mul_right h3 _

variable {l : ℕ} [hl : Fact l.Prime]

theorem isUnit_one_add {y z : Per.Acris l} {n : ℕ} (h : y ^ n = (l : Per.Acris l) * z) : IsUnit (1 + y) := by
  have := (GlobalTheory.MemLoc.acris_torsionFree_complete l).2
  have hJ : -(-y) ^ n ∈ Ideal.jacobson (⊥ : Ideal (Per.Acris l)) := by
    refine IsAdicComplete.le_jacobson_bot (Ideal.span {((l : ℕ) : Per.Acris l)}) (Ideal.mem_span_singleton.2 ⟨-((-1) ^ n * z), ?_⟩)
    rw [neg_pow, h]; ring
  have h1 := Ideal.mem_jacobson_bot.1 hJ 1
  rw [mul_one, neg_add_eq_sub] at h1
  have h2 := mul_neg_geom_sum (-y) n
  rw [sub_neg_eq_add] at h2
  exact isUnit_of_mul_isUnit_left (h2 ▸ h1)

theorem isUnit_teich_pow_add {e : ℕ} (ϖ : PiSys l e) :
    IsUnit (acrisToBcris l (ainfToAcris l (ϖ.teich ^ (e * l) + l))) := by
  obtain ⟨d, hd⟩ := ϖ.exists_dpow_teich l
  obtain ⟨d₂, hd₂⟩ := ϖ.exists_dpow_teich (l * l)
  obtain ⟨m, hm⟩ := factorial_pow_mul_dvd hl.out.one_lt.le
  have hm' : ((l * l).factorial : Per.Acris l) = (l.factorial : Per.Acris l) ^ l * l * m := by
    rw [hm]; push_cast; ring
  have h3 : ((l.factorial : Per.Acris l) * d) ^ l = ainfToAcris l ϖ.teich ^ (e * (l * l)) := by
    rw [hd, ← pow_mul, mul_assoc]
  have hdl : d ^ l = l * (m * d₂) := by
    refine sub_eq_zero.1 (acris_nat_cancel (pow_ne_zero l l.factorial_ne_zero) ?_)
    push_cast
    linear_combination h3 - hd₂ + d₂ * hm'
  have hp : ((l.factorial : ℕ) : Per.Acris l) = l * ((l - 1).factorial : ℕ) := by
    rw [← Nat.mul_factorial_pred hl.out.ne_zero]; push_cast; ring
  have h1 : ainfToAcris l (ϖ.teich ^ (e * l) + l) = l * (1 + ((l - 1).factorial : Per.Acris l) * d) := by
    rw [map_add (f := _), map_pow, map_natCast, ← hd, hp]; ring
  have hy : (((l - 1).factorial : Per.Acris l) * d) ^ l =
      l * (((l - 1).factorial : Per.Acris l) ^ l * (m * d₂)) := by
    rw [mul_pow, hdl]; ring
  rw [h1, map_mul, map_natCast]
  exact (GlobalTheory.MemLoc.isUnit_l_Bcris l).mul ((isUnit_one_add hy).map _)

theorem isUnit_toB_frob_eis : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O : Type) [CommRing O]
    [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] (ϖ : PiSys l e),
    IsUnit (toB l O (frobOA l O (1 ⊗ₜ ϖ.ev a (eis l a e)))) := by
  intro l _ a e _ _ O _ _ _ _ ϖ
  have hE : WittVector.frobenius (ϖ.ev a (eis l a e)) = ϖ.teich ^ (e * l) + l := by
    rw [← ϖ.ev_frobS a, eis, map_add (f := _), map_pow, frobS_X, map_natCast, map_add (f := _), map_pow, map_pow, PiSys.ev_X,
      map_natCast, ← pow_mul, mul_comm l e]
  have h : toB l O (frobOA l O (1 ⊗ₜ ϖ.ev a (eis l a e))) =
      (Algebra.TensorProduct.includeRight : Per.Bcris l →ₐ[ℤ_[l]] OB l O)
        (acrisToBcris l (ainfToAcris l (ϖ.teich ^ (e * l) + l))) := by
    rw [frobOA_tmul, hE]; rfl
  rw [h]
  exact (isUnit_teich_pow_add ϖ).map _

end GlobalTheory.BKGal.FrobEis
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitToBFrobEisStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isUnit_toB_frobOA_eis : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] (ϖ : PiSys l e), IsUnit (toB l O (frobOA l O (1 ⊗ₜ ϖ.ev a (eis l a e)))) := by
  first | exact @GlobalTheory.BKGal.FrobEis.isUnit_toB_frob_eis | exact GlobalTheory.BKGal.FrobEis.isUnit_toB_frob_eis | (intros; apply GlobalTheory.BKGal.FrobEis.isUnit_toB_frob_eis <;> assumption)
end
end
