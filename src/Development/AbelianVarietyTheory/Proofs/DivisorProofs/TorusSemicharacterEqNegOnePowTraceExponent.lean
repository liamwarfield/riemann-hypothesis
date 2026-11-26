module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockJetGaussianEntireOriginGridFrames
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompletedLatticeColumnLatticeMulIff
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorusAbelianQuotientPDivisibleSmoothGroup

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusSemicharacterEqNegOnePowTraceExponent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusSemicharacterEqNegOnePowTraceExponent
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SemicharTrace

open Formalism.MainNotions.TaylorLogMetric

variable {D : D7}

theorem sig_eq_star (x : D.host.E) : (D.sp.cm.sig : D.host.E →+* D.host.E) x = star x := by
  have τ0 : D.what₂.Tau := D.eTau.symm 1
  apply (tauE D τ0).injective
  rw [GlobalTheory.FockCompare.tauE_star]
  exact D.sp.cm.cmUnram.2.1 (tauE D τ0) x

theorem cT_eq {m n : ℕ} (A : Matrix (Fin m) (Fin n) D.host.E) :
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) A = Aᴴ := by
  refine Matrix.ext fun i j => ?_
  simp only [Formalism.UG.cT, Matrix.conjTranspose_apply, Matrix.transpose_apply, Matrix.map_apply]
  show (D.sp.cm.sig : D.host.E →+* D.host.E) (A j i) = star (A j i)
  exact sig_eq_star _

theorem hRat_eq (S T : HSp D) (x y : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    GlobalTheory.LatVac.hRat S T x y = Matrix.trace (S.gram⁻¹ * yᴴ * T.gram * x) := by
  simp only [GlobalTheory.LatVac.hRat, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => arg 2; ext c; rw [Finset.sum_comm]
  rw [Finset.sum_comm]

end GlobalTheory.SemicharTrace

namespace GlobalTheory.SemicharTrace

open Formalism.MainNotions.TaylorLogMetric

variable {D : D7}

theorem hRat_frames (S T : HSp D) (B : GL (Fin S.rank) D.host.E) (B' : GL (Fin T.rank) D.host.E)
    (hB : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) B.1 * S.gram * B.1 = 1)
    (hB' : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) B'.1 * T.gram * B'.1 = 1)
    (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    GlobalTheory.LatVac.hRat S T (B'.1 * M * (B⁻¹ : GL (Fin S.rank) D.host.E).1)
      (B'.1 * M * (B⁻¹ : GL (Fin S.rank) D.host.E).1) = Matrix.trace (Mᴴ * M) := by
  rw [cT_eq] at hB hB'
  rw [hRat_eq]
  set Bi := (B⁻¹ : GL (Fin S.rank) D.host.E).1 with hBi_def
  have hBi : Bi * B.1 = 1 := by rw [hBi_def, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hSi : S.gram⁻¹ = B.1 * B.1ᴴ := by
    have h1 : B.1 * (B.1ᴴ * S.gram) = 1 := mul_eq_one_comm.1 hB
    have h2 : (B.1 * B.1ᴴ) * S.gram = 1 := by rw [Matrix.mul_assoc]; exact h1
    exact Matrix.inv_eq_left_inv h2
  have hBB : B.1ᴴ * Biᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, hBi, Matrix.conjTranspose_one]
  calc Matrix.trace (S.gram⁻¹ * (B'.1 * M * Bi)ᴴ * T.gram * (B'.1 * M * Bi))
      = Matrix.trace (B.1 * ((B.1ᴴ * Biᴴ) * (Mᴴ * ((B'.1ᴴ * T.gram * B'.1) * (M * Bi))))) := by
        rw [hSi]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Matrix.trace (B.1 * (Mᴴ * (M * Bi))) := by rw [hBB, hB', Matrix.one_mul, Matrix.one_mul]
    _ = Matrix.trace ((Mᴴ * M * Bi) * B.1) := by
        rw [Matrix.trace_mul_comm]; simp only [Matrix.mul_assoc]
    _ = Matrix.trace (Mᴴ * M) := by rw [Matrix.mul_assoc, hBi, Matrix.mul_one]

theorem embT_sqrt (τ : D.what₂.Tau) :
    embT D τ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) :=
  Formalism.L2.Theta.tauE_sqrtMinusD D τ

theorem embT_ne_conj (τ τ' : D.what₂.Tau) : embT D τ ≠ (starRingEnd ℂ).comp (embT D τ') := by
  intro h
  have h1 := congrArg Complex.im (DFunLike.congr_fun h D.host.sqrtMinusD)
  rw [RingHom.comp_apply, embT_sqrt, embT_sqrt] at h1
  have := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.sqrt_d_pos D
  simp at h1
  linarith

theorem trace_split (z : D.host.E) :
    ((Algebra.trace ℚ D.host.E z : ℚ) : ℂ) = ∑ τ : D.what₂.Tau, (embT D τ z + starRingEnd ℂ (embT D τ z)) := by
  have h := trace_eq_sum_embeddings ℂ (K := ℚ) (x := z)
  let e : D.what₂.Tau ⊕ D.what₂.Tau → (D.host.E →ₐ[ℚ] ℂ) := fun s =>
    RingHom.equivRatAlgHom _ _ (Sum.elim (embT D) (fun τ => (starRingEnd ℂ).comp (embT D τ)) s)
  have he : Function.Bijective e := by
    refine (RingHom.equivRatAlgHom _ _).bijective.comp ⟨?_, fun σ => ?_⟩
    · rintro (a | a) (b | b) hab
      · rw [Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL.embT_inj D hab]
      · exact absurd hab (embT_ne_conj a b)
      · exact absurd hab.symm (embT_ne_conj b a)
      · have : embT D a = embT D b := RingHom.ext fun x =>
          (starRingEnd ℂ).injective (DFunLike.congr_fun hab x)
        rw [Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL.embT_inj D this]
    · obtain ⟨τ, h | h⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FL.emb_cases D σ
      · exact ⟨Sum.inl τ, h.symm⟩
      · exact ⟨Sum.inr τ, h.symm⟩
  rw [← Fintype.sum_bijective e he (fun s => e s z) (fun σ => σ z) fun _ => rfl, Fintype.sum_sum_type] at h
  rw [show ((Algebra.trace ℚ D.host.E z : ℚ) : ℂ) = algebraMap ℚ ℂ (Algebra.trace ℚ D.host.E z) from rfl, h,
    ← Finset.sum_add_distrib]
  rfl

end GlobalTheory.SemicharTrace

namespace GlobalTheory.SemicharTrace

open Formalism.MainNotions.TaylorLogMetric

variable {D : D7}

theorem embT_star (τ : D.what₂.Tau) (x : D.host.E) : embT D τ (star x) = starRingEnd ℂ (embT D τ x) :=
  GlobalTheory.FockCompare.tauE_star τ x

theorem absNorm_ne : ((Ideal.absNorm D.host.ccK : ℕ) : ℂ) ≠ 0 := by
  have : Ideal.absNorm D.host.ccK ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact D.host.ccK_ne_bot
  exact_mod_cast this

theorem embT_c_add_conj (τ : D.what₂.Tau) :
    embT D τ (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2) +
      starRingEnd ℂ (embT D τ (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2)) =
      -1 / ((Ideal.absNorm D.host.ccK : ℕ) : ℂ) := by
  have hN := absNorm_ne (D := D)
  have hs : ((Real.sqrt D.host.d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.sqrt_d_pos D).ne'
  have e : embT D τ (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2) =
      -1 / (((Ideal.absNorm D.host.ccK : ℕ) : ℂ) * (Complex.I * (Real.sqrt D.host.d : ℂ))) *
        ((1 + Complex.I * (Real.sqrt D.host.d : ℂ)) / 2) ^ 2 := by
    unfold Formalism.BasicNotions.Host.xi0
    simp only [map_mul, map_div₀, map_neg, map_one, map_natCast, map_pow, map_add (f := _), map_ofNat, embT_sqrt]
  rw [e]
  simp only [map_mul, map_div₀, map_neg, map_one, map_pow, map_add (f := _), map_natCast, Complex.conj_I,
    Complex.conj_ofReal, map_ofNat]
  field_simp
  ring_nf

end GlobalTheory.SemicharTrace

namespace GlobalTheory.SemicharTrace

open Formalism.MainNotions.TaylorLogMetric

variable {D : D7}

theorem embT_trace (τ : D.what₂.Tau) {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) :
    embT D τ (Matrix.trace (Mᴴ * M)) =
      ((∑ i, ∑ j, Complex.normSq (embT D τ (M i j)) : ℝ) : ℂ) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, map_sum, map_mul,
    embT_star, Complex.ofReal_sum, Complex.normSq_eq_conj_mul_self]
  rw [Finset.sum_comm]

theorem k_eq {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) (k : ℤ)
    (hk : (k : ℚ) = Algebra.trace ℚ D.host.E (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2 *
      Matrix.trace (Mᴴ * M))) :
    (k : ℝ) = -(∑ τ : D.what₂.Tau, ∑ i, ∑ j, Complex.normSq (embT D τ (M i j))) /
      (Ideal.absNorm D.host.ccK : ℝ) := by
  have h : ((k : ℚ) : ℂ) = ((Algebra.trace ℚ D.host.E (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2 *
      Matrix.trace (Mᴴ * M)) : ℚ) : ℂ) := by rw [hk]
  rw [trace_split] at h
  have h2 : ∀ τ : D.what₂.Tau,
      embT D τ (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2 * Matrix.trace (Mᴴ * M)) +
        starRingEnd ℂ (embT D τ (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2 * Matrix.trace (Mᴴ * M))) =
      -1 / ((Ideal.absNorm D.host.ccK : ℕ) : ℂ) *
        ((∑ i, ∑ j, Complex.normSq (embT D τ (M i j)) : ℝ) : ℂ) := by
    intro τ
    rw [show embT D τ (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2 * Matrix.trace (Mᴴ * M)) =
        embT D τ (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2) * embT D τ (Matrix.trace (Mᴴ * M)) from
        map_mul _ _ _, embT_trace, map_mul (starRingEnd ℂ), Complex.conj_ofReal, ← add_mul, embT_c_add_conj]
  rw [Finset.sum_congr rfl fun τ _ => h2 τ, ← Finset.mul_sum] at h
  have hN := absNorm_ne (D := D)
  have h3 : ((k : ℝ) : ℂ) = (((-(∑ τ : D.what₂.Tau, ∑ i, ∑ j, Complex.normSq (embT D τ (M i j))) /
      (Ideal.absNorm D.host.ccK : ℝ)) : ℝ) : ℂ) := by
    push_cast
    rw [show ((k : ℂ)) = ((k : ℚ) : ℂ) by push_cast; rfl, h]
    field_simp
    simp only [Complex.ofReal_sum]
  exact_mod_cast h3

end GlobalTheory.SemicharTrace

namespace GlobalTheory.SemicharTrace

open Formalism.MainNotions.TaylorLogMetric

variable {D : D7}

theorem qH_eq {m n : ℕ} (δ : ℂ) (hδ : δ ≠ 0) (M : Matrix (Fin m) (Fin n) D.host.E) :
    Real.sqrt D.host.d / 2 *
      (Hf D (tor0 D D.host.ccK δ) (δ • embV D (tor0 D D.host.ccK δ) M)
        (δ • embV D (tor0 D D.host.ccK δ) M)).re =
      (∑ τ : D.what₂.Tau, ∑ i, ∑ j, Complex.normSq (embT D τ (M i j))) / (Ideal.absNorm D.host.ccK : ℝ) := by
  have hA := GlobalTheory.MomDict.area_lamOf D D.host.ccK δ D.host.ccK_ne_bot
  have hH : Hf D (tor0 D D.host.ccK δ) (δ • embV D (tor0 D D.host.ccK δ) M)
        (δ • embV D (tor0 D D.host.ccK δ) M) =
      (((Complex.normSq δ * ∑ τ : D.what₂.Tau, ∑ i, ∑ j, Complex.normSq (embT D τ (M i j))) /
        area (lamOf D D.host.ccK δ) : ℝ) : ℂ) := by
    unfold Hf
    rw [Complex.ofReal_div]
    congr 1
    simp only [embV, tor0, Pi.smul_apply, smul_eq_mul, Complex.mul_conj, Complex.normSq_mul,
      Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum]
  rw [hH, Complex.ofReal_re, hA]
  have hN : (0 : ℝ) < (Ideal.absNorm D.host.ccK : ℝ) := by
    have : Ideal.absNorm D.host.ccK ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact D.host.ccK_ne_bot
    exact_mod_cast Nat.pos_of_ne_zero this
  have hs := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.sqrt_d_pos D
  have hδ2 : 0 < Complex.normSq δ := Complex.normSq_pos.mpr hδ
  field_simp

theorem al_mul_neg_one_pow : ∀ {D : D7} (S T : HSp D) (B : GL (Fin S.rank) D.host.E) (B' : GL (Fin T.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) B.1 * S.gram * B.1 = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) B'.1 * T.gram * B'.1 = 1 → ∀ (δ : ℂ), δ ≠ 0 → ∀ (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (k : ℤ), (k : ℚ) = Algebra.trace ℚ D.host.E (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2 * GlobalTheory.LatVac.hRat S T (B'.1 * M * (B⁻¹ : GL (Fin S.rank) D.host.E).1) (B'.1 * M * (B⁻¹ : GL (Fin S.rank) D.host.E).1)) → Formalism.MainNotions.TaylorLogMetric.al D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (δ • Formalism.MainNotions.TaylorLogMetric.embV D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) M) * (-1 : ℂ) ^ k = 1 := by
  intro D S T B B' hB hB' δ hδ M k hk
  rw [hRat_frames S T B B' hB hB' M] at hk
  have hk' := k_eq M k hk
  have hq := qH_eq δ hδ M
  have hr : Real.sqrt D.host.d / 2 *
      (Hf D (tor0 D D.host.ccK δ) (δ • embV D (tor0 D D.host.ccK δ) M)
        (δ • embV D (tor0 D D.host.ccK δ) M)).re = ((-k : ℤ) : ℝ) := by
    rw [hq, Int.cast_neg, hk', neg_div, neg_neg]
  unfold al
  rw [hr, round_intCast, _root_.zpow_neg]
  exact inv_mul_cancel₀ (zpow_ne_zero _ (by norm_num))

end GlobalTheory.SemicharTrace
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusSemicharacterEqNegOnePowTraceExponentStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusSemicharacter_eq_neg_one_pow_traceExponent : ∀ {D : D7} (S T : HSp D) (B : GL (Fin S.rank) D.host.E) (B' : GL (Fin T.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) B.1 * S.gram * B.1 = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) B'.1 * T.gram * B'.1 = 1 → ∀ (δ : ℂ), δ ≠ 0 → ∀ (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (k : ℤ), (k : ℚ) = Algebra.trace ℚ D.host.E (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2 * GlobalTheory.LatVac.hRat S T (B'.1 * M * (B⁻¹ : GL (Fin S.rank) D.host.E).1) (B'.1 * M * (B⁻¹ : GL (Fin S.rank) D.host.E).1)) → Formalism.MainNotions.TaylorLogMetric.al D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (δ • Formalism.MainNotions.TaylorLogMetric.embV D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) M) * (-1 : ℂ) ^ k = 1 := by
  first | exact @GlobalTheory.SemicharTrace.al_mul_neg_one_pow | exact GlobalTheory.SemicharTrace.al_mul_neg_one_pow | (intros; apply GlobalTheory.SemicharTrace.al_mul_neg_one_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperSmoothConnGroupOfManyTorsionCharP
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTorsionTorusExtensionAbelianVarietyLe
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTorsionTorusExtensionAbelianVarietyLe
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorusExtTorsion

theorem card_le : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], IsCommMonObj G → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (B : Over (Sp k)) [GrpObj B] (i : splitTorus (Sp k) X ⟶ G) (q : G ⟶ B), GlobalTheory.SS.IsQuot i q → IsAbelianScheme B → ∀ a : ℕ, SmoothOfRelativeDimension a B.hom → ∀ m : ℕ, (m : k) ≠ 0 → ∀ s : Finset (𝟙_ (Over (Sp k)) ⟶ G), (∀ x ∈ s, x ^ m = 1) → s.card ≤ m ^ (Module.finrank ℤ X + 2 * a) := by
  classical
  intro k _ _ G _ hGc X _ _ _ B _ i q hQ hB a ha m hm s hs
  obtain ⟨hi, hq, -, -, -, hk, -⟩ := hQ
  haveI := hGc
  let P := 𝟙_ (Over (Sp k))
  let I := IsMonHom.monoidHom i P
  let Q := IsMonHom.monoidHom q P
  have hIinj : Function.Injective I := fun a b h => hk.hom_ext h (toUnit_unique _ _)
  have hm0 : m ≠ 0 := by rintro rfl; exact hm Nat.cast_zero

  obtain ⟨e⟩ := GlobalTheory.SemiAbTorsionCount.nonempty_torus_points_mulEquiv k X
  obtain ⟨-, hTcard⟩ := GlobalTheory.SemiAbTorsionCount.divisible_and_card e m hm
  haveI hTfin : Finite {t : P ⟶ splitTorus (Sp k) X // t ^ m = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hTcard]; exact pow_ne_zero _ hm0)
  letI : Fintype {t : P ⟶ splitTorus (Sp k) X // t ^ m = 1} := Fintype.ofFinite _

  have hBcard := GlobalTheory.UU.TorsionCount.card_torsion_points_unconditional k B a m hB ha hm
  haveI hBfin : Finite {b : P ⟶ B // b ^ m = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hBcard]; exact pow_ne_zero _ hm0)

  have himg : (s.image Q).card ≤ m ^ (2 * a) := by
    rw [← hBcard, ← Nat.card_eq_finsetCard]
    refine Nat.card_le_card_of_injective (fun y => ⟨y.1, ?_⟩) (fun y z h => Subtype.ext (congrArg Subtype.val h :))
    obtain ⟨x, hx, hy⟩ := Finset.mem_image.1 y.2
    rw [← hy, ← map_pow, hs x hx, map_one]

  have hfib : ∀ b ∈ s.image Q, (s.filter (fun x => Q x = b)).card ≤ m ^ Module.finrank ℤ X := by
    intro b hb
    obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.1 hb
    have hsub : s.filter (fun x => Q x = Q x₀) ⊆
        Finset.univ.image (fun t : {t : P ⟶ splitTorus (Sp k) X // t ^ m = 1} => x₀ * I t.1) := by
      intro x hx
      obtain ⟨hxs, hxq⟩ := Finset.mem_filter.1 hx
      have hy : (x₀⁻¹ * x) ≫ q = 1 := by
        change Q (x₀⁻¹ * x) = 1
        rw [map_mul, map_inv, hxq, inv_mul_cancel]
      let t := hk.lift (x₀⁻¹ * x) (toUnit _) (by rw [hy, Hom.one_def])
      have ht : I t = x₀⁻¹ * x := hk.lift_fst _ _ _
      have htm : t ^ m = 1 := by
        apply hIinj
        rw [map_pow, ht, map_one, mul_pow, inv_pow, hs x hxs, hs x₀ hx₀, inv_one, _root_.one_mul]
      refine Finset.mem_image.2 ⟨⟨t, htm⟩, Finset.mem_univ _, ?_⟩
      change x₀ * I t = x
      rw [ht, mul_inv_cancel_left]
    calc (s.filter (fun x => Q x = Q x₀)).card ≤ _ := Finset.card_le_card hsub
      _ ≤ Finset.univ.card := Finset.card_image_le
      _ = m ^ Module.finrank ℤ X := by rw [Finset.card_univ, Fintype.card_eq_nat_card, hTcard]
  calc s.card ≤ m ^ Module.finrank ℤ X * (s.image Q).card := Finset.card_le_mul_card_image s _ hfib
    _ ≤ m ^ Module.finrank ℤ X * m ^ (2 * a) := Nat.mul_le_mul_left _ himg
    _ = m ^ (Module.finrank ℤ X + 2 * a) := (pow_add _ _ _).symm

end GlobalTheory.TorusExtTorsion
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTorsionTorusExtensionAbelianVarietyLeStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_torsion_torusExtension_abelianVariety_le : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G], IsCommMonObj G → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (B : Over (Sp k)) [GrpObj B] (i : splitTorus (Sp k) X ⟶ G) (q : G ⟶ B), GlobalTheory.SS.IsQuot i q → IsAbelianScheme B → ∀ a : ℕ, SmoothOfRelativeDimension a B.hom → ∀ m : ℕ, (m : k) ≠ 0 → ∀ s : Finset (𝟙_ (Over (Sp k)) ⟶ G), (∀ x ∈ s, x ^ m = 1) → s.card ≤ m ^ (Module.finrank ℤ X + 2 * a) := by
  first | exact @GlobalTheory.TorusExtTorsion.card_le | exact GlobalTheory.TorusExtTorsion.card_le | (intros; apply GlobalTheory.TorusExtTorsion.card_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperOfIsQuotOfFinrankEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperOfIsQuotOfFinrankEqZero
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SS

theorem isProper_of_isQuot_of_finrank_eq_zero : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (B : Over (Sp k)) [GrpObj B] (i : splitTorus (Sp k) X ⟶ G) (q : G ⟶ B), GlobalTheory.SS.IsQuot i q → IsAbelianScheme B → Module.finrank ℤ X = 0 → IsProper G.hom := by
  intro k _ _ G _ X _ _ _ B _ i q hQ hB hX
  obtain ⟨hi, hq, hf, hsu, ha, hp, -⟩ := hQ
  have hsub : Subsingleton X := Module.finrank_zero_iff.1 hX
  have : Mono q := ⟨fun {Y} x y hxy => by
    have h1 : (x * y⁻¹) ≫ q = toUnit _ ≫ η[B] := by
      rw [MonObj.mul_comp, GrpObj.inv_comp, hxy, mul_inv_cancel]
      rfl
    have h2 : hp.lift _ _ h1 = 1 := by
      apply (GlobalTheory.splitTorusPointsEquiv (Sp k) X Y).injective
      refine MonoidHom.ext fun a => ?_
      have ha1 : a = 1 := by
        show a = Multiplicative.ofAdd 0
        rw [← ofAdd_toAdd a, Subsingleton.elim (Multiplicative.toAdd a) 0]
      rw [ha1, map_one, map_one]
    have h3 := hp.lift_fst _ _ h1
    rw [h2, MonObj.one_comp] at h3
    exact mul_inv_eq_one.1 h3.symm⟩
  have : Mono q.left := inferInstanceAs (Mono ((Over.forget _).map q))
  have := hB.proper
  have : Flat q.left := hf
  have : Surjective q.left := hsu
  have : IsAffineHom q.left := ha
  have : IsIso q.left := Flat.isIso_of_surjective_of_mono q.left
  rw [← Over.w q]
  infer_instance

end GlobalTheory.SS
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperOfIsQuotOfFinrankEqZeroStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isProper_of_isQuot_abelian_of_finrank_eq_zero : ∀ (k : Type) [Field k] [IsAlgClosed k] (G : Over (Sp k)) [GrpObj G] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (B : Over (Sp k)) [GrpObj B] (i : splitTorus (Sp k) X ⟶ G) (q : G ⟶ B), GlobalTheory.SS.IsQuot i q → IsAbelianScheme B → Module.finrank ℤ X = 0 → IsProper G.hom := by
  first | exact @GlobalTheory.SS.isProper_of_isQuot_of_finrank_eq_zero | exact GlobalTheory.SS.isProper_of_isQuot_of_finrank_eq_zero | (intros; apply GlobalTheory.SS.isProper_of_isQuot_of_finrank_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperSmoothConnGroupOfManyTorsionCharP
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SerreTateProperness

theorem main : ∀ (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (G : Over (Sp k)) [GrpObj G], GlobalTheory.SS.SmConn G → ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → ∀ m : ℕ, (m : k) ≠ 0 → ∀ s : Finset (𝟙_ (Over (Sp k)) ⟶ G), (∀ x ∈ s, x ^ m = 1) → m ^ (2 * g) < m * s.card → IsProper G.hom := by
  intro k _ _ p _ _ G _ hG g hg m hm s hs hcard
  classical
  obtain ⟨N, _, ν, hN, hνmon, hνci, hpdiv, hlift, -, hdim⟩ :=
    GlobalTheory.DivisiblePart.exists_divisiblePart k p G hG
  obtain ⟨g', hg', hiso⟩ := hdim g hg
  obtain ⟨X, _, _, _, B, _, i, q, hq, hB, hdimB⟩ :=
    GlobalTheory.SS.DivSemi.exists_torus_abelian_quotient k p N hN hpdiv
  obtain ⟨a, ha, hga⟩ := hdimB g' hg'

  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (by simp)
  have hcop : m.Coprime p := by
    have hnd : ¬ p ∣ m := fun h => hm ((CharP.cast_eq_zero_iff k p m).mpr h)
    exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (Fact.out)).mpr hnd)

  have hmono : Mono ν.left := inferInstance
  have hinj : ∀ y y' : 𝟙_ (Over (Sp k)) ⟶ N, y ≫ ν = y' ≫ ν → y = y' := by
    intro y y' h
    ext1
    exact (cancel_mono ν.left).mp (by simpa using congrArg CommaMorphism.left h)

  have hlift' : ∀ x ∈ s, ∃ y : 𝟙_ (Over (Sp k)) ⟶ N, y ≫ ν = x ∧ y ^ m = 1 := by
    intro x hx
    obtain ⟨y, hy⟩ := hlift x m hcop hm0 (hs x hx)
    refine ⟨y, hy, hinj _ _ ?_⟩
    rw [MonObj.pow_comp, hy, hs x hx, MonObj.one_comp]
  choose! f hf1 hf2 using hlift'
  have hfinj : Set.InjOn f s := by
    intro x hx x' hx' h
    rw [← hf1 x hx, ← hf1 x' hx', h]
  have hcardN : (s.image f).card ≤ m ^ (Module.finrank ℤ X + 2 * a) := by
    refine GlobalTheory.T.card_torsion_torusExtension_abelianVariety_le k N hN.1 X B i q hq hB a ha m hm (s.image f) ?_
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact hf2 x hx
  rw [Finset.card_image_of_injOn hfinj] at hcardN

  have hpt : Nonempty (𝟙_ (Over (Sp k))).left := by
    change Nonempty (Sp k)
    first
    | infer_instance
    | exact ⟨IsLocalRing.closedPoint k⟩
  have hne : Nonempty N.left := ⟨(1 : 𝟙_ (Over (Sp k)) ⟶ N).left hpt.some⟩
  have hgle : g' ≤ g := GlobalTheory.T.relDim_le_of_smooth_of_isClosedImmersion k N G ν hνci hne g g' hg hg'

  have hm1 : 1 < m := by
    rcases Nat.lt_or_ge 1 m with h | h
    · exact h
    · exfalso
      have : m = 1 := by omega
      subst this
      simp at hcard hcardN
      omega
  have hlt : m ^ (2 * g) < m ^ (Module.finrank ℤ X + 2 * a + 1) := by
    calc m ^ (2 * g) < m * s.card := hcard
      _ ≤ m * m ^ (Module.finrank ℤ X + 2 * a) := Nat.mul_le_mul_left m hcardN
      _ = m ^ (Module.finrank ℤ X + 2 * a + 1) := by ring
  have hexp := (Nat.pow_lt_pow_iff_right (by omega)).mp hlt
  have ht : Module.finrank ℤ X = 0 := by omega
  have hgg : g ≤ g' := by omega
  haveI hP : IsProper N.hom := GlobalTheory.T.isProper_of_isQuot_abelian_of_finrank_eq_zero k N X B i q hq hB ht
  haveI : IsIso ν.left := by
    haveI := hiso hgg
    exact Functor.map_isIso (Over.forget (Sp k)) ν
  have hw : G.hom = inv ν.left ≫ N.hom := by
    rw [← Over.w ν]
    simp
  rw [hw]
  infer_instance

end GlobalTheory.SerreTateProperness
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperSmoothConnGroupOfManyTorsionCharPStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isProper_smoothConnGroup_of_many_torsion_charP : ∀ (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (G : Over (Sp k)) [GrpObj G], GlobalTheory.SS.SmConn G → ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → ∀ m : ℕ, (m : k) ≠ 0 → ∀ s : Finset (𝟙_ (Over (Sp k)) ⟶ G), (∀ x ∈ s, x ^ m = 1) → m ^ (2 * g) < m * s.card → IsProper G.hom := by
  first | exact @GlobalTheory.SerreTateProperness.main | exact GlobalTheory.SerreTateProperness.main | (intros; apply GlobalTheory.SerreTateProperness.main <;> assumption)
end
end
