module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatIntegrandFlippedTensorLocallyConstantCompact
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharUniformiserValueIsAlgebraic
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmFockCompact

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharFiniteIdelesIsAlgebraicOfResEta
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharFiniteIdelesIsAlgebraicOfResEta
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open scoped TensorProduct

section Reformulated
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta
open IsDedekindDomain NumberField Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinValAlg

theorem isAlgebraic_unit_zpow {z : ℂ} (hz : IsAlgebraic ℚ z) (n : ℤ) :
    IsAlgebraic ℚ ((z / ((‖z‖ : ℝ) : ℂ)) ^ n) := by
  have hc : IsAlgebraic ℚ (starRingEnd ℂ z) := hz.algHom (starRingEnd ℂ).toRatAlgHom
  have hn : IsAlgebraic ℚ (((‖z‖ : ℝ) : ℂ)) := by
    refine IsAlgebraic.of_pow (n := 2) two_pos ?_
    rw [← Complex.conj_mul']
    exact (mem_algebraicClosure_iff.1 (mul_mem (mem_algebraicClosure_iff.2 hc) (mem_algebraicClosure_iff.2 hz)))
  rw [← mem_algebraicClosure_iff] at hz hn ⊢
  exact zpow_mem (div_mem hz hn) n

variable {D : D7}

theorem finPart_incA (e : D.host.E) : finPart D (incA D e) = (1 : Af D.host.F) ⊗ₜ[D.host.F] e := by
  change Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id _ _) ((1 : AF D.host.F) ⊗ₜ[D.host.F] e) = _
  rw [Algebra.TensorProduct.map_tmul, map_one]
  rfl

theorem int_of_val_eq_one (ι : Af D.host.F ⊗[D.host.F] D.host.E ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E)
    (hι2 : ∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1) (z : (AE D)ˣ)
    (hv : ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι (finPart D (z : AE D)) P) = 1) :
    finPart D (z : AE D) ∈ intAE D ∧ finPart D ((z⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D := by
  refine ⟨(hι2 _).2 fun P => (hv P).le, (hι2 _).2 fun P => le_of_eq ?_⟩
  have e : ι (finPart D ((z⁻¹ : (AE D)ˣ) : AE D)) * ι (finPart D (z : AE D)) = 1 := by
    rw [← map_mul, ← map_mul, Units.inv_mul, map_one, map_one]
  have e2 : ι (finPart D ((z⁻¹ : (AE D)ˣ) : AE D)) P * ι (finPart D (z : AE D)) P = 1 := by
    have := congrArg (fun w : FiniteAdeleRing (𝓞 D.host.E) D.host.E => w P) e
    exact this
  have := congrArg Valued.v e2
  rwa [map_mul, hv, mul_one, map_one] at this

theorem ι_finPart_pow_mul (ι : Af D.host.F ⊗[D.host.F] D.host.E ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E)
    (hι1 : ∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x)
    (x : (AE D)ˣ) (h : ℕ) (k : D.host.Eˣ) :
    ι (finPart D ((x ^ h * Units.map (incA D).toMonoidHom k : (AE D)ˣ) : AE D)) =
      ι (finPart D (x : AE D)) ^ h * algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) (k : D.host.E) := by
  have e : ((x ^ h * Units.map (incA D).toMonoidHom k : (AE D)ˣ) : AE D) = (x : AE D) ^ h * incA D (k : D.host.E) := by
    rw [Units.val_mul, Units.val_pow_eq_pow_val]
    rfl
  rw [e, map_mul, map_pow, map_mul, map_pow, finPart_incA, hι1]

theorem exists_pow_mul_int (x : (AE D)ˣ) : ∃ h : ℕ, 0 < h ∧ ∃ k : D.host.Eˣ,
    finPart D (((x ^ h * Units.map (incA D).toMonoidHom k : (AE D)ˣ)) : AE D) ∈ intAE D ∧
    finPart D ((((x ^ h * Units.map (incA D).toMonoidHom k)⁻¹ : (AE D)ˣ)) : AE D) ∈ intAE D := by
  obtain ⟨ι, hι1, hι2, -⟩ := GlobalTheory.HostAdeleIso.exists_finiteAdele_equiv D
  obtain ⟨h, hh, hX⟩ := Formalism.L2.Host.CharEx.classExp D.host.E
  obtain ⟨a, a', haa, haa', ha⟩ : ∃ a a' : Af D.host.F ⊗[D.host.F] D.host.E, a * a' = 1 ∧ a' * a = 1 ∧
      a = finPart D (x : AE D) :=
    ⟨_, _, by rw [← map_mul, Units.mul_inv, map_one], by rw [← map_mul, Units.inv_mul, map_one], rfl⟩
  let X : (AdeleRing (𝓞 D.host.E) D.host.E)ˣ :=
    ⟨((1 : InfiniteAdeleRing D.host.E), ι a), ((1 : InfiniteAdeleRing D.host.E), ι a'),
      Prod.ext (show (1 : InfiniteAdeleRing D.host.E) * 1 = 1 from mul_one _)
        (show ι a * ι a' = 1 by rw [← map_mul, haa, map_one]),
      Prod.ext (show (1 : InfiniteAdeleRing D.host.E) * 1 = 1 from mul_one _)
        (show ι a' * ι a = 1 by rw [← map_mul, haa', map_one])⟩
  obtain ⟨k, hk⟩ := hX X
  refine ⟨h, hh, k, int_of_val_eq_one ι hι2 _ fun P => ?_⟩
  rw [ι_finPart_pow_mul ι hι1, ← ha]
  have e : ((X ^ h * Neutral.B1.diagUnits D.host.E k : (AdeleRing (𝓞 D.host.E) D.host.E)ˣ) :
      AdeleRing (𝓞 D.host.E) D.host.E).2 = ι a ^ h * algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) (k : D.host.E) := by
    rw [Units.val_mul, Units.val_pow_eq_pow_val]
    rfl
  rw [← e]
  exact hk P

end GlobalTheory.FinValAlg

namespace GlobalTheory.FinValAlg

variable {D : D7}

theorem infPart_incA (e : D.host.E) : infPart D (incA D e) = (1 : Ainf D.host.F) ⊗ₜ[D.host.F] e := by
  change Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id _ _) ((1 : AF D.host.F) ⊗ₜ[D.host.F] e) = _
  rw [Algebra.TensorProduct.map_tmul, map_one]
  rfl

theorem infPart_pairE (a : Ainf D.host.F ⊗[D.host.F] D.host.E) (b : Af D.host.F ⊗[D.host.F] D.host.E) :
    infPart D (Formalism.L2.Fam.ThC.pairE a b) = a := Formalism.L2.Fam.ThC.fst_pairE a b

theorem finPart_pairE (a : Ainf D.host.F ⊗[D.host.F] D.host.E) (b : Af D.host.F ⊗[D.host.F] D.host.E) :
    finPart D (Formalism.L2.Fam.ThC.pairE a b) = b := Formalism.L2.Fam.ThC.snd_pairE a b

theorem pairE_mul_eq_one (z : (AE D)ˣ) :
    Formalism.L2.Fam.ThC.pairE (infPart D (z : AE D)) 1 * Formalism.L2.Fam.ThC.pairE (infPart D ((z⁻¹ : (AE D)ˣ) : AE D)) 1 = 1 := by
  refine Formalism.L2.Fam.ThC.ae_ext ?_ ?_
  · rw [map_mul, infPart_pairE, infPart_pairE, ← map_mul, Units.mul_inv]
  · rw [map_mul, finPart_pairE, finPart_pairE, mul_one, map_one]

theorem pairE_mul_eq_one' (z : (AE D)ˣ) :
    Formalism.L2.Fam.ThC.pairE (infPart D ((z⁻¹ : (AE D)ˣ) : AE D)) 1 * Formalism.L2.Fam.ThC.pairE (infPart D (z : AE D)) 1 = 1 := by
  refine Formalism.L2.Fam.ThC.ae_ext ?_ ?_
  · rw [map_mul, infPart_pairE, infPart_pairE, ← map_mul, Units.inv_mul]
  · rw [map_mul, finPart_pairE, finPart_pairE, mul_one, map_one]


set_option maxHeartbeats 1000000 in
theorem exists_decomp (x : (AE D)ˣ) (hx : infPart D (x : AE D) = 1) :
    ∃ h : ℕ, 0 < h ∧ ∃ (k : D.host.Eˣ) (y u : (AE D)ˣ), finPart D (y : AE D) = 1 ∧ Formalism.L2.Pj.FinUnit u ∧
      infPart D (y : AE D) = infPart D (incA D (k : D.host.E)) ∧ x ^ h * Units.map (incA D).toMonoidHom k = y * u := by
  obtain ⟨h, hh, k, h1, h2⟩ := exists_pow_mul_int x
  refine ⟨h, hh, k, ?_⟩
  generalize hz : x ^ h * Units.map (incA D).toMonoidHom k = z at h1 h2
  have hiz : infPart D (z : AE D) = infPart D (incA D (k : D.host.E)) := by
    rw [← hz, Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, hx, one_pow, one_mul]
    rfl
  have m1 := pairE_mul_eq_one z
  have m2 := pairE_mul_eq_one' z
  obtain ⟨y, hyv, hyi⟩ : ∃ y : (AE D)ˣ, (y : AE D) = Formalism.L2.Fam.ThC.pairE (infPart D (z : AE D)) 1 ∧
      ((y⁻¹ : (AE D)ˣ) : AE D) = Formalism.L2.Fam.ThC.pairE (infPart D ((z⁻¹ : (AE D)ˣ) : AE D)) 1 :=
    ⟨⟨_, _, m1, m2⟩, rfl, rfl⟩
  refine ⟨y, y⁻¹ * z, by rw [hyv, finPart_pairE], ⟨?_, ?_, ?_⟩, by rw [hyv, infPart_pairE, hiz], by rw [mul_inv_cancel_left]⟩
  · rw [Units.val_mul, map_mul, hyi, infPart_pairE, ← map_mul, Units.inv_mul, map_one]
  · rw [Units.val_mul, map_mul, hyi, finPart_pairE, one_mul]; exact h1
  · rw [mul_inv_rev, inv_inv, Units.val_mul, map_mul, hyv, finPart_pairE, mul_one]; exact h2

theorem char_eq_prod {θ : InfFam D} (hθ : IsInfFam θ) {χ : (AE D)ˣ →* Circle} (nτ : D.what₂.Tau → ℤ)
    (hn : ∀ τ (x : (AE D)ˣ), finPart D (x : AE D) = 1 → (∀ τ', τ' ≠ τ → θ τ' (infPart D (x : AE D)) = 1) →
      ((χ x : Circle) : ℂ) = (θ τ (infPart D (x : AE D)) / (‖θ τ (infPart D (x : AE D))‖ : ℂ)) ^ nτ τ)
    (y : (AE D)ˣ) (hy : finPart D (y : AE D) = 1) :
    ((χ y : Circle) : ℂ) = ∏ τ, (θ τ (infPart D (y : AE D)) / (‖θ τ (infPart D (y : AE D))‖ : ℂ)) ^ nτ τ := by
  classical
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨e, -, e1, e2⟩ := GlobalTheory.SplitCharExp.exists_real_hom hσ
  let wU : D.what₂.Tau → ℂˣ := fun τ => (y.isUnit.map ((θ τ).comp (infPart D))).unit
  have hwU : ∀ τ, ((wU τ : ℂˣ) : ℂ) = θ τ (infPart D (y : AE D)) := fun τ => rfl
  let f : (D.what₂.Tau → ℂ)ˣ →* (AE D)ˣ := Units.map e
  have hf1 : ∀ W, finPart D ((f W : (AE D)ˣ) : AE D) = 1 := fun W => e1 _
  have hf2 : ∀ W τ, θ τ (infPart D ((f W : (AE D)ˣ) : AE D)) = (W : D.what₂.Tau → ℂ) τ := fun W τ => e2 _ τ
  have hy' : y = ∏ τ, f (MulEquiv.piUnits.symm (Pi.mulSingle τ (wU τ))) := by
    rw [← map_prod, ← map_prod, Finset.univ_prod_mulSingle]
    apply Units.ext
    refine GlobalTheory.SplitCharExp.ext_of_chart hσ (by rw [hy, hf1]) fun τ => ?_
    rw [hf2]
    exact (hwU τ).symm
  have hc : ((χ y : Circle) : ℂ) = ∏ τ, ((χ (f (MulEquiv.piUnits.symm (Pi.mulSingle τ (wU τ)))) : Circle) : ℂ) := by
    show Circle.coeHom (χ y) = ∏ τ, Circle.coeHom (χ (f (MulEquiv.piUnits.symm (Pi.mulSingle τ (wU τ)))))
    rw [← map_prod, ← map_prod, ← hy']
  rw [hc]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have hs : ∀ τ', θ τ' (infPart D ((f (MulEquiv.piUnits.symm (Pi.mulSingle τ (wU τ))) : (AE D)ˣ) : AE D)) =
      (((Pi.mulSingle τ (wU τ) : D.what₂.Tau → ℂˣ) τ' : ℂˣ) : ℂ) := fun τ' => by rw [hf2]; rfl
  rw [hn τ _ (hf1 _) fun τ' h => by rw [hs, Pi.mulSingle_eq_of_ne h, Units.val_one], hs, Pi.mulSingle_eq_same, hwU]

theorem isAlgebraic_of_infPart_eq_one : ∀ {D : D7} {θ : InfFam D} {χ : (Formalism.L2.Theta.AE D)ˣ →* Circle} {n : ℕ},
    IsInfFam θ → IsHeckeChar D χ → ResEta D χ n →
    ∀ x : (Formalism.L2.Theta.AE D)ˣ, infPart D (x : Formalism.L2.Theta.AE D) = 1 → IsAlgebraic ℚ ((χ x : Circle) : ℂ) := by
  intro D θ χ n hθ hχ hr x hx
  choose a ha using fun τ => GlobalTheory.SplitCharExp.exists_hasInfExp D θ χ n τ hθ hχ hr
  choose nτ hn2 hn using ha
  have hn' : ∀ τ (x : (AE D)ˣ), finPart D (x : AE D) = 1 → (∀ τ', τ' ≠ τ → θ τ' (infPart D (x : AE D)) = 1) →
      ((χ x : Circle) : ℂ) = (θ τ (infPart D (x : AE D)) / (‖θ τ (infPart D (x : AE D))‖ : ℂ)) ^ nτ τ :=
    fun τ => (hn τ).2 θ hθ
  obtain ⟨h, hh, k, y, u, hy1, hu, hyi, e⟩ := exists_decomp x hx
  obtain ⟨-, -, -, m, hm, hum⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D χ hχ.1
  have hyalg : IsAlgebraic ℚ ((χ y : Circle) : ℂ) := by
    rw [char_eq_prod hθ nτ hn' y hy1, ← mem_algebraicClosure_iff]
    refine prod_mem fun τ _ => ?_
    rw [mem_algebraicClosure_iff, hyi, infPart_incA, (hθ τ).1]
    exact isAlgebraic_unit_zpow (GlobalTheory.isAlgebraic_embedding_apply _ _) _
  have e2 : χ x ^ (h * m) = χ y ^ m := by
    have := congrArg (fun g => χ g ^ m) e
    simp only [map_mul, mul_pow, hum u hu, mul_one, hχ.2 k, one_pow, map_pow] at this
    rw [pow_mul]
    exact this
  refine IsAlgebraic.of_pow (Nat.mul_pos hh hm) ?_
  rw [← Circle.coe_pow, e2, Circle.coe_pow, ← mem_algebraicClosure_iff]
  exact pow_mem (mem_algebraicClosure_iff.2 hyalg) _

end GlobalTheory.FinValAlg

end

end Reformulated

theorem GlobalTheory.FinValAlg.finite_values_isAlgebraic : ∀ {D : D7} {θ : InfFam D} {χ : (Formalism.L2.Theta.AE D)ˣ →* Circle} {n : ℕ}, IsInfFam θ → IsHeckeChar D χ → ResEta D χ n →
    ∀ x : (Formalism.L2.Theta.AE D)ˣ, infPart D (x : Formalism.L2.Theta.AE D) = 1 → IsAlgebraic ℚ ((χ x : Circle) : ℂ) :=
  GlobalTheory.FinValAlg.isAlgebraic_of_infPart_eq_one
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharFiniteIdelesIsAlgebraicOfResEtaStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChar_finiteIdeles_isAlgebraic_of_resEta : ∀ {D : D7} {θ : InfFam D} {χ : (Formalism.L2.Theta.AE D)ˣ →* Circle} {n : ℕ}, IsInfFam θ → IsHeckeChar D χ → ResEta D χ n →
    ∀ x : (Formalism.L2.Theta.AE D)ˣ, infPart D (x : Formalism.L2.Theta.AE D) = 1 → IsAlgebraic ℚ ((χ x : Circle) : ℂ) := by
  first | exact @GlobalTheory.FinValAlg.finite_values_isAlgebraic | exact GlobalTheory.FinValAlg.finite_values_isAlgebraic | (intros; apply GlobalTheory.FinValAlg.finite_values_isAlgebraic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdaptedFrameOrthonormal
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.RowReal
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowReal

theorem adaptedFrame_orthonormal {N r c N' : ℕ} (Γ : Matrix (Fin N) (Fin N) ℂ) (Γ' O : Matrix (Fin r) (Fin r) ℂ)
    (F : Matrix (Fin N) (Fin r) ℂ) (Zc : Matrix (Fin N) (Fin 1) ℂ) (hr : r = c) (hc : c + 1 = N') (hN : N = N')
    (hΓ : Γᴴ = Γ) (h1 : Fᴴ * Γ * F = Γ') (hO : Oᴴ * Γ' * O = 1) (h2 : Fᴴ * Γ * Zc = 0) (h3 : Zcᴴ * Γ * Zc = 1) :
    (Matrix.of (fun a k => Sum.elim (fun b : Fin c => (F * O) a (Fin.cast hr.symm b)) (fun _ : Fin 1 => Zc a 0)
      ((finSumFinEquiv.trans (finCongr hc)).symm (Fin.cast hN k))))ᴴ * Γ *
    Matrix.of (fun a k => Sum.elim (fun b : Fin c => (F * O) a (Fin.cast hr.symm b)) (fun _ : Fin 1 => Zc a 0)
      ((finSumFinEquiv.trans (finCongr hc)).symm (Fin.cast hN k))) = 1 := by
  subst hr hc hN
  set e := finSumFinEquiv (m := r) (n := 1)
  have hT : Matrix.of (fun a k => Sum.elim (fun b : Fin r => (F * O) a (Fin.cast rfl b)) (fun _ : Fin 1 => Zc a 0)
      ((e.trans (finCongr rfl)).symm (Fin.cast rfl k))) = (Matrix.fromCols (F * O) Zc).submatrix id e.symm := by
    ext a k
    simp only [Matrix.of_apply, Fin.cast_eq_self, Matrix.submatrix_apply, id]
    rcases h : e.symm k with b | b
    · simp [h, Matrix.fromCols]
    · simp [h, Matrix.fromCols, Subsingleton.elim b 0]
  have h4 : Zcᴴ * Γ * F = 0 := by
    have := congrArg Matrix.conjTranspose h2
    simpa [Matrix.conjTranspose_mul, hΓ, Matrix.mul_assoc] using this
  have a1 : ((Matrix.fromCols (F * O) Zc).submatrix id e.symm)ᴴ * Γ * (Matrix.fromCols (F * O) Zc).submatrix id e.symm =
      ((Matrix.fromCols (F * O) Zc)ᴴ * Γ * Matrix.fromCols (F * O) Zc).submatrix e.symm e.symm := rfl
  have b1 : (F * O)ᴴ * Γ * (F * O) = 1 := by
    rw [← hO, ← h1]; simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have b2 : (F * O)ᴴ * Γ * Zc = 0 := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Fᴴ, h2, Matrix.mul_zero]
  have b3 : Zcᴴ * Γ * (F * O) = 0 := by rw [← Matrix.mul_assoc, h4, Matrix.zero_mul]
  rw [hT, a1, Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.fromRows_mul, Matrix.fromRows_mul_fromCols,
    b1, b2, b3, h3, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem topFrame_orthonormal {μ0 : T} (hL : L.Is μ0) (W : G.Weil) (τ : D.what₂.Tau) :
    (topFrame W τ)ᴴ * gramAt D (G.V (.top D.R.m)) τ * topFrame W τ = 1 := by
  have hPt : PosOnb W (.top D.R.m) := posOnb_of_defNode W μ0 hL (X := .top D.R.m) le_rfl
  have hPg : PosOnb W (.grid D.R.m D.R.m) := posOnb_of_defNode W μ0 hL (X := .grid D.R.m D.R.m) ⟨le_rfl, rfl⟩
  have hm : ∀ {a b : ℕ} (X : Matrix (Fin (G.V (.top D.R.m)).rank) (Fin a) D.host.E)
      (Z : Matrix (Fin (G.V (.top D.R.m)).rank) (Fin b) D.host.E),
      (X.map (tauE D τ))ᴴ * gramAt D (G.V (.top D.R.m)) τ * Z.map (tauE D τ) =
        (Xᴴ * (G.V (.top D.R.m)).gram * Z).map (tauE D τ) := fun X Z => by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.conjTranspose_map _ (GlobalTheory.FockCompare.tauE_star τ)]; rfl
  have hΓ : (gramAt D (G.V (.top D.R.m)) τ)ᴴ = gramAt D (G.V (.top D.R.m)) τ := by
    have hB := hPt τ
    generalize W.onb (.top D.R.m) τ = B at hB
    generalize gramAt D (G.V (.top D.R.m)) τ = Γ at hB
    have hd : IsUnit B.det := Matrix.isUnit_det_of_left_inverse hB
    have h1 : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
    have hG : Γ = (B⁻¹)ᴴ * B⁻¹ := by
      calc Γ = (B * B⁻¹)ᴴ * Γ * (B * B⁻¹) := by rw [h1, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
        _ = (B⁻¹)ᴴ * (Bᴴ * Γ * B) * B⁻¹ := by rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
        _ = _ := by rw [hB, Matrix.mul_one]
    rw [hG, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  refine adaptedFrame_orthonormal (c := (rowSizes D).nC D.R.m) _ (gramAt D (G.V (.grid D.R.m D.R.m)) τ) _ _ _
    (rank_gridM G (i := D.R.m) le_rfl) (rowSizes D).nC_succ (rank_top G (j := D.R.m) le_rfl) hΓ ?_ (hPg τ) ?_ ?_
  · exact (hm _ _).trans (congrArg (fun M => Matrix.map M (tauE D τ))
      (GlobalTheory.AutFunCounterexample.gram_pull (G.V (.top D.R.m)) (G.V (.grid D.R.m D.R.m)) G.sp.topDec.ι G.sp.topDec.isom))
  · refine (hm _ _).trans ((congrArg (fun M => Matrix.map M (tauE D τ)) G.sp.topDec.perp).trans ?_)
    ext i j; simp
  · refine (hm _ _).trans ((congrArg (fun M => Matrix.map M (tauE D τ)) G.sp.topDec.gram).trans ?_)
    ext i j
    obtain rfl := Subsingleton.elim i j
    simp [antiDiagonalSignGramMatrix]

theorem kappaTop_mul_topFrame {μ0 : T} (hL : L.Is μ0) (W : G.Weil) (g : Gc D.what₂.Tau (rowSizes D)) (τ : D.what₂.Tau) :
    compAt W.θ τ (mt _ (kappaTop W g)) * topFrame W τ = topFrame W τ *
      (embed (rowSizes D).nC_succ (g.2 (Fin.last D.R.m)) τ).1.submatrix
        (Fin.cast (rank_top G (j := D.R.m) le_rfl)) (Fin.cast (rank_top G (j := D.R.m) le_rfl)) := by
  have hPg : PosOnb W (.grid (Fin.last D.R.m : Fin (D.R.m + 1)) D.R.m) :=
    posOnb_of_defNode W μ0 hL (X := .grid (Fin.last D.R.m : Fin (D.R.m + 1)) D.R.m) ⟨Nat.lt_succ_iff.1 (Fin.last D.R.m).2, rfl⟩
  have hdO : IsUnit (W.onb (.grid D.R.m D.R.m) τ).det := Matrix.isUnit_det_of_left_inverse (hPg τ)
  have h1 : compAt W.θ τ (mt (G.V (.top D.R.m)) (kappaTop W g)) *
      (frameMat (G.V (.top D.R.m)) (G.V (.grid D.R.m D.R.m)) G.sp.topDec.ι).map (tauE D τ) =
      (frameMat (G.V (.top D.R.m)) (G.V (.grid D.R.m D.R.m)) G.sp.topDec.ι).map (tauE D τ) *
        compAt W.θ τ (mt (G.V (.grid D.R.m D.R.m)) ((kappa W g).2 (Fin.last D.R.m))) := (archM_kappaTop W g τ).1
  have h3 : compAt W.θ τ (mt (G.V (.top D.R.m)) (kappaTop W g)) * G.sp.topDec.a.map (tauE D τ) =
      G.sp.topDec.a.map (tauE D τ) := (archM_kappaTop W g τ).2
  have h2 : compAt W.θ τ (mt (G.V (.grid D.R.m D.R.m)) ((kappa W g).2 (Fin.last D.R.m))) =
      W.onb (.grid D.R.m D.R.m) τ * (g.2 (Fin.last D.R.m) τ).1.submatrix (Fin.cast (rank_gridM G (i := D.R.m) le_rfl))
        (Fin.cast (rank_gridM G (i := D.R.m) le_rfl)) * (W.onb (.grid D.R.m D.R.m) τ)⁻¹ :=
    compAt_kappa_snd g (Fin.last D.R.m) hPg τ
  exact mul_adaptedFrame_of_blocks (c := (rowSizes D).nC D.R.m) _ _ _ _ _
    ((g.2 (Fin.last D.R.m) τ).1 : Matrix (Fin ((rowSizes D).nC D.R.m)) (Fin ((rowSizes D).nC D.R.m)) ℂ)
    (rank_gridM G (i := D.R.m) le_rfl) (rowSizes D).nC_succ (rank_top G (j := D.R.m) le_rfl) hdO h1 h2 h3

theorem exists_unitary_change {a b : ℕ} (h : a = b) {Γ B F : Matrix (Fin a) (Fin a) ℂ} (hB : Bᴴ * Γ * B = 1)
    (hF : Fᴴ * Γ * F = 1) : ∃ c : Matrix.unitaryGroup (Fin b) ℂ, ∀ (A : Matrix (Fin a) (Fin a) ℂ) (v : Matrix.unitaryGroup (Fin b) ℂ),
      A * F = F * v.1.submatrix (Fin.cast h) (Fin.cast h) →
      A = B * (c * v * c⁻¹).1.submatrix (Fin.cast h) (Fin.cast h) * B⁻¹ := by
  subst h
  have hd : IsUnit B.det := Matrix.isUnit_det_of_left_inverse hB
  have hdF : IsUnit F.det := Matrix.isUnit_det_of_left_inverse hF
  have h1 : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  have hu : (B⁻¹ * F)ᴴ * (B⁻¹ * F) = 1 := by
    calc (B⁻¹ * F)ᴴ * (B⁻¹ * F) = (B⁻¹ * F)ᴴ * (Bᴴ * Γ * B) * (B⁻¹ * F) := by rw [hB, Matrix.mul_one]
      _ = Fᴴ * ((B * B⁻¹)ᴴ * Γ * (B * B⁻¹)) * F := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [h1, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one, hF]
  have hu' : (B⁻¹ * F) * (B⁻¹ * F)ᴴ = 1 := mul_eq_one_comm.1 hu
  refine ⟨⟨B⁻¹ * F, Matrix.mem_unitaryGroup_iff'.2 hu⟩, fun A v hA => ?_⟩
  have hA' : A * F = F * v.1 := hA
  show A = B * (B⁻¹ * F * v.1 * (B⁻¹ * F)ᴴ) * B⁻¹
  calc A = A * (B * ((B⁻¹ * F) * (B⁻¹ * F)ᴴ) * B⁻¹) := by rw [hu', Matrix.mul_one, h1, Matrix.mul_one]
    _ = A * (B * B⁻¹) * F * (B⁻¹ * F)ᴴ * B⁻¹ := by simp only [Matrix.mul_assoc]
    _ = (B * B⁻¹) * (F * v.1) * (B⁻¹ * F)ᴴ * B⁻¹ := by rw [h1, Matrix.mul_one, Matrix.one_mul, hA']
    _ = _ := by simp only [Matrix.mul_assoc]

theorem exists_ptTop_conj {μ0 : T} (hL : L.Is μ0) (W : G.Weil) (n : Fin (D.R.m + 1)) :
    ∃ c : UG D.what₂.Tau ((rowSizes D).nR n), ∀ (g : Gc D.what₂.Tau (rowSizes D)) τ,
      compAt W.θ τ (mt _ (ptTop W g n)) = W.onb (.top n) τ *
        ((c * rowComp (rowSizes D) g n * c⁻¹) τ).1.submatrix (Fin.cast (rank_top G (Nat.lt_succ_iff.1 n.2)))
          (Fin.cast (rank_top G (Nat.lt_succ_iff.1 n.2))) * (W.onb (.top n) τ)⁻¹ := by
  have hP : PosOnb W (.top n) := posOnb_of_defNode W μ0 hL (X := .top n) (Nat.lt_succ_iff.1 n.2)
  by_cases h : (n : ℕ) = D.R.m
  · obtain rfl : n = Fin.last D.R.m := Fin.ext h
    choose c hc using fun τ => exists_unitary_change (rank_top G (j := D.R.m) le_rfl) (hP τ) (topFrame_orthonormal hL W τ)
    refine ⟨c, fun g τ => ?_⟩
    have hlast : rowComp (rowSizes D) g (Fin.last D.R.m) = embed (rowSizes D).nC_succ (g.2 (Fin.last D.R.m)) := by
      simp only [rowComp, MonoidHom.coe_mk, OneHom.coe_mk]
      exact Fin.snoc_last (α := fun j : Fin ((rowSizes D).m + 1) => UG D.what₂.Tau ((rowSizes D).nR j)) _ _
    rw [show ptTop W g ((Fin.last D.R.m : Fin (D.R.m + 1)) : ℕ) = kappaTop W g from ptTop_m W g]
    erw [hlast]
    exact hc τ _ _ (kappaTop_mul_topFrame hL W g τ)
  · refine ⟨1, fun g τ => ?_⟩
    rw [one_mul, inv_one, mul_one]
    exact eq_conj_of_inFrame (Matrix.isUnit_det_of_left_inverse (hP τ)) (GlobalTheory.T.compactChainTopRowRealPoint_inOrthonormalBasis hL W g n (fun e => absurd e h) τ)

def trColEquiv (G : GridData L sc) (j : Fin D.R.m) :
    PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank ≃ₗ[ℂ] Pol D.what₂.Tau ((rowSizes D).nR j) ((rowSizes D).nR (j + 1)) :=
  LinearEquiv.ofBijective (trCol G j).toLinearMap ⟨trCol_injective G j, MvPolynomial.rename_surjective _ fun y =>
    ⟨(y.1, Fin.cast (rank_top G (j := (j : ℕ) + 1) j.2).symm y.2.1, Fin.cast (rank_top G j.2.le).symm y.2.2), rfl⟩⟩

def trRowEquiv (G : GridData L sc) (i : Fin D.R.m) :
    PolF D (G.V (.grid i D.R.m)).rank (G.V (.grid (i + 1) D.R.m)).rank ≃ₗ[ℂ]
      Pol D.what₂.Tau ((rowSizes D).nC i) ((rowSizes D).nC (i + 1)) :=
  LinearEquiv.ofBijective (trRow G i).toLinearMap ⟨trRow_injective G i, MvPolynomial.rename_surjective _ fun y =>
    ⟨(y.1, Fin.cast (rank_gridM G i.2.le).symm y.2.2, Fin.cast (rank_gridM G (i := (i : ℕ) + 1) i.2).symm y.2.1), rfl⟩⟩

def subEquiv {ι : Type} [Fintype ι] {a b : ℕ} (x : UG ι a × UG ι b) : Pol ι a b ≃ₗ[ℂ] Pol ι a b :=
  LinearEquiv.ofLinear (linSub (homMat a b x)) (linSub (homMat a b x⁻¹))
    (by rw [← Module.End.mul_eq_comp, ← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one]; rfl)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one]; rfl)

theorem linSub_homMat_mul {ι : Type} [Fintype ι] {a b : ℕ} (x y : UG ι a × UG ι b) (p : Pol ι a b) :
    linSub (homMat a b x) (linSub (homMat a b y) p) = linSub (homMat a b (x * y)) p := by
  rw [map_mul, map_mul]; rfl

theorem om_fock_top_of_mat {μ0 : T} (hL : L.Is μ0) (W : G.Weil) {U : Set T} (S : GridChoice W U)
    (g : Gc D.what₂.Tau (rowSizes D)) (t : T) (j : Fin D.R.m)
    (u : UG D.what₂.Tau ((rowSizes D).nR j)) (v : UG D.what₂.Tau ((rowSizes D).nR (j + 1)))
    (c1 : ∀ τ, compAt W.θ τ (mt _ (ptTop W g j)) = W.onb (.top (j : ℕ)) τ *
      (u τ).1.submatrix (Fin.cast (rank_top G (j := j) j.2.le)) (Fin.cast (rank_top G (j := j) j.2.le)) *
      (W.onb (.top (j : ℕ)) τ)⁻¹)
    (c2 : ∀ τ, compAt W.θ τ (mt _ (ptTop W g ((j : ℕ) + 1))) = W.onb (.top ((j : ℕ) + 1)) τ *
      (v τ).1.submatrix (Fin.cast (rank_top G (j := (j : ℕ) + 1) j.2)) (Fin.cast (rank_top G (j := (j : ℕ) + 1) j.2)) *
      (W.onb (.top ((j : ℕ) + 1)) τ)⁻¹)
    (d : FinDatum G t (.top t j)) (hd : S.Z.HasVec d) (Q Q' : PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank)
    (hQ : trCol G j Q' = rowScal (rowEntries D sc.cGap) j g • linSub (homMat _ _ (u, v)) (trCol G j Q)) :
    W.om (.top t j) (G.toPair (.top t j) (ptTop W g j) (ptTop W g (j + 1))) (W.fock (.top t j) (movedVec t S d) Q) =
      W.fock (.top t j) (movedVec t S d) Q' := by
  have hX : DefNode D.R.m (.top (j : ℕ)) := j.2.le
  have hY : DefNode D.R.m (.top ((j : ℕ) + 1)) := j.2
  have hp : DefPair D.R.m (Pair.top t (j : ℕ)) := j.2
  obtain ⟨hf, hv⟩ := GlobalTheory.T.movedVector_definitePair_theta_fockVacuum W S t (.top t j) hp d hd
  have hc := GlobalTheory.T.compactChain_topPair_movedVector_rowCharacter hL W S g t j d hd
  have key := GlobalTheory.T.weil_compactRealPoint_fockVector_substitution W (.top t j) j.2 (fun _ => (G.V (.top (j : ℕ))).rank) (fun _ => (G.V (.top ((j : ℕ) + 1))).rank)
    (fun _ => le_rfl) (fun _ => le_rfl) (fun ρ => (GlobalTheory.T.definiteNode_cartan_orthonormalBasis_allPlaces hL W _ hX ρ).1) (fun ρ => (GlobalTheory.T.definiteNode_cartan_orthonormalBasis_allPlaces hL W _ hY ρ).1)
    (fun ρ => (GlobalTheory.T.definiteNode_cartan_orthonormalBasis_allPlaces hL W _ hX ρ).2.1) (fun ρ => (GlobalTheory.T.definiteNode_cartan_orthonormalBasis_allPlaces hL W _ hY ρ).2.1) _ hf hv
    (fun τ => (u τ).1.submatrix (Fin.cast (rank_top G (j := j) j.2.le)) (Fin.cast (rank_top G (j := j) j.2.le)))
    (fun τ => (v τ).1.submatrix (Fin.cast (rank_top G (j := (j : ℕ) + 1) j.2)) (Fin.cast (rank_top G (j := (j : ℕ) + 1) j.2)))
    (fun ρ => isKMat_cast _ _ (Or.inl rfl)) (fun ρ => isKMat_cast _ _ (Or.inl rfl))
    (ptTop W g j) (ptTop W g (j + 1)) (ptTop_mem W g _) (ptTop_mem W g _) c1 c2 _ hc Q
  have hQ' : Q' = rowScal (rowEntries D sc.cGap) j g • fockSubAll (fun _ => (G.V (.top (j : ℕ))).rank)
      (fun _ => (G.V (.top ((j : ℕ) + 1))).rank)
      (fun τ => (u τ).1.submatrix (Fin.cast (rank_top G (j := j) j.2.le)) (Fin.cast (rank_top G (j := j) j.2.le)))
      (fun τ => (v τ).1.submatrix (Fin.cast (rank_top G (j := (j : ℕ) + 1) j.2)) (Fin.cast (rank_top G (j := (j : ℕ) + 1) j.2)))
      Q := by
    apply trCol_injective G j
    rw [hQ, map_smul, GlobalTheory.T.fockSubstitution_rowStep_rename_unitary G j u v Q]
  show W.om (.top t j) (ptTop W g j, ptTop W g (j + 1)) _ = _
  rw [key, hQ', LinearMap.map_smul]

theorem exists_fock_transport : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ0 : T} (hL : L.Is μ0)
    (W : G.Weil), ∃ (tc : ∀ j : Fin D.R.m, PolF D (G.V (.top ((j : ℕ) + 1))).rank (G.V (.top j)).rank ≃ₗ[ℂ]
        Pol D.what₂.Tau ((rowSizes D).nR (j.castSucc : Fin ((rowSizes D).m + 1))) ((rowSizes D).nR (j.succ : Fin ((rowSizes D).m + 1))))
      (tr : ∀ i : Fin D.R.m, PolF D (G.V (.grid i D.R.m)).rank (G.V (.grid ((i : ℕ) + 1) D.R.m)).rank ≃ₗ[ℂ]
        Pol D.what₂.Tau ((rowSizes D).nC (i.castSucc : Fin ((rowSizes D).m + 1))) ((rowSizes D).nC (i.succ : Fin ((rowSizes D).m + 1)))),
      ∀ {U : Set T} (S : GridChoice W U) (g : Gc D.what₂.Tau (rowSizes D)) (t : T),
        (∀ (j : Fin D.R.m) (d : FinDatum G t (.top t j)), S.Z.HasVec d → ∀ Q,
          W.om (.top t j) (G.toPair (.top t j) (ptTop W g j) (ptTop W g (j + 1))) (W.fock (.top t j) (movedVec t S d) Q) =
            W.fock (.top t j) (movedVec t S d) ((tc j).symm (rowFock (rowEntries D sc.cGap) j g (tc j Q)))) ∧
        (∀ (i : Fin D.R.m) (d : FinDatum G t (.chi i D.R.m)), S.Z.HasVec d → ∀ Q,
          W.om (.chi i D.R.m) (G.toPair (.chi i D.R.m) (ptGrid W g i) (ptGrid W g (i + 1)))
              (W.fock (.chi i D.R.m) (movedVec t S d) Q) =
            W.fock (.chi i D.R.m) (movedVec t S d) ((tr i).symm (colFock (rowEntries D sc.cGap) i g (tr i Q)))) := by
  intro D T L sc G μ0 hL W
  choose c hc using exists_ptTop_conj hL W
  refine ⟨fun j => (trColEquiv G j).trans (subEquiv (c j.castSucc, c j.succ)).symm, fun i => trRowEquiv G i,
    fun S g t => ⟨fun j d hd Q => ?_, fun i d hd Q => ?_⟩⟩
  · refine om_fock_top_of_mat hL W S g t j _ _ (hc j.castSucc g) (hc j.succ g) d hd Q _ ?_
    have e : ∀ y, trCol G j ((trColEquiv G j).symm y) = y := fun y => (trColEquiv G j).apply_symm_apply y
    refine (e _).trans ?_
    show linSub (homMat _ _ (c j.castSucc, c j.succ)) (rowScal (rowEntries D sc.cGap) j g •
      linSub (homMat _ _ (rowComp (rowSizes D) g j.castSucc, rowComp (rowSizes D) g j.succ))
        (linSub (homMat _ _ (c j.castSucc, c j.succ)⁻¹) (trCol G j Q))) = _
    rw [LinearMap.map_smul, linSub_homMat_mul, linSub_homMat_mul]
    rfl
  · exact om_fock_chi hL W S g t i d hd Q _ ((trRowEquiv G i).apply_symm_apply _)

end GlobalTheory.RowReal
end
end
