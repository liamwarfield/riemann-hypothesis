module

public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ETPointStatement
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.PhiCMinK
public import Formalism.SharpRestriction.Divisibility.WeightAlgebra
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.ReducedBasis

@[expose] public section

section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.PhiCMinima
section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.PhiCMinD
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin

open Matrix

theorem finiteShort_holds : FiniteShortStatement := by
  intro d G hG B
  obtain ⟨R, hRu, hGR⟩ := whiten_holds d G hG
  set A : ℝ := ∑ i, ∑ j, |R⁻¹ i j| with hA
  set M : ℤ := ⌈A * (1 + B)⌉ with hM
  refine (Set.Finite.pi (t := fun _ : Fin d => Set.Icc (-M) M) fun _ => Set.finite_Icc _ _).subset ?_
  intro c hc
  simp only [Set.mem_setOf_eq] at hc
  simp only [Set.mem_pi, Set.mem_univ, true_implies]
  intro i
  set cv : Fin d → ℝ := fun i => (c i : ℝ) with hcv
  set y : Fin d → ℝ := R *ᵥ cv with hy
  have hyy : ∑ j, y j * y j ≤ B := by
    have e : cv ⬝ᵥ (G *ᵥ cv) = y ⬝ᵥ y := by
      rw [hGR, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
    rw [e] at hc
    simpa [dotProduct] using hc
  have hyj : ∀ j, |y j| ≤ 1 + B := by
    intro j
    have h1 : y j * y j ≤ ∑ k, y k * y k :=
      Finset.single_le_sum (f := fun k => y k * y k) (fun k _ => mul_self_nonneg (y k)) (Finset.mem_univ j)
    have h2 : |y j| ≤ 1 + y j * y j := by
      nlinarith [abs_nonneg (y j), sq_abs (y j), abs_mul_abs_self (y j)]
    linarith
  have hB : 0 ≤ 1 + B := (abs_nonneg _).trans (hyj i)
  have hcvR : cv = R⁻¹ *ᵥ y := by
    rw [hy, mulVec_mulVec, nonsing_inv_mul R hRu, one_mulVec]
  have hci : |cv i| ≤ A * (1 + B) := by
    have e : cv i = ∑ j, R⁻¹ i j * y j := by
      rw [hcvR]
      rfl
    rw [e]
    calc |∑ j, R⁻¹ i j * y j| ≤ ∑ j, |R⁻¹ i j * y j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |R⁻¹ i j| * |y j| := by simp only [abs_mul]
      _ ≤ ∑ j, |R⁻¹ i j| * (1 + B) :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hyj j) (abs_nonneg _)
      _ = (∑ j, |R⁻¹ i j|) * (1 + B) := by rw [Finset.sum_mul]
      _ ≤ A * (1 + B) := by
          refine mul_le_mul_of_nonneg_right ?_ hB
          exact Finset.single_le_sum (f := fun i => ∑ j, |R⁻¹ i j|)
            (fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _) (Finset.mem_univ i)
  have hle : ((|c i| : ℤ) : ℝ) ≤ (M : ℝ) := by
    rw [Int.cast_abs]
    exact hci.trans (Int.le_ceil _)
  have hle' : |c i| ≤ M := by exact_mod_cast hle
  exact abs_le.1 hle'

end Formalism.MainNotions.ModuliIntegralCharts.H1.PhiCMin
end
end

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open NumberField Module Formalism.MainNotions.ModuliIntegralCharts Matrix PhiCMin

theorem const_eq (E : Type) [Field E] [NumberField E] :
    ((((discr E).natAbs : ℝ) ^ 2)⁻¹) ^ ((1 : ℝ) / finrank ℚ E) *
      |(discr E : ℝ)| ^ ((2 : ℝ) / finrank ℚ E) = 1 := by
  have hd : (discr E : ℝ) ≠ 0 := by exact_mod_cast NumberField.discr_ne_zero E
  have ha : (((discr E).natAbs : ℝ)) = |(discr E : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [ha]
  have ha0 : 0 < |(discr E : ℝ)| := abs_pos.mpr hd
  rw [Real.inv_rpow (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul ha0.le]
  have h2 : ((2 : ℕ) : ℝ) * (1 / (finrank ℚ E : ℝ)) = 2 / (finrank ℚ E : ℝ) := by
    push_cast; ring
  rw [h2]
  exact inv_mul_cancel₀ (Real.rpow_pos_of_pos ha0 _).ne'

theorem phiCMinima_holds : PhiCMinimaStatement := by
  intro E _ _ cj hcj hne w₀ hw Y _ _ _ _ β hβ
  classical
  obtain ⟨ι, hι, b0, hpd⟩ := hβ
  have hcard : Fintype.card ι = finrank ℤ Y := (Module.finrank_eq_card_basis b0).symm
  set d := finrank ℤ Y with hd_def
  let b : Basis (Fin d) ℤ Y := b0.reindex (Fintype.equivFinOfCardEq hcard)
  have hG : (Matrix.of fun a c => (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (b a) (b c)).PosDef := by
    have h := hpd.submatrix (Fintype.equivFinOfCardEq hcard).symm.injective
    convert h using 1
    ext a c
    simp [b, Basis.reindex_apply]
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · have : IsEmpty (Fin d) := by rw [hd0]; infer_instance
    exact ⟨fun i => isEmptyElim i, linearIndependent_empty_type, fun i => isEmptyElim i⟩
  set G := Matrix.of fun a c => (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (b a) (b c) with hGdef

  have hcjO : ∀ c : 𝓞 E, ∃ c' : 𝓞 E, (c' : E) = cj c := cj_integral hcj
  let l0 : SymB cj Y →ₗ[ℝ] ℝ :=
    { toFun := fun γ => ∑ a, (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (w₀ • b a) (b a)
      map_add' := fun γ γ' => by simp [Finset.sum_add_distrib]
      map_smul' := fun t γ => by simp [Finset.mul_sum] }
  have hl0int : ∀ γ : SymB cj Y, (∀ a c, ∃ z : ℤ, (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a c = z) →
      ∃ z : ℤ, l0 γ = z := by
    intro γ hγ
    choose f hf using hγ
    refine ⟨∑ a, f (w₀ • b a) (b a), ?_⟩
    show ∑ a, (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (w₀ • b a) (b a) = _
    push_cast
    exact Finset.sum_congr rfl fun a _ => hf _ _
  have hl0pos : ∀ γ : SymB cj Y, (∀ a, 0 ≤ (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a a) → γ ≠ 0 → 0 < l0 γ := by
    intro γ hγ hne0
    have h2 : ∀ a, 2 * (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (w₀ • b a) (b a) =
        (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (b a) (b a) := fun a => two_mul_form_half_unit hcjO w₀ hw γ (b a)
    have hnn : ∀ a, 0 ≤ (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (w₀ • b a) (b a) := fun a => by
      linarith [h2 a, hγ (b a)]
    show 0 < ∑ a, (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (w₀ • b a) (b a)
    by_contra hle
    push Not at hle
    have hz : ∀ a, (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (w₀ • b a) (b a) = 0 := fun a =>
      (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => hnn a)).1
        (le_antisymm hle (Finset.sum_nonneg fun a _ => hnn a)) a (Finset.mem_univ _)
    have hrad : ∀ a z, (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (b a) z = 0 := fun a z =>
      bil_rad _ γ.2.1 hγ (b a) (by rw [← h2 a, hz a, mul_zero]) z
    apply hne0
    apply Subtype.ext
    refine LinearMap.ext₂ fun y z => ?_
    rw [← repr_left b (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) y z]
    simp [hrad]

  let Q : (Fin d → ℤ) → ℝ := fun c => (fun i => (c i : ℝ)) ⬝ᵥ (G *ᵥ fun i => (c i : ℝ))
  have hne_u : (Finset.univ : Finset (Fin d)).Nonempty := ⟨⟨0, hdpos⟩, Finset.mem_univ _⟩
  let F : (Fin d → Fin d → ℤ) → ℝ := fun c => Finset.univ.sup' hne_u fun j => Q (c j)
  let B0 : ℝ := (1 / 2) * l0 β * ((d : ℝ) / muC E + 1) ^ 2
  let T : Set (Fin d → Fin d → ℤ) := {c | LinearIndependent ℤ c ∧ ∀ j, Q (c j) ≤ B0}
  have hTfin : T.Finite := by
    refine (Set.Finite.pi (t := fun _ : Fin d => {c : Fin d → ℤ | Q c ≤ B0})
      fun _ => finiteShort_holds d G hG B0).subset ?_
    intro c hc j _
    exact hc.2 j
  obtain ⟨c1, hc1li, hc1⟩ := main_ineq hcj hne hdpos b β hG l0 hl0int hl0pos 1 one_pos
  have hTne : T.Nonempty := ⟨c1, hc1li, hc1⟩
  obtain ⟨cs, hcsT, hcsmin⟩ := Set.exists_min_image T F hTfin hTne
  have hclaim : ∀ l : SymB cj Y →ₗ[ℝ] ℝ,
      (∀ γ : SymB cj Y, (∀ a c, ∃ z : ℤ, (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a c = z) → ∃ z : ℤ, l γ = z) →
      (∀ γ : SymB cj Y, (∀ a, 0 ≤ (γ : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a a) → γ ≠ 0 → 0 < l γ) →
      F cs ≤ (1 / 2) * l β * ((d : ℝ) / muC E) ^ 2 := by
    intro l hlint hlpos
    have hev : ∀ δ : ℝ, 0 < δ → F cs ≤ (1 / 2) * l β * ((d : ℝ) / muC E + δ) ^ 2 := by
      intro δ hδ
      obtain ⟨c, hcli, hcq⟩ := main_ineq hcj hne hdpos b β hG l hlint hlpos δ hδ
      by_cases hle : (1 / 2) * l β * ((d : ℝ) / muC E + δ) ^ 2 ≤ B0
      · exact (hcsmin c ⟨hcli, fun j => (hcq j).trans hle⟩).trans
          (Finset.sup'_le _ _ fun j _ => hcq j)
      · push Not at hle
        exact (Finset.sup'_le _ _ fun j _ => hcsT.2 j).trans hle.le
    have hcont : Continuous fun δ : ℝ => (1 / 2) * l β * ((d : ℝ) / muC E + δ) ^ 2 := by fun_prop
    have ht := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    simp only [add_zero] at ht
    exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun δ hδ => hev δ hδ)

  have hn : (0 : ℝ) < finrank ℚ E := by exact_mod_cast Module.finrank_pos
  have hD : (0 : ℝ) < ((discr E).natAbs : ℝ) := by
    exact_mod_cast Int.natAbs_pos.mpr (discr_ne_zero E)
  have hXpos : (0 : ℝ) < ((((discr E).natAbs : ℝ) ^ 2)⁻¹) ^ ((1 : ℝ) / finrank ℚ E) := by
    positivity
  have hP : |(discr E : ℝ)| ^ ((2 : ℝ) / finrank ℚ E) =
      (((((discr E).natAbs : ℝ) ^ 2)⁻¹) ^ ((1 : ℝ) / finrank ℚ E))⁻¹ :=
    eq_inv_of_mul_eq_one_right (const_eq E)
  have hdpos' : (0 : ℝ) < d := by exact_mod_cast hdpos
  set κ : ℝ := |(discr E : ℝ)| ^ ((2 : ℝ) / finrank ℚ E) / (finrank ℚ E) * (d : ℝ) ^ 2 with hκdef
  have hκpos : 0 < κ := by rw [hκdef, hP]; positivity
  have hκ : ∀ l : SymB cj Y →ₗ[ℝ] ℝ, (1 / 2) * l β * ((d : ℝ) / muC E) ^ 2 = κ * l β := by
    intro l
    rw [div_pow, muC_sq, hκdef, hP]
    field_simp
  have hphi : F cs ≤ κ * phiC cj β := by
    have h1 : F cs / κ ≤ phiC cj β := by
      unfold phiC
      refine le_csInf ⟨l0 β, l0, hl0int, hl0pos, rfl⟩ ?_
      rintro _ ⟨l, hl1, hl2, rfl⟩
      rw [div_le_iff₀ hκpos, mul_comm, ← hκ l]
      exact hclaim l hl1 hl2
    rwa [div_le_iff₀ hκpos, mul_comm] at h1

  refine ⟨fun j => b.equivFun.symm (cs j), ?_, fun j => ?_⟩
  · exact hcsT.1.map' b.equivFun.symm.toLinearMap (LinearEquiv.ker _)
  · have hr : ∀ a : Fin d, PhiCMin.bs b a (b.equivFun.symm (cs j)) = (cs j a : ℝ) := fun a => by
      rw [PhiCMin.bs_apply]
      congr 1
      rw [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    have hq : (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (b.equivFun.symm (cs j)) (b.equivFun.symm (cs j)) =
        Q (cs j) := by
      rw [← gram_expand b _ (b.equivFun.symm (cs j)) (b.equivFun.symm (cs j))]
      simp only [hr, Q, dotProduct, Matrix.mulVec, hGdef, Matrix.of_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => by ring
    have hle : Q (cs j) ≤ F cs := Finset.le_sup' (fun j => Q (cs j)) (Finset.mem_univ j)
    rw [hq]
    have hk : κ * phiC cj β = 2 * (|(discr E : ℝ)| ^ ((2 : ℝ) / finrank ℚ E) /
        (2 * finrank ℚ E) * (d : ℝ) ^ 2 * phiC cj β) := by
      rw [hκdef]; field_simp
    linarith

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.ConjugateMinimaInstance
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

namespace ConjugateMinimaInstance

open NumberField Formalism.MainNotions.ModuliIntegralCharts Formalism.BasicNotions

theorem scalar_frame_w_zero_exists (D : D7) : ∃ w₀ : 𝓞 D.host.E, (w₀ : D.host.E) + D.host.conj w₀ = 1 := by
  have hd : D.host.d % 16 = 7 := D.host.hyp.2.2.2.1
  have hcc : (((D.host.gal D.host.conj).1.2 : ℤˣ) : ℤ) = -1 := by
    have hg : D.host.gal D.host.conj = Formalism.HC.Frame.cc _ := by
      simp [Formalism.HC.HostRaw.conj]
    rw [hg]
    simp only [Formalism.HC.Frame.cc] <;> decide
  have hc : D.host.conj D.host.sqd = -D.host.sqd := by
    rw [D.host.gal_sqd, hcc]
    simp
  obtain ⟨m, hm⟩ : ∃ m : ℕ, D.host.d = 4 * m + 3 := ⟨D.host.d / 4, by omega⟩
  have hs : D.host.sqd ^ 2 = -(4 * (m : D.host.E) + 3) := by
    have h0 := D.host.sqd_sq
    rw [hm] at h0
    push_cast at h0
    exact h0
  have hint : IsIntegral ℤ ((1 + D.host.sqd) / 2) := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C ((m : ℤ) + 1), by monicity!, ?_⟩
    rw [← Polynomial.aeval_def]
    simp only [map_add (f := _), map_sub, map_pow, map_one, map_natCast, Polynomial.aeval_X, Polynomial.aeval_C,
      algebraMap_int_eq, eq_intCast, Int.cast_add, Int.cast_natCast, Int.cast_one]
    linear_combination (1 / 4 : D.host.E) * hs
  refine ⟨⟨(1 + D.host.sqd) / 2, hint⟩, ?_⟩
  show (1 + D.host.sqd) / 2 + D.host.conj ((1 + D.host.sqd) / 2) = 1
  rw [map_div₀, map_add (f := _), map_one, hc, map_ofNat]
  ring

theorem conj_ne (D : D7) : ∃ z : D.host.E, D.host.conj z ≠ z := by
  by_contra h
  push_neg at h
  have h1 : D.host.conj = 1 := AlgEquiv.ext h
  have h2 : Formalism.HC.Frame.cc D.R.toFrame = 1 := by
    have := congrArg D.host.gal h1
    simpa [Formalism.HC.HostRaw.conj] using this
  have h3 := congrArg Prod.fst h2
  simp only [Formalism.HC.Frame.cc, Prod.fst_one] at h3
  revert h3
  decide

theorem phiC_rec_eq {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : WeightAlgebra.PJ D B P j) (hj : j < D.R.m)
    (la : IsDedekindDomain.HeightOneSpectrum (𝓞 B.KO)) (y : X.Pt la) :
    X.phiC la y = (eWL B.KO la : ℝ) * (P.loc X.dat (WeightAlgebra.resCh la)).phiCy (X.pt66 la y) := by
  simp [WeightAlgebra.PJ.phiC, hj]

end ConjugateMinimaInstance

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.GramSpace
section -- merged from Formalism.SharpRestriction.Divisibility.GeneratorPowers.GramFormPhiStatement
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open NumberField Formalism.MainNotions.ModuliIntegralCharts

def GramFormPhiStatement : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (cj : E → E),
    (∀ (φ : E →+* ℂ) (z : E), φ (cj z) = star (φ z)) → (∃ z : E, cj z ≠ z) →
    ∀ (w₀ : 𝓞 E), (w₀ : E) + cj w₀ = 1 →
    ∀ (Y : Type) [AddCommGroup Y] [Module (𝓞 E) Y] [Module.Free ℤ Y] [Module.Finite ℤ Y]
      (β : SymB cj Y),
      (∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℤ Y),
        (Matrix.of fun i j => (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (b i) (b j)).PosDef) →
      ∃ b : Module.Basis (Fin (Module.finrank ℤ Y)) ℤ Y,
        (∀ j, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (b j) (b j) / 2 ≤
          (|(NumberField.discr E : ℝ)| ^ ((2 : ℝ) / Module.finrank ℚ E)) /
              (2 * Module.finrank ℚ E) * (Module.finrank ℤ Y : ℝ) ^ 3 * phiC cj β) ∧
        ∀ j (z : Y), |(β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (b j) z| ≤
          2 * Real.sqrt (Module.finrank ℤ Y) * ((β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) z z / 2)

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open NumberField Module Formalism.MainNotions.ModuliIntegralCharts Matrix

namespace GramSpaceAlt

def GramSp (ι : Type) : Type := ι → ℝ

instance (ι : Type) : AddCommGroup (GramSp ι) := inferInstanceAs (AddCommGroup (ι → ℝ))
instance (ι : Type) : Module ℝ (GramSp ι) := inferInstanceAs (Module ℝ (ι → ℝ))
instance (ι : Type) [Fintype ι] : FiniteDimensional ℝ (GramSp ι) :=
  inferInstanceAs (FiniteDimensional ℝ (ι → ℝ))

def toG (ι : Type) : (ι → ℝ) ≃ₗ[ℝ] GramSp ι := LinearEquiv.refl ℝ (ι → ℝ)

def gBasis (ι : Type) [Fintype ι] [DecidableEq ι] : Basis ι ℝ (GramSp ι) := (Pi.basisFun ℝ ι).map (toG ι)

@[instance_reducible]
def gramCore {ι : Type} [Fintype ι] (G : Matrix ι ι ℝ) (hG : G.PosDef) : InnerProductSpace.Core ℝ (GramSp ι) where
  inner x y := dotProduct ((toG ι).symm x) (G *ᵥ (toG ι).symm y)
  conj_inner_symm x y := by
    have hT : Gᵀ = G := by
      have h := hG.1
      rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at h
    simp only [conj_trivial]
    rw [dotProduct_mulVec, ← mulVec_transpose, hT, dotProduct_comm]
  re_inner_nonneg x := by
    simp only [RCLike.re_to_real]
    by_cases hx : (toG ι).symm x = 0
    · rw [hx, zero_dotProduct]
    · have h := hG.dotProduct_mulVec_pos hx
      rw [star_trivial] at h
      exact h.le
  add_left x y z := by simp only [map_add (f := _), add_dotProduct]
  smul_left x y r := by simp only [map_smul, smul_dotProduct, conj_trivial, smul_eq_mul]
  definite x h := by
    by_contra hx
    have hx' : (toG ι).symm x ≠ 0 := fun h0 => hx (by simpa using congrArg (toG ι) h0)
    have h2 := hG.dotProduct_mulVec_pos hx'
    rw [star_trivial] at h2
    exact h2.ne' h

end GramSpaceAlt

open GramSpaceAlt

theorem gram_form_phi_holds : GramFormPhiStatement := by
  classical
  intro E _ _ cj hcj hcm w₀ hw₀ Y _ _ _ _ β hpos
  obtain ⟨v, hv, hvb⟩ := phiCMinima_holds E cj hcj hcm w₀ hw₀ Y β hpos
  obtain ⟨ι, hι, b0, hG⟩ := hpos
  let _ := hι
  set B : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ := (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) with hBdef
  set G : Matrix ι ι ℝ := Matrix.of fun i j => B (b0 i) (b0 j) with hGdef
  let cd : InnerProductSpace.Core ℝ (GramSp ι) := gramCore G hG
  let _ : NormedAddCommGroup (GramSp ι) := @InnerProductSpace.Core.toNormedAddCommGroup ℝ _ _ _ _ cd
  let _ : InnerProductSpace ℝ (GramSp ι) := InnerProductSpace.ofCore cd.toCore

  let ψ0 : Y →ₗ[ℤ] (ι → ℝ) :=
    { toFun := fun y i => (b0.repr y i : ℝ)
      map_add' := fun y z => by funext i; simp
      map_smul' := fun c y => by funext i; simp }
  let ψ : Y →ₗ[ℤ] GramSp ι := ((toG ι).toLinearMap.restrictScalars ℤ).comp ψ0
  have hψ_apply : ∀ y, (toG ι).symm (ψ y) = ψ0 y := fun y => rfl

  have key : ∀ y z, B y z = ∑ i, ∑ j, (b0.repr y i : ℝ) * ((b0.repr z j : ℝ) * B (b0 i) (b0 j)) := by
    intro y z
    rw [← LinearMap.sum_repr_mul_repr_mul b0 b0 (B := B) y z, Finsupp.sum_fintype _ _ (by simp)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finsupp.sum_fintype _ _ (by simp)]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [zsmul_eq_mul]
  have hin : ∀ y z, inner ℝ (ψ y) (ψ z) = B y z := by
    intro y z
    rw [key]
    change dotProduct (ψ0 y) (G *ᵥ ψ0 z) = _
    simp only [dotProduct, mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [ψ0, LinearMap.coe_mk, AddHom.coe_mk, hGdef, Matrix.of_apply]
    ring
  have hnorm : ∀ y, ‖ψ y‖ ^ 2 = B y y := fun y => by
    rw [← real_inner_self_eq_norm_sq, hin]

  have hψX : ∀ y, ψ y ∈ Submodule.span ℤ (Set.range (gBasis ι)) := by
    intro y
    rw [(gBasis ι).mem_span_iff_repr_mem ℤ]
    intro i
    refine ⟨b0.repr y i, ?_⟩
    simp only [gBasis, Basis.map_repr, LinearEquiv.trans_apply, Pi.basisFun_repr, algebraMap_int_eq, eq_intCast]
    rfl
  have hinj : Function.Injective ψ := by
    intro y z h
    apply b0.ext_elem
    intro i
    have h2 := congrArg (fun x => ((toG ι).symm x) i) h
    simp only [hψ_apply, ψ0, LinearMap.coe_mk, AddHom.coe_mk] at h2
    exact_mod_cast h2
  have hsurj : ∀ x ∈ Submodule.span ℤ (Set.range (gBasis ι)), ∃ y, ψ y = x := by
    intro x hx
    have h := ((gBasis ι).mem_span_iff_repr_mem ℤ x).1 hx
    choose c hc using h
    refine ⟨b0.equivFun.symm c, ?_⟩
    apply (toG ι).symm.injective
    funext i
    rw [hψ_apply]
    simp only [ψ0, LinearMap.coe_mk, AddHom.coe_mk]
    rw [show b0.repr (b0.equivFun.symm c) i = c i from by
      rw [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]]
    have := hc i
    simp only [gBasis, Basis.map_repr, LinearEquiv.trans_apply, Pi.basisFun_repr, algebraMap_int_eq,
      eq_intCast] at this
    exact this
  let eX : Y ≃ₗ[ℤ] Submodule.span ℤ (Set.range (gBasis ι)) :=
    LinearEquiv.ofBijective (ψ.codRestrict _ hψX)
      ⟨fun y z h => hinj (congrArg Subtype.val h), fun x => by
        obtain ⟨y, hy⟩ := hsurj x x.2
        exact ⟨y, Subtype.ext hy⟩⟩
  have heX : ∀ x, ψ (eX.symm x) = (x : GramSp ι) := fun x =>
    congrArg Subtype.val (eX.apply_symm_apply x)

  have hdY : finrank ℤ Y = Fintype.card ι := finrank_eq_card_basis b0
  have hdV : finrank ℝ (GramSp ι) = Fintype.card ι := finrank_eq_card_basis (gBasis ι)
  have hd : finrank ℤ Y = finrank ℝ (GramSp ι) := hdY.trans hdV.symm
  have hdR : ((finrank ℝ (GramSp ι) : ℕ) : ℝ) = ((finrank ℤ Y : ℕ) : ℝ) := by rw [hd]

  have hvR : LinearIndependent ℝ fun i => ψ (v i) := by
    let e : ι ≃ Fin (finrank ℤ Y) := Fintype.equivFinOfCardEq hdY.symm
    let Mz : Matrix (Fin (finrank ℤ Y)) (Fin (finrank ℤ Y)) ℤ := Matrix.of fun a i => b0.repr (v i) (e.symm a)
    have hMz : Mz.det ≠ 0 := by
      intro h0
      obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
      apply hc0
      have hsum : ∑ i, c i • v i = 0 := by
        apply b0.ext_elem
        intro k
        have h1 := congrFun hc (e k)
        simp only [Mz, mulVec, dotProduct, Matrix.of_apply, Equiv.symm_apply_apply, Pi.zero_apply] at h1
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, map_zsmul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
          smul_eq_mul, map_zero, Finsupp.coe_zero, Pi.zero_apply]
        rw [← h1]
        exact Finset.sum_congr rfl fun i _ => mul_comm _ _
      funext i
      exact Fintype.linearIndependent_iff.1 hv c hsum i
    rw [Fintype.linearIndependent_iff]
    intro g hg
    by_contra hne
    push Not at hne
    have hdet : ((Int.castRingHom ℝ).mapMatrix Mz).det = 0 := by
      refine Matrix.exists_mulVec_eq_zero_iff.1 ⟨g, fun h => ?_, ?_⟩
      · obtain ⟨i, hi⟩ := hne
        exact hi (congrFun h i)
      · funext a
        have h1 := congrArg (fun x => ((toG ι).symm x) (e.symm a)) hg
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hψ_apply, map_zero,
          Pi.zero_apply, ψ0, LinearMap.coe_mk, AddHom.coe_mk] at h1
        simp only [mulVec, dotProduct, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, Mz,
          eq_intCast, Pi.zero_apply]
        rw [← h1]
        exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [← RingHom.map_det, eq_intCast, Int.cast_eq_zero] at hdet
    exact hMz hdet

  let vX : Fin (finrank ℝ (GramSp ι)) → GramSp ι := fun i => ψ (v (Fin.cast hd.symm i))
  have hvX : LinearIndependent ℝ vX := hvR.comp _ (Fin.cast_injective _)
  obtain ⟨b, hb1, hb2⟩ := ReciprocityTheory.ChartRestriction.G.H1.reducedBasis_holds (GramSp ι)
    (Submodule.span ℤ (Set.range (gBasis ι)))
    ((|(NumberField.discr E : ℝ)| ^ ((2 : ℝ) / Module.finrank ℚ E)) /
      (2 * Module.finrank ℚ E) * (Module.finrank ℤ Y : ℝ) ^ 2 * phiC cj β) vX hvX
    (fun i => hψX _) (fun i => by rw [hnorm]; exact hvb _)
  refine ⟨(b.map eX.symm).reindex (finCongr hd.symm), fun j => ?_, fun j z => ?_⟩
  · have hbj : ψ (((b.map eX.symm).reindex (finCongr hd.symm)) j) = (b (Fin.cast hd j) : GramSp ι) := by
      rw [Basis.reindex_apply, Basis.map_apply, heX]
      rfl
    rw [← hnorm, hbj]
    have h1 := hb1 (Fin.cast hd j)
    rw [hdR] at h1
    calc ‖(b (Fin.cast hd j) : GramSp ι)‖ ^ 2 / 2 ≤ _ := h1
      _ = _ := by ring
  · have hbj : ψ (((b.map eX.symm).reindex (finCongr hd.symm)) j) = (b (Fin.cast hd j) : GramSp ι) := by
      rw [Basis.reindex_apply, Basis.map_apply, heX]
      rfl
    rw [← hin, hbj, ← hnorm]
    have h2 := hb2 (Fin.cast hd j) (ψ z) (hψX z)
    rw [hdR] at h2
    exact h2

end Formalism.MainNotions.ModuliIntegralCharts.H1
end
end
