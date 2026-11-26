module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinAinfDiscIsDomainNormBounds
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClosedDiscToDiscInjectiveOfAdicBasis
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfAdicTopologicalBasisOverBreuilKisin
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.UnramifiedNoJump

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineDiscPeriodsGaloisActionEq
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineDiscPeriodsGaloisActionEq
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

noncomputable section

namespace GlobalTheory.BSP

theorem ringHom_ext_of_sep_galPer {R B : Type} [CommRing R] [CommRing B] {f g : R⟦X⟧ →+* B}
    (hC : ∀ r, f (C r) = g (C r)) (hX : f X = g X) (hsep : ∀ b : B, (∀ n, f X ^ n ∣ b) → b = 0) :
    f = g := by
  have hp : ∀ p : Polynomial R, f p = g p := fun p => by
    induction p using Polynomial.induction_on with
    | C a => simpa using hC a
    | add p q hp hq => simp [hp, hq]
    | monomial n a _ => simp [hC, hX]
  ext1 a
  rw [← sub_eq_zero]
  refine hsep _ fun n => ?_
  rw [a.eq_X_pow_mul_shift_add_trunc n, map_add (f := _), map_add (f := _), hp, map_mul, map_mul, map_pow, map_pow, ← hX]
  exact ⟨_, by rw [add_sub_add_right_eq_sub, ← mul_sub]⟩

theorem mat_mul_right_cancel_galPer {R : Type} [CommRing R] [IsDomain R] {n : Type} [Fintype n] [DecidableEq n]
    {A B P : Matrix n n R} (hP : P.det ≠ 0) (h : A * P = B * P) : A = B := by
  have h2 : (A - B) * P = 0 := by rw [Matrix.sub_mul, h, sub_self]
  have h3 : P.det • (A - B) = 0 := by
    rw [← Matrix.mul_one (A - B), ← Matrix.mul_smul, ← Matrix.mul_adjugate P, ← Matrix.mul_assoc, h2,
      Matrix.zero_mul]
  rw [← sub_eq_zero]
  ext i j
  have h4 := congr_fun₂ h3 i j
  rw [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at h4
  rw [Matrix.zero_apply]
  exact (mul_eq_zero.1 h4).resolve_left hP

theorem mat_smul_cancel_galPer {R : Type} [CommRing R] [IsDomain R] {m n : Type} {c : R} (hc : c ≠ 0)
    {A B : Matrix m n R} (h : c • A = c • B) : A = B := by
  ext i j
  have h1 := congr_fun₂ h i j
  rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul] at h1
  exact mul_left_cancel₀ hc h1

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l}

namespace BK

variable (bk : BK K)

theorem X_pow_mem_J_galPer : (X : bk.S) ^ bk.Ep.natDegree ∈ bk.J := by
  have e1 : bk.Ep - Polynomial.X ^ bk.Ep.natDegree =
      ∑ i ∈ Finset.range bk.Ep.natDegree, Polynomial.C (bk.Ep.coeff i) * Polynomial.X ^ i := by
    rw [sub_eq_iff_eq_add']
    exact bk.monic.as_sum
  have h1 : (l : Polynomial (Wq l bk.a)) ∣ bk.Ep - Polynomial.X ^ bk.Ep.natDegree := by
    rw [e1]
    refine Finset.dvd_sum fun i hi => ?_
    obtain ⟨c, hc⟩ := bk.dvd_coeff i (Finset.mem_range.1 hi)
    exact ⟨Polynomial.C c * Polynomial.X ^ i, by rw [hc, map_mul, map_natCast]; ring⟩
  have h2 : (l : bk.S) ∣ bk.E - X ^ bk.Ep.natDegree := by
    have := map_dvd (Polynomial.coeToPowerSeries.ringHom (R := Wq l bk.a)) h1
    simpa using this
  have e2 : (X : bk.S) ^ bk.Ep.natDegree = bk.E - (bk.E - X ^ bk.Ep.natDegree) := by ring
  rw [e2]
  exact Submodule.sub_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    (Ideal.mem_sup_left (Ideal.mem_span_singleton.2 h2))

theorem ev_sep_galPer (b : Ainf l) (hb : ∀ n, bk.ev X ^ n ∣ b) : b = 0 := by
  obtain ⟨ι, ⟨tb⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  have hc := tb.complete
  refine IsHausdorff.haus hc.toIsHausdorff b fun n => ?_
  rw [SModEq.zero, Ideal.smul_eq_mul, Ideal.mul_top]
  obtain ⟨c, hc⟩ := hb (bk.Ep.natDegree * n)
  rw [hc, pow_mul, ← map_pow]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (Ideal.mem_map_of_mem bk.ev bk.X_pow_mem_J_galPer) n)

theorem σA_ev_galPer {g : ↥(GK K)} (hg : bk.FixFlat g) (a : bk.S) : Per.σA (g : GQ l) (bk.ev a) = bk.ev a := by
  have hg' : Per.σF (g : GQ l) bk.flat = bk.flat := hg
  have hX : ((Per.σA (g : GQ l)).comp bk.ev) X = bk.ev X := by
    show Per.σA _ (bk.ev X) = bk.ev X
    rw [bk.ev_X, GlobalTheory.RingIface.sigA_teich, hg']
  have h := ringHom_ext_of_sep_galPer (f := (Per.σA (g : GQ l)).comp bk.ev) (g := bk.ev)
    (fun w => by
      show Per.σA _ (bk.ev (C w)) = bk.ev (C w)
      rw [bk.ev_C, bk.gal_w]) hX
    (fun b hb => bk.ev_sep_galPer b fun n => by rw [← hX]; exact hb n)
  exact RingHom.congr_fun h a

theorem ev_injective_galPer : Function.Injective bk.ev := by
  obtain ⟨ι, ⟨tb⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  have key : ∀ a, tb.c tb.i₀ (bk.ev a * tb.b tb.i₀) = a := fun a => by
    rw [tb.c_mul, tb.c_self, mul_one]
  intro a a' h
  rw [← key a, ← key a', h]

theorem ρ₀_pos_lt_one_galPer : 0 < bk.ρ₀ ∧ bk.ρ₀ < 1 := by
  have hl1 : (1 : ℝ≥0) < l := by exact_mod_cast hl.out.one_lt
  have he : (0 : ℝ) < bk.Ep.natDegree := by exact_mod_cast bk.deg_pos
  refine ⟨NNReal.rpow_pos (zero_lt_one.trans hl1), ?_⟩
  exact NNReal.rpow_lt_one_of_one_lt_of_neg hl1 (neg_neg_of_pos (one_div_pos.2 he))

end BK

theorem seed_gal_periods : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ)
    (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ),
    ∀ g : ↥(GK K), bk.FixFlat g → ∀ G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA (g : GQ l)) G →
      (∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → ∀ x, G (j x) = j x) ∧
      bk.iA τ ^ s.N • ((ρ g).map (bk.iA.comp (algebraMap ℤ_[l] (Ainf l))) * s.W.map G) =
        G (bk.iA τ) ^ s.N • s.W := by
  intro l _ K bk τ _ d ρ _ s g hg G hG
  obtain ⟨h0, h1⟩ := bk.ρ₀_pos_lt_one_galPer
  haveI : IsDomain (bk.DA bk.ρ₀) := (GlobalTheory.T.breuilKisin_ainfDisc_isDomain_norm_bounds l K bk bk.ρ₀ h0 h1).1
  obtain ⟨ι, ⟨tb⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  have hinj : Function.Injective bk.iA := (GlobalTheory.T.closedDisc_toDisc_injective_of_adicBasis l K bk (Ainf l) bk.ev ι tb bk.ρ₀ h0 h1).1
  have hGS : ∀ a, G (bk.iA (bk.ev a)) = bk.iA (bk.ev a) := fun a => by
    show G (toDisc l (bk.ev X) bk.ρ₀ (bk.ev a)) = _
    rw [hG.ext, bk.σA_ev_galPer hg]
  have hGτ : G (bk.iA τ) = bk.iA (Per.σA (g : GQ l) τ) := hG.ext τ
  refine ⟨fun j hj x => ?_, ?_⟩
  · have hGj : IsDiscMap (l := _) (u := _) (ρ := _) bk.ev (G.comp j) :=
      ⟨fun a => by
        show G (j (toDisc l X bk.ρ₀ a)) = _
        rw [hj.ext]; exact hGS a,
       fun x => (hG.norm_le _).trans (hj.norm_le x)⟩
    exact RingHom.congr_fun (IsDiscMap.unique hGj hj) x
  · have he : bk.iA (bk.ev bk.E) ≠ 0 := fun h =>
      bk.E_ne_zero (bk.ev_injective_galPer (hinj (h.trans (map_zero _).symm) |>.trans (map_zero _).symm))
    have hl0 : ((l : ℕ) : bk.DA bk.ρ₀) ≠ 0 := (isUnit_l_disc l (bk.ev X) bk.ρ₀).ne_zero
    have hdet : (s.X'.map bk.iS).det ≠ 0 := by
      intro h0'
      have hm := congrArg (fun M => (M.map bk.iS).det) s.X_mul
      rw [Matrix.map_mul, Matrix.det_mul, h0', mul_zero] at hm
      have hc : (((l : bk.S) ^ s.c₂ * bk.E ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) bk.S)).map bk.iS =
          bk.iS ((l : bk.S) ^ s.c₂ * bk.E ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) := by
        ext i j
        by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
      rw [hc, Matrix.det_smul, Matrix.det_one, mul_one] at hm
      have h3 := pow_eq_zero_iff'.1 hm.symm
      rw [map_mul, map_pow, map_pow, map_natCast] at h3
      exact mul_ne_zero (pow_ne_zero _ hl0) (pow_ne_zero _ he) h3.1
    have hX' : (s.X'.map bk.iS).map G = s.X'.map bk.iS := by
      rw [Matrix.map_map]
      congr 1
      funext a
      exact hGS a
    have hσ : bk.iA (Per.σA (g : GQ l) (bk.ev bk.E * τ)) = bk.iA (bk.ev bk.E) * G (bk.iA τ) := by
      rw [map_mul, bk.σA_ev_galPer hg, map_mul, hGτ]
    have h := s.gal g G hG
    rw [Matrix.map_mul, hX', hσ, map_mul, mul_pow, mul_pow, mul_smul, mul_smul] at h
    have h' := mat_smul_cancel_galPer (pow_ne_zero _ he) h
    refine mat_mul_right_cancel_galPer hdet ?_
    rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_assoc]
    exact h'

end GlobalTheory.BSP
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineDiscPeriodsGaloisActionEqStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystallineDiscPeriods_galois_action_eq : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l) (hτ : bk.IsPer τ) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (hρ : ∀ g, IsUnit (ρ g)) (s : Seed bk d ρ τ), ∀ g : ↥(GK K), bk.FixFlat g → ∀ G : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) (Per.σA (g : GQ l)) G → (∀ j : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) bk.ev j → ∀ x, G (j x) = j x) ∧ bk.iA τ ^ s.N • ((ρ g).map (bk.iA.comp (algebraMap ℤ_[l] (Ainf l))) * s.W.map G) = G (bk.iA τ) ^ s.N • s.W := by
  first | exact @GlobalTheory.BSP.seed_gal_periods | exact GlobalTheory.BSP.seed_gal_periods | (intros; apply GlobalTheory.BSP.seed_gal_periods <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoDecompositionInvariantsAboveLOfNoHodgeJump
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoDecompositionInvariantsAboveLOfNoHodgeJump
noncomputable section

namespace GlobalTheory.InvJump

section Generic

open Formalism.WeaklyAdmissibleFiltrations TensorProduct

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem eq_zero_of_mem_Fil_one (c : K) (h : algebraMap K BdR c ∈ PD.Fil 1) : c = 0 := by
  by_contra hc
  have h1 : (1 : BdR) ∈ PD.Fil 1 := by
    have := (PD.Fil 1).smul_mem c⁻¹ h
    rwa [Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hc, map_one] at this
  exact PD.not_mem_filtration_two (by simpa using PD.Fil_mul 1 1 _ _ h1 PD.mem_filtration_one)

theorem isJumpV_zero_of_invariant [CharZero Qp] (ρ : Representation LL G V) (x : V) (hx : x ≠ 0)
    (hinv : ∀ g, ρ g x = x) (τ : K →ₐ[Qp] LL) : IsJumpV PD ρ τ 0 := by
  classical
  haveI := PD.finK
  let b := Module.finBasis Qp K
  let b' := b.traceDual
  let y : V ⊗[Qp] BdR := ∑ i, (τ (b' i) • x) ⊗ₜ[Qp] algebraMap K BdR (b i)
  have e1 : ∀ z : K, z = ∑ j, Algebra.trace Qp K (z * b' j) • b j := by
    intro z
    conv_lhs => rw [← b.sum_repr z]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    set_option synthInstance.maxHeartbeats 100000 in
      conv_rhs => rw [← b.sum_repr z, Finset.sum_mul, map_sum]
    simp only [b', smul_mul_assoc, map_smul, Module.Basis.trace_mul_traceDual]
    simp
  have e2 : ∀ z : K, z = ∑ j, Algebra.trace Qp K (z * b j) • b' j := by
    intro z
    conv_lhs => rw [← b'.sum_repr z]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    conv_rhs => rw [← b'.sum_repr z]
    simp [b', Finset.sum_mul, Module.Basis.trace_traceDual_mul]
  have h0 : y ∈ FildR PD ρ τ 0 := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simp only [DdR, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero]
      intro g
      set_option synthInstance.maxHeartbeats 100000 in
        simp [y, actVdR, map_sum, hinv]
    · simp only [SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero, LinearMap.smul_apply]
      intro c
      have l : mulVdR (LL := LL) (V := V) c y =
          ∑ i, ∑ j, Algebra.trace Qp K (c * b i * b' j) •
            ((τ (b' i) • x) ⊗ₜ[Qp] algebraMap K BdR (b j)) := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [y, map_sum, mulVdR, AlgebraTensorModule.map_tmul, LinearMap.id_apply,
          LinearMap.mulLeft_apply, ← map_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        set_option synthInstance.maxHeartbeats 100000 in
          conv_lhs => rw [e1 (c * b i), map_sum, tmul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← tmul_smul, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, ← Algebra.smul_def]
      have r : τ c • y =
          ∑ j, ∑ i, Algebra.trace Qp K (c * b' j * b i) •
            ((τ (b' i) • x) ⊗ₜ[Qp] algebraMap K BdR (b j)) := by
        simp only [y, Finset.smul_sum, smul_tmul', smul_smul, ← map_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        set_option synthInstance.maxHeartbeats 100000 in
          conv_lhs => rw [e2 (c * b' j), map_sum, Finset.sum_smul, sum_tmul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_smul, smul_assoc]
      rw [l, r, Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
      rw [mul_right_comm]
    · refine Submodule.sum_mem _ fun i _ => ⟨(τ (b' i) • x) ⊗ₜ ⟨algebraMap K BdR (b i), ?_⟩, rfl⟩
      rw [Algebra.algebraMap_eq_smul_one]
      exact (PD.Fil 0).smul_mem _ PD.one_mem
  intro h
  rw [← h] at h0
  obtain ⟨w, hw⟩ := h0.2
  obtain ⟨φ, hφ⟩ : ∃ φ : LL →ₗ[Qp] Qp, φ 1 = 1 := by
    obtain ⟨φ, hφ⟩ := (Algebra.linearMap Qp LL).exists_leftInverse_of_injective
      (LinearMap.ker_eq_bot.2 (algebraMap Qp LL).injective)
    exact ⟨φ, by simpa using LinearMap.congr_fun hφ 1⟩
  obtain ⟨f, hf⟩ : ∃ f : V →ₗ[LL] LL, f x = 1 := Module.Projective.exists_dual_eq_one LL hx
  let m : V ⊗[Qp] BdR →ₗ[Qp] BdR :=
    (TensorProduct.lid Qp BdR).toLinearMap ∘ₗ (φ ∘ₗ f.restrictScalars Qp).rTensor BdR
  have hm : ∀ w, m (AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V)
      ((PD.Fil (0 + 1)).restrictScalars Qp).subtype w) ∈ (PD.Fil (0 + 1)).restrictScalars Qp := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul v c => simpa [m] using ((PD.Fil (0 + 1)).restrictScalars Qp).smul_mem (φ (f v)) c.2
    | add a b ha hb => simpa only [map_add (f := _)] using Submodule.add_mem _ ha hb
  have h1 := hm w
  rw [hw] at h1
  have h2 : m y = algebraMap K BdR (∑ i, φ (τ (b' i)) • b i) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [y, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [m, hf, Algebra.smul_def, ← IsScalarTower.algebraMap_apply]
  rw [h2] at h1
  have h3 := eq_zero_of_mem_Fil_one PD _ (by rw [zero_add] at h1; exact h1)
  have h4 : ∀ i, φ (τ (b' i)) = 0 := Fintype.linearIndependent_iff.1 b.linearIndependent _ h3
  have h5 : φ ∘ₗ τ.toLinearMap = 0 := b'.ext fun i => by simpa using h4 i
  have := LinearMap.congr_fun h5 1
  simp [hφ] at this

end Generic

open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial


open scoped Pointwise in
theorem noInv_of_noJump : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i), NoJump bkP i s → ∀ v ∈ placesOver D.host.E (D.ntw.l i), NoInv i (Tmat i s) v := by
  intro D bkP i s hJ v hv A hA x hx
  by_contra hx0
  obtain ⟨k, hk⟩ := exists_smul_eq_of_isPlaceOver (F := D.host.E) (D.nd.plOm.2 v) hA
  let Bw := bkP.br i v hv
  have inj : Function.Injective Bw.toLL := Subtype.val_injective.comp Bw.eO.injective
  let ψ : FractionRing (D.ntw.O0 i) →+* ↥Bw.LL.1 := IsFractionRing.lift inj
  have hψ : ∀ a, ψ (algebraMap _ _ a) = Bw.toLL a := fun a => IsFractionRing.lift_algebraMap inj a
  let M : Gen.GE D.nd → Matrix (Fin D.R.r) (Fin D.R.r) ↥Bw.LL.1 := fun g => (Tmat i s g).map Bw.toLL
  have hM : ∀ g g', M (g * g') = M g * M g' := fun g g' => by
    simp only [M, ← Tgl_coe, map_mul, Units.val_mul, Matrix.map_mul]
  have hM1 : M 1 = 1 := by
    simp only [M, ← Tgl_coe, map_one, Units.val_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  let z : Fin D.R.r → ↥Bw.LL.1 := fun a => ψ (x a)
  have hz : ∀ g ∈ Dec (F := D.host.E) A, (M g).mulVec z = z := fun g hg => by
    funext a
    have := congrArg ψ (congrFun (hx g hg) a)
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [Matrix.mulVec, dotProduct, map_sum, hψ, M, z] using this
  have hz0 : (M k⁻¹).mulVec z ≠ 0 := fun h => hx0 (by
    have h1 := congrArg (M k).mulVec h
    rw [Matrix.mulVec_mulVec, ← hM, mul_inv_cancel, hM1, Matrix.one_mulVec, Matrix.mulVec_zero] at h1
    funext a
    exact ψ.injective (by simpa [z] using congrFun h1 a))
  let τ : EmbV bkP i v hv := Bw.Kw.1.val.codRestrict Bw.LL.1.toSubalgebra (Bw.LL_split Bw.Kw.1.val)
  have hj := isJumpV_zero_of_invariant (PDv bkP i v hv) (repV bkP i v hv (Tgl i s)) _ hz0 (fun g => by
    have hg : k * (Bw.e.symm g : Gen.GE D.nd) * k⁻¹ ∈ Dec (F := D.host.E) A := by
      have h : (Bw.e.symm g : Gen.GE D.nd) • D.nd.plOm.1 v = D.nd.plOm.1 v := (Bw.e.symm g).2
      show (k * (Bw.e.symm g : Gen.GE D.nd) * k⁻¹) • A = A
      rw [← hk, mul_smul, inv_smul_smul, mul_smul, h]
    have e : repV bkP i v hv (Tgl i s) g ((M k⁻¹).mulVec z) =
        (M (Bw.e.symm g : Gen.GE D.nd)).mulVec ((M k⁻¹).mulVec z) := by
      simp only [M, ← Tgl_coe]
      rfl
    rw [e]
    conv_rhs => rw [← hz _ hg]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hM, ← hM, ← mul_assoc, ← mul_assoc,
      inv_mul_cancel, one_mul]) τ
  have := hJ v hv τ 0 hj
  omega

end GlobalTheory.InvJump

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoDecompositionInvariantsAboveLOfNoHodgeJumpStatement
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.noDecompositionInvariants_aboveL_of_noHodgeJump : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i), NoJump bkP i s → ∀ v ∈ placesOver D.host.E (D.ntw.l i), NoInv i (Tmat i s) v := by
  first | exact @GlobalTheory.InvJump.noInv_of_noJump | exact GlobalTheory.InvJump.noInv_of_noJump | (intros; apply GlobalTheory.InvJump.noInv_of_noJump <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateNegativeJumpCountOfGoodHodgeJumps
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsComplexReadingLocalEmbeddingStatement
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complex_reading_local_embedding : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (ι : FractionRing (D.ntw.O0 i) →+* ℂ) (v : HeightOneSpectrum (𝓞 D.host.E)) (hv : v ∈ placesOver D.host.E (D.ntw.l i)) (τ : EmbV bkP i v hv), ∃ τc : D.host.E →+* ℂ, ReadEmb bkP i ι v hv τ τc ∧ ∀ (v' : HeightOneSpectrum (𝓞 D.host.E)) (hv' : v' ∈ placesOver D.host.E (D.ntw.l i)) (τ' : EmbV bkP i v' hv'), IsConjEmb bkP i v v' hv hv' τ τ' → ReadEmb bkP i ι v' hv' τ' (τc.comp (cj D)) := by
  first | exact @GlobalTheory.ReadEmbEx.exists_readEmb | exact GlobalTheory.ReadEmbEx.exists_readEmb | (intros; apply GlobalTheory.ReadEmbEx.exists_readEmb <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankDdRAndFilZeroOfJumpMultiset
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankDdRAndFilZeroOfJumpMultiset
namespace GlobalTheory.JumpDims

open Module
open scoped TensorProduct

section Linear

variable {L U : Type} [Field L] [AddCommGroup U] [Module L U]

theorem exists_le_of_exh (D : Submodule L U) [FiniteDimensional L D] (F : ℤ → Submodule L U)
    (hanti : Antitone F) (hexh : ∀ x, ∃ a, x ∈ F a) : ∃ a, D ≤ F a := by
  obtain ⟨S, hS⟩ : D.FG := Module.Finite.iff_fg.mp inferInstance
  choose n hn using hexh
  obtain ⟨a, ha⟩ := (S.image n).bddBelow
  refine ⟨a, ?_⟩
  rw [← hS, Submodule.span_le]
  intro x hx
  exact hanti (ha (Finset.mem_coe.mpr (Finset.mem_image_of_mem n hx))) (hn x)

theorem exists_inf_eq_bot_of_sep (D : Submodule L U) [FiniteDimensional L D] (F : ℤ → Submodule L U)
    (hanti : Antitone F) (hsep : ∀ x, (∀ a, x ∈ F a) → x = 0) : ∃ a, D ⊓ F a = ⊥ := by
  have hfin : ∀ a, FiniteDimensional L ↥(D ⊓ F a) := fun a =>
    Submodule.finiteDimensional_of_le inf_le_left
  let a : ℤ := Function.argmin (fun a : ℤ => finrank L ↥(D ⊓ F a))
  have ha : ∀ b, finrank L ↥(D ⊓ F a) ≤ finrank L ↥(D ⊓ F b) := fun b =>
    Function.argmin_le (fun a : ℤ => finrank L ↥(D ⊓ F a)) b
  refine ⟨a, eq_bot_iff.mpr fun x hx => ?_⟩
  rw [Submodule.mem_bot]
  refine hsep x fun b => ?_
  rcases le_total a b with h | h
  · have : D ⊓ F b = D ⊓ F a :=
      Submodule.eq_of_le_of_finrank_le (inf_le_inf_left D (hanti h)) (ha b)
    exact (this ▸ hx : x ∈ D ⊓ F b).2
  · exact hanti h hx.2

theorem card_filter_succ (M : Multiset ℤ) (a : ℤ) :
    Multiset.card (M.filter (a ≤ ·)) = Multiset.card (M.filter (a + 1 ≤ ·)) + M.count a := by
  induction M using Multiset.induction_on with
  | empty => simp
  | cons b M ih =>
    rw [Multiset.filter_cons, Multiset.filter_cons, Multiset.count_cons, Multiset.card_add,
      Multiset.card_add, ih]
    split_ifs <;> simp <;> omega

theorem finrank_of_mult (D : Submodule L U) [FiniteDimensional L D] (F : ℤ → Submodule L U)
    (hanti : Antitone F) (hexh : ∀ x, ∃ a, x ∈ F a) (hsep : ∀ x, (∀ a, x ∈ F a) → x = 0)
    (M : Multiset ℤ)
    (hM : ∀ a, (finrank L ↥(D ⊓ F a) : ℤ) - finrank L ↥(D ⊓ F (a + 1)) = (M.count a : ℤ)) :
    finrank L D = Multiset.card M ∧
      ∀ a, finrank L ↥(D ⊓ F a) = Multiset.card (M.filter (a ≤ ·)) := by
  let g : ℤ → ℤ := fun a => (finrank L ↥(D ⊓ F a) : ℤ) - Multiset.card (M.filter (a ≤ ·))
  have hstep : ∀ a, g (a + 1) = g a := fun a => by
    have h1 := hM a
    have h2 := card_filter_succ M a
    simp only [g]
    omega
  have hconst : ∀ a, g a = g 0 := fun a => by
    induction a using Int.induction_on with
    | zero => rfl
    | succ n ih => rw [hstep, ih]
    | pred n ih => rw [← ih, ← hstep]; congr 1; ring
  obtain ⟨hi, hhi⟩ := exists_inf_eq_bot_of_sep D F hanti hsep
  obtain ⟨lo, hlo⟩ := exists_le_of_exh D F hanti hexh
  obtain ⟨u, hu⟩ := M.toFinset.bddAbove
  obtain ⟨l, hl⟩ := M.toFinset.bddBelow
  have hu' : ∀ x ∈ M, x ≤ u := fun x hx => hu (by simpa using hx)
  have hl' : ∀ x ∈ M, l ≤ x := fun x hx => hl (by simpa using hx)
  have h0 : g (max hi (u + 1)) = 0 := by
    have e1 : D ⊓ F (max hi (u + 1)) = ⊥ :=
      eq_bot_iff.mpr (hhi ▸ inf_le_inf_left D (hanti (le_max_left _ _)))
    have e2 : M.filter (max hi (u + 1) ≤ ·) = 0 :=
      Multiset.filter_eq_nil.mpr fun x hx h => by
        have := hu' x hx
        have := le_max_right hi (u + 1)
        omega
    show (finrank L ↥(D ⊓ F (max hi (u + 1))) : ℤ) - Multiset.card (M.filter (max hi (u + 1) ≤ ·)) = 0
    rw [e1, e2]
    simp
  have hall : ∀ a, finrank L ↥(D ⊓ F a) = Multiset.card (M.filter (a ≤ ·)) := fun a => by
    have : g a = 0 := by rw [hconst a, ← hconst (max hi (u + 1)), h0]
    simp only [g] at this
    omega
  refine ⟨?_, hall⟩
  have e1 : D ⊓ F (min lo l) = D := inf_eq_left.mpr (hlo.trans (hanti (min_le_left _ _)))
  have e2 : M.filter (min lo l ≤ ·) = M :=
    Multiset.filter_eq_self.mpr fun x hx => (min_le_right _ _).trans (hl' x hx)
  have := hall (min lo l)
  rwa [e1, e2] at this

end Linear

open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

theorem finite_of_isdR {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
    {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω Gw O) (P : LocPrime l) {m : ℕ}
    (r : ↥Gw →* Matrix.GeneralLinearGroup (Fin m) O) (h : Bw.IsdRW P r) :
    FiniteDimensional ↥Bw.LL.1 ↥(Formalism.WeaklyAdmissibleFiltrations.DdR (P.PD Bw.Kw) (Bw.rep r)) := by
  set_option synthInstance.maxHeartbeats 200000 in
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · haveI : Subsingleton (Formalism.WeaklyAdmissibleFiltrations.DdR (P.PD Bw.Kw) (Bw.rep r)) := by
      refine ⟨fun x y => Subtype.ext ?_⟩
      have hz : ∀ z : (Fin 0 → ↥Bw.LL.1) ⊗[ℚ_[l]] P.R.BdR, z = 0 := fun z => by
        induction z using TensorProduct.induction_on with
        | zero => rfl
        | tmul a b => rw [Subsingleton.elim a 0, TensorProduct.zero_tmul]
        | add a b ha hb => rw [ha, hb, add_zero]
      rw [hz x.1, hz y.1]
    haveI : Finite (Formalism.WeaklyAdmissibleFiltrations.DdR (P.PD Bw.Kw) (Bw.rep r)) := Finite.of_subsingleton
    exact Module.Finite.of_finite
  · haveI := (P.PD Bw.Kw).finK
    haveI : Module.Free ↥Bw.LL.1 ↥(Formalism.WeaklyAdmissibleFiltrations.DdR (P.PD Bw.Kw) (Bw.rep r)) := Module.Free.of_divisionRing _ _
    exact Module.finite_of_finrank_pos (by rw [h]; exact Nat.mul_pos Module.finrank_pos hm)

theorem dims_of_mult : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i), ∀ (v : HeightOneSpectrum (𝓞 D.host.E)) (hv : v ∈ placesOver D.host.E (D.ntw.l i)) (τ : EmbV bkP i v hv) (M : Multiset ℤ), HodgeL bkP i s → (∀ a : ℤ, Formalism.WeaklyAdmissibleFiltrations.multV (PDv bkP i v hv) (repV bkP i v hv (Tgl i s)) τ a = (M.count a : ℤ)) → dimD bkP i v hv (Tgl i s) τ = Multiset.card M ∧ dimFil0 bkP i v hv (Tgl i s) τ = Multiset.card (M.filter (0 ≤ ·)) := by
  set_option synthInstance.maxHeartbeats 200000 in
  intro D bkP i s v hv τ M hH hM
  have hdR := (hH v hv (Tgl i s) (Or.inr rfl)).1
  haveI := finite_of_isdR _ _ _ hdR
  haveI : FiniteDimensional _ ↥(Formalism.WeaklyAdmissibleFiltrations.DdRE (PDv bkP i v hv) (repV bkP i v hv (Tgl i s)) τ) :=
    Submodule.finiteDimensional_of_le (S₂ := Formalism.WeaklyAdmissibleFiltrations.DdR (PDv bkP i v hv) (repV bkP i v hv (Tgl i s)))
      inf_le_left
  have key := finrank_of_mult (Formalism.WeaklyAdmissibleFiltrations.DdRE (PDv bkP i v hv) (repV bkP i v hv (Tgl i s)) τ)
    (Formalism.WeaklyAdmissibleFiltrations.FilV (PDv bkP i v hv)) (GlobalTheory.DRFil.FilV_antitone _) (GlobalTheory.DRFil.exists_mem_FilV _)
    (GlobalTheory.DRFil.eq_zero_of_forall_mem_FilV _) M hM
  exact ⟨key.1, key.2 0⟩

end GlobalTheory.JumpDims
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankDdRAndFilZeroOfJumpMultisetStatement
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_DdR_and_fil_zero_of_jump_multiset : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i), ∀ (v : HeightOneSpectrum (𝓞 D.host.E)) (hv : v ∈ placesOver D.host.E (D.ntw.l i)) (τ : EmbV bkP i v hv) (M : Multiset ℤ), HodgeL bkP i s → (∀ a : ℤ, Formalism.WeaklyAdmissibleFiltrations.multV (PDv bkP i v hv) (repV bkP i v hv (Tgl i s)) τ a = (M.count a : ℤ)) → dimD bkP i v hv (Tgl i s) τ = Multiset.card M ∧ dimFil0 bkP i v hv (Tgl i s) τ = Multiset.card (M.filter (0 ≤ ·)) := by
  first | exact @GlobalTheory.JumpDims.dims_of_mult | exact GlobalTheory.JumpDims.dims_of_mult | (intros; apply GlobalTheory.JumpDims.dims_of_mult <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateNegativeJumpCountOfGoodHodgeJumps
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.TripleGal

theorem card_filter_nonneg_add_reflect (t : ℤ) (ht : 0 ≤ t) (M : Multiset ℤ) (h : ∀ a ∈ M, a < -1 ∨ t < a) :
    Multiset.card (M.filter (0 ≤ ·)) + Multiset.card ((M.map (fun a => t - 1 - a)).filter (0 ≤ ·)) =
      Multiset.card M := by
  rw [Multiset.filter_map, Multiset.card_map]
  have e : M.filter ((fun a => 0 ≤ a) ∘ fun a => t - 1 - a) = M.filter (fun a => ¬ 0 ≤ a) := by
    apply Multiset.filter_congr
    intro a ha
    have := h a ha
    simp only [Function.comp_apply]
    omega
  rw [e, ← Multiset.card_add, Multiset.filter_add_not]

theorem negCount_of_goodJ : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i), ∀ (ι : FractionRing (D.ntw.O0 i) →+* ℂ) (J : (D.host.E →+* ℂ) → Multiset ℤ), HodgeL bkP i s → JumpsAre bkP i s ι J → GoodJ D J → NegCount bkP i s := by
  intro D bkP i s ι J hH hJ hG v v' hv hv' τ τ' hc
  obtain ⟨τc, h1, h2⟩ := GlobalTheory.T.exists_complex_reading_local_embedding D bkP i ι v hv τ
  have h2' := h2 v' hv' τ' hc
  obtain ⟨a1, a2⟩ := GlobalTheory.T.finrank_DdR_and_fil_zero_of_jump_multiset D bkP i s v hv τ (J τc) hH (hJ v hv τ τc h1)
  obtain ⟨b1, b2⟩ := GlobalTheory.T.finrank_DdR_and_fil_zero_of_jump_multiset D bkP i s v' hv' τ' (J (τc.comp (cj D))) hH (hJ v' hv' τ' _ h2')
  obtain ⟨g1, g2, g3⟩ := hG τc
  have k := card_filter_nonneg_add_reflect (D.R.t : ℤ) (by positivity) (J τc) g3
  rw [a1, a2, b1, b2, g2, Multiset.card_map]
  omega

end GlobalTheory.TripleGal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateNegativeJumpCountOfGoodHodgeJumpsStatement
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugateNegativeJumpCount_of_goodHodgeJumps : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i), ∀ (ι : FractionRing (D.ntw.O0 i) →+* ℂ) (J : (D.host.E →+* ℂ) → Multiset ℤ), HodgeL bkP i s → JumpsAre bkP i s ι J → GoodJ D J → NegCount bkP i s := by
  first | exact @GlobalTheory.TripleGal.negCount_of_goodJ | exact GlobalTheory.TripleGal.negCount_of_goodJ | (intros; apply GlobalTheory.TripleGal.negCount_of_goodJ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.T2SpaceCoefficientRing
noncomputable section

namespace GlobalTheory.ComplementCompare

open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions.N ReciprocityTheory.Gal
open GlobalTheory.IndefiniteRowSideFullHecke

section General

variable {k Γ : Type} [Field k] [Group Γ]

theorem semisimple_congr {V W : Type} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    {ρ : Representation k Γ V} {σ : Representation k Γ W} (e : V ≃ₗ[k] W)
    (he : ∀ g v, e (ρ g v) = σ g (e v)) :
    ρ.IsSemisimpleRepresentation ↔ σ.IsSemisimpleRepresentation := by
  have he' : ∀ g w, e.symm (σ g w) = ρ g (e.symm w) := fun g w => by
    rw [LinearEquiv.symm_apply_eq, he, LinearEquiv.apply_symm_apply]
  let o : Subrepresentation ρ ≃o Subrepresentation σ :=
    { toFun := fun P => ⟨P.toSubmodule.comap e.symm.toLinearMap, fun g w hw => by
        change e.symm (σ g w) ∈ P.toSubmodule
        rw [he']
        exact P.apply_mem_toSubmodule g hw⟩
      invFun := fun Q => ⟨Q.toSubmodule.comap e.toLinearMap, fun g v hv => by
        change e (ρ g v) ∈ Q.toSubmodule
        rw [he]
        exact Q.apply_mem_toSubmodule g hv⟩
      left_inv := fun P => by ext v; simp
      right_inv := fun Q => by ext w; simp
      map_rel_iff' := by
        intro P Q
        constructor
        · intro h v hv
          have := @h (e v) (by
            change e.symm (e v) ∈ P.toSubmodule
            rw [e.symm_apply_apply]
            exact hv)
          change e.symm (e v) ∈ Q.toSubmodule at this
          rw [e.symm_apply_apply] at this
          exact this
        · intro h w hw
          exact @h (e.symm w) hw }
  exact OrderIso.complementedLattice_iff o

theorem isCompl_sub_iff {V : Type} [AddCommGroup V] [Module k V] {ρ : Representation k Γ V}
    (P Q : Subrepresentation ρ) : IsCompl P Q ↔ IsCompl P.toSubmodule Q.toSubmodule := by
  rw [isCompl_iff, isCompl_iff, disjoint_iff, disjoint_iff, codisjoint_iff, codisjoint_iff,
    ← Subrepresentation.toSubmodule_injective.eq_iff, ← Subrepresentation.toSubmodule_injective.eq_iff]
  rfl

theorem isSSRep_iff {a : ℕ} (ρ : Γ →* GL (Fin a) k) :
    IsSSRep ρ ↔ (glRep ρ).IsSemisimpleRepresentation := by
  constructor
  · intro h
    refine ⟨fun P => ?_⟩
    obtain ⟨W', h1, h2⟩ := h P.toSubmodule fun g v hv => P.apply_mem_toSubmodule g hv
    exact ⟨⟨W', fun g v hv => h1 g v hv⟩, (isCompl_sub_iff _ _).2 h2⟩
  · intro h W hW
    obtain ⟨Q, hQ⟩ := h.exists_isCompl ⟨W, fun g v hv => hW g v hv⟩
    exact ⟨Q.toSubmodule, fun g v hv => Q.apply_mem_toSubmodule g hv, (isCompl_sub_iff _ _).1 hQ⟩

variable {O : Type} [CommRing O] [IsDomain O]

theorem fracRep_eq {a : ℕ} (r : Γ →* GL (Fin a) O) :
    BlockRepresentationsSemisimple.fracRep r = RepresentationOverSumChar.repOver (FractionRing O) ((Units.coeHom _).comp r) := rfl

theorem sum_equivariant {a : ℕ} (ρ : Γ →* GL (Fin a) O) (χ : ℕ → (Γ →* Oˣ)) (t : ℕ) (g : Γ)
    (v : Fin a ⊕ Fin t → FractionRing O) :
    LinearEquiv.sumArrowLequivProdArrow (Fin a) (Fin t) (FractionRing O) (FractionRing O)
        (RepresentationOverSumChar.repOver (FractionRing O) (RepresentationOverSumChar.blockSum t ρ χ) g v) =
      BlockRepresentationsSemisimple.blockRep ρ χ t g
        (LinearEquiv.sumArrowLequivProdArrow (Fin a) (Fin t) (FractionRing O) (FractionRing O) v) := by
  rw [BlockRepresentationsSemisimple.blockRep_apply]
  have key : ∀ s : Fin a ⊕ Fin t, RepresentationOverSumChar.repOver (FractionRing O) (RepresentationOverSumChar.blockSum t ρ χ) g v s =
      ∑ s' : Fin a ⊕ Fin t, algebraMap O (FractionRing O)
        (Matrix.fromBlocks ((ρ g : GL (Fin a) O) : Matrix (Fin a) (Fin a) O) 0 0
          (Matrix.diagonal fun c : Fin t => ((χ (c.1 + 1) g : Oˣ) : O)) s s') * v s' := fun s => rfl
  refine Prod.ext (funext fun j => ?_) (funext fun c => ?_)
  · refine (key (Sum.inl j)).trans ?_
    simp [Fintype.sum_sum_type, Matrix.mulVec, dotProduct]
  · refine (key (Sum.inr c)).trans ?_
    simp [Fintype.sum_sum_type, Matrix.diagonal_apply, apply_ite]

theorem trace_repOver {n : Type} [Fintype n] [DecidableEq n] (M : Γ →* Matrix n n O) (g : Γ) :
    LinearMap.trace _ _ (RepresentationOverSumChar.repOver (FractionRing O) M g) =
      algebraMap O (FractionRing O) (M g).trace := by
  change LinearMap.trace _ _ (Matrix.toLin' ((M g).map (algebraMap O (FractionRing O)))) = _
  rw [Matrix.trace_toLin'_eq, AddMonoidHom.map_trace]

omit [IsDomain O] in
theorem trace_eq_of_charpoly_eq [Nontrivial O] {m n : Type} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] (A : Matrix m m O) (B : Matrix n n O) (h : A.charpoly = B.charpoly) :
    A.trace = B.trace := by
  rw [Matrix.trace_eq_neg_charpoly_nextCoeff, Matrix.trace_eq_neg_charpoly_nextCoeff, h]

end General

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)

theorem ss_iff (i : N.Loc) (ρ : GE N →* GL (Fin R.r) (N.O i)) :
    BlockRepresentationsSemisimple.BlockSemisimple ρ (N.chi i) R.t ↔ RepresentationOverSumChar.IsSSSum N i ρ :=
  (semisimple_congr _ (sum_equivariant ρ (N.chi i) R.t)).symm

theorem isoBlock_iff (i : N.Loc) (r₀ : GE N →* GL (Fin R.nV) (N.O i)) (ρ : GE N →* GL (Fin R.r) (N.O i)) :
    BlockRepresentationsSemisimple.IsoBlock r₀ ρ (N.chi i) R.t ↔ RepresentationOverSumChar.SplitsAs N i r₀ ρ := by
  constructor
  · rintro ⟨e, he⟩
    refine ⟨e.trans (LinearEquiv.sumArrowLequivProdArrow _ _ _ _).symm, fun g u => ?_⟩
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.symm_apply_eq]
    refine (he g u).trans ?_
    refine Eq.trans ?_ (sum_equivariant ρ (N.chi i) R.t g _).symm
    rw [LinearEquiv.apply_symm_apply]
  · rintro ⟨e, he⟩
    refine ⟨e.trans (LinearEquiv.sumArrowLequivProdArrow _ _ _ _), fun g u => ?_⟩
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, fracRep_eq, he g u]
    exact sum_equivariant ρ (N.chi i) R.t g _

theorem isHeckeGalois_iff (i : N.Loc) (x : N.X i) (r : GE N →* GL (Fin R.nV) (N.O i)) :
    IsHeckeGalois N i x r ↔ RepresentationOverSumChar.IsRx N i x ((Units.coeHom _).comp r) :=
  and_congr Iff.rfl (and_congr (isSSRep_iff _) Iff.rfl)

theorem second_of_first (i : N.Loc) (π : N.X i) (r₀ : GE N →* GL (Fin R.nV) (N.O i))
    (ρ : GE N →* GL (Fin R.r) (N.O i)) (hr : IsHeckeGalois N i π r₀)
    (h : BlockRepresentationsSemisimple.IsComplement N i r₀ ρ) : RepresentationOverSumChar.IsComplement N i π ρ :=
  ⟨RepresentationOverSumChar.isRhoAt_of_splitsAs N i π r₀ ρ hr.2.2 ((isoBlock_iff N i r₀ ρ).1 h.rho),
    (ss_iff N i ρ).1 h.ss, h.cont⟩

theorem exists_conj_ne (H : Host R) : ∃ x y : 𝓞 H.E, (y : H.E) = H.conj (x : H.E) ∧ y - x ≠ 0 := by
  by_contra hc
  push Not at hc
  have h1 : ∀ x : 𝓞 H.E, H.conj (x : H.E) = x := fun x => by
    have := hc x ⟨H.conj x, (RingOfIntegers.isIntegral_coe x).map (H.conj.toAlgHom.restrictScalars ℤ)⟩ rfl
    exact congrArg (fun z : 𝓞 H.E => (z : H.E)) (sub_eq_zero.1 this)
  have h2 : ∀ z : H.E, H.conj z = z := fun z => by
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 H.E) z
    rw [map_div₀]
    exact congrArg₂ (· / ·) (h1 a) (h1 b)
  have := H.isCMField_hostE
  refine IsTotallyComplex.complexEmbedding_not_isReal H.φ₀ (ComplexEmbedding.isReal_iff.2 ?_)
  ext z
  exact (H.conjE_apply H.φ₀ z).symm.trans (congrArg H.φ₀ (h2 z))

theorem exists_int_sub_mem {E : Type} [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E))
    (hv : v.asIdeal.inertiaDeg ℤ = 1) (x : 𝓞 E) : ∃ n : ℤ, x - n ∈ v.asIdeal := by
  have := v.isPrime
  have : NeZero v.asIdeal := ⟨v.ne_bot⟩
  have hp := Nat.absNorm_under_prime v.asIdeal
  have h := Ideal.absNorm_pow_inertiaDeg (v.asIdeal.under ℤ) v.asIdeal
  rw [hv, pow_one] at h
  rw [h] at hp
  have : Fact (Ideal.absNorm v.asIdeal).Prime := ⟨hp⟩
  have hc : Nat.card (𝓞 E ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal :=
    (Ideal.absNorm_eq_natCard v.asIdeal).symm
  have : Nontrivial (𝓞 E ⧸ v.asIdeal) := Ideal.Quotient.nontrivial_iff.2 v.isPrime.ne_top
  have hm := mem_zmultiples_of_prime_card hc (g := (1 : 𝓞 E ⧸ v.asIdeal)) (g' := Ideal.Quotient.mk _ x)
    one_ne_zero
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.1 hm
  refine ⟨n, Ideal.Quotient.eq.1 ?_⟩
  rw [← hn]
  simp

theorem eq_univ_of_frob (hC : GlobalTheory.TwSys.Cheb) (i : N.Loc) (s : Set (GE N)) (hs : IsClosed s)
    (h : ∀ w : PlE H, SplitOut N i w → ∀ (B : ValuationSubring N.Om) (σ : GE N),
      IsPlaceOver (F := H.E) B w → IsFrob (F := H.E) B (normV w) σ → σ ∈ s) (g : GE N) : g ∈ s := by
  classical
  by_contra hg
  have : IsGalois H.E N.Om := {}
  have hn : (fun u : GE N => u * g) ⁻¹' sᶜ ∈ nhds (1 : GE N) :=
    (hs.isOpen_compl.preimage (continuous_mul_const g)).mem_nhds (by simpa using hg)
  obtain ⟨L, hfd, hN, hL⟩ := (krullTopology_mem_nhds_one_iff_of_normal H.E N.Om _).1 hn
  have hgal : IsGalois H.E L := {}
  obtain ⟨x, y, hxy, hne⟩ := exists_conj_ne H
  have f1 : {v : PlE H | v.asIdeal ∣ Ideal.span {y - x}}.Finite :=
    Ideal.finite_factors (by simpa using hne)
  have f2 : {v : PlE H | v.asIdeal ∣ Ideal.span {((N.l i : ℕ) : 𝓞 H.E)}}.Finite :=
    Ideal.finite_factors (by simpa using (N.lPrime i).out.ne_zero)
  obtain ⟨v, hv, hf, -, B, hB, -, σ, hσ, hU⟩ := hC H.E N.Om L.fixingSubgroup L.fixingSubgroup_isOpen
    ((InfiniteGalois.normal_iff_isGalois L).2 hgal) g (f1.toFinset ∪ f2.toFinset ∪ N.S i ∪ N.Q i)
  simp only [Finset.mem_union, Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_span_singleton,
    not_or] at hv
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hv
  obtain ⟨n, hx⟩ := exists_int_sub_mem v hf x
  have hsplit : IsSplitPl H v := by
    refine ⟨x - n, hx, fun z hz hzv => h1 ?_⟩
    have hz' : z = y - n := by
      apply RingOfIntegers.ext
      rw [hz]
      simp [hxy]
    have := v.asIdeal.sub_mem hzv hx
    rwa [hz', sub_sub_sub_cancel_right] at this
  have := hL hU
  simp only [Set.mem_preimage, inv_mul_cancel_right, Set.mem_compl_iff] at this
  exact this (h v ⟨hsplit, h2, h3, h4⟩ B σ hB hσ)

theorem t2Space_coefficientRing (i : N.Loc) : T2Space (N.O i) :=
  have := N.O_complete i
  (N.O_adic i).isHausdorff_iff.1 inferInstance

theorem isRx_unique (hC : GlobalTheory.TwSys.Cheb) (i : N.Loc) (x : N.X i) {m n : Type} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (M : GE N →* Matrix m m (N.O i)) (M' : GE N →* Matrix n n (N.O i))
    (h : RepresentationOverSumChar.IsRx N i x M) (h' : RepresentationOverSumChar.IsRx N i x M') :
    ∃ e : (m → KK N i) ≃ₗ[KK N i] (n → KK N i), ∀ g u,
      e (RepresentationOverSumChar.repOver (KK N i) M g u) = RepresentationOverSumChar.repOver (KK N i) M' g (e u) := by
  have := t2Space_coefficientRing N i
  have : CharZero what₂.LL := what₂.embLL.charZero
  have : CharZero (FractionRing (N.O i)) :=
    (N.embK i).charZero_iff (N.embK i).injective |>.1 inferInstance
  refine GlobalTheory.TraceIso.exists_equiv_of_trace_eq _ _ h.2.1 h'.2.1 fun g => ?_
  rw [trace_repOver, trace_repOver]
  congr 1
  refine eq_univ_of_frob N hC i {g | (M g).trace = (M' g).trace}
    (isClosed_eq h.1.matrix_trace h'.1.matrix_trace) (fun w hw B σ hB hσ => ?_) g
  exact trace_eq_of_charpoly_eq _ _ ((h.2.2 w hw B σ hB hσ).trans (h'.2.2 w hw B σ hB hσ).symm)

end GlobalTheory.ComplementCompare

end
end
