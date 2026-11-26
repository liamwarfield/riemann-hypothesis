module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassSumSmallerLevel
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrysInclusion

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeBasisFrobeniusEquationDisc
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusPeriodMemNonZeroDivisorsDisc
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusPeriodMemNonZeroDivisorsDisc
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem per_ne_zero {l : ℕ} [Fact l.Prime] {K : FinExt l} (bk : BK K) {τ : Ainf l} (h : bk.IsPer τ) : τ ≠ 0 := by
  rintro rfl
  obtain ⟨-, ε, η, hε, hφ⟩ := h
  rw [map_zero] at hφ
  have h1 : WittVector.teichmuller l ε - 1 = 0 := (Units.mul_right_eq_zero η).1 hφ.symm
  have h2 : ε = 1 := by
    have := congrArg (fun w => WittVector.coeff w 0) (sub_eq_zero.1 h1)
    simpa using this
  subst h2
  exact hε.2 (by simp)

theorem iA_per_mem_nonZeroDivisors : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l),
    bk.IsPer τ → bk.iA τ ∈ nonZeroDivisors (bk.DA bk.ρ₀) := by
  intro l _ K bk τ hτ
  obtain ⟨h0, h1, -, -⟩ := GlobalTheory.T.breuilKisin_norm_eisenstein_le_radius l K bk (Ainf l) bk.ev
  haveI : IsDomain (bk.DA bk.ρ₀) := (discAinf_isDomain l K bk bk.ρ₀ h0 h1).1
  obtain ⟨ι, ⟨tb⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  have hinj : Function.Injective bk.iA := (GlobalTheory.T.toDisc_injective_and_nonZeroDivisors_of_topBasis l K bk (Ainf l) bk.ev ι tb).1
  refine mem_nonZeroDivisors_of_ne_zero ?_
  rw [← map_zero bk.iA]
  exact fun h => per_ne_zero bk hτ (hinj h)

end GlobalTheory.BSP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusPeriodMemNonZeroDivisorsDiscStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobeniusPeriod_mem_nonZeroDivisors_disc : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → bk.iA τ ∈ nonZeroDivisors (bk.DA bk.ρ₀) := by
  first | exact @GlobalTheory.BSP.iA_per_mem_nonZeroDivisors | exact GlobalTheory.BSP.iA_per_mem_nonZeroDivisors | (intros; apply GlobalTheory.BSP.iA_per_mem_nonZeroDivisors <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeBasisFrobeniusEquationDisc
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP

theorem mul_eq_smul_one_comm {R : Type} [CommRing R] [IsDomain R] {d : ℕ}
    {M M' : Matrix (Fin d) (Fin d) R} {c : R} (hc : c ≠ 0) (h : M * M' = c • (1 : Matrix (Fin d) (Fin d) R)) :
    M' * M = c • (1 : Matrix (Fin d) (Fin d) R) := by
  have hdet : M.det ≠ 0 := by
    intro h0
    have h1 := congrArg Matrix.det h
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_smul, Matrix.det_one, mul_one] at h1
    exact pow_ne_zero _ hc h1.symm
  have key : M.det • (M' * M) = M.det • (c • (1 : Matrix (Fin d) (Fin d) R)) := by
    calc M.det • (M' * M) = (M.adjugate * M) * (M' * M) := by
          rw [Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]
      _ = M.adjugate * (M * M') * M := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.adjugate_mul, smul_comm]
  ext i j
  have h2 := congrFun (congrFun key i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at h2
  simpa [Matrix.smul_apply] using mul_left_cancel₀ hdet h2

theorem eq_zero_of_mul_eq_zero_of_mul_eq_smul {R : Type} [CommRing R] {d : ℕ}
    {W W' M : Matrix (Fin d) (Fin d) R} {t : R} (ht : t ∈ nonZeroDivisors R)
    (h : W * W' = t • (1 : Matrix (Fin d) (Fin d) R)) (hM : W * M = 0) : M = 0 := by
  have hdet : W.det ∈ nonZeroDivisors R := by
    have h1 := congrArg Matrix.det h
    rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one] at h1
    have htp : t ^ Fintype.card (Fin d) ∈ nonZeroDivisors R := pow_mem ht _
    rw [mem_nonZeroDivisors_iff] at htp ⊢
    refine ⟨fun x hx => htp.1 x (by rw [← h1, mul_comm W.det, mul_assoc, hx, mul_zero]),
      fun x hx => htp.2 x (by rw [← h1, ← mul_assoc, hx, zero_mul])⟩
  have key : W.det • M = 0 := by
    rw [← Matrix.one_mul M, ← Matrix.smul_mul, ← Matrix.adjugate_mul, Matrix.mul_assoc, hM, Matrix.mul_zero]
  ext i j
  have h2 := congrFun (congrFun key i) j
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at h2 ⊢
  exact (mem_nonZeroDivisors_iff.1 hdet).1 _ h2

theorem map_smul_ringHom {R R' : Type} [CommRing R] [CommRing R'] {m n : Type} (f : R →+* R') (c : R)
    (M : Matrix m n R) : (c • M).map f = f c • M.map f := by
  ext i j; simp

end GlobalTheory.BSP

namespace GlobalTheory.BSP

theorem Height.bas_frob : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s), bk.IsPer τ → ∀ Φ : bk.DS bk.ρ₀ →+* bk.DS bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) (frobS l bk.a) Φ → ((l : bk.DS bk.ρ₀) ^ s.c₁ * toDisc l (X : bk.S) bk.ρ₀ (frobS l bk.a bk.E) ^ s.N) • (ht.bas * ht.A.map (toDisc l (X : bk.S) bk.ρ₀)) = toDisc l (X : bk.S) bk.ρ₀ bk.E ^ (ht.a + 2 * s.N) • (s.F.map ((toDisc l (X : bk.S) bk.ρ₀).comp C) * ht.bas.map Φ) := by
  intro l _ K bk d ρ τ s ht hτ Φ hΦ
  have hρ : (0 : ℝ≥0) < bk.ρ₀ := by
    unfold BK.ρ₀
    exact NNReal.rpow_pos (Nat.cast_pos.2 (Fact.out : l.Prime).pos)
  have hρ1 : bk.ρ₀ ≤ 1 := by
    unfold BK.ρ₀
    apply NNReal.rpow_le_one_of_one_le_of_nonpos
    · exact_mod_cast (Fact.out : l.Prime).one_lt.le
    · have : (0:ℝ) ≤ 1 / (bk.Ep.natDegree : ℝ) := by positivity
      linarith
  have hev : ‖toDisc l (bk.ev X) bk.ρ₀ (bk.ev X)‖ ≤ bk.ρ₀ := by
    simpa using norm_toDisc_pow_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) 1 hρ
  have hXl : frobS l bk.a (X : bk.S) = X ^ l := by
    simp [frobS]
  have hfr : ‖toDisc l (bk.ev X) bk.ρ₀ (WittVector.frobenius (bk.ev X))‖ ≤ bk.ρ₀ := by
    rw [← bk.ev_frob, hXl, map_pow]
    refine (norm_toDisc_pow_le (l := l) (u := bk.ev X) (ρ := bk.ρ₀) l hρ).trans ?_
    exact pow_le_of_le_one (by positivity) (by exact_mod_cast hρ1) (Fact.out : l.Prime).ne_zero
  set i : bk.DS bk.ρ₀ →+* bk.DA bk.ρ₀ := Disc.map bk.ev hev with hi_def
  have hi : IsDiscMap (l := _) (u := _) (ρ := _) bk.ev i := isDiscMap_map _ _
  set ΦA : bk.DA bk.ρ₀ →+* bk.DA bk.ρ₀ := Disc.map WittVector.frobenius hfr with hΦA_def
  have hΦA : IsDiscMap (l := _) (u := _) (ρ := _) WittVector.frobenius ΦA := isDiscMap_map _ _
  have hcomm : i.comp Φ = ΦA.comp i := by
    have h1 : IsDiscMap (l := _) (u := _) (ρ := _) (bk.ev.comp (frobS l bk.a)) (i.comp Φ) :=
      ⟨fun a => by simp only [RingHom.comp_apply, hΦ.ext, hi.ext], fun x => (hi.norm_le _).trans (hΦ.norm_le _)⟩
    have h2 : IsDiscMap (l := _) (u := _) (ρ := _) (bk.ev.comp (frobS l bk.a)) (ΦA.comp i) := by
      have e : bk.ev.comp (frobS l bk.a) = (WittVector.frobenius : Ainf l →+* Ainf l).comp bk.ev :=
        RingHom.ext bk.ev_frob
      rw [e]
      exact ⟨fun a => by simp only [RingHom.comp_apply, hΦA.ext, hi.ext], fun x => (hΦA.norm_le _).trans (hi.norm_le _)⟩
    exact h1.unique h2
  obtain ⟨ι, ⟨tb⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  have hinj : Function.Injective i := (GlobalTheory.T.toDisc_injective_and_nonZeroDivisors_of_topBasis l K bk _ bk.ev ι tb).2.2.2 i hi
  have hlS : (l : bk.S) ∈ nonZeroDivisors bk.S :=
    (GlobalTheory.T.toDisc_injective_and_nonZeroDivisors_of_topBasis l K bk bk.S (RingHom.id _) Unit (@TopBasis.self _ _ bk.J bk.complete)).2.2.1
  have hτr : bk.iA τ ∈ nonZeroDivisors (bk.DA bk.ρ₀) := GlobalTheory.T.frobeniusPeriod_mem_nonZeroDivisors_disc l K bk τ hτ
  have hφE : IsUnit (bk.iS (frobS l bk.a bk.E)) := by
    have h := (GlobalTheory.T.isUnit_closedDisc_frobenius_eisenstein l K bk).map i
    rw [hi.ext] at h; exact h
  have hL : IsUnit ((l : ℕ) : bk.DA bk.ρ₀) := isUnit_l_disc l (bk.ev X) bk.ρ₀
  have hiS : ∀ a, i (toDisc l (X : bk.S) bk.ρ₀ a) = bk.iS a := hi.ext
  have hΦiA : ∀ a, ΦA (bk.iA a) = bk.iA (WittVector.frobenius a) := hΦA.ext
  have hΦiS : ∀ a, ΦA (bk.iS a) = bk.iS (frobS l bk.a a) := fun a => by
    simp only [BK.iS, RingHom.comp_apply, hΦiA, bk.ev_frob]
  have hXX : s.X' * s.X = ((l : bk.S) ^ s.c₂ * bk.E ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) bk.S) :=
    mul_eq_smul_one_comm (mul_ne_zero (pow_ne_zero _ (nonZeroDivisors.ne_zero hlS)) (pow_ne_zero _ bk.E_ne_zero)) s.X_mul

  have hmapinj : ∀ M M' : Matrix (Fin d) (Fin d) (bk.DS bk.ρ₀), M.map i = M'.map i → M = M' := fun M M' h => by
    ext a b; exact hinj (congrFun (congrFun h a) b)
  apply hmapinj
  have hcomm' : ∀ z, i (Φ z) = ΦA (i z) := RingHom.congr_fun hcomm
  simp only [map_smul_ringHom, Matrix.map_mul, Height.bas, Matrix.map_map, Function.comp_def, hiS, map_mul, map_pow,
    map_natCast, RingHom.comp_apply, hcomm', hΦ.ext]

  set L : bk.DA bk.ρ₀ := ((l : ℕ) : bk.DA bk.ρ₀) with hL_def
  set e : bk.DA bk.ρ₀ := bk.iS bk.E with he_def
  set φe : bk.DA bk.ρ₀ := bk.iS (frobS l bk.a bk.E) with hφe_def
  set XA := s.X.map bk.iS with hXA
  set X'A := s.X'.map bk.iS with hX'A
  set φXA := s.X.map (bk.iS.comp (frobS l bk.a)) with hφXA
  set φX'A := s.X'.map (bk.iS.comp (frobS l bk.a)) with hφX'A
  set FA := s.F.map (bk.iS.comp C) with hFA
  set AA := ht.A.map bk.iS with hAA
  set Zi := ht.Z.map i with hZi
  set ZΦ := ht.Z.map (fun z => ΦA (i z)) with hZΦ
  set YA := ht.Y.map bk.iA with hYA
  have hW : s.W * Zi = YA := ht.W_mul i hi
  have hZΦ' : ZΦ = Zi.map ΦA := by rw [hZΦ, hZi, Matrix.map_map]; rfl
  have hWΦ : s.W.map ΦA * ZΦ = YA.map ΦA := by rw [hZΦ', ← Matrix.map_mul, hW]
  have hP : e ^ ht.a • YA.map ΦA = YA * AA := by
    have h := congrArg (fun M => M.map bk.iA) ht.φ
    simp only [map_smul_ringHom, Matrix.map_mul, Matrix.map_map] at h
    have e1 : YA.map ΦA = ht.Y.map (bk.iA.comp WittVector.frobenius) := by
      rw [hYA, Matrix.map_map]; congr 1; funext x; exact hΦiA x
    rw [e1]; rw [map_pow] at h; exact h
  have hS : L ^ s.c₁ • (s.W.map ΦA * φX'A) = φe ^ s.N • (s.W * X'A * FA) := by
    have h := s.φ ΦA hΦA
    rw [Matrix.map_mul] at h
    have e1 : (s.X'.map bk.iS).map ΦA = φX'A := by
      rw [Matrix.map_map, hφX'A]; congr 1; funext x; exact hΦiS x
    rw [e1] at h
    simpa only [map_natCast, map_pow] using h
  have hXXφ : φX'A * φXA = (L ^ s.c₂ * φe ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) := by
    have h := congrArg (fun M => M.map (bk.iS.comp (frobS l bk.a))) hXX
    simp only [Matrix.map_mul, map_smul_ringHom, Matrix.map_one _ (map_zero _) (map_one _), map_mul, map_pow,
      map_natCast] at h
    exact h
  have hXX2 : XA * X'A = (L ^ s.c₂ * e ^ (2 * s.N)) • (1 : Matrix (Fin d) (Fin d) (bk.DA bk.ρ₀)) := by
    have h := congrArg (fun M => M.map bk.iS) s.X_mul
    simp only [Matrix.map_mul, map_smul_ringHom, Matrix.map_one _ (map_zero _) (map_one _), map_mul, map_pow,
      map_natCast] at h
    exact h
  have hQ : (L ^ s.c₁ * L ^ s.c₂ * φe ^ s.N) • s.W.map ΦA = s.W * X'A * FA * φXA := by
    apply ((hφE.pow s.N).smul_left_cancel).1
    calc φe ^ s.N • (L ^ s.c₁ * L ^ s.c₂ * φe ^ s.N) • s.W.map ΦA
        = (L ^ s.c₁ • (s.W.map ΦA * φX'A)) * φXA := by
          rw [Matrix.smul_mul, Matrix.mul_assoc, hXXφ, Matrix.mul_smul, Matrix.mul_one, smul_smul, smul_smul]
          congr 1; ring
      _ = _ := by rw [hS, Matrix.smul_mul]
  have hD : s.W * ((L ^ s.c₁ * L ^ s.c₂ * φe ^ s.N) • (Zi * AA) - e ^ ht.a • (X'A * FA * φXA * ZΦ)) = 0 := by
    rw [Matrix.mul_sub, sub_eq_zero, Matrix.mul_smul, Matrix.mul_smul, ← Matrix.mul_assoc, hW, ← hP, ← hWΦ,
      smul_comm, ← Matrix.smul_mul, hQ]
    simp only [Matrix.mul_assoc]
  have hD' := eq_zero_of_mul_eq_zero_of_mul_eq_smul (pow_mem hτr _) s.W_mul hD
  rw [sub_eq_zero] at hD'
  have hX := congrArg (fun M => XA * M) hD'
  simp only [Matrix.mul_smul, ← Matrix.mul_assoc, hXX2, Matrix.smul_mul, Matrix.one_mul, smul_smul] at hX
  have G : (L ^ s.c₁ * φe ^ s.N) • (XA * Zi * AA) = e ^ (ht.a + 2 * s.N) • (FA * (φXA * ZΦ)) := by
    apply ((hL.pow s.c₂).smul_left_cancel).1
    rw [smul_smul, smul_smul]
    calc (L ^ s.c₂ * (L ^ s.c₁ * φe ^ s.N)) • (XA * Zi * AA) = (L ^ s.c₁ * L ^ s.c₂ * φe ^ s.N) • (XA * Zi * AA) := by
          congr 1; ring
      _ = _ := by rw [hX, ← Matrix.mul_assoc]; congr 1; ring
  exact G

end GlobalTheory.BSP
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeBasisFrobeniusEquationDiscStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeBasis_frobenius_equation_disc : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s), bk.IsPer τ → ∀ Φ : bk.DS bk.ρ₀ →+* bk.DS bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) (frobS l bk.a) Φ → ((l : bk.DS bk.ρ₀) ^ s.c₁ * toDisc l (X : bk.S) bk.ρ₀ (frobS l bk.a bk.E) ^ s.N) • (ht.bas * ht.A.map (toDisc l (X : bk.S) bk.ρ₀)) = toDisc l (X : bk.S) bk.ρ₀ bk.E ^ (ht.a + 2 * s.N) • (s.F.map ((toDisc l (X : bk.S) bk.ρ₀).comp C) * ht.bas.map Φ) := by
  first | exact @GlobalTheory.BSP.Height.bas_frob | exact GlobalTheory.BSP.Height.bas_frob | (intros; apply GlobalTheory.BSP.Height.bas_frob <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrismHomsAgreeOnWitt
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrismHomsAgreeOnWitt
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.PairW

theorem eq_zero_of_mem_pow {A : Type} [CommRing A] {J : Ideal A} [IsHausdorff J A] {x : A}
    (h : ∀ n : ℕ, x ∈ J ^ n) : x = 0 :=
  IsHausdorff.haus' (I := J) x fun n => by rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]; exact h n

theorem pow_sub_pow_mem_succ {A : Type} [CommRing A] {J : Ideal A} (p : ℕ) (hp : (p : A) ∈ J) {y z : A}
    {k : ℕ} (h : y - z ∈ J ^ (k + 1)) : y ^ p - z ^ p ∈ J ^ (k + 1 + 1) := by
  have h1 : y - z ∈ J := Ideal.pow_le_self (Nat.succ_ne_zero k) h
  have hs : (∑ i ∈ Finset.range p, y ^ i * z ^ (p - 1 - i)) ∈ J := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have hyz : Ideal.Quotient.mk J y = Ideal.Quotient.mk J z := Ideal.Quotient.eq.2 h1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_mul, map_pow, hyz]
    rw [geom_sum₂_self, ← map_natCast (Ideal.Quotient.mk J), Ideal.Quotient.eq_zero_iff_mem.2 hp, zero_mul]
  have e := geom_sum₂_mul y z p
  rw [← e, mul_comm, pow_succ]
  exact Ideal.mul_mem_mul h hs

theorem pow_pow_sub_mem {A : Type} [CommRing A] {J : Ideal A} (p : ℕ) (hp : (p : A) ∈ J) {y z : A}
    (h : y - z ∈ J) (n : ℕ) : y ^ p ^ n - z ^ p ^ n ∈ J ^ (n + 1) := by
  induction n with
  | zero => simpa using h
  | succ n ih => rw [pow_succ p n, pow_mul, pow_mul]; exact pow_sub_pow_mem_succ p hp ih

theorem eq_of_pow_eq_self {A : Type} [CommRing A] {J : Ideal A} [IsHausdorff J A] (p : ℕ) (hp : (p : A) ∈ J)
    {a : ℕ} (ha : 0 < a) {y z : A} (hy : y ^ p ^ a = y) (hz : z ^ p ^ a = z) (h : y - z ∈ J) : y = z := by
  have hy' : ∀ n, y ^ p ^ (a * n) = y := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, hy]
  have hz' : ∀ n, z ^ p ^ (a * n) = z := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, hz]
  rw [← sub_eq_zero]
  refine eq_zero_of_mem_pow (J := J) fun n => ?_
  have h2 := pow_pow_sub_mem p hp h (a * n)
  rw [hy', hz'] at h2
  exact Ideal.pow_le_pow_right (Nat.le_succ_of_le (Nat.le_mul_of_pos_left n ha)) h2

theorem padicInt_ringHom_eq {A : Type} [CommRing A] {J : Ideal A} [IsHausdorff J A] (p : ℕ) [Fact p.Prime]
    (hp : (p : A) ∈ J) (φ ψ : ℤ_[p] →+* A) (u : ℤ_[p]) : φ u = ψ u := by
  rw [← sub_eq_zero]
  refine eq_zero_of_mem_pow (J := J) fun n => ?_
  obtain ⟨v, hv⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n u)
  have hu : u = ((u.appr n : ℕ) : ℤ_[p]) + v * (p : ℤ_[p]) ^ n := by linear_combination -hv
  have e : φ u - ψ u = (φ v - ψ v) * (p : A) ^ n := by
    rw [hu]; simp only [map_add (f := _), map_mul, map_pow, map_natCast]; ring
  rw [e]
  exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hp n)

end GlobalTheory.BSP.PairW

namespace GlobalTheory.BSP

open GlobalTheory.BSP.PairW

theorem hf_C_eq_of_pair : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K))
    (f g : Hom bk.prism B) (w : Wq l bk.a), BK.hf f (C w) = BK.hf g (C w) := by
  intro l _ K bk B f g w
  haveI := B.complete
  have hlJ : (l : B.A) ∈ Ideal.span {(l : B.A)} ⊔ B.I := Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
  have hI : ∀ v : Wq l bk.a, BK.hf f (C v) - BK.hf g (C v) ∈ B.I := by
    intro v
    have hr : Ideal.Quotient.mk bk.prism.I (C v : bk.prism.A) =
        bk.prism.str (bk.str.symm (Ideal.Quotient.mk _ (C v))) :=
      (bk.str.apply_symm_apply _).symm
    rw [← Ideal.Quotient.eq]
    exact (f.f_str _ _ hr).trans (g.f_str _ _ hr).symm
  have hT : ∀ x : Fq l bk.a, BK.hf f (C (WittVector.teichmuller l x)) = BK.hf g (C (WittVector.teichmuller l x)) := by
    intro x
    have ht : (WittVector.teichmuller l x) ^ l ^ bk.a = WittVector.teichmuller l x := by
      rw [← map_pow, Fq.pow_card]
    refine eq_of_pow_eq_self (J := Ideal.span {(l : B.A)} ⊔ B.I) l hlJ (Nat.pos_of_ne_zero (NeZero.ne bk.a))
      ?_ ?_ (Ideal.mem_sup_right (hI _))
    · rw [← map_pow, ← map_pow, ht]
    · rw [← map_pow, ← map_pow, ht]
  have hZ : ∀ u : ℤ_[l], BK.hf f (C (algebraMap ℤ_[l] (Wq l bk.a) u)) = BK.hf g (C (algebraMap ℤ_[l] (Wq l bk.a) u)) :=
    fun u => padicInt_ringHom_eq (J := Ideal.span {(l : B.A)} ⊔ B.I) l hlJ
      (((BK.hf f).comp C).comp (algebraMap ℤ_[l] (Wq l bk.a)))
      (((BK.hf g).comp C).comp (algebraMap ℤ_[l] (Wq l bk.a))) u
  have hw : w ∈ Submodule.span ℤ_[l] (Set.range (WittVector.teichmuller l : Fq l bk.a → Wq l bk.a)) := by
    rw [span_teich]; trivial
  induction hw using Submodule.span_induction with
  | mem x hx => obtain ⟨y, rfl⟩ := hx; exact hT y
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add (f := _), hx, hy]
  | smul c x _ hx => rw [Algebra.smul_def]; simp only [map_mul, hx, hZ]

end GlobalTheory.BSP
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrismHomsAgreeOnWittStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_prism_homs_agree_on_witt : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K)) (f g : Hom bk.prism B) (w : Wq l bk.a), BK.hf f (C w) = BK.hf g (C w) := by
  first | exact @GlobalTheory.BSP.hf_C_eq_of_pair | exact GlobalTheory.BSP.hf_C_eq_of_pair | (intros; apply GlobalTheory.BSP.hf_C_eq_of_pair <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComparisonMatrixFrobeniusDisc
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.Height

private theorem map_smul_ringHom' {n : Type} {α β : Type} [CommRing α] [CommRing β] (F : α →+* β) (c : α)
    (M : Matrix n n α) : (c • M).map F = F c • M.map F :=
  Matrix.map_smul' F c M (map_mul F)

private theorem smul_cancel' {n : Type} {D : Type} [CommRing D] {c : D} (hc : c ∈ nonZeroDivisors D)
    {M M' : Matrix n n D} (h : c • M = c • M') : M = M' := by
  ext i j
  have := congrFun (congrFun h i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  exact (mul_cancel_left_mem_nonZeroDivisors hc).1 this

private theorem alg' {n : Type} [Fintype n] [DecidableEq n] {D : Type} [CommRing D] (Φ : D →+* D)
    (L pf pg fE gE : D) (a N : ℕ) (xf xg Af Ag ε Fm : Matrix n n D)
    (h1f : (L * pf ^ N) • (xf * Af) = fE ^ (a + 2 * N) • (Fm * xf.map Φ))
    (h1g : (L * pg ^ N) • (xg * Ag) = gE ^ (a + 2 * N) • (Fm * xg.map Φ))
    (hR : gE ^ N • (xf * ε) = fE ^ N • xg) (hpf : Φ fE = pf) (hpg : Φ gE = pg) :
    (L * pf ^ N * pg ^ N * gE ^ N) • (xf * (gE ^ (a + N) • (Af * ε.map Φ))) =
      (L * pf ^ N * pg ^ N * gE ^ N) • (xf * (fE ^ (a + N) • (ε * Ag))) := by
  have hΦR : pg ^ N • (xf.map Φ * ε.map Φ) = pf ^ N • xg.map Φ := by
    have := congrArg (fun M => M.map Φ) hR
    simpa only [map_smul_ringHom', Matrix.map_mul, map_pow, hpf, hpg] using this
  calc (L * pf ^ N * pg ^ N * gE ^ N) • (xf * (gE ^ (a + N) • (Af * ε.map Φ)))
      = (pg ^ N * gE ^ (a + 2 * N)) • (((L * pf ^ N) • (xf * Af)) * ε.map Φ) := by
        simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc]; congr 1; ring
    _ = (pg ^ N * gE ^ (a + 2 * N)) • ((fE ^ (a + 2 * N) • (Fm * xf.map Φ)) * ε.map Φ) := by rw [h1f]
    _ = (gE ^ (a + 2 * N) * fE ^ (a + 2 * N)) • (Fm * (pg ^ N • (xf.map Φ * ε.map Φ))) := by
        simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc]; congr 1; ring
    _ = (gE ^ (a + 2 * N) * fE ^ (a + 2 * N)) • (Fm * (pf ^ N • xg.map Φ)) := by rw [hΦR]
    _ = (fE ^ (a + 2 * N) * pf ^ N) • (gE ^ (a + 2 * N) • (Fm * xg.map Φ)) := by
        simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc]; congr 1; ring
    _ = (fE ^ (a + 2 * N) * pf ^ N) • ((L * pg ^ N) • (xg * Ag)) := by rw [h1g]
    _ = (fE ^ (a + N) * L * pf ^ N * pg ^ N) • ((fE ^ N • xg) * Ag) := by
        simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc]; congr 1; ring
    _ = (fE ^ (a + N) * L * pf ^ N * pg ^ N) • ((gE ^ N • (xf * ε)) * Ag) := by rw [hR]
    _ = (L * pf ^ N * pg ^ N * gE ^ N) • (xf * (fE ^ (a + N) • (ε * Ag))) := by
        simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, Matrix.mul_assoc]; congr 1; ring

theorem rel_frob : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s), bk.IsPer τ → ∀ (B : Obj l ↥(OL K)) (f₀ : Hom bk.prism B), toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf f₀ bk.E) ∈ nonZeroDivisors (Disc l (BK.hf f₀ X) bk.ρ₀) → ∀ (f g : Hom bk.prism B) (ε : Matrix (Fin d) (Fin d) (Disc l (BK.hf f₀ X) bk.ρ₀)), ht.Rel (BK.hf f₀ X) f g ε → ∀ Φ : Disc l (BK.hf f₀ X) bk.ρ₀ →+* Disc l (BK.hf f₀ X) bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) B.D.φ Φ → toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf g bk.E) ^ (ht.a + s.N) • ((ht.A.map (BK.hf f)).map (toDisc l (BK.hf f₀ X) bk.ρ₀) * ε.map Φ) = toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf f bk.E) ^ (ht.a + s.N) • (ε * (ht.A.map (BK.hf g)).map (toDisc l (BK.hf f₀ X) bk.ρ₀)) := by
  intro l _ K bk d ρ τ s ht hτ B f₀ hE f g ε hR Φ hΦ

  have hρpos : 0 < bk.ρ₀ := by
    unfold BK.ρ₀; exact NNReal.rpow_pos (by exact_mod_cast (Fact.out : l.Prime).pos)
  have hρle : bk.ρ₀ ≤ 1 := by
    unfold BK.ρ₀
    exact NNReal.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast (Fact.out : l.Prime).one_lt.le)
      (by have : (0 : ℝ) ≤ 1 / (bk.Ep.natDegree : ℝ) := by positivity
          linarith)

  have hnS : ‖toDisc l (X : bk.S) bk.ρ₀ (frobS l bk.a X)‖ ≤ bk.ρ₀ := by
    rw [frobS_X]
    refine (norm_toDisc_pow_le (l := l) (u := (X : bk.S)) l hρpos).trans ?_
    exact pow_le_of_le_one (by positivity) (by exact_mod_cast hρle) (Fact.out : l.Prime).ne_zero
  have hΦS := isDiscMap_map (frobS l bk.a) hnS

  have key : ∀ (h : Hom bk.prism B) (Fh : Disc l (X : bk.S) bk.ρ₀ →+* Disc l (BK.hf f₀ X) bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) (BK.hf h) Fh →
      (((l : Disc l (BK.hf f₀ X) bk.ρ₀) ^ s.c₁ * toDisc l (BK.hf f₀ X) bk.ρ₀ (B.D.φ (BK.hf h bk.E)) ^ s.N) •
        (ht.bas.map Fh * (ht.A.map (BK.hf h)).map (toDisc l (BK.hf f₀ X) bk.ρ₀)) =
      toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf h bk.E) ^ (ht.a + 2 * s.N) • (s.F.map ((toDisc l (BK.hf f₀ X) bk.ρ₀).comp ((BK.hf h).comp C)) * (ht.bas.map Fh).map Φ)) := by
    intro h Fh hFh
    have hφ : ∀ x, BK.hf h (frobS l bk.a x) = B.D.φ (BK.hf h x) := fun x => h.f_φ x
    have c1 : IsDiscMap (l := _) (u := _) (ρ := _) (B.D.φ.comp (BK.hf h)) (Φ.comp Fh) :=
      ⟨fun x => by simp [hFh.ext, hΦ.ext], fun x => (hΦ.norm_le _).trans (hFh.norm_le _)⟩
    have c2 : IsDiscMap (l := _) (u := _) (ρ := _) (B.D.φ.comp (BK.hf h)) (Fh.comp (Disc.map (frobS l bk.a) hnS)) :=
      ⟨fun x => by simp [hFh.ext, hΦS.ext, hφ], fun x => (hFh.norm_le _).trans (hΦS.norm_le _)⟩
    have hc : Φ.comp Fh = Fh.comp (Disc.map (frobS l bk.a) hnS) := c1.unique c2
    have hP := congrArg (fun M => M.map Fh) (GlobalTheory.T.latticeBasis_frobenius_equation_disc l K bk d ρ τ s ht hτ _ hΦS)
    simp only [map_smul_ringHom', Matrix.map_mul, Matrix.map_map, map_mul, map_pow, map_natCast] at hP
    have eA : (ht.A.map (BK.hf h)).map (toDisc l (BK.hf f₀ X) bk.ρ₀) = ht.A.map (Fh ∘ toDisc l (X : bk.S) bk.ρ₀) := by
      ext i j; exact (hFh.ext _).symm
    have eF : s.F.map ((toDisc l (BK.hf f₀ X) bk.ρ₀).comp ((BK.hf h).comp C)) =
        s.F.map (Fh ∘ (toDisc l (X : bk.S) bk.ρ₀).comp C) := by
      ext i j; exact (hFh.ext _).symm
    have eB : (ht.bas.map Fh).map Φ = ht.bas.map (Fh ∘ Disc.map (frobS l bk.a) hnS) := by
      ext i j; exact RingHom.congr_fun hc _
    have e1 : toDisc l (BK.hf f₀ X) bk.ρ₀ (B.D.φ (BK.hf h bk.E)) = Fh (toDisc l (X : bk.S) bk.ρ₀ (frobS l bk.a bk.E)) :=
      ((hFh.ext _).trans (congrArg _ (hφ _))).symm
    have e2 : toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf h bk.E) = Fh (toDisc l (X : bk.S) bk.ρ₀ bk.E) := (hFh.ext _).symm
    simp only [eA, eF, eB, e1, e2]
    exact hP

  have hn := GlobalTheory.T.norm_breuilKisinHom_uniformizer_frobenius_le l K bk B f₀
  have hFf := isDiscMap_map (BK.hf f) (hn f).1
  have hFg := isDiscMap_map (BK.hf g) (hn g).1
  have h1f := key f _ hFf
  have h1g := key g _ hFg
  have hFm : s.F.map ((toDisc l (BK.hf f₀ X) bk.ρ₀).comp ((BK.hf g).comp C)) = s.F.map ((toDisc l (BK.hf f₀ X) bk.ρ₀).comp ((BK.hf f).comp C)) := by
    congr 1; funext w; simp [GlobalTheory.T.breuilKisin_prism_homs_agree_on_witt l K bk B f g w]
  simp only [hFm] at h1g

  have hreg : ∀ h : Hom bk.prism B, toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf h bk.E) ∈ nonZeroDivisors (Disc l (BK.hf f₀ X) bk.ρ₀) := by
    intro h
    obtain ⟨v, hv⟩ := (GlobalTheory.T.breuilKisin_two_homs_E_regular_associated l K bk B f₀ h).2.1
    have e : toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf h bk.E) = toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf f₀ bk.E) * toDisc l (BK.hf f₀ X) bk.ρ₀ (v : B.A) :=
      (congrArg _ hv).symm.trans (map_mul _ _ _)
    exact (congrArg (· ∈ nonZeroDivisors (Disc l (BK.hf f₀ X) bk.ρ₀)) e).mpr
      (Submonoid.mul_mem _ hE ((v.isUnit.map (toDisc l (BK.hf f₀ X) bk.ρ₀)).mem_nonZeroDivisors))
  have hunit : ∀ (h : Hom bk.prism B) (Fh : Disc l (X : bk.S) bk.ρ₀ →+* Disc l (BK.hf f₀ X) bk.ρ₀), IsDiscMap (l := _) (u := _) (ρ := _) (BK.hf h) Fh →
      IsUnit (toDisc l (BK.hf f₀ X) bk.ρ₀ (B.D.φ (BK.hf h bk.E))) := by
    intro h Fh hFh
    have := (GlobalTheory.T.isUnit_closedDisc_frobenius_eisenstein l K bk).map Fh
    have e : Fh (toDisc l (X : bk.S) bk.ρ₀ (frobS l bk.a bk.E)) = toDisc l (BK.hf f₀ X) bk.ρ₀ (B.D.φ (BK.hf h bk.E)) :=
      (hFh.ext _).trans (congrArg _ (h.f_φ _))
    exact (congrArg IsUnit e).mp this
  have hpf : Φ (toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf f bk.E)) = toDisc l (BK.hf f₀ X) bk.ρ₀ (B.D.φ (BK.hf f bk.E)) := hΦ.ext _
  have hpg : Φ (toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf g bk.E)) = toDisc l (BK.hf f₀ X) bk.ρ₀ (B.D.φ (BK.hf g bk.E)) := hΦ.ext _
  have hAlg := alg' Φ _ _ _ _ _ _ _ _ _ _ _ _ _ h1f h1g (hR _ _ hFf hFg) hpf hpg
  have hc : ((l : Disc l (BK.hf f₀ X) bk.ρ₀) ^ s.c₁ * toDisc l (BK.hf f₀ X) bk.ρ₀ (B.D.φ (BK.hf f bk.E)) ^ s.N *
      toDisc l (BK.hf f₀ X) bk.ρ₀ (B.D.φ (BK.hf g bk.E)) ^ s.N * toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf g bk.E) ^ s.N) ∈ nonZeroDivisors _ := by
    refine Submonoid.mul_mem _ (Submonoid.mul_mem _ (Submonoid.mul_mem _ ?_ ?_) ?_) (pow_mem (hreg g) _)
    · exact ((isUnit_l_disc l (BK.hf f₀ X) bk.ρ₀).pow _).mem_nonZeroDivisors
    · exact ((hunit f _ hFf).pow _).mem_nonZeroDivisors
    · exact ((hunit g _ hFg).pow _).mem_nonZeroDivisors
  have hM := smul_cancel' hc hAlg
  have hF0 : Disc.map (BK.hf f) (hn f).1 (toDisc l (X : bk.S) bk.ρ₀ bk.E) ∈ nonZeroDivisors _ :=
    (congrArg (· ∈ nonZeroDivisors (Disc l (BK.hf f₀ X) bk.ρ₀)) (hFf.ext bk.E)).mpr (hreg f)
  have := GlobalTheory.T.basis_matrix_map_cancel_left l K bk d ρ τ s ht _ _ hF0 _ _ hM
  exact this

end GlobalTheory.BSP.Height
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComparisonMatrixFrobeniusDiscStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comparisonMatrix_frobenius_disc : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s), bk.IsPer τ → ∀ (B : Obj l ↥(OL K)) (f₀ : Hom bk.prism B), toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf f₀ bk.E) ∈ nonZeroDivisors (Disc l (BK.hf f₀ X) bk.ρ₀) → ∀ (f g : Hom bk.prism B) (ε : Matrix (Fin d) (Fin d) (Disc l (BK.hf f₀ X) bk.ρ₀)), ht.Rel (BK.hf f₀ X) f g ε → ∀ Φ : Disc l (BK.hf f₀ X) bk.ρ₀ →+* Disc l (BK.hf f₀ X) bk.ρ₀, IsDiscMap (l := _) (u := _) (ρ := _) B.D.φ Φ → toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf g bk.E) ^ (ht.a + s.N) • ((ht.A.map (BK.hf f)).map (toDisc l (BK.hf f₀ X) bk.ρ₀) * ε.map Φ) = toDisc l (BK.hf f₀ X) bk.ρ₀ (BK.hf f bk.E) ^ (ht.a + s.N) • (ε * (ht.A.map (BK.hf g)).map (toDisc l (BK.hf f₀ X) bk.ρ₀)) := by
  first | exact @GlobalTheory.BSP.Height.rel_frob | exact GlobalTheory.BSP.Height.rel_frob | (intros; apply GlobalTheory.BSP.Height.rel_frob <;> assumption)
end
