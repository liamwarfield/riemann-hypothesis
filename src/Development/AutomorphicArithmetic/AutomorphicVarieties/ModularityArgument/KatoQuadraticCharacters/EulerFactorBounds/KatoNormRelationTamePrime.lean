module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.CohApi
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SXiCoh
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.XiTame
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.LineCoh
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.TopRel
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeLevelRows.ExistsRowsHeckeCompatibleLevelPrimePow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeLevelRows.HeckeMatrixMemGammaZeroInfAndExistsUnitInv

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.XiHecke
open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

namespace UpperTheory.V.Z.Kato.Nb.XiHecke

private theorem vc {M k : ℕ} [NeZero M] (h : k ∣ M) (a : ZMod M) :
    ((a.val : ℕ) : ZMod k) = ZMod.castHom h (ZMod k) a := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]

private theorem ent {M k : ℕ} [NeZero M] (hk : k ∣ M) (h : Matrix (Fin 2) (Fin 2) ℤ) (m : Matrix (Fin 2) (Fin 2) (ZMod M))
    (i j : Fin 2) : (((m * h.map (Int.castRingHom (ZMod M))) i j).val : ZMod k) =
      ((m i 0).val : ZMod k) * (h 0 j : ZMod k) + ((m i 1).val : ZMod k) * (h 1 j : ZMod k) := by
  have h0 : (m * h.map (Int.castRingHom (ZMod M))) i j = m i 0 * (h 0 j : ZMod M) + m i 1 * (h 1 j : ZMod M) := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [h0, vc hk, vc hk, vc hk, map_add (f := _), map_mul, map_mul, map_intCast, map_intCast]

private theorem cnd_iff (l N M : ℕ) [Fact l.Prime] [NeZero M] (hN : N ∣ M) (hl : l ∣ M) (g : SL(2, ℤ))
    (h : Matrix (Fin 2) (Fin 2) ℤ) (hN1 : ((h 1 0 : ℤ) : ZMod N) = 0) (hl1 : ((h 1 0 : ℤ) : ZMod l) = 0)
    (hN0 : ((h 0 0 : ℤ) : ZMod N) = 1) (hl0 : ((h 0 0 : ℤ) : ZMod l) ≠ 0) (m : Matrix (Fin 2) (Fin 2) (ZMod M)) :
    Cnd l N g m ↔ Cnd l N g (m * h.map (Int.castRingHom (ZMod M))) := by
  unfold Cnd
  rw [ent hN, ent hN, ent hl, ent hl, hN1, hl1, hN0]
  simp only [mul_zero, add_zero, mul_one]
  rw [← mul_assoc, ← mul_assoc, mul_left_inj' hl0]

private theorem wt_dvd (l n M w p : ℕ) [Fact l.Prime] [NeZero M] (hl : l ^ n ∣ M) (h : Matrix (Fin 2) (Fin 2) ℤ)
    (d d' : ZMod M) (hd : d = p * d') (m : Matrix (Fin 2) (Fin 2) (ZMod M)) (u : Fin 2 → ℤ_[l]) :
    (l : ℤ_[l]) ^ n ∣ (d.val : ℤ_[l]) * (((m 0 0).val : ℤ_[l]) * (mZl l h *ᵥ u) 0 + ((m 0 1).val : ℤ_[l]) * (mZl l h *ᵥ u) 1) ^ w -
      (p : ℤ_[l]) * ((d'.val : ℤ_[l]) * ((((m * h.map (Int.castRingHom (ZMod M))) 0 0).val : ℤ_[l]) * u 0 +
        (((m * h.map (Int.castRingHom (ZMod M))) 0 1).val : ℤ_[l]) * u 1) ^ w) := by
  rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker]
  have ed : (d.val : ZMod (l ^ n)) = p * (d'.val : ZMod (l ^ n)) := by
    rw [vc hl d, hd, map_mul, map_natCast, ← vc hl]
  have ev : ∀ i, (mZl l h *ᵥ u) i = (h i 0 : ℤ_[l]) * u 0 + (h i 1 : ℤ_[l]) * u 1 := by
    intro i
    simp [mZl, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [ev, ev]
  simp only [map_sub, map_mul, map_pow, map_add (f := _), map_natCast, map_intCast]
  rw [ed, ent hl, ent hl, sub_eq_zero, mul_assoc]
  congr 3
  ring

private theorem cd_row (N M₀ M p : ℕ) [NeZero N] [NeZero M₀] [NeZero M] (hM : M = N * M₀) (h h' : Matrix (Fin 2) (Fin 2) ℤ)
    (hN1 : ((h 1 0 : ℤ) : ZMod N) = 0) (hc : !![(N : ℤ), 0; 0, 1] * h = h' * !![(N : ℤ), 0; 0, 1]) (hd : h'.det = p)
    (m : Matrix (Fin 2) (Fin 2) (ZMod M)) (hm : ((m 1 0).val : ZMod N) = 0) (x : Row M₀) :
    (x ᵥ* cD N M₀ (m * h.map (Int.castRingHom (ZMod M)))) ᵥ* h'.adjugate.map (Int.castRingHom (ZMod M₀)) =
      ((p : ZMod M₀) • x) ᵥ* cD N M₀ m := by
  obtain ⟨d1, -, -, d4⟩ := sCdFacts N M₀ M hM
  have hN : N ∣ M := hM ▸ dvd_mul_right N M₀
  rw [d1 _ _ hm ?_, d4 _ _ hc, Matrix.vecMul_vecMul, Matrix.mul_assoc, ← Matrix.map_mul, Matrix.mul_adjugate, hd]
  · have : ((p : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ)).map (Int.castRingHom (ZMod M₀)) = (p : ZMod M₀) • 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.natCast_apply]
    rw [this, Matrix.mul_smul, Matrix.mul_one, Matrix.vecMul_smul, Matrix.smul_vecMul]
  · rw [vc hN, Matrix.map_apply, eq_intCast, map_intCast]; exact hN1

section

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n N : ℕ)

private theorem cls_step (hN : 0 < N) (h h' : Matrix (Fin 2) (Fin 2) ℤ) (hd : 0 < h.det)
    (hc : !![(N : ℤ), 0; 0, 1] * h = h' * !![(N : ℤ), 0; 0, 1])
    (f : X.Kˣ) (k k' : ℤ_[l]) (hk : (l : ℤ_[l]) ^ n ∣ k - k') :
    AdicCompletion.eval (idl l) (X.Kl l) n
      (k • X.kmap l (X.sl (toGQ h)).toRingEquiv (clsK X l n (slD X N (f : X.K))) -
        k' • clsK X l n (slD X N (slU X (toGQ h') f : X.K))) = 0 := by
  obtain ⟨c1, -, -, c4, c5, -⟩ := sCls Ω ε X l n
  obtain ⟨-, -, -, -, a5, -⟩ := sApi Ω ε X l n
  obtain ⟨-, s2, -⟩ := sSlD Ω ε X N hN
  have r1 := c5 (X.sl (toGQ h)).toRingEquiv _ _ (c1 (slU X (toGQ !![(N : ℤ), 0; 0, 1]) f))
  have r2 := c1 (slU X (toGQ !![(N : ℤ), 0; 0, 1]) (slU X (toGQ h') f))
  have r3 := c4 _ _ _ _ r1 r2 (by
    refine ⟨1, ?_⟩
    rw [one_pow, mul_one]
    apply Units.ext
    exact s2 _ _ hd hc (f : X.K))
  have r4 := a5 k k' (X.kmap l (X.sl (toGQ h)).toRingEquiv (clsK X l n (slD X N (f : X.K)))) hk
  have r5 : AdicCompletion.eval (idl l) (X.Kl l) n
      (X.kmap l (X.sl (toGQ h)).toRingEquiv (clsK X l n (slD X N (f : X.K))) -
        clsK X l n (slD X N (slU X (toGQ h') f : X.K))) = 0 := r3
  rw [← sub_add_sub_cancel _ (k' • X.kmap l (X.sl (toGQ h)).toRingEquiv (clsK X l n (slD X N (f : X.K)))),
    map_add, r4, ← smul_sub, map_smul, r5, smul_zero, add_zero]

private theorem cls_prod {ι : Type} (S : Finset ι) (f : ι → X.Kˣ) :
    AdicCompletion.eval (idl l) (X.Kl l) n
      (∑ i ∈ S, clsK X l n (slD X N (f i : X.K)) - clsK X l n (slD X N ((∏ i ∈ S, f i : X.Kˣ) : X.K))) = 0 := by
  obtain ⟨c1, c2, c3, c4, -⟩ := sCls Ω ε X l n
  have r : Rep X l n (slU X (toGQ !![(N : ℤ), 0; 0, 1]) (∏ i ∈ S, f i)) (∑ i ∈ S, clsK X l n (slD X N (f i : X.K))) := by
    induction S using Finset.induction_on with
    | empty => simpa using c3 1 _ 0 (c1 1)
    | insert i S hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, map_mul]
      exact (c2 _ _ _ _ (c1 (slU X (toGQ !![(N : ℤ), 0; 0, 1]) (f i))) ih).1
  exact c4 _ _ _ _ r (c1 (slU X (toGQ !![(N : ℤ), 0; 0, 1]) (∏ i ∈ S, f i))) ⟨1, by simp⟩

private theorem xi_prod (M₀ M w : ℕ) [NeZero M] (g : SL(2, ℤ)) (x y : Row M₀) (P : (ZMod M)ˣ → Prop) {ι : Type} (S : Finset ι)
    (f : ι → Fam X M₀) : CgF X l n (∑ i ∈ S, Xi X l n N M₀ M w g x y P (f i))
      (Xi X l n N M₀ M w g x y P fun x y => ∏ i ∈ S, f i x y) := by
  intro u
  rw [Finset.sum_apply]
  unfold Xi
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.sum_comm, ← Finset.sum_sub_distrib, map_sum]
  refine Finset.sum_eq_zero fun m _ => ?_
  rw [← Finset.smul_sum, ← smul_sub, map_smul, cls_prod, smul_zero]

private theorem step (M₀ M w : ℕ) [NeZero N] [NeZero M₀] [NeZero M] (g : SL(2, ℤ)) (L : Lev l n N M₀ M g) (p : ℕ) (hp : 0 < p)
    (q : (ZMod M)ˣ) (hq : (q : ZMod M) = p) (x y : Row M₀) (P : (ZMod M)ˣ → Prop) (a : Fam X M₀)
    (h h' : Matrix (Fin 2) (Fin 2) ℤ) (hc : !![(N : ℤ), 0; 0, 1] * h = h' * !![(N : ℤ), 0; 0, 1]) (hd : h.det = p)
    (hN1 : ((h 1 0 : ℤ) : ZMod N) = 0) (hl1 : ((h 1 0 : ℤ) : ZMod l) = 0) (hN0 : ((h 0 0 : ℤ) : ZMod N) = 1) :
    CgF X l n (X.act l h (Xi X l n N M₀ M w g ((p : ZMod M₀) • x) ((p : ZMod M₀) • y) (fun z => P (z * q)) a))
      ((p : ℤ_[l]) • Xi X l n N M₀ M w g x y P fun x y => slU X (toGQ h')
        (a (x ᵥ* h'.adjugate.map (Int.castRingHom (ZMod M₀))) (y ᵥ* h'.adjugate.map (Int.castRingHom (ZMod M₀))))) := by
  intro u
  have hN : N ∣ M := L.eq ▸ dvd_mul_right N M₀
  have hln : l ^ n ∣ M := L.eq ▸ L.dl.mul_left N
  have hl : l ∣ M := (dvd_pow_self l (by have := L.pos; omega)).trans hln
  have hd' : h'.det = p := by
    have := congrArg Matrix.det hc
    rw [Matrix.det_mul, Matrix.det_mul, mul_comm, hd] at this
    refine (mul_right_cancel₀ ?_ this).symm
    simpa using NeZero.ne N
  have hl0 : ((h 0 0 : ℤ) : ZMod l) ≠ 0 := by
    intro h0
    have e := congrArg (Int.cast : ℤ → ZMod l) hd
    rw [Matrix.det_fin_two] at e
    push_cast at e
    rw [h0, hl1, zero_mul, mul_zero, sub_zero] at e
    have := (q.isUnit.map (ZMod.castHom hl (ZMod l))).ne_zero
    rw [hq, map_natCast] at this
    exact this e.symm
  have hdm : (h.map (Int.castRingHom (ZMod M))).det = q := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hd, hq, map_natCast]
  let D : GL (Fin 2) (ZMod M) := Matrix.GeneralLinearGroup.mk'' (h.map (Int.castRingHom (ZMod M))) (hdm ▸ q.isUnit)
  have hrel : ∀ m : GL (Fin 2) (ZMod M), ((Equiv.mulRight D m : GL (Fin 2) (ZMod M)) : Matrix (Fin 2) (Fin 2) (ZMod M)) =
      (m : Matrix (Fin 2) (Fin 2) (ZMod M)) * h.map (Int.castRingHom (ZMod M)) := fun m => rfl
  have hdet : ∀ m, Matrix.GeneralLinearGroup.det (Equiv.mulRight D m) = Matrix.GeneralLinearGroup.det m * q := by
    intro m
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, hrel, Matrix.det_mul, hdm]
    rfl
  show AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l _ (Xi X l n N M₀ M w g _ _ _ a _) - (p : ℤ_[l]) • Xi X l n N M₀ M w g x y P _ u) = 0
  unfold Xi
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.smul_sum, map_sum, map_sub, map_sum, map_sum, sub_eq_zero]
  refine Finset.sum_equiv (Equiv.mulRight D) (fun m => ?_) (fun m hm => ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hdet m, hrel, ← cnd_iff l N M hN hl g h hN1 hl1 hN0 hl0]
  · have hm1 := (Finset.mem_filter.1 hm).2.1
    rw [← sub_eq_zero, ← map_sub, map_smul, smul_smul, hrel]
    beta_reduce
    rw [cd_row N M₀ M p L.eq h h' hN1 hc hd' _ hm1.1, cd_row N M₀ M p L.eq h h' hN1 hc hd' _ hm1.1]
    refine cls_step X l n N (NeZero.pos N) h h' (by rw [hd]; exact_mod_cast hp) hc _ _ _ ?_
    refine wt_dvd l n M w p hln h _ _ ?_ _ u
    rw [hdet m, ← hq, ← Units.val_mul]
    congr 1
    rw [mul_inv, mul_left_comm, mul_inv_cancel, mul_one]

end

private theorem diam_spec (N l p : ℕ) (h : Nat.Coprime p (N * l)) : IsDiam N l p (sgD N l p) := by
  apply Classical.epsilon_spec
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 h
  refine ⟨⟨!![a, -b; ((N * l : ℕ) : ℤ), p], ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · rw [Matrix.det_fin_two_of]; linear_combination hab
  · exact CongruenceSubgroup.Gamma0_mem.2 (by simp)
  · exact CongruenceSubgroup.Gamma0_mem.2 (by simp)
  · simp [en]

end UpperTheory.V.Z.Kato.Nb.XiHecke

open UpperTheory.V.Z.Kato.Nb.XiHecke in
theorem UpperTheory.V.Z.Kato.Nb.sXiHecke :
    UpperTheory.V.Z.Kato.Nb.SXiHecke := by
  intro Ω _ _ _ ε X l _ n N M₀ M w _ _ _ g L p hp q hq x y P a
  obtain ⟨aE, a2, a3, a4, -⟩ := sApi Ω ε X l n
  have hco : Nat.Coprime p (N * l) := by
    have h1 : Nat.Coprime p M := (ZMod.isUnit_iff_coprime p M).1 (hq ▸ q.isUnit)
    refine Nat.Coprime.coprime_dvd_right ?_ h1
    rw [L.eq]
    exact Nat.mul_dvd_mul_left N ((dvd_pow_self l (by have := L.pos; omega)).trans L.dl)
  obtain ⟨⟨s1, s2⟩, s3⟩ := diam_spec N l p hco
  have hsN : ((en (sgD N l p) 1 0 : ℤ) : ZMod N) = 0 := CongruenceSubgroup.Gamma0_mem.1 s1
  have hsl : ((en (sgD N l p) 1 0 : ℤ) : ZMod l) = 0 := CongruenceSubgroup.Gamma0_mem.1 s2
  have hdet : en (sgD N l p) 0 0 * en (sgD N l p) 1 1 - en (sgD N l p) 0 1 * en (sgD N l p) 1 0 = 1 := by
    have := (sgD N l p).det_coe
    rwa [Matrix.det_fin_two] at this
  have hs : (sgD N l p : Matrix (Fin 2) (Fin 2) ℤ) * !![(p : ℤ), 0; 0, 1] =
      !![en (sgD N l p) 0 0 * p, en (sgD N l p) 0 1; en (sgD N l p) 1 0 * p, en (sgD N l p) 1 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, en]
  refine aE.trans ?_ (a3 (p : ℤ_[l]) _ _ (xi_prod X l n N M₀ M w g x y P Finset.univ fun o x y => slU X (toGQ (hP l p N o))
    (a (x ᵥ* (hP l p N o).adjugate.map (Int.castRingHom (ZMod M₀))) (y ᵥ* (hP l p N o).adjugate.map (Int.castRingHom (ZMod M₀))))))
  rw [Finset.smul_sum, Fintype.sum_option, add_comm, Tower.heckeT, LinearMap.add_apply, LinearMap.sum_apply,
    Finset.sum_range, hs]
  refine (a2 _ _ _ _ (a4 _ _ _ _ fun j _ => ?_) ?_).1
  · refine step X l n N M₀ M w g L p hp.out.pos q hq x y P a _ _ ?_ ?_ ?_ ?_ ?_
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [hP, Matrix.mul_apply, Fin.sum_univ_two]
    all_goals simp [Matrix.det_fin_two]
  · refine step X l n N M₀ M w g L p hp.out.pos q hq x y P a _ _ ?_ ?_ ?_ ?_ ?_
    · have := Int.ediv_mul_cancel ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hsN)
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hP, Matrix.mul_apply, Fin.sum_univ_two]
      · ring
      · linear_combination -(p : ℤ) * this
    · rw [Matrix.det_fin_two_of]; linear_combination (p : ℤ) * hdet
    · simp [hsN]
    · simp [hsl]
    · have := congrArg (Int.cast : ℤ → ZMod N) hdet
      push_cast at this
      rw [hsN, s3] at this
      simpa using this
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.ClsStep
open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

namespace UpperTheory.V.Z.Kato.Nb.XiAction

private theorem vc {M k : ℕ} [NeZero M] (h : k ∣ M) (a : ZMod M) :
    ((a.val : ℕ) : ZMod k) = ZMod.castHom h (ZMod k) a := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]

private theorem cnd_iff (l N M : ℕ) [NeZero M] (hN : N ∣ M) (hl : l ∣ M) (g δ : SL(2, ℤ))
    (hδN : ((en δ 1 0 : ℤ) : ZMod N) = 0) (hδl : ((en δ 1 0 : ℤ) : ZMod l) = 0) (ν : (ZMod M)ˣ)
    (h1 : ((ν : ZMod M).val : ZMod N) = (en δ 0 0 : ZMod N)) (h2 : ((ν : ZMod M).val : ZMod l) = 1)
    (m m' : Matrix (Fin 2) (Fin 2) (ZMod M))
    (h : m * (δ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom (ZMod M)) = (ν : ZMod M) • m') :
    Cnd l N g m ↔ Cnd l N g m' := by
  have e : ∀ i, m i 0 * (en δ 0 0 : ZMod M) + m i 1 * (en δ 1 0 : ZMod M) = (ν : ZMod M) * m' i 0 := by
    intro i
    have := congrFun (congrFun h i) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two, en] using this
  have hdet : en δ 0 0 * en δ 1 1 - en δ 0 1 * en δ 1 0 = 1 := by
    have := δ.det_coe
    rwa [Matrix.det_fin_two] at this
  have uN : (en δ 0 0 : ZMod N) * (en δ 1 1 : ZMod N) = 1 := by
    have := congrArg (Int.cast : ℤ → ZMod N) hdet
    push_cast at this
    rw [hδN] at this; simpa using this
  have ul : (en δ 0 0 : ZMod l) * (en δ 1 1 : ZMod l) = 1 := by
    have := congrArg (Int.cast : ℤ → ZMod l) hdet
    push_cast at this
    rw [hδl] at this; simpa using this
  have eN : ∀ i, ((m i 0).val : ZMod N) = ((m' i 0).val : ZMod N) := by
    intro i
    have := congrArg (ZMod.castHom hN (ZMod N)) (e i)
    rw [map_add (f := _), map_mul, map_mul, map_mul, map_intCast, map_intCast, hδN, ← vc hN, ← vc hN, ← vc hN, ← vc hN, h1] at this
    linear_combination (en δ 1 1 : ZMod N) * this - (((m i 0).val : ZMod N) - ((m' i 0).val : ZMod N)) * uN
  have el : ∀ i, ((m i 0).val : ZMod l) * (en δ 0 0 : ZMod l) = ((m' i 0).val : ZMod l) := by
    intro i
    have := congrArg (ZMod.castHom hl (ZMod l)) (e i)
    rw [map_add (f := _), map_mul, map_mul, map_mul, map_intCast, map_intCast, hδl, ← vc hl, ← vc hl, ← vc hl, ← vc hl, h2] at this
    linear_combination this
  unfold Cnd
  rw [eN 0, eN 1, ← el 0, ← el 1]
  refine and_congr Iff.rfl (and_congr Iff.rfl ⟨fun h3 => ?_, fun h3 => ?_⟩)
  · linear_combination (en δ 0 0 : ZMod l) * h3
  · linear_combination (en δ 1 1 : ZMod l) * h3 -
      ((en g 1 0 : ZMod l) * ((m 0 0).val : ZMod l) - (en g 0 0 : ZMod l) * ((m 1 0).val : ZMod l)) * ul

private theorem wt_dvd (l n M w : ℕ) [Fact l.Prime] [NeZero M] (hl : l ^ n ∣ M) (δ : Matrix (Fin 2) (Fin 2) ℤ)
    (ν : ZMod M) (h2 : (ν.val : ZMod (l ^ n)) = 1) (d d' : ZMod M) (hd : d' = ν ^ 2 * d)
    (m m' : Matrix (Fin 2) (Fin 2) (ZMod M))
    (h : m * δ.map (Int.castRingHom (ZMod M)) = ν • m') (u : Fin 2 → ℤ_[l]) :
    (l : ℤ_[l]) ^ n ∣ (d.val : ℤ_[l]) * (((m 0 0).val : ℤ_[l]) * (mZl l δ *ᵥ u) 0 + ((m 0 1).val : ℤ_[l]) * (mZl l δ *ᵥ u) 1) ^ w -
      (d'.val : ℤ_[l]) * (((m' 0 0).val : ℤ_[l]) * u 0 + ((m' 0 1).val : ℤ_[l]) * u 1) ^ w := by
  rw [← Ideal.mem_span_singleton, ← PadicInt.ker_toZModPow, RingHom.mem_ker]
  have e : ∀ j, ((m 0 0).val : ZMod (l ^ n)) * (δ 0 j : ZMod (l ^ n)) + ((m 0 1).val : ZMod (l ^ n)) * (δ 1 j : ZMod (l ^ n)) =
      ((m' 0 j).val : ZMod (l ^ n)) := by
    intro j
    have h0 : m 0 0 * (δ 0 j : ZMod M) + m 0 1 * (δ 1 j : ZMod M) = ν * m' 0 j := by
      have := congrFun (congrFun h 0) j
      simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
    have := congrArg (ZMod.castHom hl (ZMod (l ^ n))) h0
    rw [map_add (f := _), map_mul, map_mul, map_mul, map_intCast, map_intCast, ← vc hl, ← vc hl, ← vc hl, ← vc hl, h2, one_mul] at this
    exact this
  have ed : (d'.val : ZMod (l ^ n)) = (d.val : ZMod (l ^ n)) := by
    rw [vc hl d', hd, map_mul, map_pow, ← vc hl, ← vc hl, h2, one_pow, one_mul]
  have ev : ∀ i, (mZl l δ *ᵥ u) i = (δ i 0 : ℤ_[l]) * u 0 + (δ i 1 : ℤ_[l]) * u 1 := by
    intro i
    simp [mZl, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [ev, ev]
  simp only [map_sub, map_mul, map_pow, map_add (f := _), map_natCast, map_intCast]
  rw [ed, ← e 0, ← e 1, sub_eq_zero]
  congr 2
  ring

private theorem cls_step {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε)
    (l : ℕ) [Fact l.Prime] (n N : ℕ) (hN : 0 < N) (δ δ' : SL(2, ℤ))
    (hc : !![(N : ℤ), 0; 0, 1] * (δ : Matrix (Fin 2) (Fin 2) ℤ) = (δ' : Matrix (Fin 2) (Fin 2) ℤ) * !![(N : ℤ), 0; 0, 1])
    (f f' : X.Kˣ) (hf : Cgr (l ^ n) (slU X (ofSL δ') f) f') (k k' : ℤ_[l]) (hk : (l : ℤ_[l]) ^ n ∣ k - k') :
    AdicCompletion.eval (idl l) (X.Kl l) n
      (k • X.kmap l (X.sl (toGQ (δ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv (clsK X l n (slD X N (f : X.K))) -
        k' • clsK X l n (slD X N (f' : X.K))) = 0 := by
  obtain ⟨c1, -, -, c4, c5, -⟩ := sCls Ω ε X l n
  obtain ⟨-, -, -, -, a5, -⟩ := sApi Ω ε X l n
  obtain ⟨-, s2, s3, -⟩ := sSlD Ω ε X N hN
  have r1 := c5 (X.sl (toGQ (δ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv _ _ (c1 (slU X (toGQ !![(N : ℤ), 0; 0, 1]) f))
  have r2 := c1 (slU X (toGQ !![(N : ℤ), 0; 0, 1]) f')
  have r3 := c4 _ _ _ _ r1 r2 (by
    obtain ⟨h, hh⟩ := hf
    refine ⟨slU X (toGQ !![(N : ℤ), 0; 0, 1]) h, ?_⟩
    rw [← map_pow, ← map_mul, ← hh]
    apply Units.ext
    have := s2 _ _ (by rw [δ.det_coe]; exact one_pos) hc (f : X.K)
    rw [s3 δ'] at this
    exact this)
  have r4 := a5 k k' (X.kmap l (X.sl (toGQ (δ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv (clsK X l n (slD X N (f : X.K)))) hk
  have r5 : AdicCompletion.eval (idl l) (X.Kl l) n
      (X.kmap l (X.sl (toGQ (δ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv (clsK X l n (slD X N (f : X.K))) -
        clsK X l n (slD X N (f' : X.K))) = 0 := r3
  rw [← sub_add_sub_cancel _ (k' • X.kmap l (X.sl (toGQ (δ : Matrix (Fin 2) (Fin 2) ℤ))).toRingEquiv (clsK X l n (slD X N (f : X.K)))),
    map_add, r4, ← smul_sub, map_smul, r5, smul_zero, add_zero]

private theorem conj_ex (N : ℕ) (δ : SL(2, ℤ)) (h : (N : ℤ) ∣ en δ 1 0) : ∃ δ' : SL(2, ℤ),
    !![(N : ℤ), 0; 0, 1] * (δ : Matrix (Fin 2) (Fin 2) ℤ) = (δ' : Matrix (Fin 2) (Fin 2) ℤ) * !![(N : ℤ), 0; 0, 1] := by
  obtain ⟨c, hc⟩ := h
  have hdet : en δ 0 0 * en δ 1 1 - en δ 0 1 * en δ 1 0 = 1 := by
    have := δ.det_coe
    rwa [Matrix.det_fin_two] at this
  refine ⟨⟨!![en δ 0 0, N * en δ 0 1; c, en δ 1 1], ?_⟩, ?_⟩
  · rw [Matrix.det_fin_two_of, ← hdet, hc]; ring
  · unfold en at hc
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, en, hc, mul_comm]

private theorem cd_row (N M₀ M : ℕ) [NeZero N] [NeZero M₀] [NeZero M] (hM : M = N * M₀) (δ δ' : SL(2, ℤ))
    (hδN : ((en δ 1 0 : ℤ) : ZMod N) = 0)
    (hc : !![(N : ℤ), 0; 0, 1] * (δ : Matrix (Fin 2) (Fin 2) ℤ) = (δ' : Matrix (Fin 2) (Fin 2) ℤ) * !![(N : ℤ), 0; 0, 1])
    (ν : ZMod M) (m m' : Matrix (Fin 2) (Fin 2) (ZMod M)) (hm : ((m 1 0).val : ZMod N) = 0) (hm' : ((m' 1 0).val : ZMod N) = 0)
    (h : m * (δ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom (ZMod M)) = ν • m') (x : Row M₀) :
    rt (x ᵥ* cD N M₀ m) δ' = ((ν.val : ZMod M₀) • x) ᵥ* cD N M₀ m' := by
  obtain ⟨d1, -, -, d4⟩ := sCdFacts N M₀ M hM
  have hN : N ∣ M := hM ▸ dvd_mul_right N M₀
  have e1 : ν • m' = !![ν, 0; 0, ν] * m' := by
    ext i j
    fin_cases i <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have e2 : x ᵥ* cD N M₀ (!![ν, 0; 0, ν] : Matrix (Fin 2) (Fin 2) (ZMod M)) = (ν.val : ZMod M₀) • x := by
    funext j
    fin_cases j <;> simp [cD, Matrix.vecMul, dotProduct, Fin.sum_univ_two, mul_comm]
  unfold rt
  rw [← d4 _ _ hc, Matrix.vecMul_vecMul, ← d1 _ _ hm ?_, h, e1, d1 _ _ ?_ hm', ← Matrix.vecMul_vecMul, e2]
  · simp
  · rw [vc hN, Matrix.map_apply, eq_intCast, map_intCast]; exact hδN

end UpperTheory.V.Z.Kato.Nb.XiAction

open UpperTheory.V.Z.Kato.Nb.XiAction in
theorem UpperTheory.V.Z.Kato.Nb.sXiAct :
    UpperTheory.V.Z.Kato.Nb.SXiAct := by
  intro Ω _ _ _ ε X l _ n N M₀ M w _ _ _ g L x y hxy P a ha δ hδ ν h1 h2 hP u
  have hN : N ∣ M := L.eq ▸ dvd_mul_right N M₀
  have hln : l ^ n ∣ M := L.eq ▸ L.dl.mul_left N
  have hl1 : l ∣ l ^ n := dvd_pow_self l (by have := L.pos; omega)
  have hδN : ((en δ 1 0 : ℤ) : ZMod N) = 0 := CongruenceSubgroup.Gamma0_mem.1 hδ.1
  have hδl : ((en δ 1 0 : ℤ) : ZMod l) = 0 := CongruenceSubgroup.Gamma0_mem.1 hδ.2
  have h2' : ((ν : ZMod M).val : ZMod l) = 1 := by
    have := congrArg (ZMod.castHom hl1 (ZMod l)) h2
    rwa [map_natCast, map_one] at this
  obtain ⟨δ', hc⟩ := conj_ex N δ ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hδN)
  let D : GL (Fin 2) (ZMod M) := Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) δ)
  let S : GL (Fin 2) (ZMod M) := Matrix.GeneralLinearGroup.scalar (Fin 2) ν
  let e : GL (Fin 2) (ZMod M) ≃ GL (Fin 2) (ZMod M) := (Equiv.mulRight D).trans (Equiv.mulLeft S⁻¹)
  have he : ∀ m, m * D = S * e m := fun m => by simp [e]
  have hrel : ∀ m : GL (Fin 2) (ZMod M), (m : Matrix (Fin 2) (Fin 2) (ZMod M)) *
      (δ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom (ZMod M)) = (ν : ZMod M) • (e m : Matrix (Fin 2) (Fin 2) (ZMod M)) := by
    intro m
    have := congrArg (fun z : GL (Fin 2) (ZMod M) => (z : Matrix (Fin 2) (Fin 2) (ZMod M))) (he m)
    simp only [Units.val_mul] at this
    rw [Matrix.smul_eq_diagonal_mul]
    exact this
  have hdet : ∀ m, Matrix.GeneralLinearGroup.det m = Matrix.GeneralLinearGroup.det (e m) * ν ^ 2 := by
    intro m
    apply Units.ext
    have := congrArg Matrix.det (hrel m)
    rw [Matrix.det_mul, Matrix.det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, δ.det_coe, map_one, mul_one] at this
    simp only [Matrix.GeneralLinearGroup.val_det_apply, Units.val_mul, Units.val_pow_eq_pow_val]
    rw [this, mul_comm]; simp
  have hcnd := fun m : GL (Fin 2) (ZMod M) => cnd_iff l N M hN (hl1.trans hln) g δ hδN hδl ν h1 h2' _ _ (hrel m)
  show AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l _ (Xi X l n N M₀ M w g x y P a _) - _) = 0
  unfold Xi
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sub, map_sum, map_sum, sub_eq_zero]
  refine Finset.sum_equiv e (fun m => ?_) (fun m hm => ?_)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hcnd m, hdet m, hP]
  · have hm1 := (Finset.mem_filter.1 hm).2.1
    have hm2 := (hcnd m).1 hm1
    rw [← sub_eq_zero, ← map_sub, map_smul]
    refine cls_step X l n N (NeZero.pos N) δ δ' hc _ _ ?_ _ _ ?_
    · rw [← cd_row N M₀ M L.eq δ δ' hδN hc _ _ _ hm1.1 hm2.1 (hrel m), ← cd_row N M₀ M L.eq δ δ' hδN hc _ _ _ hm1.1 hm2.1 (hrel m)]
      exact (ha _ _ ((sCdFacts N M₀ M L.eq).2.2.1 m hm1.1 x y hxy)).2 δ'
    · refine wt_dvd l n M w hln _ ν h2 _ _ ?_ _ _ (hrel m) u
      rw [hdet m, ← Units.val_pow_eq_pow_val, ← Units.val_mul]
      congr 1
      rw [mul_inv, mul_comm _ (ν ^ 2)⁻¹, mul_inv_cancel_left]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.ProdPairs
open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

namespace UpperTheory.V.Z.Kato.Nb

private theorem tp_inj (p M : ℕ) [NeZero p] [NeZero M] (s t : ZMod p)
    (h : ((M * s.val : ℕ) : ZMod (p * M)) = ((M * t.val : ℕ) : ZMod (p * M))) : s = t := by
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hlt : ∀ u : ZMod p, M * u.val < p * M := fun u => by
    rw [mul_comm p M]
    exact (Nat.mul_lt_mul_left hM).2 (ZMod.val_lt u)
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (hlt s), Nat.mod_eq_of_lt (hlt t)] at h
  exact ZMod.val_injective p (Nat.eq_of_mul_eq_mul_left hM h)

private theorem tp_surj (p M : ℕ) [NeZero p] [NeZero M] (w : ZMod (p * M))
    (h : ZMod.castHom (dvd_mul_left M p) (ZMod M) w = 0) : ∃ t : ZMod p, w = ((M * t.val : ℕ) : ZMod (p * M)) := by
  have hw : M ∣ w.val := by
    rw [ZMod.castHom_apply, ZMod.cast_eq_val, CharP.cast_eq_zero_iff (ZMod M) M] at h
    exact h
  obtain ⟨k, hk⟩ := hw
  have hkp : k < p := by
    have hv := ZMod.val_lt w
    rw [hk, mul_comm p M] at hv
    exact Nat.lt_of_mul_lt_mul_left hv
  refine ⟨(k : ZMod p), ?_⟩
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hkp, ← hk, ZMod.natCast_zmod_val]

private theorem dn_up (p M : ℕ) [NeZero p] [NeZero M] (x : Row M) (i : Fin 2) :
    ZMod.castHom (dvd_mul_left M p) (ZMod M) (up p M x i) = ((p : ZMod M) • x) i := by
  unfold up
  rw [map_natCast]
  simp

private theorem prod_fib {G : Type} [CommMonoid G] (p M : ℕ) [NeZero p] [NeZero M] [NeZero (p * M)] (x : Row M)
    (S : Finset (Row (p * M))) (hS : ∀ z, z ∈ S ↔ dn p M z = (p : ZMod M) • x) (f : Row (p * M) → G) :
    ∏ z ∈ S, f z = ∏ t : Fin 2 → ZMod p, f (up p M x + tp p M t) := by
  have htp : ∀ (t : Fin 2 → ZMod p) (i : Fin 2),
      ZMod.castHom (dvd_mul_left M p) (ZMod M) (tp p M t i) = 0 := by
    intro t i
    show ZMod.castHom (dvd_mul_left M p) (ZMod M) ((M * (t i).val : ℕ) : ZMod (p * M)) = 0
    rw [map_natCast, Nat.cast_mul, ZMod.natCast_self, zero_mul]
  symm
  refine Finset.prod_bij (fun t _ => up p M x + tp p M t) ?_ ?_ ?_ ?_
  · intro t _
    rw [hS]
    funext i
    show ZMod.castHom (dvd_mul_left M p) (ZMod M) (up p M x i + tp p M t i) = ((p : ZMod M) • x) i
    rw [map_add (f := _), dn_up, htp, add_zero]
  · intro t _ t' _ h
    funext i
    have hi := add_left_cancel (congrFun h i)
    exact tp_inj p M (t i) (t' i) hi
  · intro z hz
    rw [hS] at hz
    have hex : ∀ i, ∃ s : ZMod p, z i - up p M x i = ((M * s.val : ℕ) : ZMod (p * M)) := by
      intro i
      apply tp_surj p M
      have hzi : ZMod.castHom (dvd_mul_left M p) (ZMod M) (z i) = ((p : ZMod M) • x) i := congrFun hz i
      rw [map_sub, dn_up, hzi, sub_self]
    choose t ht using hex
    refine ⟨t, Finset.mem_univ _, ?_⟩
    funext i
    show up p M x i + ((M * (t i).val : ℕ) : ZMod (p * M)) = z i
    rw [← ht i]
    abel
  · intro t _
    rfl

private theorem lin_ne (p N : ℕ) [Fact p.Prime] (o : Option (Fin p)) : lin p N o ≠ 0 := by
  intro h
  cases o with
  | none => simpa [lin] using congrFun h 1
  | some j => simpa [lin] using congrFun h 0

private theorem lin_eq (p N : ℕ) [Fact p.Prime] (hN : (N : ZMod p) ≠ 0) (o o' : Option (Fin p)) (i i' : ZMod p) (hi : i ≠ 0)
    (h : i • lin p N o = i' • lin p N o') : o = o' := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  cases o with
  | none =>
    cases o' with
    | none => rfl
    | some j' =>
      exfalso
      simp [lin] at h0 h1
      apply hi
      rw [← h0] at h1
      simpa using h1
  | some j =>
    cases o' with
    | none =>
      exfalso
      simp [lin] at h0
      exact hi h0
    | some j' =>
      simp [lin] at h0 h1
      subst h0
      have h2 : ((N * (j : ℕ) : ℕ) : ZMod p) = ((N * (j' : ℕ) : ℕ) : ZMod p) := by
        push_cast at h1 ⊢
        exact mul_left_cancel₀ hi h1
      push_cast at h2
      have h3 : ((j : ℕ) : ZMod p) = ((j' : ℕ) : ZMod p) := mul_left_cancel₀ hN h2
      rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt j.isLt, Nat.mod_eq_of_lt j'.isLt] at h3
      rw [Fin.ext h3]

private theorem lin_dep (p N : ℕ) [Fact p.Prime] (o : Option (Fin p)) (w : Fin 2 → ZMod p)
    (h : lin p N o 0 * w 1 - lin p N o 1 * w 0 = 0) : ∃ j : ZMod p, w = j • lin p N o := by
  cases o with
  | none =>
    refine ⟨w 1, ?_⟩
    funext i
    fin_cases i
    · simpa [lin] using h
    · simp [lin]
  | some j =>
    refine ⟨w 0, ?_⟩
    funext i
    fin_cases i
    · simp [lin]
    · simp [lin] at h ⊢
      linear_combination h

private theorem lin_surj (p N : ℕ) [Fact p.Prime] (hN : (N : ZMod p) ≠ 0) (w : Fin 2 → ZMod p) :
    ∃ (o : Option (Fin p)) (j : ZMod p), w = j • lin p N o := by
  by_cases h0 : w 0 = 0
  · exact ⟨none, lin_dep p N none w (by simp [lin, h0])⟩
  · refine ⟨some ⟨(w 1 / w 0 / N).val, ZMod.val_lt _⟩, lin_dep p N _ w ?_⟩
    simp only [lin]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Nat.cast_mul, ZMod.natCast_val, ZMod.cast_id', id]
    field_simp
    ring

private theorem prod_dep {G : Type} [CommMonoid G] (p N : ℕ) [Fact p.Prime] (hN : (N : ZMod p) ≠ 0)
    (F : (Fin 2 → ZMod p) → (Fin 2 → ZMod p) → G) :
    ∏ o : Option (Fin p), ∏ ij ∈ (Finset.univ : Finset (ZMod p × ZMod p)).erase 0, F (ij.1 • lin p N o) (ij.2 • lin p N o) =
      ∏ tt ∈ (Finset.univ.filter (fun tt : (Fin 2 → ZMod p) × (Fin 2 → ZMod p) =>
        ¬ (tt.1 0 * tt.2 1 - tt.1 1 * tt.2 0 ≠ 0))).erase 0, F tt.1 tt.2 := by
  rw [← Finset.prod_product' (s := Finset.univ) (t := (Finset.univ : Finset (ZMod p × ZMod p)).erase 0)
    (fun o ij => F (ij.1 • lin p N o) (ij.2 • lin p N o))]
  refine Finset.prod_bij (fun oij _ => (oij.2.1 • lin p N oij.1, oij.2.2 • lin p N oij.1)) ?_ ?_ ?_ ?_
  · rintro ⟨o, i, j⟩ h
    have hne : ((i, j) : ZMod p × ZMod p) ≠ 0 := Finset.ne_of_mem_erase (Finset.mem_product.1 h).2
    rw [Finset.mem_erase, Finset.mem_filter]
    refine ⟨?_, Finset.mem_univ _, ?_⟩
    · intro h0
      apply hne
      have h1 := congrArg Prod.fst h0
      have h2 := congrArg Prod.snd h0
      simp only [Prod.fst_zero, Prod.snd_zero, smul_eq_zero] at h1 h2
      have hl := lin_ne p N o
      rw [show i = 0 from h1.resolve_right hl, show j = 0 from h2.resolve_right hl]
      rfl
    · rw [not_not]
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
  · rintro ⟨o, i, j⟩ h ⟨o', i', j'⟩ h' heq
    have hne : ((i, j) : ZMod p × ZMod p) ≠ 0 := Finset.ne_of_mem_erase (Finset.mem_product.1 h).2
    have hi := congrArg Prod.fst heq
    have hj := congrArg Prod.snd heq
    simp only at hi hj
    have ho : o = o' := by
      by_cases hi0 : i = 0
      · have hj0 : j ≠ 0 := by
          intro hj0
          apply hne
          rw [hi0, hj0]
          rfl
        exact lin_eq p N hN o o' j j' hj0 hj
      · exact lin_eq p N hN o o' i i' hi0 hi
    subst ho
    have hl := lin_ne p N o
    have e1 : i = i' := smul_left_injective (ZMod p) hl hi
    have e2 : j = j' := smul_left_injective (ZMod p) hl hj
    rw [e1, e2]
  · rintro ⟨t, t'⟩ hmem
    rw [Finset.mem_erase, Finset.mem_filter, not_not] at hmem
    obtain ⟨hne, -, hdet⟩ := hmem
    simp only at hdet
    by_cases ht : t = 0
    · obtain ⟨o, j, hj⟩ := lin_surj p N hN t'
      have hj0 : j ≠ 0 := by
        intro hj0
        apply hne
        rw [ht, hj, hj0, zero_smul]
        rfl
      refine ⟨⟨o, 0, j⟩, ?_, ?_⟩
      · rw [Finset.mem_product, Finset.mem_erase]
        refine ⟨Finset.mem_univ _, ?_, Finset.mem_univ _⟩
        intro h0
        exact hj0 (congrArg Prod.snd h0)
      · simp only [zero_smul]
        rw [ht, hj]
    · obtain ⟨o, i, hi⟩ := lin_surj p N hN t
      have hi0 : i ≠ 0 := by
        intro hi0
        apply ht
        rw [hi, hi0, zero_smul]
      have hd : lin p N o 0 * t' 1 - lin p N o 1 * t' 0 = 0 := by
        have hd' : i * (lin p N o 0 * t' 1 - lin p N o 1 * t' 0) = 0 := by
          rw [hi] at hdet
          simp only [Pi.smul_apply, smul_eq_mul] at hdet
          linear_combination hdet
        exact (mul_eq_zero.1 hd').resolve_left hi0
      obtain ⟨j, hj⟩ := lin_dep p N o t' hd
      refine ⟨⟨o, i, j⟩, ?_, ?_⟩
      · rw [Finset.mem_product, Finset.mem_erase]
        refine ⟨Finset.mem_univ _, ?_, Finset.mem_univ _⟩
        intro h0
        exact hi0 (congrArg Prod.fst h0)
      · simp only
        rw [hi, hj]
  · intro _ _
    rfl

private theorem prod_pairs {G : Type} [CommMonoid G] (p N : ℕ) [Fact p.Prime] (hN : (N : ZMod p) ≠ 0)
    (F : (Fin 2 → ZMod p) → (Fin 2 → ZMod p) → G) :
    (∏ tt ∈ Finset.univ.filter (fun tt : (Fin 2 → ZMod p) × (Fin 2 → ZMod p) =>
        tt.1 0 * tt.2 1 - tt.1 1 * tt.2 0 ≠ 0), F tt.1 tt.2) *
      ∏ o : Option (Fin p), ∏ i : ZMod p, ∏ j : ZMod p, F (i • lin p N o) (j • lin p N o) =
      (∏ t, ∏ t', F t t') * F 0 0 ^ p := by
  have hinner : ∀ o : Option (Fin p), ∏ i : ZMod p, ∏ j : ZMod p, F (i • lin p N o) (j • lin p N o) =
      (∏ ij ∈ (Finset.univ : Finset (ZMod p × ZMod p)).erase 0, F (ij.1 • lin p N o) (ij.2 • lin p N o)) * F 0 0 := by
    intro o
    rw [← Fintype.prod_prod_type' (fun i j => F (i • lin p N o) (j • lin p N o))]
    rw [← Finset.mul_prod_erase Finset.univ (fun ij : ZMod p × ZMod p => F (ij.1 • lin p N o) (ij.2 • lin p N o))
      (Finset.mem_univ 0)]
    rw [mul_comm]
    congr 1
    simp
  have hmem : (0 : (Fin 2 → ZMod p) × (Fin 2 → ZMod p)) ∈ Finset.univ.filter
      (fun tt : (Fin 2 → ZMod p) × (Fin 2 → ZMod p) => ¬ (tt.1 0 * tt.2 1 - tt.1 1 * tt.2 0 ≠ 0)) := by
    simp
  have hfull : ∏ t, ∏ t', F t t' =
      (∏ tt ∈ Finset.univ.filter (fun tt : (Fin 2 → ZMod p) × (Fin 2 → ZMod p) =>
        tt.1 0 * tt.2 1 - tt.1 1 * tt.2 0 ≠ 0), F tt.1 tt.2) *
      (F 0 0 * ∏ tt ∈ (Finset.univ.filter (fun tt : (Fin 2 → ZMod p) × (Fin 2 → ZMod p) =>
        ¬ (tt.1 0 * tt.2 1 - tt.1 1 * tt.2 0 ≠ 0))).erase 0, F tt.1 tt.2) := by
    rw [← Fintype.prod_prod_type' F]
    rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ
      (fun tt : (Fin 2 → ZMod p) × (Fin 2 → ZMod p) => tt.1 0 * tt.2 1 - tt.1 1 * tt.2 0 ≠ 0)]
    congr 1
    exact (Finset.mul_prod_erase _ (fun tt : (Fin 2 → ZMod p) × (Fin 2 → ZMod p) => F tt.1 tt.2) hmem).symm
  rw [Finset.prod_congr rfl (fun o _ => hinner o), Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_option, Fintype.card_fin, prod_dep p N hN F, hfull, pow_succ]
  simp only [mul_assoc, mul_comm, mul_left_comm]

end UpperTheory.V.Z.Kato.Nb

theorem UpperTheory.V.Z.Kato.Nb.sPairs :
    UpperTheory.V.Z.Kato.Nb.SPairs := by
  intro Ω _ _ ε X p N M₀ _ _ hcop a x y
  have hN : (N : ZMod p) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff (ZMod p) p] at h
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).1 (Nat.Coprime.coprime_dvd_right (dvd_mul_right N M₀) hcop) h
  have htp0 : tp p M₀ 0 = 0 := by
    funext i
    simp [tp]
  have key := prod_pairs p N hN (fun t t' => a (up p M₀ x + tp p M₀ t) (up p M₀ y + tp p M₀ t'))
  unfold pushB pushL pushD
  rw [key, htp0, add_zero, add_zero]
  congr 1
  rw [prod_fib p M₀ x (Finset.univ.filter fun x' => dn p M₀ x' = (p : ZMod M₀) • x) (by simp)
    (fun x' => ∏ y' ∈ Finset.univ.filter (fun y' => dn p M₀ y' = (p : ZMod M₀) • y), a x' y')]
  refine Finset.prod_congr rfl (fun t _ => ?_)
  have hy := prod_fib p M₀ y (Finset.univ.filter fun y' => dn p M₀ y' = (p : ZMod M₀) • y)
    (fun z => by simp) (a (up p M₀ x + tp p M₀ t))
  exact hy.symm
end

open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

namespace UpperTheory.V.Z.Kato.Nb

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ}

private theorem zmod_val_cast_eq_cast_hom {d M : ℕ} [NeZero M] (h : d ∣ M) (z : ZMod M) :
    ((z.val : ℕ) : ZMod d) = ZMod.castHom h (ZMod d) z := by
  rw [ZMod.castHom_apply, ZMod.natCast_val]

omit [IsAlgClosure ℚ Ω] in
private theorem xi_scalar_first_entry (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n N M₀ M w : ℕ) [NeZero M] (g : SL(2, ℤ)) (x y : Row M₀)
    (P : (ZMod M)ˣ → Prop) (c : ZMod M₀) (b : Fam X M₀) :
    Xi X l n N M₀ M w g x y P (fun x y => b (c • x) (c • y)) = Xi X l n N M₀ M w g (c • x) (c • y) P b := by
  funext u
  simp only [Xi, Matrix.smul_vecMul]

private theorem congruence_scalar_pow (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (k k' j : ℕ) (h : (k : ZMod (l ^ n)) = k') (a : X.Fn l) :
    CgF X l n ((k : ℤ_[l]) ^ j • a) ((k' : ℤ_[l]) ^ j • a) := by
  intro u
  refine (sApi Ω ε X l n).2.2.2.2.1 _ _ (a u) (Dvd.dvd.trans ?_ (sub_dvd_pow_sub_pow _ _ j))
  obtain ⟨c, hc⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub (k' : ℤ) (k : ℤ) (l ^ n)).1 (by exact_mod_cast h.symm)
  exact ⟨(c : ℤ_[l]), by exact_mod_cast congrArg (Int.cast : ℤ → ℤ_[l]) hc⟩

private theorem xi_hecke_third_relation (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n N M₀ M w : ℕ) [NeZero N] [NeZero M₀] [NeZero M] (g : SL(2, ℤ))
    (hL : Lev l n N M₀ M g) (p : ℕ) (xb yb : Row M₀) (hok : Ok ((p : ZMod M₀) • xb) ((p : ZMod M₀) • yb))
    (a : Fam X M₀) (ha : Eqv X (l ^ n) M₀ a) (A : Type) [CommGroup A] (π : (ZMod M)ˣ →* A) (q : (ZMod M)ˣ) (hq : (q : ZMod M) = p)
    (δ : SL(2, ℤ)) (hδ : δ ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l) (ν : (ZMod M)ˣ)
    (h1 : ((ν : ZMod M).val : ZMod N) = (en δ 0 0 : ZMod N)) (h2 : ((ν : ZMod M).val : ZMod (l ^ n)) = 1)
    (h3 : ((ν : ZMod M).val : ZMod N) * (p : ZMod N) = 1) (hπ : π ν = 1) (t : A) :
    CgF X l n ((p : ℤ_[l]) ^ 2 • Xi X l n N M₀ M w g xb yb (fun z => π z = t) a)
      ((p : ℤ_[l]) ^ w • X.act l (δ : Matrix (Fin 2) (Fin 2) ℤ)
        (Xi X l n N M₀ M w g ((p : ZMod M₀) • xb) ((p : ZMod M₀) • yb) (fun z => π z = t * (π q)⁻¹ ^ 2) a)) := by
  have hN : N ∣ M := ⟨M₀, hL.eq⟩
  have hM : M₀ ∣ M := ⟨N, by rw [hL.eq, mul_comm]⟩
  have hln : l ^ n ∣ M := hL.dl.trans hM
  obtain ⟨E, -, hs, -⟩ := sApi Ω ε X l n
  have a1 := sXiAct Ω ε X l n N M₀ M w g hL _ _ hok (fun z => π z = t * (π q)⁻¹ ^ 2) a ha δ hδ ν h1 h2
    (fun z => by simp only [map_mul, map_pow, hπ, one_pow, mul_one])
  have hμ : ((((ν * q : (ZMod M)ˣ) : ZMod M).val : ℕ) : ZMod N) = 1 := by
    rw [zmod_val_cast_eq_cast_hom hN] at h3 ⊢
    rw [Units.val_mul, hq, map_mul, map_natCast, h3]
  have hμ' : ((((ν * q : (ZMod M)ˣ) : ZMod M).val : ℕ) : ZMod (l ^ n)) = p := by
    rw [zmod_val_cast_eq_cast_hom hln] at h2 ⊢
    rw [Units.val_mul, hq, map_mul, map_natCast, h2, one_mul]
  have a2 := sXiScal Ω ε X l n N M₀ M w g hL xb yb (fun z => π z = t * (π q)⁻¹ ^ 2) a (ν * q) hμ
  have e1 : ∀ x : Row M₀, (((ν : ZMod M).val : ℕ) : ZMod M₀) • (p : ZMod M₀) • x =
      ((((ν * q : (ZMod M)ˣ) : ZMod M).val : ℕ) : ZMod M₀) • x := by
    intro x
    rw [smul_smul, zmod_val_cast_eq_cast_hom hM, zmod_val_cast_eq_cast_hom hM, Units.val_mul, hq, map_mul, map_natCast]
  have e2 : (fun z : (ZMod M)ˣ => π (z * (ν * q)⁻¹ ^ 2) = t * (π q)⁻¹ ^ 2) = fun z => π z = t := by
    funext z
    simp only [map_mul, map_pow, map_inv, hπ, one_mul, mul_left_inj]
  rw [e1, e1] at a1
  beta_reduce at a2
  rw [e2] at a2
  exact E.trans (E.symm (congruence_scalar_pow X l n _ p 2 hμ' _)) (E.trans (E.symm a2)
    (E.trans (congruence_scalar_pow X l n _ p w hμ' _) (hs _ _ _ (E.symm a1))))

private theorem xi_hecke_prime_relation (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n N M₀ M w : ℕ) [NeZero N] [NeZero M₀] [NeZero M] (g : SL(2, ℤ))
    (hL : Lev l n N M₀ M g) (hlift : LiftsWith X l N w (cL X l N w)) (p M' : ℕ) [Fact p.Prime] [NeZero M'] [NeZero (p * M₀)]
    (h : M ∣ M') (hM' : M' = N * (p * M₀)) (hp : Nat.Coprime p M) (hpl : Nat.Coprime p l)
    (c d : ℕ) (ws : ∀ (_ M : ℕ), (Ω ≃ₐ[ℚ] Ω) → Fam X M) (hws : Laws X l c d ws) (hLv : Lv c d (p * M₀))
    (xb yb : Row M₀) (hokb : Ok xb yb) (hok : Ok ((p : ZMod M₀) • xb) ((p : ZMod M₀) • yb))
    (A : Type) [CommGroup A] (π : (ZMod M)ˣ →* A) (q : (ZMod M)ˣ) (hq : (q : ZMod M) = p)
    (hδ : sgD N l p ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l) (ν : (ZMod M)ˣ)
    (h1 : ((ν : ZMod M).val : ZMod N) = (en (sgD N l p) 0 0 : ZMod N)) (h2 : ((ν : ZMod M).val : ZMod (l ^ n)) = 1)
    (h3 : ((ν : ZMod M).val : ZMod N) * (p : ZMod N) = 1) (hπ : π ν = 1) :
    CohB X l N w n (fun s => (π (cycM M s))⁻¹)
      (fun s t => (p : ℤ_[l]) • Xi X l n N (p * M₀) M' w g (up p M₀ xb + tp p M₀ ![1, 0]) (up p M₀ yb + tp p M₀ ![0, 1])
        (fun z => π (Units.map (ZMod.castHom h (ZMod M)).toMonoidHom z) = t) (ws n (p * M₀) s))
      fun s t => (p : ℤ_[l]) • Xi X l n N M₀ M w g ((p : ZMod M₀) • xb) ((p : ZMod M₀) • yb) (fun z => π z = t) (ws n M₀ s) -
        X.heckeT N l p (Xi X l n N M₀ M w g ((p : ZMod M₀) • xb) ((p : ZMod M₀) • yb) (fun z => π z = t * (π q)⁻¹) (ws n M₀ s)) +
        (p : ℤ_[l]) ^ w • X.diam N l p
          (Xi X l n N M₀ M w g ((p : ZMod M₀) • xb) ((p : ZMod M₀) • yb) (fun z => π z = t * (π q)⁻¹ ^ 2) (ws n M₀ s)) := by
  obtain ⟨E, hadd, hs, -⟩ := sApi Ω ε X l n
  obtain ⟨F, fc, fadd, fs, -⟩ := sCohApi Ω ε X l N w n (NeZero.pos N) A (fun s => (π (cycM M s))⁻¹)
  have fs' : ∀ (k : ℤ_[l]) z z', CohB X l N w n (fun s => (π (cycM M s))⁻¹) z z' →
      CohB X l N w n (fun s => (π (cycM M s))⁻¹) (fun s y => k • z s y) fun s y => k • z' s y := by
    intro k z z' hz
    simpa only [mul_one] using fs k 1 z z' hz
  have hpNM : Nat.Coprime p (N * M₀) := hL.eq ▸ hp
  have hLv0 : Lv c d M₀ := ⟨NeZero.pos M₀, hLv.2.1.coprime_mul_left_right, hLv.2.2.coprime_mul_left_right⟩
  have C1 := sXiCoh Ω ε X l n N M₀ M w g hL hlift _ _ hok A π _ _ (hws.dist n p M₀ hLv)
  have C2 := sXiCoh Ω ε X l n N M₀ M w g hL hlift _ _ hokb A π _ _ (hws.lev n p M₀ hLv)
  have C3 := sXiCoh Ω ε X l n N M₀ M w g hL hlift _ _ hokb A π _ _
    (sLineCoh Ω ε X l n N M₀ p c d (by rw [mul_assoc]; exact Nat.Coprime.mul_right hpl hpNM) ws hws hLv)
  have C := (fadd _ _ _ _ (fs' (p : ℤ_[l]) _ _ C1) (fadd _ _ _ _ (fs' ((p : ℤ_[l]) ^ 2) _ _ C2) (fs' (p : ℤ_[l]) _ _ C3)).2).1
  refine F.trans (fc _ _ ?_) (F.trans C (fc _ _ ?_))
  · intro s t
    obtain ⟨m1, m2, -⟩ := sXiMul Ω ε X l n N M₀ M w g hL xb yb hokb (fun z => π z = t)
    have b1 := sXiTame Ω ε X l n N M₀ M w g hL p M' h hM' hp xb yb ![1, 0] ![0, 1] (by simp) (fun z => π z = t) (ws n (p * M₀) s)
    have b2 := m1 (pushB X p M₀ (ws n (p * M₀) s))
      (fun x y => pushD X p M₀ (ws n (p * M₀) s) ((p : ZMod M₀) • x) ((p : ZMod M₀) • y))
      (fun x y => ws n (p * M₀) s (up p M₀ x) (up p M₀ y) ^ p) (pushL X p N M₀ (ws n (p * M₀) s))
      (fun x y _ => ⟨1, by rw [← sPairs Ω ε X p N M₀ hpNM, one_pow, mul_one, mul_div_cancel_right]⟩)
    rw [xi_scalar_first_entry] at b2
    have b3 := m2 (fun x y => ws n (p * M₀) s (up p M₀ x) (up p M₀ y)) p
    have b4 := hs (p : ℤ_[l]) _ _ (E.trans b1 (E.trans b2 (hadd _ _ _ _ (E.refl _) (hadd _ _ _ _ b3 (E.refl _)).2).1))
    simpa only [Pi.add_apply, Pi.sub_apply, smul_add, smul_sub, smul_smul, ← sq] using b4
  · intro s t
    have b1 := sXiHecke Ω ε X l n N M₀ M w g hL p q hq xb yb (fun z => π z = t) (ws n M₀ s)
    have e : (fun z : (ZMod M)ˣ => π (z * q) = t) = fun z => π z = t * (π q)⁻¹ := by
      funext z
      rw [map_mul, eq_mul_inv_iff_mul_eq]
    beta_reduce at b1
    rw [e] at b1
    have b2 := xi_hecke_third_relation X l n N M₀ M w g hL p xb yb hok (ws n M₀ s) ((hws.coc n M₀ hLv0).eqv s) A π q hq _ hδ ν h1 h2 h3 hπ t
    have b3 := (hadd _ _ _ _ (E.refl ((p : ℤ_[l]) • Xi X l n N M₀ M w g ((p : ZMod M₀) • xb) ((p : ZMod M₀) • yb)
      (fun z => π z = t) (ws n M₀ s))) (hadd _ _ _ _ b2 (E.symm b1)).2).1
    rw [sub_add_eq_add_sub, add_sub_assoc]
    exact b3

private theorem sum_filter_fiber_eq {G B : Type} [CommGroup G] [Fintype G] {H ι : Type} [Fintype ι] [AddCommMonoid B] [DecidableEq (G × H)]
    [DecidableEq H] (ρ : ι → G × H) (f : ι → B) (e : G) (y : H) :
    ∑ a : G, ∑ i ∈ Finset.univ.filter (fun i => ρ i = (a * e, y)), f i = ∑ i ∈ Finset.univ.filter (fun i => (ρ i).2 = y), f i := by
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single ((ρ i).1 * e⁻¹)]
  · simp [Prod.ext_iff]
  · intro a _ ha
    rw [if_neg]
    intro h
    apply ha
    rw [h]
    simp
  · simp

end UpperTheory.V.Z.Kato.Nb

theorem UpperTheory.V.Z.Kato.Nb.kato_norm_relation_tame_prime :
    UpperTheory.V.Z.Kato.Nb.KatoClassHeckeEulerFactorRelation := by
  intro Ω _ _ _ ε X l _ N p _ _ x c d w g H hp hcop ⟨ws, hws⟩ hlift n r
  obtain ⟨F, fc, fadd, fs, -, f0, -, fh⟩ := sCohApi Ω ε X l N w n (NeZero.pos N) (ZMod (l ^ r))ˣ
    (fun s => (ReciprocityTheory.Gal.cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact f0 _ _
  haveI : Fact p.Prime := ⟨hp⟩
  have hl : l.Prime := Fact.out
  have hpN : Nat.Coprime p (l * N) := hcop.coprime_mul_right_right.coprime_mul_right_right
  have hpl : Nat.Coprime p l := hpN.coprime_mul_right_right
  have hpN' : Nat.Coprime p N := hpN.coprime_mul_left_right
  haveI : NeZero (N * l ^ (r + n)) := ⟨mul_ne_zero (NeZero.ne N) (pow_ne_zero _ hl.ne_zero)⟩
  haveI : NeZero (p * (N * l ^ (r + n))) := ⟨mul_ne_zero hp.ne_zero (NeZero.ne _)⟩
  have hL : Lev l n N (N * l ^ (r + n)) (topM l n r (N * N)) g :=
    ⟨by unfold topM; ring, dvd_mul_right _ _, (pow_dvd_pow l (Nat.le_add_left n r)).mul_left _, hn, H.cop, H.g0⟩
  have hL' : Lev l n N (p * (N * l ^ (r + n))) (lvT l n r N p) g :=
    ⟨by unfold lvT; ring, hL.dN.mul_left _, hL.dl.mul_left _, hn, H.cop, H.g0⟩
  have hMM : topM l n r (N * N) ∣ lvT l n r N p := dvd_mul_right _ _
  have hrM : l ^ r ∣ topM l n r (N * N) := (pow_dvd_pow l (Nat.le_add_right r n)).mul_right _
  have hpM : Nat.Coprime p (topM l n r (N * N)) := (hpl.pow_right _).mul_right (hpN'.mul_right hpN')
  have hc : ∀ c : ℕ, Nat.Coprime c (6 * l * N) → Nat.Coprime p c → Nat.Coprime c (p * (N * l ^ (r + n))) := fun c h h' =>
    h'.symm.mul_right (h.coprime_mul_left_right.mul_right (h.coprime_mul_right_right.coprime_mul_left_right.pow_right _))
  have hLv : Lv c d (p * (N * l ^ (r + n))) :=
    ⟨NeZero.pos _, hc c H.cc hcop.coprime_mul_right_right.coprime_mul_left_right, hc d H.cd hcop.coprime_mul_left_right⟩
  have hLv0 : Lv c d (N * l ^ (r + n)) := ⟨NeZero.pos _, hLv.2.1.coprime_mul_left_right, hLv.2.2.coprime_mul_left_right⟩
  obtain ⟨xb, yb, ob, o0, oT, iU, iV, iUT, iVT⟩ := UpperTheory.exists_rows_hecke_compatible_level_prime_pow l N p (r + n) x H.odd H.cop hpN (le_add_left hn)
  obtain ⟨hδ, ν, h1, h2, h3⟩ := UpperTheory.heckeMatrix_mem_gammaZero_inf_and_exists_unit_inv l N p (r + n) H.cop hpN
  let π : (ZMod (topM l n r (N * N)))ˣ →* (ZMod (l ^ r))ˣ := Units.map (ZMod.castHom hrM (ZMod (l ^ r))).toMonoidHom
  let π' : (ZMod (lvT l n r N p))ˣ →* (ZMod (l ^ r))ˣ := Units.map (ZMod.castHom (hrM.trans hMM) (ZMod (l ^ r))).toMonoidHom
  have hππ : ∀ z, π' z = π (Units.map (ZMod.castHom hMM (ZMod (topM l n r (N * N)))).toMonoidHom z) := by
    intro z
    ext
    exact (RingHom.congr_fun (ZMod.castHom_comp hrM hMM) (z : ZMod (lvT l n r N p))).symm
  have hcy := (sSlD Ω ε X N (NeZero.pos N)).2.2.2.2.2.2.2
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have k0 : (fun s : Ω ≃ₐ[ℚ] Ω => (π (cycM (topM l n r (N * N)) s))⁻¹) =
      fun s => (ReciprocityTheory.Gal.cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹ := by
    funext s
    rw [(sCycZ Ω l r s).1, ← (hcy (topM l n r (N * N)) s).2.2.2.2 (l ^ r) hrM]
  have kT' : (fun s : Ω ≃ₐ[ℚ] Ω => (π' (cycM (lvT l n r N p) s))⁻¹) =
      fun s => (ReciprocityTheory.Gal.cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹ := by
    funext s
    rw [(sCycZ Ω l r s).1, ← (hcy (lvT l n r N p) s).2.2.2.2 (l ^ r) (hrM.trans hMM)]
  have hred : ∀ j, j ≤ r + n → (((ν : ZMod (l ^ (r + n) * (N * N))).val : ℕ) : ZMod (l ^ j)) = 1 := by
    intro j hj
    have := congrArg (ZMod.castHom (pow_dvd_pow l hj) (ZMod (l ^ j))) h2
    rwa [map_natCast, map_one] at this
  have hπ : π ν = 1 := by
    ext
    exact (zmod_val_cast_eq_cast_hom hrM (Units.val ν)).symm.trans (hred r (Nat.le_add_right r n))
  have hq : (π (ZMod.unitOfCoprime p hpM))⁻¹ = inv1 (l ^ r) p := by
    have hu : IsUnit (p : ZMod (l ^ r)) := (ZMod.isUnit_iff_coprime _ _).2 (hpl.pow_right _)
    rw [inv1, dite_eq_left hu]
    congr 1
    ext
    exact map_natCast (ZMod.castHom hrM (ZMod (l ^ r))) p
  have C := xi_hecke_prime_relation X l n N _ _ w g hL hlift p (lvT l n r N p) hMM hL'.eq hpM hpl c d ws hws hLv xb yb ob o0 _ π
    (ZMod.unitOfCoprime p hpM) rfl hδ ν h1 (hred n (Nat.le_add_left n r)) h3 hπ
  obtain ⟨β, hβ, hβ'⟩ := sTopRel Ω ε X l n N _ _ w g hL hlift c d ws hws hLv0 _ _ o0 _ _ iU iV
  have B0 := sBridge Ω ε X l n N _ _ w g hL hlift _ _ o0 _ (hws.coc n _ hLv0) _ β hβ hβ' _ π
  obtain ⟨βT, hβT, hβT'⟩ := sTopRel Ω ε X l n N _ _ w g hL' hlift c d ws hws hLv _ _ oT _ _ iUT iVT
  have BT := sBridge Ω ε X l n N _ _ w g hL' hlift _ _ oT _ (hws.coc n _ hLv) _ βT hβT hβT' _ π'
  rw [k0] at C B0
  rw [kT'] at BT
  rw [hq] at C
  simp only [← hππ] at C
  have B0' : CohB X l N w n _ (Y0 X l n r N x c d w g) _ := B0
  have D1 := fs (p : ℤ_[l]) 1 _ _ B0'
  have D2 := (fh p hp hpN _ _ (fs 1 (inv1 (l ^ r) p) _ _ B0')).1
  have D3 := fs ((p : ℤ_[l]) ^ w) 1 _ _ (fh p hp hpN _ _ (fs 1 (inv1 (l ^ r) p ^ 2) _ _ B0')).2
  have D4 := fs (p : ℤ_[l]) 1 _ _ BT
  simp only [one_smul, mul_one] at D1 D2 D3 D4
  have D := (fadd _ _ _ _ (fadd _ _ _ _ D1 D2).2 D3).1
  have e : (fun s y => (p : ℤ_[l]) • ∑ a, YT X l n r N p x c d w g s (a, y)) =
      fun s y => (p : ℤ_[l]) • GlobalTheory.KA.push π' (shB X l (lvT l n r N p) (clsT X l n r N p x c d w g)) s y := by
    funext s y
    congr 1
    exact sum_filter_fiber_eq (rdT l n r N p) _ _ y
  rw [e]
  exact F.trans D4 (F.trans C (F.symm D))
