module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LawsAndChart
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalizedVectorTranslatesPrimeOrderIntegral
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsAnalyticSetupPeriodLatticePair
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TotallyDefiniteMass
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowCardWordsLe

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PrimePowSmulGoodLiftMemSetupLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PrimePowSmulGoodLiftMemSetupLattice
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

namespace GlobalTheory

theorem goodLift_pow_smul_mem : ∀ (g : ℕ) (S : JMB.Setup g) (p : ℕ) [Fact p.Prime] (lam : JMB.Qbar →+* ℂ_[p]) (N₀ n : ℕ), S.Ok →
    ∀ y ∈ AddSubgroup.closure {y : Fin g → ℂ | ∃ κ ∈ JMB.OK S.d,
      ‖JMB.lamA lam ((starRingEnd ℂ) κ)‖ ≤ (p : ℝ) ^ (-(2 * n : ℤ)) ∧
      ∃ x ∈ S.La, y = (κ * (N₀ : ℂ) / (p : ℂ) ^ n) • x}, ((p : ℂ) ^ n) • y ∈ S.La := by
  intro g S p _ lam N₀ n hS y hy
  have hw : ∀ x ∈ S.La, JMB.w0 S.d • x ∈ S.La := hS.2.2.2.2.2.1
  have hzs : ∀ (z : ℤ) (x : Fin g → ℂ), x ∈ S.La → ((z : ℂ)) • x ∈ S.La := by
    intro z x hx
    rw [Int.cast_smul_eq_zsmul ℂ z x]
    exact S.La.smul_mem z hx
  have hp : ((p : ℂ) ^ n) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨κ, ⟨u, v, hκ⟩, _, x, hx, rfl⟩ := hy
    rw [smul_smul, mul_div_cancel₀ _ hp, hκ]
    have : ((u : ℂ) + (v : ℂ) * JMB.w0 S.d) * (N₀ : ℂ) = ((u * N₀ : ℤ) : ℂ) + ((v * N₀ : ℤ) : ℂ) * JMB.w0 S.d := by
      push_cast; ring
    rw [this, add_smul, mul_smul]
    exact S.La.add_mem (hzs _ _ hx) (hzs _ _ (hw x hx))
  | zero => simp
  | add a b _ _ ha hb => rw [smul_add]; exact S.La.add_mem ha hb
  | neg a _ ha => rw [smul_neg]; exact S.La.neg_mem ha

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PrimePowSmulGoodLiftMemSetupLatticeStatement
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prime_pow_smul_goodLift_mem_setupLattice : ∀ (g : ℕ) (S : JMB.Setup g) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (N₀ n : ℕ), S.Ok → ∀ y ∈ AddSubgroup.closure {y : Fin g → ℂ | ∃ κ ∈ JMB.OK S.d, ‖JMB.lamA lam ((starRingEnd ℂ) κ)‖ ≤ (p : ℝ) ^ (-(2 * n : ℤ)) ∧ ∃ x ∈ S.La, y = (κ * (N₀ : ℂ) / (p : ℂ) ^ n) • x}, ((p : ℂ) ^ n) • y ∈ S.La := by
  first | exact @GlobalTheory.goodLift_pow_smul_mem | exact GlobalTheory.goodLift_pow_smul_mem | (intros; apply GlobalTheory.goodLift_pow_smul_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AlgebraicDirectionScaledEmbedding
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AlgebraicDirectionScaledEmbedding
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

noncomputable section

namespace GlobalTheory.AlgDirMom

theorem exists_nat_mul_isIntegral {E : Type} [Field E] [NumberField E] (c : E) :
    ∃ m : ℕ, 0 < m ∧ IsIntegral ℤ ((m : E) * c) := by
  have hc : IsAlgebraic ℤ c :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic c)
  obtain ⟨z, hz0, hz⟩ := hc.exists_integral_multiple
  refine ⟨z.natAbs, Int.natAbs_pos.2 hz0, ?_⟩
  rw [zsmul_eq_mul] at hz
  rcases Int.natAbs_eq z with h | h
  · rw [h] at hz; simpa using hz
  · rw [h] at hz
    have := hz.neg
    simpa using this

theorem exists_nat_smul_mem {E : Type} [Field E] [NumberField E] {n : ℕ} (L' : Submodule (𝓞 E) (Fin n → E))
    (hL' : Submodule.span E (L' : Set (Fin n → E)) = ⊤) (v : Fin n → E) :
    ∃ k : ℕ, 0 < k ∧ (k : E) • v ∈ L' := by
  have hv : v ∈ Submodule.span E (L' : Set (Fin n → E)) := hL' ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
    have e : ((a * b : ℕ) : E) • (x + y) = b • ((a : E) • x) + a • ((b : E) • y) := by
      rw [smul_add, ← Nat.cast_smul_eq_nsmul E b, ← Nat.cast_smul_eq_nsmul E a, smul_smul, smul_smul]
      push_cast
      rw [mul_comm (b : E) (a : E)]
    rw [e]
    exact L'.add_mem (L'.toAddSubmonoid.nsmul_mem hax b) (L'.toAddSubmonoid.nsmul_mem hby a)
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨m, hm, hint⟩ := exists_nat_mul_isIntegral c
    refine ⟨m * a, Nat.mul_pos hm ha, ?_⟩
    have h2 : (⟨(m : E) * c, hint⟩ : 𝓞 E) • ((a : E) • x) ∈ L' := L'.smul_mem _ hax
    rw [← algebraMap_smul E] at h2
    convert h2 using 1
    change _ = ((m : E) * c) • ((a : E) • x)
    rw [smul_smul, smul_smul]
    push_cast
    ring_nf

theorem exists_nat_smul_maps {E : Type} [Field E] [NumberField E] {N N' : ℕ}
    (L : Submodule (𝓞 E) (Fin N → E)) (L' : Submodule (𝓞 E) (Fin N' → E)) (hL : L.FG)
    (hL' : Submodule.span E (L' : Set (Fin N' → E)) = ⊤) (y : Matrix (Fin N') (Fin N) E) :
    ∃ k : ℕ, 0 < k ∧ ∀ x ∈ L, ((k : E) • y).mulVec x ∈ L' := by
  obtain ⟨s, hs⟩ := hL
  have hk : ∀ g ∈ s, ∃ k : ℕ, 0 < k ∧ (k : E) • y.mulVec g ∈ L' := fun g _ => exists_nat_smul_mem L' hL' _
  choose! kf hkpos hkmem using hk
  refine ⟨∏ g ∈ s, kf g, Finset.prod_pos fun g hg => hkpos g hg, ?_⟩
  intro x hx
  rw [← hs] at hx
  induction hx using Submodule.span_induction with
  | mem g hg =>
    rw [Matrix.smul_mulVec]
    rw [← Finset.mul_prod_erase s kf hg]
    push_cast
    rw [mul_comm, ← smul_smul]
    rw [← Nat.cast_prod, Nat.cast_smul_eq_nsmul]
    exact L'.toAddSubmonoid.nsmul_mem (hkmem g hg) _
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact L'.add_mem hx hy
  | smul r x _ hx =>
    rw [Matrix.mulVec_smul]
    exact L'.smul_mem r hx

end GlobalTheory.AlgDirMom

namespace GlobalTheory.AlgDirMom

theorem embV_natCast_smul {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) {N N' : ℕ} (n : ℕ)
    (y : Matrix (Fin N') (Fin N) D.host.E) :
    embV D B.tor ((n : D.host.E) • y) = (n : ℂ) • embV D B.tor y := by
  funext τ i j
  simp [embV, Base.tor, tor0]

theorem algDir_smul_embV : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ δ₀ : ℂ) (B : Base D cc δ) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), IsCurveIdeal D cc → admitted D N N' L L' → δ / δ₀ ∈ Qbar → δ / δ₀ ≠ 0 → ∀ (g : ℕ) (S : JMB.Setup g) (e : VC D N N' ≃L[ℂ] (Fin g → ℂ)), (∀ x, e x ∈ S.La ↔ x ∈ La D B.tor L L') → ∀ y : Matrix (Fin N') (Fin N) D.host.E, S.AlgDir ((δ₀ / δ) • e (δ • embV D B.tor y)) := by
  intro D cc δ δ₀ B N N' L L' hcc hadm hq hq0 g S e he y
  have hδ : δ ≠ 0 := fun h => hq0 (by simp [h])
  have hδ₀ : δ₀ ≠ 0 := fun h => hq0 (by simp [h])
  obtain ⟨-, -, ⟨hLfg, -, -⟩, ⟨-, hL'sp, -⟩⟩ := hadm
  obtain ⟨n, hn, hnmap⟩ := exists_nat_smul_maps L L' hLfg hL'sp y
  have hNc : Ideal.absNorm cc ≠ 0 := fun h => hcc.1 (Ideal.absNorm_eq_zero_iff.1 h)
  have hA : (n : D.host.E) • y ∈ YYl D L L' :=
    Submodule.subset_span ⟨1, Formalism.L2.Pj.one_mem_inverse_halfDifferent D, _, Submodule.subset_span (fun x hx => hnmap x hx),
      (one_smul _ _).symm⟩
  have hw : δ * (Ideal.absNorm cc : ℂ) ∈ B.tor.abelian₂ := by
    change _ ∈ lamOf D cc δ
    exact AddSubgroup.subset_closure ⟨_, Ideal.absNorm_mem cc, by simp⟩
  have hx : (δ * (Ideal.absNorm cc : ℂ)) • embV D B.tor ((n : D.host.E) • y) ∈ La D B.tor L L' :=
    AddSubgroup.subset_closure ⟨_, hw, _, hA, rfl⟩
  have hu := (he _).2 hx
  have hc : (δ₀ / δ) / ((n : ℂ) * (Ideal.absNorm cc : ℂ)) ∈ JMB.Qbar := by
    have h1 : δ₀ / δ = (δ / δ₀)⁻¹ := (inv_div δ δ₀).symm
    rw [h1]
    exact div_mem (inv_mem hq) (mul_mem (natCast_mem _ n) (natCast_mem _ _))
  refine ⟨1, fun _ => (δ₀ / δ) / ((n : ℂ) * (Ideal.absNorm cc : ℂ)),
    fun _ => e ((δ * (Ideal.absNorm cc : ℂ)) • embV D B.tor ((n : D.host.E) • y)), fun _ => hc, fun _ => hu, ?_⟩
  rw [Fin.sum_univ_one, embV_natCast_smul, smul_smul, map_smul, map_smul, smul_smul, smul_smul]
  congr 1
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hN0 : (Ideal.absNorm cc : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hNc
  field_simp

end GlobalTheory.AlgDirMom
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AlgebraicDirectionScaledEmbeddingStatement
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraicDirection_scaled_embedding : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ δ₀ : ℂ) (B : Base D cc δ) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), IsCurveIdeal D cc → admitted D N N' L L' → δ / δ₀ ∈ Qbar → δ / δ₀ ≠ 0 → ∀ (g : ℕ) (S : JMB.Setup g) (e : VC D N N' ≃L[ℂ] (Fin g → ℂ)), (∀ x, e x ∈ S.La ↔ x ∈ La D B.tor L L') → ∀ y : Matrix (Fin N') (Fin N) D.host.E, S.AlgDir ((δ₀ / δ) • e (δ • embV D B.tor y)) := by
  first | exact @GlobalTheory.AlgDirMom.algDir_smul_embV | exact GlobalTheory.AlgDirMom.algDir_smul_embV | (intros; apply GlobalTheory.AlgDirMom.algDir_smul_embV <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PairingScaledDirectionsEqPeriodPairing
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PairingScaledDirectionsEqPeriodPairing
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

namespace GlobalTheory.MomFin

theorem pairing_scaled : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ δ₀ : ℂ) (B : Base D cc δ) (N N' : ℕ) (g : ℕ) (S : JMB.Setup g) (e : VC D N N' ≃L[ℂ] (Fin g → ℂ)) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (Ω : ℂ_[p]) (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (y : Matrix (Fin N') (Fin N) D.host.E) (a : Fin r → ℤ_[p]), δ / δ₀ ∈ Qbar → δ / δ₀ ≠ 0 → Nat.Coprime (Ideal.absNorm cc) p → (∀ x y : Matrix (Fin N') (Fin N) D.host.E, JMB.beta S.d S.Hm (e (δ • embV D B.tor x)) (e (δ • embV D B.tor y)) = D.host.φ₀ ((hYY D x y : D.host.K) : D.host.E) / (Ideal.absNorm cc : ℂ)) → JMB.pairD lam Ω S.d S.Hm (fun i => e (δ • embV D B.tor (b i))) ((δ₀ / δ) • e (δ • embV D B.tor y)) a = pairN D lam (Ω * (Ideal.absNorm cc : ℂ_[p]) * lamC lam (δ / δ₀)) b y a := by
  intro D cc δ δ₀ B N N' g S e p _ lam Ω r b y a hq _ _ hb
  have hphi : ∀ z : D.host.E, D.host.φ₀ z ∈ Qbar := fun z => by
    have hx : IsAlgebraic ℚ z := Algebra.IsAlgebraic.isAlgebraic z
    exact (mem_algebraicClosure_iff).2 (hx.algHom D.host.φ₀.toRatAlgHom)

  have hlin : ∀ (c : ℂ) (z w : Fin g → ℂ), JMB.beta S.d S.Hm (c • z) w = c * JMB.beta S.d S.Hm z w := by
    intro c z w
    simp only [JMB.beta, JMB.hf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  set n := Ideal.absNorm cc
  have key : ∀ i, JMB.lamA lam (JMB.beta S.d S.Hm ((δ₀ / δ) • e (δ • embV D B.tor y)) (e (δ • embV D B.tor (b i))))
      = (lamC lam (δ / δ₀))⁻¹ * ((n : ℂ_[p]))⁻¹ * lamC lam (D.host.φ₀ ((hYY D y (b i) : D.host.K) : D.host.E)) := by
    intro i
    rw [hlin, hb]
    set z := D.host.φ₀ ((hYY D y (b i) : D.host.K) : D.host.E)
    have hz := hphi ((hYY D y (b i) : D.host.K) : D.host.E)
    have heq : δ₀ / δ * (z / (n : ℂ)) = (((⟨δ / δ₀, hq⟩ : Qbar)⁻¹ * ((n : Qbar))⁻¹ * ⟨z, hz⟩ : Qbar) : ℂ) := by
      have hc : (((n : Qbar)) : ℂ) = (n : ℂ) := by norm_cast
      simp only [IntermediateField.coe_mul, IntermediateField.coe_inv, hc]
      rw [inv_div]; ring
    have hmem : δ₀ / δ * (z / (n : ℂ)) ∈ Qbar := by rw [heq]; exact SetLike.coe_mem _
    unfold JMB.lamA lamC
    rw [dite_eq_left hmem, dite_eq_left hq, dite_eq_left hz]
    have : (⟨δ₀ / δ * (z / (n : ℂ)), hmem⟩ : Qbar) = (⟨δ / δ₀, hq⟩ : Qbar)⁻¹ * ((n : Qbar))⁻¹ * ⟨z, hz⟩ := Subtype.ext heq
    rw [this, map_mul, map_mul, map_inv₀, map_inv₀, map_natCast]
  unfold JMB.pairD pairN
  simp only [key]
  have hzc : ∀ i, JMB.zc (a i) = zc (a i) := fun i => rfl
  simp only [hzc, mul_inv, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => by ring

end GlobalTheory.MomFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PairingScaledDirectionsEqPeriodPairingStatement
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairing_scaledDirections_eq_period_pairing : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ δ₀ : ℂ) (B : Base D cc δ) (N N' : ℕ) (g : ℕ) (S : JMB.Setup g) (e : VC D N N' ≃L[ℂ] (Fin g → ℂ)) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (Ω : ℂ_[p]) (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (y : Matrix (Fin N') (Fin N) D.host.E) (a : Fin r → ℤ_[p]), δ / δ₀ ∈ Qbar → δ / δ₀ ≠ 0 → Nat.Coprime (Ideal.absNorm cc) p → (∀ x y : Matrix (Fin N') (Fin N) D.host.E, JMB.beta S.d S.Hm (e (δ • embV D B.tor x)) (e (δ • embV D B.tor y)) = D.host.φ₀ ((hYY D x y : D.host.K) : D.host.E) / (Ideal.absNorm cc : ℂ)) → JMB.pairD lam Ω S.d S.Hm (fun i => e (δ • embV D B.tor (b i))) ((δ₀ / δ) • e (δ • embV D B.tor y)) a = pairN D lam (Ω * (Ideal.absNorm cc : ℂ_[p]) * lamC lam (δ / δ₀)) b y a := by
  first | exact @GlobalTheory.MomFin.pairing_scaled | exact GlobalTheory.MomFin.pairing_scaled | (intros; apply GlobalTheory.MomFin.pairing_scaled <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CoefInWeilOperatorTranslateAlgebraic
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CoefInWeilOperatorTranslateAlgebraic
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

namespace GlobalTheory.CoefWop

lemma Hf_add_left (D : D7) (T : Tor D) {N N' : ℕ} (a b w : VC D N N') :
    Hf D T (a + b) w = Hf D T a w + Hf D T b w := by
  simp only [Hf, Pi.add_apply, add_mul, Finset.sum_add_distrib, add_div]

lemma Hf_add_right (D : D7) (T : Tor D) {N N' : ℕ} (a b w : VC D N N') :
    Hf D T w (a + b) = Hf D T w a + Hf D T w b := by
  simp only [Hf, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib, add_div]

lemma Hf_nsmul (D : D7) (T : Tor D) {N N' : ℕ} (a b : ℕ) (y t : VC D N N') :
    Hf D T (a • y) (b • t) = (a * b : ℂ) * Hf D T y t := by
  simp only [Hf, Pi.smul_apply, nsmul_eq_mul, map_mul, map_natCast, mul_div_assoc', Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

lemma U_U (D : D7) (T : Tor D) {N N' : ℕ} (y t : VC D N N') (F : VC D N N' → ℂ) (z : VC D N N') :
    U D T y (U D T t F) z
      = Complex.exp (-(Real.pi : ℂ) * ((Hf D T y t - Hf D T t y) / 2)) * U D T (y + t) F z := by
  simp only [U]
  rw [show z + y + t = z + (y + t) by abel]
  rw [mul_comm (Complex.exp _) (F _ * _), mul_assoc, mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
  congr 2
  simp only [Hf_add_left, Hf_add_right]
  ring

lemma taylor_const_mul (D : D7) {N N' : ℕ} (c : ℂ) (G : VC D N N' → ℂ) (hG : ContDiff ℂ ⊤ G)
    (α : Mono D N N') : Formalism.MainNotions.TaylorLogMetric.taylor D (fun z => c * G z) α = c * Formalism.MainNotions.TaylorLogMetric.taylor D G α := by
  simp only [Formalism.MainNotions.TaylorLogMetric.taylor]
  have h := iteratedFDeriv_const_smul_apply (𝕜 := ℂ) (i := (Finsupp.toMultiset α).card) (a := c) (x := (0 : VC D N N'))
    (hG.contDiffAt.of_le (by exact_mod_cast le_top))
  rw [show (fun z => c * G z) = c • G from rfl, h]
  rw [ContinuousMultilinearMap.smul_apply, smul_eq_mul, mul_div_assoc]

lemma contDiff_U (D : D7) (T : Tor D) {N N' : ℕ} (x : VC D N N') (F : VC D N N' → ℂ)
    (hF : ContDiff ℂ ⊤ F) : ContDiff ℂ ⊤ (U D T x F) := by
  unfold U Hf
  apply ContDiff.mul
  · exact hF.comp (contDiff_id.add contDiff_const)
  · apply ContDiff.cexp
    apply ContDiff.sub _ contDiff_const
    apply ContDiff.mul contDiff_const
    apply ContDiff.div_const
    apply ContDiff.sum fun τ _ => ContDiff.sum fun i _ => ContDiff.sum fun j _ => ?_
    apply ContDiff.mul _ contDiff_const
    exact (contDiff_apply ℂ _ j).comp ((contDiff_apply ℂ _ i).comp (contDiff_apply ℂ _ τ))

lemma sq_one_alg {c : ℂ} {n : ℕ} (hn : 0 < n) (h : c ^ n = 1) : c ∈ Qbar := by
  rw [mem_algebraicClosure_iff]
  apply IsIntegral.isAlgebraic
  exact IsIntegral.of_pow hn (by rw [h]; exact isIntegral_one)

lemma Hf_swap (D : D7) (T : Tor D) {N N' : ℕ} (y t : VC D N N') :
    Hf D T t y = (starRingEnd ℂ) (Hf D T y t) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Hf, map_div₀, map_sum, map_mul, Complex.conj_conj, Complex.conj_ofReal]
  congr 1
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

lemma wPh_sq (D : D7) (T : Tor D) {N N' : ℕ} (p : ℕ) (y : VC D N N') (m : ℤ) (hm : qH D T y = m) :
    wPh D T p y ^ 2 = 1 := by
  unfold wPh
  split_ifs with hp
  · rw [← Complex.exp_nat_mul, hm]
    have : ((2 : ℕ) : ℂ) * ((Real.pi : ℂ) * Complex.I * ((m : ℝ) : ℂ)) = (m : ℂ) * (2 * Real.pi * Complex.I) := by
      push_cast; ring
    rw [this, Complex.exp_int_mul_two_pi_mul_I]
  · have hex : ∃ s : ℂ, ∃ k : ℕ, ∃ m' : ℤ, (p : ℝ) ^ k * qH D T y = m' ∧ s = (-1) ^ m' :=
      ⟨(-1) ^ m, 0, m, by simp [hm], rfl⟩
    obtain ⟨k, m', -, hs⟩ := Classical.epsilon_spec hex
    rw [hs, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    norm_num

lemma root_alg (D : D7) (T : Tor D) {N N' : ℕ} (y t : VC D N N') (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (k : ℤ)
    (hk : (Hf D T (a • y) (b • t)).im = k) :
    Complex.exp (-(Real.pi : ℂ) * ((Hf D T y t - Hf D T t y) / 2)) ∈ Qbar := by
  rw [Hf_nsmul] at hk
  have hk' : ((a * b : ℕ) : ℝ) * (Hf D T y t).im = k := by
    rw [← hk]; push_cast
    rw [show ((a : ℂ) * b) = (((a * b : ℝ)) : ℂ) by push_cast; ring, Complex.im_ofReal_mul]
  have hdiff : Hf D T y t - Hf D T t y = 2 * Complex.I * ((Hf D T y t).im : ℂ) := by
    rw [Hf_swap]
    apply Complex.ext <;> simp <;> ring
  apply sq_one_alg (n := 2 * (a * b)) (by positivity)
  rw [hdiff, ← Complex.exp_nat_mul]
  have : ((2 * (a * b) : ℕ) : ℂ) * (-(Real.pi : ℂ) * (2 * Complex.I * ((Hf D T y t).im : ℂ) / 2))
      = ((-k : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    have hk'' : ((a * b : ℕ) : ℂ) * ((Hf D T y t).im : ℂ) = (k : ℂ) := by exact_mod_cast hk'
    push_cast at hk'' ⊢
    linear_combination (-(Real.pi : ℂ) * 2 * Complex.I) * hk''
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

end GlobalTheory.CoefWop

namespace GlobalTheory


open GlobalTheory.CoefWop in
theorem coefIn_Wop_U_translate : ∀ (D : D7) (T : Tor D) (N N' : ℕ) (F : VC D N N' → ℂ) (Λ : AddSubgroup (VC D N N')) (p : ℕ) [Fact p.Prime] (y t : VC D N N'), ContDiff ℂ ⊤ F → (∀ s : VC D N N', (∃ a : ℕ, 0 < a ∧ a • s ∈ Λ) → CoefIn D (U D T s F) Qbar) → (∃ a : ℕ, 0 < a ∧ a • t ∈ Λ) → (∃ a : ℕ, 0 < a ∧ a • y ∈ Λ) → (∀ x ∈ Λ, ∀ x' ∈ Λ, ∃ k : ℤ, (Hf D T x x').im = k) → (∃ m : ℤ, qH D T y = m) → CoefIn D (Wop D T p y (U D T t F)) Qbar := by
  intro D T N N' F Λ p _ y t hF hΛ ⟨b, hb, hbt⟩ ⟨a, ha, hay⟩ hHf ⟨m, hm⟩
  have hfun : Wop D T p y (U D T t F)
      = fun z => (wPh D T p y * Complex.exp (-(Real.pi : ℂ) * ((Hf D T y t - Hf D T t y) / 2)))
          * U D T (y + t) F z := by
    funext z
    simp only [Wop, U_U]
    ring
  have hyt : CoefIn D (U D T (y + t) F) Qbar := by
    refine hΛ _ ⟨a * b, by positivity, ?_⟩
    rw [smul_add, mul_comm a b, mul_smul, mul_comm b a, mul_smul]
    exact Λ.add_mem (Λ.nsmul_mem hay b) (Λ.nsmul_mem hbt a)
  obtain ⟨k, hk⟩ := hHf _ hay _ hbt
  have hw : wPh D T p y ∈ Qbar := sq_one_alg (n := 2) (by norm_num) (wPh_sq D T p y m hm)
  unfold CoefIn
  intro α
  rw [hfun, taylor_const_mul D _ _ (contDiff_U D T _ F hF)]
  exact Qbar.mul_mem (Qbar.mul_mem hw (root_alg D T y t a b ha hb k hk)) (hyt α)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CoefInWeilOperatorTranslateAlgebraicStatement
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefIn_weilOperator_translate_algebraic : ∀ (D : D7) (T : Tor D) (N N' : ℕ) (F : VC D N N' → ℂ) (Λ : AddSubgroup (VC D N N')) (p : ℕ) [Fact p.Prime] (y t : VC D N N'), ContDiff ℂ ⊤ F → (∀ s : VC D N N', (∃ a : ℕ, 0 < a ∧ a • s ∈ Λ) → CoefIn D (U D T s F) Qbar) → (∃ a : ℕ, 0 < a ∧ a • t ∈ Λ) → (∃ a : ℕ, 0 < a ∧ a • y ∈ Λ) → (∀ x ∈ Λ, ∀ x' ∈ Λ, ∃ k : ℤ, (Hf D T x x').im = k) → (∃ m : ℤ, qH D T y = m) → CoefIn D (Wop D T p y (U D T t F)) Qbar := by
  first | exact @GlobalTheory.coefIn_Wop_U_translate | exact GlobalTheory.coefIn_Wop_U_translate | (intros; apply GlobalTheory.coefIn_Wop_U_translate <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GoodLiftEqIdempotentLift
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GoodLiftEqIdempotentLift
open GlobalTheory.MomN Formalism.L2.Ker.JMB
open scoped ComplexConjugate

namespace GlobalTheory.MomN.GoodLift
open GlobalTheory.MomOne.LiftChange

variable {g : ℕ} {q : ℕ} [Fact q.Prime]

theorem hf_add_right (Hm : Matrix (Fin g) (Fin g) ℂ) (x y y' : Fin g → ℂ) :
    hf Hm x (y + y') = hf Hm x y + hf Hm x y' := by
  simp only [hf, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]

theorem hf_neg_right (Hm : Matrix (Fin g) (Fin g) ℂ) (x y : Fin g → ℂ) : hf Hm x (-y) = -hf Hm x y := by
  have h := hf_smul_right Hm (-1) x y
  rw [neg_one_smul, map_neg, map_one, neg_one_mul] at h
  exact h

theorem hf_sub_right (Hm : Matrix (Fin g) (Fin g) ℂ) (x y y' : Fin g → ℂ) :
    hf Hm x (y - y') = hf Hm x y - hf Hm x y' := by
  rw [sub_eq_add_neg, hf_add_right, hf_neg_right, ← sub_eq_add_neg]

theorem hf_sub_left (Hm : Matrix (Fin g) (Fin g) ℂ) (x x' y : Fin g → ℂ) :
    hf Hm (x - x') y = hf Hm x y - hf Hm x' y := by
  rw [sub_eq_add_neg, hf_add_left, ← neg_one_smul ℂ x', hf_smul_left]; ring

theorem hf_sum_right (Hm : Matrix (Fin g) (Fin g) ℂ) {r : ℕ} (x : Fin g → ℂ) (y : Fin r → Fin g → ℂ) :
    hf Hm x (∑ i, y i) = ∑ i, hf Hm x (y i) := by
  have : ∀ s : Finset (Fin r), hf Hm x (∑ i ∈ s, y i) = ∑ i ∈ s, hf Hm x (y i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [hf]
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hf_add_right, ih]
  exact this _

theorem norm_zc (a : ℤ_[q]) : ‖GlobalTheory.MomOne.zc a‖ = ‖a‖ := by
  rw [GlobalTheory.MomOne.zc, norm_algebraMap']; rfl

theorem norm_natCast_le (N : ℕ) : ‖(N : ℂ_[q])‖ ≤ 1 := by
  have : (N : ℂ_[q]) = GlobalTheory.MomOne.zc (N : ℤ_[q]) := by simp [GlobalTheory.MomOne.zc]
  rw [this, norm_zc]; exact PadicInt.norm_le_one _

theorem norm_q_pow (n : ℕ) : ‖(q : ℂ_[q]) ^ n‖ = (q : ℝ) ^ (-(n : ℤ)) := by
  have : (q : ℂ_[q]) = algebraMap ℚ_[q] ℂ_[q] (q : ℚ_[q]) := by simp
  rw [norm_pow, this, norm_algebraMap', Padic.norm_p, zpow_neg, zpow_natCast, inv_pow]

end GlobalTheory.MomN.GoodLift

namespace GlobalTheory.MomN
open GlobalTheory.MomOne.LiftChange GlobalTheory.MomN.GoodLift
open scoped ComplexOrder


set_option maxHeartbeats 4000000 in
theorem goodLift_eq : ∀ (q : ℕ) [Fact q.Prime] (lam : Qbar →+* ℂ_[q]) (g : ℕ) (S : Setup g) (r : ℕ) (b : Fin r → Fin g → ℂ) (e : (Fin g → ℂ) → ℂ) (t : Fin g → ℂ), S.Ok → GlobalTheory.MomOne.Split S.d q → S.NNBasis q b → S.IsTheta e → ∀ N₀ : ℕ, 0 < N₀ → Nat.Coprime N₀ q → (N₀ : ℂ) • t ∈ S.La → ∀ (n : ℕ), ∀ y ∈ AddSubgroup.closure {y : Fin g → ℂ | ∃ κ ∈ OK S.d, ‖lamA lam (conj κ)‖ ≤ (q : ℝ) ^ (-(2 * n : ℤ)) ∧ ∃ x ∈ S.La, y = (κ * (N₀ : ℂ) / (q : ℂ) ^ n) • x}, (∃ z : ℤ, (beta S.d S.Hm y y).re = z) ∧ ∃ (m : ℕ) (eps : ℂ) (yt : Fin r → Fin (q ^ n)), IsIdem lam S.d m eps ∧ 2 * n ≤ m ∧ (∀ i, ∃ z : ℤ, (hf S.Hm (eps • b i) t).im = z) ∧ opW S.d S.Hm y (opU S.Hm t e) = opW S.d S.Hm (liftY q n eps b yt) (opU S.Hm t e) ∧ ∀ a : Fin r → ℕ, kap S.Hm (∑ i, (a i : ℂ) • b i) y = kap S.Hm (vecA n b fun i => (a i : ℤ_[q])) (liftY q n eps b yt) := by
  intro q _ lam g S r b e t hS hsp hb he N₀ hN₀ hcop hNt n y hy
  have hqp : q.Prime := Fact.out
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hqp.one_le
  have hd4 : S.d % 4 = 3 := by have := hS.2.1; omega
  obtain ⟨ι, hι⟩ := GlobalTheory.PadicComplexIso.exists_ringEquiv_extending q lam
  obtain ⟨⟨-, -, hcl⟩, hZ, hdiv, hid, -, -, -⟩ := GlobalTheory.MomOne.okArith S.d q ι hS.1 hS.2.1 hsp
  obtain ⟨H1, -, -, H4, H5, H6⟩ := GlobalTheory.HeisOps.heisenberg g S.d S.Hm hS.1.pos hS.2.2.1.isHermitian
  have hlam : ∀ x : ℂ, x ∈ Qbar → lamA lam x = ι x := fun x hx => by
    rw [lamA, dite_eq_left hx]; exact (hι ⟨x, hx⟩).symm
  have hOK1 : ∀ α ∈ OK S.d, ‖ι α‖ ≤ 1 := fun α hα => by
    obtain ⟨⟨a, ha⟩, -⟩ := hZ α hα
    rw [ha, norm_zc]; exact PadicInt.norm_le_one a
  have hbOK : ∀ x ∈ S.La, ∀ y ∈ S.La, beta S.d S.Hm x y ∈ OK S.d := hS.2.2.2.2.2.2.1
  have himI : ∀ x ∈ S.La, ∀ y ∈ S.La, ∃ k : ℤ, (hf S.Hm x y).im = k := fun x hx y hy => by
    obtain ⟨u, v, huv⟩ := hbOK x hx y hy
    exact ⟨v, H5 _ _ _ _ huv⟩
  have hnat : ∀ N : ℕ, ‖ι (N : ℂ)‖ ≤ 1 := fun N => by rw [map_natCast]; exact norm_natCast_le N
  have hnat1 : ∀ N : ℕ, Nat.Coprime N q → ‖ι (N : ℂ)‖ = 1 := fun N h => by
    rw [map_natCast]; exact GlobalTheory.MomOne.Basic.norm_nat_eq_one h.symm
  have hqn : ‖ι ((q : ℂ) ^ n)‖ = (q : ℝ) ^ (-(n : ℤ)) := by rw [map_pow, map_natCast]; exact norm_q_pow n
  have hconjOK : ∀ α ∈ OK S.d, conj α ∈ OK S.d := fun α h => (hcl α α h h).2.2.2
  have hmulOK : ∀ α β, α ∈ OK S.d → β ∈ OK S.d → α * β ∈ OK S.d := fun α β h h' => (hcl α β h h').2.1
  have hnatOK : ∀ N : ℕ, (N : ℂ) ∈ OK S.d := fun N => ⟨N, 0, by simp⟩
  have hconjB : ∀ x y, beta S.d S.Hm y x = conj (beta S.d S.Hm x y) := fun x y => by
    rw [beta, beta, H4 x y, map_mul, Complex.conj_ofReal]
  have hpow_le : (q : ℝ) ^ (-(2 * n : ℤ)) ≤ (q : ℝ) ^ (-(n : ℤ)) := zpow_le_zpow_right₀ hq1 (by omega)
  have hpos : ∀ k : ℤ, (0 : ℝ) ≤ (q : ℝ) ^ k := fun k => by positivity
  have bsr : ∀ (a : ℂ) x y, beta S.d S.Hm x (a • y) = conj a * beta S.d S.Hm x y := fun a x y => by
    rw [beta, beta, hf_smul_right]; ring
  have bsl : ∀ (a : ℂ) x y, beta S.d S.Hm (a • x) y = a * beta S.d S.Hm x y := fun a x y => by
    rw [beta, beta, hf_smul_left]; ring
  have bar : ∀ x y y', beta S.d S.Hm x (y + y') = beta S.d S.Hm x y + beta S.d S.Hm x y' := fun x y y' => by
    rw [beta, beta, beta, hf_add_right]; ring
  have bsubr : ∀ x y y', beta S.d S.Hm x (y - y') = beta S.d S.Hm x y - beta S.d S.Hm x y' := fun x y y' => by
    rw [beta, beta, beta, hf_sub_right]; ring
  have bsubl : ∀ x x' y, beta S.d S.Hm (x - x') y = beta S.d S.Hm x y - beta S.d S.Hm x' y := fun x x' y => by
    rw [beta, beta, beta, hf_sub_left]; ring
  have bnr : ∀ x y, beta S.d S.Hm x (-y) = -beta S.d S.Hm x y := fun x y => by
    rw [beta, beta, hf_neg_right]; ring
  have bsumr : ∀ x (y : Fin r → Fin g → ℂ), beta S.d S.Hm x (∑ j, y j) = ∑ j, beta S.d S.Hm x (y j) := fun x y => by
    rw [beta, hf_sum_right, Finset.mul_sum]; rfl
  have bsuml : ∀ (x : Fin r → Fin g → ℂ) y, beta S.d S.Hm (∑ j, x j) y = ∑ j, beta S.d S.Hm (x j) y := fun x y => by
    rw [beta, hf_sum_left, Finset.mul_sum]; rfl
  have usub : ∀ a b : ℂ_[q], ‖a - b‖ ≤ max ‖a‖ ‖b‖ := fun a b => by
    rw [sub_eq_add_neg]; simpa using IsUltrametricDist.norm_add_le_max a (-b)
  have hN0r : conj (N₀ : ℂ) = N₀ := map_natCast _ _
  have hqr : conj ((q : ℂ) ^ n) = (q : ℂ) ^ n := by rw [map_pow, map_natCast]
  have hqnC : (q : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by exact_mod_cast hqp.ne_zero)

  have step1 : ∃ v ∈ S.La, y = ((N₀ : ℂ) / (q : ℂ) ^ n) • v ∧
      ∀ x ∈ S.La, ‖ι (beta S.d S.Hm x v)‖ ≤ (q : ℝ) ^ (-(2 * n : ℤ)) := by
    induction hy using AddSubgroup.closure_induction with
    | mem y hy' =>
      obtain ⟨κ, hκ, hκs, x0, hx0, rfl⟩ := hy'
      refine ⟨κ • x0, GlobalTheory.MomOne.LiftChange.smul_mem S hS hκ hx0, by rw [smul_smul]; congr 1; ring, fun x hx => ?_⟩
      rw [bsr, map_mul, norm_mul, ← hlam _ (GlobalTheory.MomOne.LiftChange.norm_int hd4 hκ).2.1]
      calc _ ≤ (q : ℝ) ^ (-(2 * n : ℤ)) * 1 := mul_le_mul hκs (hOK1 _ (hbOK x hx x0 hx0)) (norm_nonneg _) (hpos _)
        _ = _ := mul_one _
    | zero => exact ⟨0, zero_mem _, by simp, fun x hx => by simp [beta, hf]; positivity⟩
    | add y1 y2 _ _ ih1 ih2 =>
      obtain ⟨v1, hv1, rfl, h1⟩ := ih1
      obtain ⟨v2, hv2, rfl, h2⟩ := ih2
      refine ⟨v1 + v2, add_mem hv1 hv2, (smul_add _ _ _).symm, fun x hx => ?_⟩
      rw [bar, map_add (f := _)]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h1 x hx) (h2 x hx))
    | neg y1 _ ih =>
      obtain ⟨v1, hv1, rfl, h1⟩ := ih
      refine ⟨-v1, neg_mem hv1, (smul_neg _ _).symm, fun x hx => ?_⟩
      rw [bnr, map_neg, norm_neg]; exact h1 x hx
  obtain ⟨v, hv, rfl, hvs⟩ := step1

  have hre : ∃ z : ℤ, (beta S.d S.Hm (((N₀ : ℂ) / (q : ℂ) ^ n) • v) (((N₀ : ℂ) / (q : ℂ) ^ n) • v)).re = z := by
    have hα : beta S.d S.Hm v v ∈ OK S.d := hbOK v hv v hv
    have hαc : conj (beta S.d S.Hm v v) = beta S.d S.Hm v v := (hconjB v v).symm
    have hγ : GlobalTheory.MomOne.InOK S.d (beta S.d S.Hm v v / (q : ℂ) ^ (2 * n)) :=
      hdiv _ (2 * n) hα (by push_cast; exact hvs v hv) (by rw [hαc]; push_cast; exact hvs v hv)
    obtain ⟨u, w', hu⟩ := hγ
    have hγc : conj (beta S.d S.Hm v v / (q : ℂ) ^ (2 * n)) = beta S.d S.Hm v v / (q : ℂ) ^ (2 * n) := by
      rw [map_div₀, hαc, map_pow, map_natCast]
    have hw'0 : w' = 0 := by
      have him := congrArg Complex.im hu
      have hc := congrArg Complex.im hγc
      rw [Complex.conj_im] at hc
      have h0 : (beta S.d S.Hm v v / (q : ℂ) ^ (2 * n)).im = 0 := by linarith
      rw [h0] at him
      have hs : Real.sqrt S.d ≠ 0 := by have := hS.1.pos; positivity
      simp [GlobalTheory.MomOne.wK, hs] at him
      exact_mod_cast him
    rw [hw'0, Int.cast_zero, zero_mul, add_zero, div_eq_iff (pow_ne_zero _ (by exact_mod_cast hqp.ne_zero))] at hu
    refine ⟨N₀ ^ 2 * u, ?_⟩
    have : beta S.d S.Hm (((N₀ : ℂ) / (q : ℂ) ^ n) • v) (((N₀ : ℂ) / (q : ℂ) ^ n) • v) = ((N₀ ^ 2 * u : ℤ) : ℂ) := by
      rw [bsl, bsr, map_div₀, hN0r, hqr, hu]
      push_cast
      field_simp
      ring
    rw [this, Complex.intCast_re]

  obtain ⟨e0, he0, he0a, he0b⟩ := hid (2 * n) N₀ hcop
  have he0' : e0 ∈ OK S.d := he0
  have he0b' : ‖ι (conj e0)‖ ≤ (q : ℝ) ^ (-(2 * n : ℤ)) := by have := he0b; push_cast at this; exact this
  have he0a' : ‖ι ((N₀ : ℂ) * e0 - 1)‖ ≤ (q : ℝ) ^ (-(2 * n : ℤ)) := by
    rw [map_sub, map_one]; have := he0a; push_cast at this; exact this
  have hepsOK : (N₀ : ℂ) * e0 ∈ OK S.d := hmulOK _ _ (hnatOK N₀) he0'
  have hidem : IsIdem lam S.d (2 * n) ((N₀ : ℂ) * e0) := by
    refine ⟨hepsOK, ?_, ?_⟩
    · rw [hlam _ (GlobalTheory.MomOne.LiftChange.norm_int hd4 hepsOK).1]; exact he0a
    · rw [hlam _ (GlobalTheory.MomOne.LiftChange.norm_int hd4 hepsOK).2.1, map_mul, hN0r, map_mul, norm_mul]
      calc _ ≤ 1 * (q : ℝ) ^ (-((2 * n : ℕ) : ℤ)) := mul_le_mul (hnat N₀) he0b (norm_nonneg _) zero_le_one
        _ = _ := one_mul _
  have htI : ∀ i, ∃ z : ℤ, (hf S.Hm (((N₀ : ℂ) * e0) • b i) t).im = z := fun i => by
    have : hf S.Hm (((N₀ : ℂ) * e0) • b i) t = hf S.Hm (e0 • b i) ((N₀ : ℂ) • t) := by
      rw [hf_smul_left, hf_smul_left, hf_smul_right, hN0r]; ring
    rw [this]; exact himI _ (GlobalTheory.MomOne.LiftChange.smul_mem S hS he0' (hb.1 i)) _ hNt

  obtain ⟨s, c, hs, hc, hbc, hexp⟩ := GlobalTheory.T.exists_dualBasis_of_unimodular_lattice_at_prime q g S r b hS hb
  choose a ha using fun j => (hZ _ (hbOK v hv (c j) (hc j))).1
  haveI : NeZero (q ^ n) := ⟨pow_ne_zero _ hqp.ne_zero⟩
  let A : Fin r → ZMod (q ^ n) := fun j =>
    PadicInt.toZModPow n (a j) * (N₀ : ZMod (q ^ n)) * ((s : ZMod (q ^ n)))⁻¹
  let yt : Fin r → Fin (q ^ n) := fun j => ⟨(A j).val, ZMod.val_lt _⟩
  have hyt : ∀ j, ‖ι ((N₀ : ℂ) * beta S.d S.Hm v (c j) - (s : ℂ) * ((yt j : ℕ) : ℂ))‖ ≤ (q : ℝ) ^ (-(n : ℤ)) := by
    intro j
    have e1 : ι ((N₀ : ℂ) * beta S.d S.Hm v (c j) - (s : ℂ) * ((yt j : ℕ) : ℂ)) =
        GlobalTheory.MomOne.zc ((N₀ : ℤ_[q]) * a j - (s : ℤ_[q]) * ((yt j : ℕ) : ℤ_[q])) := by
      rw [map_sub, map_mul, map_mul, ha j, map_natCast, map_natCast, map_natCast]
      simp [GlobalTheory.MomOne.zc]
    rw [e1, norm_zc, PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker]
    have hinv : (s : ZMod (q ^ n)) * (s : ZMod (q ^ n))⁻¹ = 1 := ZMod.coe_mul_inv_eq_one s (Nat.Coprime.pow_right n hs)
    have hv' : (((yt j : ℕ)) : ZMod (q ^ n)) = A j := ZMod.natCast_zmod_val (A j)
    simp only [map_sub, map_mul, map_natCast, hv', A]
    linear_combination (-(PadicInt.toZModPow n (a j) * (N₀ : ZMod (q ^ n)))) * hinv

  set B : Fin g → ℂ := ∑ i, ((yt i : ℕ) : ℂ) • b i with hBdef
  have hB : B ∈ S.La := Submodule.sum_mem _ fun i _ => by
    rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem (hb.1 i) _
  set w := v - e0 • B with hwdef
  have hw : w ∈ S.La := sub_mem hv (GlobalTheory.MomOne.LiftChange.smul_mem S hS he0' hB)
  have hbc' : ∀ i j, beta S.d S.Hm (b i) (c j) = if i = j then (s : ℂ) else 0 := fun i j => by
    rw [hconjB (c j) (b i), hbc]; split_ifs <;> simp
  have hBc : ∀ j, beta S.d S.Hm B (c j) = ((yt j : ℕ) : ℂ) * s := fun j => by
    rw [hBdef, bsuml]
    simp [bsl, hbc']
  have hkey : ∀ x ∈ S.La, ‖ι (beta S.d S.Hm x w)‖ ≤ (q : ℝ) ^ (-(2 * n : ℤ)) ∧
      ‖ι (conj (beta S.d S.Hm x w))‖ ≤ (q : ℝ) ^ (-(n : ℤ)) := by
    intro x hx
    constructor
    · rw [hwdef, bsubr, bsr, map_sub, map_mul]
      refine (usub _ _).trans (max_le (hvs x hx) ?_)
      rw [norm_mul]
      calc _ ≤ (q : ℝ) ^ (-(2 * n : ℤ)) * 1 := mul_le_mul he0b' (hOK1 _ (hbOK x hx B hB)) (norm_nonneg _) (hpos _)
        _ = _ := mul_one _
    · rw [← hconjB x w]
      have hsum : (s : ℂ) * beta S.d S.Hm w x =
          ∑ j, beta S.d S.Hm (b j) x * (beta S.d S.Hm v (c j) - e0 * (((yt j : ℕ) : ℂ) * s)) := by
        have h1 : (s : ℂ) * beta S.d S.Hm w x = beta S.d S.Hm w ((s : ℂ) • x) := by rw [bsr, map_natCast]
        rw [h1, hexp x hx, bsumr]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [bsr, ← hconjB, hwdef, bsubl, bsl, hBc]
      have hterm : ∀ j, ‖ι (beta S.d S.Hm v (c j) - e0 * (((yt j : ℕ) : ℂ) * s))‖ ≤ (q : ℝ) ^ (-(n : ℤ)) := by
        intro j
        have hdecomp : (N₀ : ℂ) * (beta S.d S.Hm v (c j) - e0 * (((yt j : ℕ) : ℂ) * s)) =
            ((N₀ : ℂ) * beta S.d S.Hm v (c j) - (s : ℂ) * ((yt j : ℕ) : ℂ)) -
              ((N₀ : ℂ) * e0 - 1) * (((yt j : ℕ) : ℂ) * s) := by ring
        have h2 : ‖ι (beta S.d S.Hm v (c j) - e0 * (((yt j : ℕ) : ℂ) * s))‖ =
            ‖ι ((N₀ : ℂ) * (beta S.d S.Hm v (c j) - e0 * (((yt j : ℕ) : ℂ) * s)))‖ := by
          rw [map_mul, norm_mul, hnat1 N₀ hcop, one_mul]
        rw [h2, hdecomp, map_sub]
        refine (usub _ _).trans (max_le (hyt j) ?_)
        rw [map_mul, norm_mul]
        calc _ ≤ (q : ℝ) ^ (-(2 * n : ℤ)) * 1 :=
              mul_le_mul he0a' (by rw [map_mul, norm_mul]; exact mul_le_one₀ (hnat _) (norm_nonneg _) (hnat _))
                (norm_nonneg _) (hpos _)
          _ ≤ _ := by rw [mul_one]; exact hpow_le
      have h3 : ‖ι (beta S.d S.Hm w x)‖ = ‖ι ((s : ℂ) * beta S.d S.Hm w x)‖ := by
        rw [map_mul, norm_mul, hnat1 s hs, one_mul]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [h3, hsum, map_sum]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (hpos _) fun j _ => ?_
      rw [map_mul, norm_mul]
      calc _ ≤ 1 * (q : ℝ) ^ (-(n : ℤ)) :=
            mul_le_mul (hOK1 _ (hbOK _ (hb.1 j) x hx)) (hterm j) (norm_nonneg _) zero_le_one
        _ = _ := one_mul _
  set L := ((q : ℂ) ^ n)⁻¹ • w with hLdef
  have hbL : ∀ x, beta S.d S.Hm x L = beta S.d S.Hm x w / (q : ℂ) ^ n := fun x => by
    rw [hLdef, bsr, map_inv₀, hqr, div_eq_inv_mul]
  have hLOK : ∀ x ∈ S.La, beta S.d S.Hm x L ∈ OK S.d := fun x hx => by
    rw [hbL]
    exact hdiv _ n (hbOK x hx w hw) ((hkey x hx).1.trans hpow_le) (hkey x hx).2
  have hL : L ∈ S.La := hS.2.2.2.2.2.2.2 L fun x hx => by
    obtain ⟨u, v', h⟩ := hLOK x hx
    exact ⟨v', H5 _ _ _ _ h⟩
  have hLs : ∀ x ∈ S.La, ‖ι (beta S.d S.Hm x L)‖ ≤ (q : ℝ) ^ (-(n : ℤ)) := fun x hx => by
    have h := (hkey x hx).1
    have e2 : beta S.d S.Hm x w = (q : ℂ) ^ n * beta S.d S.Hm x L := by rw [hbL]; field_simp
    rw [e2, map_mul, norm_mul, hqn] at h
    have hp : (0 : ℝ) < (q : ℝ) ^ (-(n : ℤ)) := by positivity
    have : (q : ℝ) ^ (-(2 * n : ℤ)) = (q : ℝ) ^ (-(n : ℤ)) * (q : ℝ) ^ (-(n : ℤ)) := by
      rw [← zpow_add₀ (by positivity)]; ring_nf
    rw [this] at h
    exact le_of_mul_le_mul_left h hp

  set lamV := (N₀ : ℂ) • L with hlamV
  have hlamL : lamV ∈ S.La := by rw [hlamV, Nat.cast_smul_eq_nsmul]; exact nsmul_mem hL _
  have hliftY : liftY q n ((N₀ : ℂ) * e0) b yt = (((N₀ : ℂ) * e0) / (q : ℂ) ^ n) • B := rfl
  have hysplit : ((N₀ : ℂ) / (q : ℂ) ^ n) • v = liftY q n ((N₀ : ℂ) * e0) b yt + lamV := by
    rw [hliftY, hlamV, hLdef, hwdef]
    simp only [smul_sub, smul_smul]
    rw [div_eq_mul_inv, div_eq_mul_inv]
    module
  have hkapt : kap S.Hm lamV t = 1 := by
    obtain ⟨k, hk⟩ := himI L hL _ hNt
    refine kap_eq_one _ _ _ k ?_
    rw [hlamV, hf_smul_left, ← hk, hf_smul_right, hN0r]
  have hWl : opW S.d S.Hm lamV (opU S.Hm t e) = opU S.Hm t e := by
    have h1 := (H1 lamV t e).2.1
    conv_rhs => rw [← he.2 lamV hlamL]
    funext z
    rw [opW, h1, hkapt]
    simp only [opU, opW]
    ring
  have hβ : beta S.d S.Hm (liftY q n ((N₀ : ℂ) * e0) b yt) lamV ∈ OK S.d := by
    have hγOK : (N₀ : ℂ) * (N₀ : ℂ) * e0 * beta S.d S.Hm B L ∈ OK S.d :=
      hmulOK _ _ (hmulOK _ _ (hmulOK _ _ (hnatOK _) (hnatOK _)) he0') (hLOK B hB)
    have e3 : beta S.d S.Hm (liftY q n ((N₀ : ℂ) * e0) b yt) lamV =
        (N₀ : ℂ) * (N₀ : ℂ) * e0 * beta S.d S.Hm B L / (q : ℂ) ^ n := by
      rw [hliftY, hlamV, bsl, bsr, hN0r]; ring
    rw [e3]
    refine hdiv _ n hγOK ?_ ?_
    · rw [map_mul, norm_mul]
      have h4 : ‖ι ((N₀ : ℂ) * (N₀ : ℂ) * e0)‖ ≤ 1 := by
        rw [map_mul, map_mul, norm_mul, norm_mul]
        exact mul_le_one₀ (mul_le_one₀ (hnat _) (norm_nonneg _) (hnat _)) (norm_nonneg _) (hOK1 _ he0')
      calc _ ≤ 1 * (q : ℝ) ^ (-(n : ℤ)) := mul_le_mul h4 (hLs B hB) (norm_nonneg _) zero_le_one
        _ = _ := one_mul _
    · have h5 := hOK1 _ (hconjOK _ (hLOK B hB))
      have h6 := hnat N₀
      simp only [map_mul, hN0r, norm_mul]
      calc _ ≤ 1 * 1 * (q : ℝ) ^ (-(2 * n : ℤ)) * 1 := by gcongr
        _ ≤ _ := by rw [one_mul, one_mul, mul_one]; exact hpow_le
  have hWeq : opW S.d S.Hm (((N₀ : ℂ) / (q : ℂ) ^ n) • v) (opU S.Hm t e) =
      opW S.d S.Hm (liftY q n ((N₀ : ℂ) * e0) b yt) (opU S.Hm t e) := by
    rw [hysplit, ← (H1 _ lamV _).2.2 hβ, hWl]

  have hkap : ∀ a : Fin r → ℕ, kap S.Hm (∑ i, (a i : ℂ) • b i) (((N₀ : ℂ) / (q : ℂ) ^ n) • v) =
      kap S.Hm (vecA n b fun i => (a i : ℤ_[q])) (liftY q n ((N₀ : ℂ) * e0) b yt) := by
    intro a
    set D : Fin g → ℂ := ∑ i, (((a i / q ^ n : ℕ)) : ℂ) • b i with hD
    have hDL : D ∈ S.La := Submodule.sum_mem _ fun i _ => by
      rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem (hb.1 i) _
    have hsplitA : ∑ i, (a i : ℂ) • b i = vecA n b (fun i => (a i : ℤ_[q])) + (q : ℂ) ^ n • D := by
      rw [vecA, hD, Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_natCast, ZMod.val_natCast, smul_smul, ← add_smul]
      congr 1
      have h : ((a i % q ^ n + q ^ n * (a i / q ^ n) : ℕ) : ℂ) = (a i : ℂ) := by rw [Nat.mod_add_div]
      push_cast at h
      linear_combination -h
    have hkD : kap S.Hm ((q : ℂ) ^ n • D) (liftY q n ((N₀ : ℂ) * e0) b yt) = 1 := by
      obtain ⟨k, hk⟩ := himI D hDL _ (GlobalTheory.MomOne.LiftChange.smul_mem S hS hepsOK hB)
      refine kap_eq_one _ _ _ k ?_
      have : hf S.Hm ((q : ℂ) ^ n • D) (liftY q n ((N₀ : ℂ) * e0) b yt) = hf S.Hm D (((N₀ : ℂ) * e0) • B) := by
        rw [hf_smul_left, hliftY, hf_smul_right, hf_smul_right, map_div₀, hqr]
        field_simp
      rw [this]; exact hk
    have hsumL : ∑ i, (a i : ℂ) • b i ∈ S.La := Submodule.sum_mem _ fun i _ => by
      rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem (hb.1 i) _
    have hkl : kap S.Hm (∑ i, (a i : ℂ) • b i) lamV = 1 := by
      obtain ⟨k, hk⟩ := himI _ hsumL lamV hlamL
      exact kap_eq_one _ _ _ k hk
    rw [hysplit, (H6 _ _ _).1, hkl, mul_one, hsplitA, (H6 _ _ _).2, hkD, mul_one]
  exact ⟨hre, 2 * n, (N₀ : ℂ) * e0, yt, hidem, le_rfl, htI, hWeq, hkap⟩

end GlobalTheory.MomN
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.GoodLiftEqIdempotentLiftStatement
open GlobalTheory.MomN Formalism.L2.Ker.JMB
open scoped ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodLift_eq_idempotent_lift : ∀ (q : ℕ) [Fact q.Prime] (lam : Qbar →+* ℂ_[q]) (g : ℕ) (S : Setup g) (r : ℕ) (b : Fin r → Fin g → ℂ) (e : (Fin g → ℂ) → ℂ) (t : Fin g → ℂ), S.Ok → GlobalTheory.MomOne.Split S.d q → S.NNBasis q b → S.IsTheta e → ∀ N₀ : ℕ, 0 < N₀ → Nat.Coprime N₀ q → (N₀ : ℂ) • t ∈ S.La → ∀ (n : ℕ), ∀ y ∈ AddSubgroup.closure {y : Fin g → ℂ | ∃ κ ∈ OK S.d, ‖lamA lam (conj κ)‖ ≤ (q : ℝ) ^ (-(2 * n : ℤ)) ∧ ∃ x ∈ S.La, y = (κ * (N₀ : ℂ) / (q : ℂ) ^ n) • x}, (∃ z : ℤ, (beta S.d S.Hm y y).re = z) ∧ ∃ (m : ℕ) (eps : ℂ) (yt : Fin r → Fin (q ^ n)), IsIdem lam S.d m eps ∧ 2 * n ≤ m ∧ (∀ i, ∃ z : ℤ, (hf S.Hm (eps • b i) t).im = z) ∧ opW S.d S.Hm y (opU S.Hm t e) = opW S.d S.Hm (liftY q n eps b yt) (opU S.Hm t e) ∧ ∀ a : Fin r → ℕ, kap S.Hm (∑ i, (a i : ℂ) • b i) y = kap S.Hm (vecA n b fun i => (a i : ℤ_[q])) (liftY q n eps b yt) := by
  first | exact @GlobalTheory.MomN.goodLift_eq | exact GlobalTheory.MomN.goodLift_eq | (intros; apply GlobalTheory.MomN.goodLift_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitPeriodTranslatesMomentsFinite
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

namespace GlobalTheory.MomFin

theorem U_zero (D : D7) (T : Tor D) {N N' : ℕ} (G : VC D N N' → ℂ) : U D T 0 G = G := by
  funext z; simp [U, Hf]

theorem U_transport (D : D7) (T : Tor D) {N N' g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (e : VC D N N' ≃L[ℂ] (Fin g → ℂ))
    (hhf : ∀ x y, JMB.hf Hm (e x) (e y) = Hf D T x y) (t : VC D N N') (F : VC D N N' → ℂ) :
    JMB.opU Hm (e t) (fun z => F (e.symm z)) = fun z => U D T t F (e.symm z) := by
  funext z
  have h1 : JMB.hf Hm z (e t) = Hf D T (e.symm z) t := by
    rw [← hhf]; simp
  simp only [JMB.opU, U, map_add (f := _), ContinuousLinearEquiv.symm_apply_apply, h1, hhf]
  congr 2
  ring

theorem wop_transport (D : D7) (T : Tor D) {N N' g : ℕ} (S : JMB.Setup g) (e : VC D N N' ≃L[ℂ] (Fin g → ℂ))
    (hhf : ∀ x y, JMB.hf S.Hm (e x) (e y) = Hf D T x y) (hd : S.d = D.host.d) (p : ℕ) [Fact p.Prime]
    (y t : VC D N N') (F : VC D N N' → ℂ) (hq : ∃ m : ℤ, (JMB.beta S.d S.Hm (e y) (e y)).re = m) :
    JMB.opW S.d S.Hm (e y) (JMB.opU S.Hm (e t) (fun z => F (e.symm z))) =
      fun z => Wop D T p y (U D T t F) (e.symm z) := by
  obtain ⟨m, hm⟩ := hq
  have hqH : qH D T y = (JMB.beta S.d S.Hm (e y) (e y)).re := by
    rw [qH, JMB.beta, hhf, hd, Complex.re_ofReal_mul]
  have hU := U_transport D T S.Hm e hhf t F
  have hUy := U_transport D T S.Hm e hhf y (U D T t F)
  have hphase : wPh D T p y = Complex.exp ((Real.pi : ℂ) * Complex.I * (qH D T y : ℂ)) := by
    have hE : Complex.exp ((Real.pi : ℂ) * Complex.I * (qH D T y : ℂ)) = (-1 : ℂ) ^ m := by
      rw [hqH.trans hm, show (Real.pi : ℂ) * Complex.I * ((m : ℝ) : ℂ) = (m : ℂ) * (Real.pi * Complex.I) by
        push_cast; ring, Complex.exp_int_mul, Complex.exp_pi_mul_I]
    unfold wPh
    split_ifs with hp
    · rfl
    · rw [hE]
      have hex : ∃ s : ℂ, ∃ (k : ℕ) (m' : ℤ), (p : ℝ) ^ k * qH D T y = (m' : ℝ) ∧ s = (-1 : ℂ) ^ m' :=
        ⟨(-1 : ℂ) ^ m, 0, m, by rw [hqH.trans hm]; simp, rfl⟩
      obtain ⟨k, m', hm', hs⟩ := Classical.epsilon_spec hex
      rw [hs]
      rw [hqH.trans hm] at hm'
      have hm'' : m' = (p : ℤ) ^ k * m := by exact_mod_cast hm'.symm
      have hodd : Odd ((p : ℤ) ^ k) := by
        have := ((Fact.out : p.Prime).odd_of_ne_two hp).pow (n := k)
        exact_mod_cast this
      rw [hm'', zpow_mul, hodd.neg_one_zpow]
  funext z
  simp only [JMB.opW, hU, hUy, Wop, hphase, hqH]

theorem jet_transport (D : D7) {N N' g : ℕ} (e : VC D N N' ≃L[ℂ] (Fin g → ℂ)) (G : VC D N N' → ℂ)
    (hG : ContDiff ℂ ⊤ G) (k : ℕ) (v : Fin k → VC D N N') :
    JMB.jetV (fun z => G (e.symm z)) (fun j => e (v j)) = iteratedFDeriv ℂ k G 0 v := by
  have h := (e.symm : (Fin g → ℂ) →L[ℂ] VC D N N').iteratedFDeriv_comp_right hG (0 : Fin g → ℂ) (i := k) le_top
  simp only [JMB.jetV]
  rw [show (fun z => G (e.symm z)) = G ∘ (e.symm : (Fin g → ℂ) →L[ℂ] VC D N N') from rfl, h]
  simp

theorem embV_sum (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' r : ℕ} (a : Fin r → ℕ)
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) :
    embV D (tor0 D cc δ) (∑ i, ((a i : ℕ) : D.host.E) • b i) = ∑ i, ((a i : ℕ) : ℂ) • embV D (tor0 D cc δ) (b i) := by
  funext τ i j
  set_option synthInstance.maxHeartbeats 100000 in
    simp [embV, tor0, Finset.sum_apply, Matrix.sum_apply, map_sum]

theorem kap_transport (D : D7) (T : Tor D) {N N' g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (e : VC D N N' ≃L[ℂ] (Fin g → ℂ))
    (hhf : ∀ x y, JMB.hf Hm (e x) (e y) = Hf D T x y) (x y : VC D N N') : kap D T x y = JMB.kap Hm (e x) (e y) := by
  simp only [kap, JMB.kap, hhf]

theorem moments_fin : (∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → B.EqP χ) → (∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' → ∀ t : VC D N N', (∃ a : ℕ, 0 < a ∧ a • t ∈ La D B.tor L L') → ∀ α, Formalism.MainNotions.TaylorLogMetric.taylor D (U D B.tor t (B.eNat χ N N' L L')) α ∈ Qbar) → (∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), p ≠ 2 → jacobiSym (-(D.host.d : ℤ)) p = 1 → Nat.Coprime (Ideal.absNorm cc) p → ∃ Ω : ℂ_[p], ‖Ω‖ = 1 ∧ GlobalTheory.MomT.MomentsAt D cc δ (B.eNat χ) lam Ω) := by
  intro hMv hAlg D cc δ B χ hcc hδ hχ p _ lam hp2 hjac hcop
  obtain ⟨hdp, hd16, -, -, -⟩ := GlobalTheory.T.cmBaseField_integers_and_curveIdeal_facts D
  have hSplit : GlobalTheory.MomOne.Split D.host.d p := Or.inr ⟨hp2, hjac⟩
  obtain ⟨ι, hι⟩ := GlobalTheory.PadicComplexIso.exists_ringEquiv_extending p lam
  obtain ⟨δ₀, θ, Ω, hPer⟩ := GlobalTheory.MomN.exists_per D.host.d p ι hdp hd16 hSplit
  obtain ⟨hTh, h12, hδ₀, hAll, hΩ, hLaws, hPerM⟩ := hPer
  obtain ⟨hQ, hUn⟩ := GlobalTheory.T.discOneScale_ratio_ideal_ring_algebraic_unit D cc δ δ₀ hcc hδ h12 p hp2 hcop
  have hne : δ / δ₀ ≠ 0 := by
    intro h; have := hUn ι; rw [h, map_zero, norm_zero] at this; exact zero_ne_one this
  have hδ0 : δ ≠ 0 := by intro h; apply hne; rw [h, zero_div]
  have hlam : lamC lam (δ / δ₀) = ι (δ / δ₀) := by rw [lamC, dite_eq_left hQ]; exact (hι ⟨_, hQ⟩).symm
  refine ⟨Ω * (Ideal.absNorm cc : ℂ_[p]) * lamC lam (δ / δ₀), ?_, ?_⟩
  · rw [norm_mul, norm_mul, hΩ, hlam, hUn ι, GlobalTheory.MomOne.Basic.norm_nat_eq_one (Nat.Coprime.symm hcop)]
    norm_num
  intro N N' L L' hA t ht
  obtain ⟨g, S, e, hSd, hSok, hLa, hhf, hbeta, hLaRep, hNN⟩ := GlobalTheory.T.exists_analyticSetup_periodLatticePair D cc δ B hcc hδ N N' L L' hA
  obtain ⟨N₀, hN₀, hN₀p, hN₀t⟩ := ht
  have hHm : S.Hm.IsHermitian := hSok.2.2.1.1
  have hd0 : 0 < S.d := hSd ▸ hdp.pos
  have hH := GlobalTheory.HeisOps.heisenberg g S.d S.Hm hd0 hHm
  refine ⟨N₀, hN₀p, fun r b hb => ?_⟩
  set F := B.eNat χ N N' L L' with hFdef
  set e' : (Fin g → ℂ) → ℂ := fun z => F (e.symm z) with he'
  have hTheta : S.IsTheta e' := GlobalTheory.T.normalizedThetaVector_isometry_isTheta D cc δ B χ hcc hδ hχ hδ0 N N' L L' hA g S e hSd hLa hhf
  have hF : ContDiff ℂ ⊤ F := by
    have : F = fun x => e' (e x) := by funext x; simp [e']
    rw [this]; exact hTheta.1.comp e.contDiff
  have hAlg0 : ∀ α, Formalism.MainNotions.TaylorLogMetric.taylor D F α ∈ Qbar := by
    have := hAlg D cc δ B χ hcc hδ hχ N N' L L' hA 0 ⟨1, one_pos, by simp⟩
    simpa [U_zero] using this
  have hAJ : S.AlgJets δ₀ e' := GlobalTheory.T.algebraicJets_of_algebraic_taylor D cc δ δ₀ B N N' L L' F hQ hδ₀ hF hAlg0 g S e hLa hLaRep
  set bS : Fin r → Fin g → ℂ := fun i => e (δ • embV D B.tor (b i)) with hbSdef
  have hbS : S.NNBasis p bS := hNN p r b hcop hb
  have hN₀S : (N₀ : ℂ) • e t ∈ S.La := by
    rw [← map_smul, Nat.cast_smul_eq_nsmul, hLa]; exact hN₀t
  have ht' : S.PrimeTo p (e t) := ⟨N₀, hN₀, hN₀p, hN₀S⟩
  obtain ⟨Nμ, hμall⟩ := GlobalTheory.MomOne.Translates.moments_of_translates D.host.d p lam δ₀ θ ι Ω hdp hd16 hSplit hTh hδ₀
    hAll hι hΩ hLaws g S hSd hSok r bS hbS e' hTheta hAJ
  obtain ⟨μ, -, hM1⟩ := hμall (e t) ht'
  have hUt : JMB.opU S.Hm (e t) e' = fun z => U D B.tor t F (e.symm z) := U_transport D B.tor S.Hm e hhf t F
  have hUF : ContDiff ℂ ⊤ (U D B.tor t F) := by
    have : U D B.tor t F = fun x => JMB.opU S.Hm (e t) e' (e x) := by funext x; rw [hUt]; simp
    rw [this]; exact ((hH.2.2.1 (e t) e' hTheta.1).1).comp e.contDiff
  have hnorm : ‖μ‖ ≤ 1 := by
    have hG : ContDiff ℂ ⊤ (JMB.opU S.Hm (e t) e') := (hH.2.2.1 (e t) e' hTheta.1).1
    refine (GlobalTheory.T.momentMeasure_norm_le_one_iff_latticeIntegral p ι lam δ₀ Ω g S r bS (e t) _ μ hι hδ₀ hΩ hSok (hSd ▸ hSplit) hbS ht' hG hM1).2 ?_
    rw [hUt]
    have hE := GlobalTheory.T.normalizedVector_translates_prime_order_integral hMv D cc δ B hcc hδ p hp2 hjac hcop ι δ₀ θ Ω ⟨hTh, h12, hδ₀, hAll, hΩ, hLaws, hPerM⟩ χ hχ
      N N' L L' hA t ⟨N₀, hN₀, hN₀p, hN₀t⟩
    exact GlobalTheory.T.latticeJetsAreBoundedMoments_pullback p ι (VC D N N') (Fin g → ℂ) _ (La D B.tor L L') S.La.toAddSubgroup
      (e.symm : (Fin g → ℂ) →L[ℂ] VC D N N') (U D B.tor t F) hUF
      (fun x hx => ⟨1, Nat.coprime_one_left _, by
        rw [one_smul, ← hLa]; simpa using hx⟩) hE
  refine ⟨μ, hnorm, fun n y hy => ?_⟩
  have hyS := GlobalTheory.T.goodLiftsLattice_map_mem_setup_goodLifts D cc δ N N' L L' g S e p lam N₀ n hSd hLa y hy
  obtain ⟨hqy, m, eps, yt, hId, hm, hIm, hW, hK⟩ :=
    GlobalTheory.T.goodLift_eq_idempotent_lift p lam g S r bS e' (e t) hSok (hSd ▸ hSplit) hbS hTheta N₀ hN₀ hN₀p hN₀S n (e y) hyS
  set G := Wop D B.tor p y (U D B.tor t F) with hGdef
  have hWt : JMB.opW S.d S.Hm (e y) (JMB.opU S.Hm (e t) e') = fun z => G (e.symm z) :=
    wop_transport D B.tor S e hhf hSd p y t F hqy
  have hGc : ContDiff ℂ ⊤ G := by
    have : G = fun x => JMB.opW S.d S.Hm (e y) (JMB.opU S.Hm (e t) e') (e x) := by funext x; rw [hWt]; simp
    rw [this]; exact ((hH.2.2.1 (e y) _ (hH.2.2.1 (e t) e' hTheta.1).1).2).comp e.contDiff
  have hImLa : ∀ x ∈ La D B.tor L L', ∀ x' ∈ La D B.tor L L', ∃ k : ℤ, (Hf D B.tor x x').im = k := by
    intro x hx x' hx'
    obtain ⟨u, v, huv⟩ := hSok.2.2.2.2.2.2.1 (e x) ((hLa x).2 hx) (e x') ((hLa x').2 hx')
    exact ⟨v, by rw [← hhf]; exact hH.2.2.2.2.1 _ _ u v huv⟩
  have hyT : ∃ a : ℕ, 0 < a ∧ a • y ∈ La D B.tor L L' := by
    refine ⟨p ^ n, pow_pos (Fact.out : p.Prime).pos n, ?_⟩
    rw [← hLa, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ]
    push_cast
    exact GlobalTheory.T.prime_pow_smul_goodLift_mem_setupLattice g S p lam N₀ n hSok (e y) hyS
  have hqH : ∃ m : ℤ, qH D B.tor y = m := by
    obtain ⟨z, hz⟩ := hqy
    refine ⟨z, ?_⟩
    rw [qH, ← hz, JMB.beta, hhf, hSd, Complex.re_ofReal_mul]
  have hCoef : CoefIn D G Qbar := GlobalTheory.T.coefIn_weilOperator_translate_algebraic D B.tor N N' F (La D B.tor L L') p y t hF
    (fun s hs α => hAlg D cc δ B χ hcc hδ hχ N N' L L' hA s hs α) ⟨N₀, hN₀, hN₀t⟩ hyT hImLa hqH
  refine ⟨hCoef, fun k y' gf hg => ?_⟩
  set ys : Fin k → Fin g → ℂ := fun j => (δ₀ / δ) • e (δ • embV D B.tor (y' j)) with hysdef
  have hys : ∀ j, S.AlgDir (ys j) := fun j => GlobalTheory.T.algebraicDirection_scaled_embedding D cc δ δ₀ B N N' L L' hcc hA hQ hne g S e hLa (y' j)
  have hdir : ∀ j, δ₀⁻¹ • ys j = e (embV D B.tor (y' j)) := by
    intro j
    simp only [ys, map_smul, smul_smul]
    rw [show δ₀⁻¹ * (δ₀ / δ * δ) = 1 by field_simp, one_smul]
  have hf := GlobalTheory.T.eq_on_padicInt_of_eq_on_naturals_moment p lam Ω g S r n k bS (JMB.liftY p n eps bS yt) ys gf (fun a => by
    rw [hg a, ← hK a, kap_transport D B.tor S.Hm e hhf, embV_sum]
    have hs : e (δ • ∑ i, ((a i : ℕ) : ℂ) • embV D (tor0 D cc δ) (b i)) = ∑ i, ((a i : ℕ) : ℂ) • bS i := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [bS, Finset.smul_sum, map_sum, map_smul, smul_comm δ]
    rw [hs]
    congr 1
    exact Finset.prod_congr rfl fun j _ => (GlobalTheory.T.pairing_scaledDirections_eq_period_pairing D cc δ δ₀ B N N' g S e p lam Ω r b (y' j) _ hQ hne hcop hbeta).symm)
  obtain ⟨-, hμf⟩ := hM1 n m eps hId hm (fun _ i => hIm i) yt k ys hys gf hf
  rw [← hW, hWt] at hμf
  simp only [hdir] at hμf
  rw [jet_transport D e G hGc k] at hμf
  obtain ⟨-, hjet⟩ := GlobalTheory.T.iteratedFDeriv_algebraic_directions_jet_transport D cc δ p lam N N' G hGc hCoef k y'
  rw [hjet, ← hμf]
  rfl

end GlobalTheory.MomFin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitPeriodTranslatesMomentsFiniteStatement
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitPeriodTranslates_moments_finite : (∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → B.EqP χ) → (∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' → ∀ t : VC D N N', (∃ a : ℕ, 0 < a ∧ a • t ∈ La D B.tor L L') → ∀ α, Formalism.MainNotions.TaylorLogMetric.taylor D (U D B.tor t (B.eNat χ N N' L L')) α ∈ Qbar) → (∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]), p ≠ 2 → jacobiSym (-(D.host.d : ℤ)) p = 1 → Nat.Coprime (Ideal.absNorm cc) p → ∃ Ω : ℂ_[p], ‖Ω‖ = 1 ∧ GlobalTheory.MomT.MomentsAt D cc δ (B.eNat χ) lam Ω) := by
  first | exact @GlobalTheory.MomFin.moments_fin | exact GlobalTheory.MomFin.moments_fin | (intros; apply GlobalTheory.MomFin.moments_fin <;> assumption)
end
