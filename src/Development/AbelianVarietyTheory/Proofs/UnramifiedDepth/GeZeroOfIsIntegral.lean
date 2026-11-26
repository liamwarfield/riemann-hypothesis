module

public import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralChartDirectionsAreEigenvectors
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.VVAlgebraMapNonnegDvr

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EigenvectorMemSpanBlockOfBasis
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField

namespace GlobalTheory

theorem eigenvector_mem_span_block_of_basis : ∀ (K C : Type) [Field K] [Field C] (ι : K →+* C) (O A : Type) [Fintype A] (n : A → ℕ) (d : ℕ) (M : O → Matrix (Fin d) (Fin d) C) (em : A → O → C) (u : (Σ a : A, Fin (n a)) → Fin d → K), Function.Injective em → (∀ x q, (M x).mulVec (fun s => ι (u q s)) = em q.1 x • fun s => ι (u q s)) → (∀ z : Fin d → K, ∃! b : (Σ a : A, Fin (n a)) → K, ∀ s, ∑ q, b q * u q s = z s) → ∀ (a : A) (z : Fin d → C), (∀ x, (M x).mulVec z = em a x • z) → ∃ b : Fin (n a) → C, z = ∑ i, b i • fun s => ι (u ⟨a, i⟩ s) := by
  intro K C _ _ ι O A _ n d M em u hem hM hb a z hz
  classical
  let U : Matrix (Σ a : A, Fin (n a)) (Fin d) K := Matrix.of u
  let W : Matrix (Fin d) (Σ a : A, Fin (n a)) K :=
    Matrix.of fun t => (hb (Pi.single t 1)).exists.choose
  have hWU : W * U = 1 := by
    ext t s
    have := (hb (Pi.single t 1)).exists.choose_spec s
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [W, U, Matrix.of_apply]
    rw [this, Pi.single_apply]
    simp [eq_comm]
  have hUW : U * W = 1 := by
    have h1 : U * W * U = U := by rw [Matrix.mul_assoc, hWU, Matrix.mul_one]
    have h2 : (1 : Matrix (Σ a : A, Fin (n a)) (Σ a : A, Fin (n a)) K) * U = U := Matrix.one_mul _
    ext q q'
    have := (hb (u q)).unique (y₁ := (U * W) q)
      (y₂ := (1 : Matrix (Σ a : A, Fin (n a)) (Σ a : A, Fin (n a)) K) q)
      (fun s => by
        have := congrFun (congrFun h1 q) s
        rw [Matrix.mul_apply] at this
        exact this)
      (fun s => by
        have := congrFun (congrFun h2 q) s
        rw [Matrix.mul_apply] at this
        exact this)
    exact congrFun this q'
  have hWU' : W.map ι * U.map ι = 1 := by
    rw [← Matrix.map_mul, hWU, Matrix.map_one _ (map_zero ι) (map_one ι)]
  have hUW' : U.map ι * W.map ι = 1 := by
    rw [← Matrix.map_mul, hUW, Matrix.map_one _ (map_zero ι) (map_one ι)]
  have hvm : ∀ c : (Σ a : A, Fin (n a)) → C,
      Matrix.vecMul c (U.map ι) = ∑ q, c q • fun s => ι (u q s) := by
    intro c
    funext s
    simp [Matrix.vecMul, dotProduct, U, Finset.sum_apply]
  have hind : ∀ c : (Σ a : A, Fin (n a)) → C,
      (∑ q, c q • fun s => ι (u q s)) = 0 → c = 0 := by
    intro c hc
    rw [← hvm] at hc
    have : Matrix.vecMul (Matrix.vecMul c (U.map ι)) (W.map ι) = c := by
      rw [Matrix.vecMul_vecMul, hUW', Matrix.vecMul_one]
    rw [← this, hc, Matrix.zero_vecMul]
  obtain ⟨c, hc⟩ : ∃ c : (Σ a : A, Fin (n a)) → C, z = ∑ q, c q • fun s => ι (u q s) := by
    refine ⟨Matrix.vecMul z (W.map ι), ?_⟩
    rw [← hvm, Matrix.vecMul_vecMul, hWU', Matrix.vecMul_one]
  have hzero : ∀ q : (Σ a : A, Fin (n a)), q.1 ≠ a → c q = 0 := by
    intro q hq
    by_contra hcq
    apply hq
    apply hem
    funext x
    have h := hz x
    have h3 : (∑ q : (Σ a : A, Fin (n a)), ((em q.1 x - em a x) * c q) • fun s => ι (u q s)) = 0 := by
      have e1 : (M x).mulVec z
          = ∑ q : (Σ a : A, Fin (n a)), (em q.1 x * c q) • fun s => ι (u q s) := by
        rw [hc, Matrix.mulVec_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [Matrix.mulVec_smul, hM, smul_smul, mul_comm]
      have e2 : em a x • z
          = ∑ q : (Σ a : A, Fin (n a)), (em a x * c q) • fun s => ι (u q s) := by
        rw [hc, Finset.smul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [smul_smul]
      simp only [sub_mul, sub_smul, Finset.sum_sub_distrib]
      rw [← e1, ← e2, h, sub_self]
    have h4 := congrFun (hind _ h3) q
    simp only [Pi.zero_apply, mul_eq_zero] at h4
    exact sub_eq_zero.mp (h4.resolve_right hcq)
  refine ⟨fun i => c ⟨a, i⟩, ?_⟩
  rw [hc, Fintype.sum_sigma, Finset.sum_eq_single a]
  · intro a' _ ha'
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [hzero ⟨a', i⟩ ha', zero_smul]
  · intro h
    exact absurd (Finset.mem_univ a) h

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.SaturatedBlocksSummand
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField

namespace GlobalTheory.SatBlocks

def intRing {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) : Subring C where
  carrier := {z | (0 : WithTop ℝ) ≤ v z}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    rw [v.map_mul]; exact add_nonneg ha hb
  one_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at *
    exact v.map_le_add ha hb
  zero_mem' := by simp
  neg_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at *
    rwa [v.map_neg]

theorem mem_intRing {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) (z : C) :
    z ∈ intRing v ↔ ((0 : ℝ) : WithTop ℝ) ≤ v z := Iff.rfl

theorem ne_zero_of_val_zero {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {z : C}
    (h : v z = 0) : z ≠ 0 := by
  rintro rfl
  simp at h

theorem inv_mem_of_val_zero {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {z : C}
    (h : v z = 0) : z⁻¹ ∈ intRing v := by
  have h1 : v (z * z⁻¹) = 0 := by rw [mul_inv_cancel₀ (ne_zero_of_val_zero v h)]; simp
  rw [v.map_mul, h, zero_add] at h1
  exact h1.ge

theorem exists_projector {C : Type} [Field C] (v : AddValuation C (WithTop ℝ)) {O A : Type}
    [DecidableEq A] {n : A → ℕ} {d : ℕ} (M : O → Matrix (Fin d) (Fin d) C) (em : A → O → C)
    (u : (Σ a : A, Fin (n a)) → Fin d → C)
    (hM : ∀ x i j, M x i j ∈ intRing v) (he : ∀ a x, em a x ∈ intRing v)
    (hu : ∀ x q, (M x).mulVec (u q) = em q.1 x • u q)
    (hs : ∀ a a', a ≠ a' → ∃ x, v (em a x - em a' x) = 0) (a : A) (S : Finset A) (ha : a ∉ S) :
    ∃ (P : Matrix (Fin d) (Fin d) C) (c : A → C), (∀ i j, P i j ∈ intRing v) ∧
      (∀ q, P.mulVec (u q) = c q.1 • u q) ∧ c a = 1 ∧ ∀ b ∈ S, c b = 0 := by
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨1, fun _ => 1, ?_, by simp, rfl, by simp⟩
    intro i j
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  | insert b S hb ih =>
    rw [Finset.mem_insert, not_or] at ha
    obtain ⟨P, c, hP, hPu, hca, hcS⟩ := ih ha.2
    obtain ⟨x, hx⟩ := hs a b ha.1
    refine ⟨((em a x - em b x)⁻¹ • (M x - em b x • (1 : Matrix (Fin d) (Fin d) C))) * P,
      fun e => (em a x - em b x)⁻¹ * (em e x - em b x) * c e, ?_, ?_, ?_, ?_⟩
    · intro i j
      rw [Matrix.mul_apply]
      refine sum_mem fun k _ => mul_mem ?_ (hP k j)
      simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
      refine mul_mem (inv_mem_of_val_zero v hx) (sub_mem (hM x i k) (mul_mem (he b x) ?_))
      rw [Matrix.one_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    · intro q
      rw [← Matrix.mulVec_mulVec, hPu, Matrix.mulVec_smul, Matrix.smul_mulVec, Matrix.sub_mulVec,
        Matrix.smul_mulVec, Matrix.one_mulVec, hu]
      ext k
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      ring
    · simp only [hca, mul_one]
      exact inv_mul_cancel₀ (ne_zero_of_val_zero v hx)
    · intro e he'
      rcases Finset.mem_insert.1 he' with rfl | h
      · simp
      · simp [hcS e h]

theorem saturated_blocks_summand : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (O A : Type) [Fintype A] [DecidableEq A] (n : A → ℕ) (d : ℕ) (M : O → Matrix (Fin d) (Fin d) C) (em : A → O → C) (u : (Σ a : A, Fin (n a)) → Fin d → C), (∀ x i j, ((0 : ℝ) : WithTop ℝ) ≤ v (M x i j)) → (∀ a x, ((0 : ℝ) : WithTop ℝ) ≤ v (em a x)) → (∀ x q, (M x).mulVec (u q) = em q.1 x • u q) → (∀ a a', a ≠ a' → ∃ x, v (em a x - em a' x) = 0) → (∀ a, ∃ w : Fin d → Fin (n a) → C, (∀ s i, ((0 : ℝ) : WithTop ℝ) ≤ v (w s i)) ∧ ∀ i i', ∑ s, u ⟨a, i⟩ s * w s i' = if i = i' then 1 else 0) → ∃ w : Fin d → (Σ a : A, Fin (n a)) → C, (∀ s q, ((0 : ℝ) : WithTop ℝ) ≤ v (w s q)) ∧ ∀ q q', ∑ s, u q s * w s q' = if q = q' then 1 else 0 := by
  intro C _ v O A _ _ n d M em u hM he hu hs hw
  choose w hwi hw using hw
  have key := fun a : A => exists_projector v M em u hM he hu hs a (Finset.univ.erase a)
    (Finset.notMem_erase a _)
  choose P c hP hPu hca hcS using key
  refine ⟨fun s q => ∑ t, P q.1 t s * w q.1 t q.2, ?_, ?_⟩
  · intro s q
    exact (mem_intRing v _).1
      (sum_mem fun t _ => mul_mem (hP _ _ _) ((mem_intRing v _).2 (hwi _ _ _)))
  · rintro ⟨b, j⟩ ⟨a, i⟩
    have h1 : ∑ s, u ⟨b, j⟩ s * ∑ t, P a t s * w a t i
        = ∑ t, (P a).mulVec (u ⟨b, j⟩) t * w a t i := by
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun s _ => by ring
    dsimp only
    rw [h1, hPu]
    by_cases hba : b = a
    · subst hba
      simp only [hca, one_smul, hw]
      simp
    · have h0 : c a b = 0 := hcS a b (by simp [hba])
      rw [if_neg (fun h => hba (congrArg Sigma.fst h))]
      simp [h0]

end GlobalTheory.SatBlocks
end

open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj Formalism.L2.FormalSeriesBounds NumberField

namespace GlobalTheory.LabelledDirections

theorem ge_zero_of_isIntegral {C : Type} [Field C] (V : VF C) {x : C} (hx : IsIntegral ℤ x) : V.Ge 0 x := by
  let A : ValuationSubring C :=
    { VF.RR V with
      mem_or_inv_mem' := by
        intro z
        by_cases hz : z = 0
        · left; rw [hz]; exact VF.Ge.zero 0
        · by_contra hc
          push Not at hc
          obtain ⟨h1, h2⟩ := hc
          have h1' : V.v z < 0 := lt_of_not_ge h1
          have h2' : V.v z⁻¹ < 0 := lt_of_not_ge h2
          have h3 : V.v (z * z⁻¹) = 0 := by rw [mul_inv_cancel₀ hz]; simp
          rw [V.v.map_mul] at h3
          have h4 : V.v z + V.v z⁻¹ ≤ V.v z + 0 := add_le_add le_rfl h2'.le
          rw [h3, add_zero] at h4
          exact absurd h1' (not_lt.2 h4) }
  have h : IsIntegral A x := hx.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral (K := C) h
  rw [← hy]
  exact y.2

theorem exists_dual {R : Type} [CommRing R] {d m : ℕ} (w : Fin d → Fin d → R) (emb : Fin m ↪ Fin d)
    (hw : ∀ v : Fin d → R, ∃! a : Fin d → R, ∀ j, ∑ k, a k * w k j = v j) :
    ∃ W : Fin d → Fin m → R, ∀ i i', ∑ s, w (emb i) s * W s i' = if i = i' then 1 else 0 := by
  classical
  let U : Matrix (Fin d) (Fin d) R := Matrix.of w
  let W : Matrix (Fin d) (Fin d) R := Matrix.of fun t => (hw (Pi.single t 1)).exists.choose
  have hWU : W * U = 1 := by
    ext t s
    have := (hw (Pi.single t 1)).exists.choose_spec s
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [W, U, Matrix.of_apply]
    rw [this, Pi.single_apply]
    simp [eq_comm]
  have hUW : U * W = 1 := mul_eq_one_comm.1 hWU
  refine ⟨fun s i' => W s (emb i'), fun i i' => ?_⟩
  have := congrFun (congrFun hUW (emb i)) (emb i')
  rw [Matrix.mul_apply, Matrix.one_apply] at this
  simpa [U] using this

theorem labGeoSt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], Formalism.L2.FormalSeriesBounds.LabGeoSt Xo c := by
  intro E _ _ _ H Dw l Xo c _ hs T io y C3 C _ _ V ι hι k Y hY Orb d _ lab ha
  classical
  letI := io.toAlgebra
  have hval : ∀ x : T.V, V.Ge 0 (ι (algebraMap T.V T.Fr x)) :=
    (GlobalTheory.nval_eq_of_extension T C V.v V.l V.l_prime.ne_zero V.v_l ι hι).1
  have huv : ∀ ℓ i, chartUnitVectors C3 ℓ i = algebraMap T.V T.Fr (C3.uvecT ℓ i) := fun ℓ i =>
    C3.gen.1.2.2.2.2.2.2 ℓ i
  have hint : ∀ (τ : E →+* ℂ) (x : 𝓞 E), V.Ge 0 (emA3 io ι τ x) := fun τ x =>
    ge_zero_of_isIntegral V (map_isIntegral_int (emA3 io ι τ) (Algebra.IsIntegral.isIntegral x))
  let M : 𝓞 E → Matrix (Fin (chD C3.ch)) (Fin (chD C3.ch)) C := fun a i j =>
    MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (Y.B.A.act a i)
  have hM : ∀ a z, linAct (Y.B.A.act a) z = (M a).mulVec z := fun a z => rfl
  have heig : ∀ (a : 𝓞 E) (ℓ : Lt1 Dw), (M a).mulVec (fun s => ι (chartUnitVectors C3 ℓ s)) =
      emA3 io ι ℓ.1 a • fun s => ι (chartUnitVectors C3 ℓ s) := by
    intro a ℓ
    funext i
    have h := congrArg ι (GlobalTheory.EigDir.linEig_holds E H Dw l Xo c T.Fr y.1 C3.ch a ℓ i)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_mul] at h
    refine Eq.trans ?_ h
    show ∑ j, M a i j * ι (chartUnitVectors C3 ℓ j) = _
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul]
    simp only [M, hY.act, MvPowerSeries.coeff_map]
    rfl
  refine ⟨fun o g a x => hint _ x, ?_, ?_, ?_, ?_, ?_⟩
  · intro o a x
    have h : embK c (ComplexEmbedding.conjugate (lab.tau o 0 a)) x = embK c (lab.tau o 0 a) (H.bar x) := by
      apply Subtype.ext
      rw [embK_coe, embK_coe, ComplexEmbedding.conjugate_coe_eq, H.bar_eq,
        IsCMField.complexEmbedding_complexConj]
    rw [ha.conj, hs]
    exact congrArg (ι.comp io) h
  · intro o g x i
    unfold lieBasisVector
    rw [huv]
    exact hval _
  · intro o g x a
    exact heig a ⟨lab.tau o g x.1, x.2⟩
  · intro o g
    have key := GlobalTheory.SatBlocks.saturated_blocks_summand C V.v (𝓞 E) (ZMod d)
      (fun a => Dw.mult (lab.tau o g a)) (chD C3.ch) M (fun a x => emA3 io ι (lab.tau o g a) x)
      (lieBasisVector C3 ι lab o g) (fun x i j => Y.intAct x i _) (fun a x => hint _ x)
      (fun x q => heig x ⟨lab.tau o g q.1, q.2⟩)
      (fun a a' h => ha.sep (o, g, a) (o, g, a') (fun e => h (congrArg (fun p => p.2.2) e)))
      (fun a => by
        obtain ⟨⟨w, emb, hw1, hw2⟩, -⟩ := Formalism.L2.Pj.SaturatedCharts.saturation_charts_holds Xo c T io y C3 (lab.tau o g a)
        obtain ⟨W, hW⟩ := exists_dual w emb hw2
        refine ⟨fun s i => ι (algebraMap T.V T.Fr (W s i)), fun s i => hval _, fun i i' => ?_⟩
        have := congrArg (ι.comp (algebraMap T.V T.Fr)) (hW i i')
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, apply_ite (ι.comp (algebraMap T.V T.Fr)), map_one, map_zero] at this
        refine Eq.trans ?_ this
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [map_mul, hw1]
        unfold lieBasisVector
        rw [huv]
        rfl)
    obtain ⟨w, h1, h2⟩ := key
    exact ⟨w, h1, fun q q' => by convert h2 q q'⟩
  · intro o g a v hv
    have hinj : Function.Injective fun (τ : E →+* ℂ) (x : 𝓞 E) => emA3 io ι τ x := by
      intro τ τ' h
      by_contra hne
      obtain ⟨b, hb⟩ := GlobalTheory.EigDir.embK_sep c τ τ' hne
      exact hb ((ι.comp io).injective (congrFun h b))
    obtain ⟨b, hb⟩ := GlobalTheory.eigenvector_mem_span_block_of_basis T.Fr C ι (𝓞 E) (E →+* ℂ) Dw.mult (chD C3.ch) M
      (fun τ x => emA3 io ι τ x) (chartUnitVectors C3) hinj heig C3.ch.chart.basis (lab.tau o g a) v hv
    refine ⟨fun q => if h : q.1 = a then b (Fin.cast (by rw [h]) q.2) else 0, fun q hq => dif_neg hq, ?_⟩
    rw [hb, Fintype.sum_sigma, Finset.sum_eq_single a]
    · refine Finset.sum_congr rfl fun i _ => ?_
      dsimp only
      rw [dite_eq_left rfl]
      rfl
    · intro a' _ ha'
      refine Finset.sum_eq_zero fun i _ => ?_
      dsimp only
      rw [dif_neg ha', zero_smul]
    · intro h
      exact absurd (Finset.mem_univ a) h

end GlobalTheory.LabelledDirections
