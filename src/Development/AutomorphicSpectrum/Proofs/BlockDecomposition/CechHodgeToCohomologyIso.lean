module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.PullHEq
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HdgAffIso
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GrCechFin

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleComplexLeadSurjective
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleComplexLeadSurjective
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

namespace GlobalTheory.CompanionTheory.CechSerre

theorem extend_step {R : Type} [CommRing R] (K : DCx.{w} R) (n b : ℕ) (x : ∀ p q, K.X p q) (hx : x ∈ K.T n)
    (h0 : ∀ p r, p < b → K.D x p r = 0)
    (hB : ∀ q, b + q = n + 1 → K.D x b q ∈ (K.col b).B q) :
    ∃ x' : ∀ p q, K.X p q, x' ∈ K.T n ∧ (∀ p r, p < b → x' p r = x p r) ∧
      ∀ p r, p < b + 1 → K.D x' p r = 0 := by
  have hD : K.D x ∈ K.T (n + 1) := K.D_mem n x hx
  by_cases hbn : b ≤ n
  · obtain ⟨r, rfl⟩ : ∃ r, n = b + r := ⟨n - b, by omega⟩
    obtain ⟨y, hy⟩ := CrystallineSemistableComparison.Cx.mem_B_succ.mp (hB (r + 1) (by omega))
    have hy' : K.dv b r y = K.D x b (r + 1) := hy
    refine ⟨x - K.sgl b r (((-1 : ℤ) ^ b) • y), sub_mem hx ?_, ?_, ?_⟩
    · intro p q hpq
      exact K.sgl_ne _ (by omega)
    · intro p r' hp
      simp only [Pi.sub_apply]
      rw [K.sgl_ne _ (Or.inl (by omega)), sub_zero]
    · intro p r' hp
      simp only [map_sub, CrystallineSemistableComparison.DCx.D_sgl, Pi.sub_apply, Pi.add_apply, Pi.smul_apply]
      rw [K.sgl_ne _ (Or.inl (by omega)), zero_add]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hp with hp | rfl
      · rw [h0 p r' hp, K.sgl_ne _ (Or.inl (by omega)), smul_zero, sub_zero]
      · by_cases hr : r' = r + 1
        · subst hr
          rw [K.sgl_self, map_zsmul, hy', smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul, sub_self]
        · have h1 : K.D x p r' = 0 := hD p r' (by omega)
          rw [h1, K.sgl_ne _ (Or.inr hr), smul_zero, sub_zero]
  · refine ⟨x, hx, fun _ _ _ => rfl, ?_⟩
    intro p r hp
    rcases Nat.lt_succ_iff_lt_or_eq.mp hp with hp | rfl
    · exact h0 p r hp
    · by_cases hr : p + r = n + 1
      · obtain rfl : r = 0 := by omega
        exact CrystallineSemistableComparison.Cx.mem_B_zero.mp (hB 0 hr)
      · exact hD p r hr

theorem leadE_surjective {R : Type} [CommRing R] (K : DCx.{w} R) (a j : ℕ)
    (hac : ∀ p q, q < a → Subsingleton ((K.col p).H q)) :
    Function.Surjective (leadE K j a (n := a + j)) := by
  intro t
  obtain ⟨c, hc, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (colH K a) j).1 t
  obtain ⟨y, hy, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (K.col j) a).1 c
  have hcls : ∀ (C : CrystallineSemistableComparison.Cx R) (m : ℕ) (u v : C.X m) (hu : C.d m u = 0) (hv : C.d m v = 0),
      u = v → C.cls u hu = C.cls v hv := by
    rintro C m u v hu hv rfl
    rfl
  have hy' : K.dv j a y = 0 := hy
  have hdh : K.dh j a y ∈ (K.col (j + 1)).B a := by
    have hb : (K.col (j + 1)).d a ((colMap K j).f a y) = 0 := by
      show K.dv (j + 1) a (K.dh j a y) = 0
      rw [← K.hv j a y, hy', map_zero]
    have h1 : (colMap K j).mapH a ((K.col j).cls y hy) = 0 := hc
    rw [CrystallineSemistableComparison.P.mapH_cls (colMap K j) a y hy hb] at h1
    exact ((CrystallineSemistableComparison.P.cls_surj (K.col (j + 1)) a).2.1 _ hb).mp h1
  have hmemT : ∀ (m : ℕ) (u : ∀ p q, K.X p q), u ∈ K.T m ↔ ∀ p q, p + q ≠ m → u p q = 0 :=
    fun _ _ => Iff.rfl
  have hx0 : K.sgl j a y ∈ K.T (a + j) := (hmemT _ _).2 fun p q hpq => K.sgl_ne y (by omega)
  have hDx0 : ∀ p r, p < j + 1 → K.D (K.sgl j a y) p r = 0 := by
    intro p r hp
    rw [CrystallineSemistableComparison.DCx.D_sgl, hy', map_zero, smul_zero, add_zero, K.sgl_ne _ (Or.inl (by omega))]
  have hstep : ∀ k : ℕ, ∃ x ∈ K.T (a + j), (∀ p r, p < j + 1 → x p r = K.sgl j a y p r) ∧
      ∀ p r, p < j + 2 + k → K.D x p r = 0 := by
    intro k
    induction k with
    | zero =>
      obtain ⟨x', hx', hag, hD'⟩ := extend_step K (a + j) (j + 1) (K.sgl j a y) hx0 hDx0 (by
        intro q hq
        obtain rfl : q = a := by omega
        rw [CrystallineSemistableComparison.DCx.D_sgl, hy', map_zero, smul_zero, add_zero, K.sgl_self]
        exact hdh)
      exact ⟨x', hx', hag, fun p r hp => hD' p r (by omega)⟩
    | succ k ih =>
      obtain ⟨x, hx, hag, hD⟩ := ih
      obtain ⟨x', hx', hag', hD'⟩ := extend_step K (a + j) (j + 2 + k) x hx hD (by
        intro q hq
        have hqa : q < a := by omega
        have hdv : (K.col (j + 2 + k)).d q (K.D x (j + 2 + k) q) = 0 :=
          dv_lead K (K.D x) (K.DD x) (j + 2 + k) q hD
        have := hac (j + 2 + k) q hqa
        exact ((CrystallineSemistableComparison.P.cls_surj (K.col (j + 2 + k)) q).2.1 _ hdv).mp (Subsingleton.elim _ _))
      exact ⟨x', hx', fun p r hp => (hag' p r (by omega)).trans (hag p r hp),
        fun p r hp => hD' p r (by omega)⟩
  obtain ⟨x, hx, hag, hD⟩ := hstep a
  have hD0 : K.D x = 0 := by
    funext p r
    by_cases hp : p < j + 2 + a
    · exact hD p r hp
    · exact (hmemT _ _).1 (K.D_mem _ x hx) p r (by omega)
  have hZ : (⟨x, hx⟩ : K.T (a + j)) ∈ K.tot.Z (a + j) := LinearMap.mem_ker.2 (Subtype.ext hD0)
  have hxy : x j a = y := (hag j a (by omega)).trans (K.sgl_self j a y)
  have hzf : (⟨⟨x, hx⟩, hZ⟩ : K.tot.Z (a + j)) ∈ Zf K (a + j) j := by
    intro p q hp
    exact (hag p q (by omega)).trans (K.sgl_ne y (Or.inl (by omega)))
  refine ⟨⟨⟨⟨x, hx⟩, hZ⟩, hzf⟩, ?_⟩
  rw [leadE_eq]
  apply hcls
  rw [leadC_eq K j a _ (by show (K.col j).d a (x j a) = 0; rw [hxy]; exact hy)]
  exact hcls _ _ _ _ _ _ hxy

end GlobalTheory.CompanionTheory.CechSerre
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleComplexLeadSurjectiveStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.double_complex_lead_surjective : ∀ {R : Type} [CommRing R] (K : DCx.{w} R) (a j : ℕ), (∀ p q, q < a → Subsingleton ((K.col p).H q)) →
    Function.Surjective (leadE K j a (n := a + j)) := by
  first | exact @GlobalTheory.CompanionTheory.CechSerre.leadE_surjective | exact GlobalTheory.CompanionTheory.CechSerre.leadE_surjective | (intros; apply GlobalTheory.CompanionTheory.CechSerre.leadE_surjective <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleComplexDegenerateColumnIso
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleComplexLeadZeroOfClassZero
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleComplexLeadZeroOfClassZero
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

noncomputable section

namespace GlobalTheory.CompanionTheory.CechSerre.RowKer

variable {R : Type} [CommRing R] (K : DCx.{w} R)

theorem Dv_mem (W : ∀ p q, K.X p q) (p q : ℕ) : K.Dv W p q ∈ (K.col p).B q := by
  cases q with
  | zero =>
    have h : K.Dv W p 0 = 0 := by cases p <;> rfl
    rw [h]
    exact Submodule.zero_mem _
  | succ q => exact ⟨W p q, rfl⟩

theorem dv_low (W x : ∀ p q, K.X p q) (hD : K.D W = x) (k q : ℕ) (h0 : ∀ p q, p < k → W p q = 0)
    (hx : x k (q + 1) = 0) : K.dv k q (W k q) = 0 := by
  have h1 := congrFun (congrFun hD k) (q + 1)
  rw [DCx.D_apply, hx] at h1
  have h2 : K.Dh W k (q + 1) = 0 := by
    cases k with
    | zero => rfl
    | succ k =>
      show K.dh k (q + 1) (W k (q + 1)) = 0
      rw [h0 k _ (by omega), map_zero]
  rw [h2, zero_add] at h1
  exact Auxfb.zsm_cancel k _ h1

theorem push_step (n k q : ℕ) (hkq : k + q + 1 = n) (W : ∀ p q, K.X p q)
    (hs : ∀ p q, p + q + 1 ≠ n → W p q = 0) (h0 : ∀ p q, p < k → W p q = 0)
    (hv : K.dv k q (W k q) = 0) (hH : Subsingleton ((K.col k).H q)) (hq : 0 < q) :
    ∃ W' : ∀ p q, K.X p q, (∀ p q, p + q + 1 ≠ n → W' p q = 0) ∧ K.D W' = K.D W ∧
      ∀ p q, p < k + 1 → W' p q = 0 := by
  have hB : W k q ∈ (K.col k).B q :=
    ((P.cls_surj (K.col k) q).2.1 _ hv).1 (Subsingleton.elim _ _)
  obtain ⟨q, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  obtain ⟨y, hy⟩ := hB
  have hy' : K.dv k q y = W k (q + 1) := hy
  have hsq : ((-1 : ℤ) ^ k * (-1) ^ k) = 1 := by rw [← mul_pow]; simp
  have hDY : K.D (K.sgl k q ((-1 : ℤ) ^ k • y)) =
      K.sgl (k + 1) q (K.dh k q ((-1 : ℤ) ^ k • y)) + K.sgl k (q + 1) (W k (q + 1)) := by
    rw [K.D_sgl, map_zsmul (K.dv k q), hy', map_zsmul (K.sgl k (q + 1)), smul_smul, hsq, one_smul]
  refine ⟨W - K.D (K.sgl k q ((-1 : ℤ) ^ k • y)), fun p r h => ?_, ?_, fun p r hp => ?_⟩
  · rw [hDY, Pi.sub_apply, Pi.sub_apply, Pi.add_apply, Pi.add_apply, hs p r h,
      K.sgl_ne _ (by omega : p ≠ k + 1 ∨ r ≠ q), K.sgl_ne _ (by omega : p ≠ k ∨ r ≠ q + 1)]
    simp
  · rw [map_sub, K.DD, sub_zero]
  · rw [hDY, Pi.sub_apply, Pi.sub_apply, Pi.add_apply, Pi.add_apply,
      K.sgl_ne _ (by omega : p ≠ k + 1 ∨ r ≠ q), zero_add]
    by_cases h : p = k ∧ r = q + 1
    · obtain ⟨rfl, rfl⟩ := h
      rw [K.sgl_self, sub_self]
    · rw [K.sgl_ne _ (by omega : p ≠ k ∨ r ≠ q + 1), sub_zero]
      by_cases hpk : p < k
      · exact h0 p r hpk
      · exact hs p r (by omega)

theorem push (n a i : ℕ) (hn : n = a + (i + 1)) (W : ∀ p q, K.X p q)
    (hs : ∀ p q, p + q + 1 ≠ n → W p q = 0) (hx : ∀ p q, p < i + 1 → K.D W p q = 0)
    (hac : ∀ p q, a < q → Subsingleton ((K.col p).H q)) (k : ℕ) (hk : k ≤ i) :
    ∃ W' : ∀ p q, K.X p q, (∀ p q, p + q + 1 ≠ n → W' p q = 0) ∧ K.D W' = K.D W ∧
      ∀ p q, p < k → W' p q = 0 := by
  induction k with
  | zero => exact ⟨W, hs, rfl, fun p q hp => absurd hp (Nat.not_lt_zero p)⟩
  | succ k ih =>
    obtain ⟨W₁, hs₁, hD₁, h₁⟩ := ih (by omega)
    have hv : K.dv k (a + i - k) (W₁ k (a + i - k)) = 0 :=
      dv_low K W₁ _ rfl k _ h₁ (by rw [hD₁]; exact hx k _ (by omega))
    obtain ⟨W₂, hs₂, hD₂, h₂⟩ := push_step K n k (a + i - k) (by omega) W₁ hs₁ h₁ hv
      (hac k _ (by omega)) (by omega)
    exact ⟨W₂, hs₂, hD₂.trans hD₁, h₂⟩

theorem exists_prim {n : ℕ} (z : K.tot.Z n) (hz : K.tot.cls z.1 z.2 = 0) :
    ∃ W : ∀ p q, K.X p q, (∀ p q, p + q + 1 ≠ n → W p q = 0) ∧ K.D W = z.1.1 := by
  have hB : z.1 ∈ K.tot.B n := ((P.cls_surj K.tot n).2.1 _ _).1 hz
  cases n with
  | zero =>
    have h : z.1 = 0 := (Submodule.mem_bot R).1 hB
    refine ⟨0, fun _ _ _ => rfl, ?_⟩
    rw [h, map_zero]
    rfl
  | succ m =>
    obtain ⟨u, hu⟩ := hB
    exact ⟨u.1, fun p q h => u.2 p q (by omega), congrArg Subtype.val hu⟩

theorem leadE_eq_zero : ∀ {R : Type} [CommRing R] (K : DCx.{w} R) (a j : ℕ),
    (∀ p q, a < q → Subsingleton ((K.col p).H q)) →
    ∀ z : Zf K (a + j) j, clsZ K (a + j) j z = 0 → leadE K j a z = 0 := by
  intro R _ K a j hac z hz
  obtain ⟨W, hs, hD⟩ := exists_prim K z.1 hz
  have hv : (K.col j).d a (z.1.1.1 j a) = 0 := dv_lead K _ (D_zero K z.1) j a z.2
  suffices h : leadC K j a z ∈ (colH K a).B j by
    rw [leadE_eq]
    exact ((P.cls_surj (colH K a) j).2.1 _ _).2 h
  cases j with
  | zero =>
    have h1 : z.1.1.1 0 a ∈ (K.col 0).B a := by
      rw [← hD, DCx.D_apply]
      have h2 : K.Dh W 0 a = 0 := rfl
      rw [h2, zero_add, pow_zero, one_smul]
      exact Dv_mem K W 0 a
    show _ ∈ (⊥ : Submodule R _)
    rw [Submodule.mem_bot, leadC_eq K 0 a z hv]
    exact ((P.cls_surj _ a).2.1 _ hv).2 h1
  | succ i =>
    obtain ⟨W', -, hD', h0⟩ := push K (a + (i + 1)) a i rfl W hs
      (fun p q hp => by rw [hD]; exact z.2 p q hp) hac i le_rfl
    have hD'' : K.D W' = z.1.1.1 := hD'.trans hD
    have hy : K.dv i a (W' i a) = 0 := dv_low K W' _ hD'' i a h0 (z.2 i _ (by omega))
    have hb : (K.col (i + 1)).d a ((colMap K i).f a (W' i a)) = 0 := by
      rw [(colMap K i).comm]
      exact (congrArg _ hy).trans (map_zero _)
    refine ⟨(K.col i).cls _ hy, ?_⟩
    show (colMap K i).mapH a _ = leadC K (i + 1) a z
    rw [P.mapH_cls _ a _ hy hb, leadC_eq K (i + 1) a z hv]
    refine ((P.cls_surj _ a).2.2.1 _ _ hb hv).2 ?_
    have h2 : z.1.1.1 (i + 1) a = K.dh i a (W' i a) + (-1 : ℤ) ^ (i + 1) • K.Dv W' (i + 1) a := by
      rw [← hD'', DCx.D_apply]
      rfl
    have e : (colMap K i).f a (W' i a) - z.1.1.1 (i + 1) a =
        -((-1 : ℤ) ^ (i + 1) • K.Dv W' (i + 1) a) := by
      rw [h2]
      show K.dh i a (W' i a) - _ = _
      abel
    rw [e]
    exact Submodule.neg_mem _ (zsmul_mem (Dv_mem K W' (i + 1) a) _)

end GlobalTheory.CompanionTheory.CechSerre.RowKer
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleComplexLeadZeroOfClassZeroStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.double_complex_lead_zero_of_class_zero : ∀ {R : Type} [CommRing R] (K : DCx.{w} R) (a j : ℕ), (∀ p q, a < q → Subsingleton ((K.col p).H q)) →
    ∀ z : Zf K (a + j) j, clsZ K (a + j) j z = 0 → leadE K j a z = 0 := by
  first | exact @GlobalTheory.CompanionTheory.CechSerre.RowKer.leadE_eq_zero | exact GlobalTheory.CompanionTheory.CechSerre.RowKer.leadE_eq_zero | (intros; apply GlobalTheory.CompanionTheory.CechSerre.RowKer.leadE_eq_zero <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleComplexClassSurjective
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleComplexClassSurjective
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

namespace GlobalTheory.CompanionTheory.CechSerre

theorem clsZ_mem_Ff_succ {R : Type} [CommRing R] (K : DCx.{w} R) {n p q : ℕ} (hpq : p + q = n)
    (hS : Subsingleton ((K.col p).H q)) (z : Zf K n p) : clsZ K n p z ∈ Ff K n (p + 1) := by
  have hv : (K.col p).d q (z.1.1.1 p q) = 0 := dv_lead K z.1.1.1 (D_zero K z.1) p q z.2
  have h1 : (K.col p).cls (z.1.1.1 p q) hv = 0 := Subsingleton.elim _ _
  rw [(P.cls_surj _ q).2.1] at h1
  obtain ⟨W, hW, hl⟩ := lower_vert K z.1.1.1 z.1.1.2 hpq z.2 0 0 (fun _ _ _ => rfl) (by simp)
    (by simpa using h1)
  exact lower K z W hW hl

theorem Ff_eq_top_of_acyclic {R : Type} [CommRing R] (K : DCx.{w} R) (a j : ℕ)
    (h : ∀ p q, a < q → Subsingleton ((K.col p).H q)) : ∀ p, p ≤ j → Ff K (a + j) p = ⊤ := by
  intro p
  induction p with
  | zero =>
    intro _
    refine (Submodule.eq_top_iff').2 fun x => ?_
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ x
    exact ⟨⟨z, fun p q hp => absurd hp (Nat.not_lt_zero p)⟩, rfl⟩
  | succ p ih =>
    intro hp
    refine (Submodule.eq_top_iff').2 fun x => ?_
    have hx : x ∈ Ff K (a + j) p := by rw [ih (by omega)]; exact Submodule.mem_top
    obtain ⟨z, rfl⟩ := hx
    exact clsZ_mem_Ff_succ K (q := a + j - p) (by omega) (h p _ (by omega)) z

theorem clsZ_surjective_of_acyclic : ∀ {R : Type} [CommRing R] (K : DCx.{w} R) (a j : ℕ),
    (∀ p q, a < q → Subsingleton ((K.col p).H q)) →
    Function.Surjective (clsZ K (a + j) j) := by
  intro R _ K a j h
  exact LinearMap.range_eq_top.1 (Ff_eq_top_of_acyclic K a j h j le_rfl)

end GlobalTheory.CompanionTheory.CechSerre
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleComplexClassSurjectiveStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.double_complex_class_surjective : ∀ {R : Type} [CommRing R] (K : DCx.{w} R) (a j : ℕ), (∀ p q, a < q → Subsingleton ((K.col p).H q)) →
    Function.Surjective (clsZ K (a + j) j) := by
  first | exact @GlobalTheory.CompanionTheory.CechSerre.clsZ_surjective_of_acyclic | exact GlobalTheory.CompanionTheory.CechSerre.clsZ_surjective_of_acyclic | (intros; apply GlobalTheory.CompanionTheory.CechSerre.clsZ_surjective_of_acyclic <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleComplexClassZeroOfLeadZero
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleComplexClassZeroOfLeadZero
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

namespace GlobalTheory.CompanionTheory.RowInj

theorem clsZ_mem_of_leadE {R : Type} [CommRing R] (K : DCx.{w} R) (n a q : ℕ) (haq : a + q = n)
    (z : Zf K n a) (hz : leadE K a q z = 0) : clsZ K n a z ∈ Ff K n (a + 1) := by
  have hT : (Subtype.val (Subtype.val (Subtype.val z)) : (p q : ℕ) → K.X p q) ∈ K.T n :=
    Subtype.prop (Subtype.val (Subtype.val z))
  have h0 : ∀ p r, p < a → (Subtype.val (Subtype.val (Subtype.val z)) : (p q : ℕ) → K.X p q) p r = 0 :=
    fun p r hp => z.2 p r hp
  have hdv : K.dv a q ((Subtype.val (Subtype.val (Subtype.val z)) : (p q : ℕ) → K.X p q) a q) = 0 :=
    dv_lead K _ (D_zero K (Subtype.val z)) a q h0
  have hB : leadC K a q z ∈ (colH K q).B a := by
    have hz' := hz
    rw [leadE_eq] at hz'
    unfold CrystallineSemistableComparison.Cx.cls at hz'
    rw [Submodule.Quotient.mk_eq_zero] at hz'
    exact hz'
  have hL := leadC_eq K a q z hdv
  obtain ⟨v₁, W₁, hW₁, hD, hv⟩ : ∃ (v₁ : K.X a q) (W₁ : (p q : ℕ) → K.X p q),
      (∀ p r, p + r + 1 ≠ n → W₁ p r = 0) ∧ K.D W₁ = K.sgl a q v₁ ∧
      (Subtype.val (Subtype.val (Subtype.val z)) : (p q : ℕ) → K.X p q) a q - v₁ ∈ (K.col a).B q := by
    cases a with
    | zero =>
      refine ⟨0, 0, fun _ _ _ => rfl, by simp, ?_⟩
      have hb : leadC K 0 q z ∈ (⊥ : Submodule R ((colH K q).X 0)) := hB
      rw [Submodule.mem_bot, hL] at hb
      unfold CrystallineSemistableComparison.Cx.cls at hb
      rw [Submodule.Quotient.mk_eq_zero] at hb
      simpa using hb
    | succ a' =>
      have hb : leadC K (a' + 1) q z ∈ LinearMap.range ((colH K q).d a') := hB
      obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hb
      obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective
        (Submodule.comap ((K.col a').Z q).subtype ((K.col a').B q)) y
      have hw : K.dv a' q (w : K.X a' q) = 0 := w.2
      refine ⟨K.dh a' q w, K.sgl a' q w, ?_, ?_, ?_⟩
      · intro p r hpr
        apply K.sgl_ne
        by_cases hp : p = a'
        · right
          intro hr
          apply hpr
          omega
        · left
          exact hp
      · rw [DCx.D_sgl, hw, map_zero, smul_zero, add_zero]
      · rw [hL] at hy
        unfold CrystallineSemistableComparison.Cx.cls at hy
        change (colMap K a').mapH q (Submodule.Quotient.mk w) = _ at hy
        unfold CrystallineSemistableComparison.Cx.Hom.mapH at hy
        rw [Submodule.mapQ_apply, Submodule.Quotient.eq] at hy
        have h2 := Submodule.neg_mem _ hy
        rw [neg_sub] at h2
        exact h2
  obtain ⟨W, hW, hW'⟩ := lower_vert K _ hT haq h0 v₁ W₁ hW₁ hD hv
  exact lower K z W hW hW'

theorem leadE_eq_zero_of_subsingleton {R : Type} [CommRing R] (K : DCx.{w} R) (n a q : ℕ)
    (hs : Subsingleton ((K.col a).H q)) (z : Zf K n a) : leadE K a q z = 0 := by
  have h0 : leadC K a q z = 0 := Subsingleton.elim _ _
  rw [leadE_eq]
  unfold CrystallineSemistableComparison.Cx.cls
  rw [Submodule.Quotient.mk_eq_zero]
  show leadC K a q z ∈ (colH K q).B a
  rw [h0]
  exact Submodule.zero_mem _

theorem Ff_eq_zero {R : Type} [CommRing R] (K : DCx.{w} R) (a j : ℕ)
    (hK : ∀ p q, q < a → Subsingleton ((K.col p).H q)) :
    ∀ k b, j < b → b + k = a + j + 1 → ∀ x ∈ Ff K (a + j) b, x = 0 := by
  intro k
  induction k with
  | zero =>
    intro b _ hbk x hx
    have hb' : b = a + j + 1 := by omega
    subst hb'
    have hs := Ff_top_subsingleton K (a + j)
    have hxx := Subsingleton.elim (⟨x, hx⟩ : ↥(Ff K (a + j) (a + j + 1))) 0
    simpa using congrArg Subtype.val hxx
  | succ k ih =>
    intro b hb hbk x hx
    have hx' : x ∈ LinearMap.range (clsZ K (a + j) b) := hx
    obtain ⟨z, rfl⟩ := LinearMap.mem_range.mp hx'
    have hq : b + (a + j - b) = a + j := by omega
    have hz : leadE K b (a + j - b) z = 0 :=
      leadE_eq_zero_of_subsingleton K (a + j) b (a + j - b) (hK b _ (by omega)) z
    exact ih (b + 1) (by omega) (by omega) _ (clsZ_mem_of_leadE K (a + j) b (a + j - b) hq z hz)

theorem clsZ_eq_zero_of_leadE : ∀ {R : Type} [CommRing R] (K : DCx.{w} R) (a j : ℕ), (∀ p q, q < a → Subsingleton ((K.col p).H q)) →
    ∀ z : Zf K (a + j) j, leadE K j a z = 0 → clsZ K (a + j) j z = 0 := by
  intro R _ K a j hK z hz
  exact Ff_eq_zero K a j hK a (j + 1) (by omega) (by omega) _
    (clsZ_mem_of_leadE K (a + j) j a (by omega) z hz)

end GlobalTheory.CompanionTheory.RowInj
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleComplexClassZeroOfLeadZeroStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.double_complex_class_zero_of_lead_zero : ∀ {R : Type} [CommRing R] (K : DCx.{w} R) (a j : ℕ), (∀ p q, q < a → Subsingleton ((K.col p).H q)) →
    ∀ z : Zf K (a + j) j, leadE K j a z = 0 → clsZ K (a + j) j z = 0 := by
  first | exact @GlobalTheory.CompanionTheory.RowInj.clsZ_eq_zero_of_leadE | exact GlobalTheory.CompanionTheory.RowInj.clsZ_eq_zero_of_leadE | (intros; apply GlobalTheory.CompanionTheory.RowInj.clsZ_eq_zero_of_leadE <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleComplexDegenerateColumnIso
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

namespace GlobalTheory.CompanionTheory.CechSerre

theorem row_iso_of_columns : ∀ {R : Type} [CommRing R] (K : DCx.{w} R) (a : ℕ), (∀ p q, q ≠ a → Subsingleton ((K.col p).H q)) →
    ∀ j, ∃ e : K.tot.H (a + j) ≃ₗ[R] (colH K a).H j, ∀ z : Zf K (a + j) j, e (clsZ K (a + j) j z) = leadE K j a z := by
  intro R _ K a hK j
  have hab : ∀ p q, a < q → Subsingleton ((K.col p).H q) := fun p q h => hK p q (ne_of_gt h)
  have hbe : ∀ p q, q < a → Subsingleton ((K.col p).H q) := fun p q h => hK p q (ne_of_lt h)
  have hs := GlobalTheory.T.double_complex_class_surjective K a j hab
  have hk := GlobalTheory.T.double_complex_lead_zero_of_class_zero K a j hab
  have hi := GlobalTheory.T.double_complex_class_zero_of_lead_zero K a j hbe
  have hl := GlobalTheory.T.double_complex_lead_surjective K a j hbe
  let c := clsZ K (a + j) j
  let ψ : Zf K (a + j) j →ₗ[R] (colH K a).H j := leadE K j a
  have hle : LinearMap.ker c ≤ LinearMap.ker ψ := fun z hz => hk z hz
  let L := (LinearMap.ker c).liftQ ψ hle
  have hL : Function.Bijective L := by
    constructor
    · refine (injective_iff_map_eq_zero L).2 fun x hx => ?_
      obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ x
      have hz : ψ z = 0 := by simpa [L] using hx
      have hc : c z = 0 := hi z hz
      exact (Submodule.Quotient.mk_eq_zero _).2 hc
    · intro y
      obtain ⟨z, rfl⟩ := hl y
      exact ⟨Submodule.Quotient.mk z, Submodule.liftQ_apply _ _ _⟩
  let e0 := c.quotKerEquivOfSurjective hs
  refine ⟨e0.symm.trans (LinearEquiv.ofBijective L hL), fun z => ?_⟩
  have h0 : e0.symm (c z) = Submodule.Quotient.mk z :=
    e0.symm_apply_eq.2 (LinearMap.quotKerEquivOfSurjective_apply_mk c hs z).symm
  change L (e0.symm (c z)) = ψ z
  rw [h0]
  exact Submodule.liftQ_apply _ _ _

end GlobalTheory.CompanionTheory.CechSerre
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleComplexDegenerateColumnIsoStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.double_complex_degenerate_column_iso : ∀ {R : Type} [CommRing R] (K : DCx.{w} R) (a : ℕ), (∀ p q, q ≠ a → Subsingleton ((K.col p).H q)) →
    ∀ j, ∃ e : K.tot.H (a + j) ≃ₗ[R] (colH K a).H j, ∀ z : Zf K (a + j) j, e (clsZ K (a + j) j z) = leadE K j a z := by
  first | exact @GlobalTheory.CompanionTheory.CechSerre.row_iso_of_columns | exact GlobalTheory.CompanionTheory.CechSerre.row_iso_of_columns | (intros; apply GlobalTheory.CompanionTheory.CechSerre.row_iso_of_columns <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechDoubleComplexMap
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechDoubleComplexMap
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

noncomputable section

namespace GlobalTheory.CompanionTheory.CechSerre

section MorDbl

variable {R : Type} [CommRing R] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
  {F : C ⥤ ModuleCat.{0} R} {F' : C' ⥤ ModuleCat.{0} R} {ι ι' : Type}
  {U : ι → ObjectProperty C} {U' : ι' → ObjectProperty C'} {hU : ∀ α, Cosieve (U α)}
  {hU' : ∀ α, Cosieve (U' α)}

def nerveG (m : CH.Mor F F' (RingHom.id R)) (τ : ι' → ι) (hτ : ∀ α T, U' α T → U (τ α) (m.G.obj T)) (p : ℕ) :
    (CH.cech (idxπ U' hU') p).Elements ⥤ (CH.cech (idxπ U hU) p).Elements where
  obj x := (CH.cech (idxπ U hU) p).elementsMk (m.G.obj x.obj)
    ⟨fun k => ⟨τ (x.val.1 k).1, hτ _ _ (x.val.1 k).2⟩, fun _ _ => rfl⟩
  map {_x y} f := ⟨m.G.map f.hom, Subtype.ext (funext fun k => Subtype.ext
    (congrArg (fun z : (CH.cech (idxπ U' hU') p).obj y.obj => τ (z.1 k).1) f.map_val))⟩
  map_id x := Functor.Elements.hom_ext (m.G.map_id x.obj)
  map_comp f g := Functor.Elements.hom_ext (m.G.map_comp f.hom g.hom)

def nerveM (m : CH.Mor F F' (RingHom.id R)) (τ : ι' → ι) (hτ : ∀ α T, U' α T → U (τ α) (m.G.obj T)) (p : ℕ) :
    CH.Mor (CH.elF (CH.cech (idxπ U hU) p) F) (CH.elF (CH.cech (idxπ U' hU') p) F') (RingHom.id R) where
  G := nerveG m τ hτ p
  τ T := m.τ T.obj
  nat φ x := m.nat φ.hom x

theorem nerveM_face (m : CH.Mor F F' (RingHom.id R)) (τ : ι' → ι) (hτ : ∀ α T, U' α T → U (τ α) (m.G.obj T))
    (p q : ℕ) (k : Fin (p + 2)) (x : CH.Cn (CH.elF (CH.cech (idxπ U hU) p) F) q) :
    (CH.elMor (CH.cechMap (idxπ U' hU') k.succAbove) F').pullC q ((nerveM (hU := hU) (hU' := hU') m τ hτ p).pullC q x) =
      (nerveM (hU := hU) (hU' := hU') m τ hτ (p + 1)).pullC q ((CH.elMor (CH.cechMap (idxπ U hU) k.succAbove) F).pullC q x) :=
  rfl

def dblHom (m : CH.Mor F F' (RingHom.id R)) (τ : ι' → ι) (hτ : ∀ α T, U' α T → U (τ α) (m.G.obj T)) :
    DCx.Hom (dbl U hU F) (dbl U' hU' F') (RingHom.id R) where
  f p q := (nerveM m τ hτ p).pullC q
  ch p q x := by
    refine (Cos.d_apply ((CH.cechCos (idxπ U' hU') F').cos q) p _).trans ?_
    refine Eq.trans ?_ (congrArg _ (Cos.d_apply ((CH.cechCos (idxπ U hU) F).cos q) p x).symm)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_zsmul]
    exact congrArg _ (nerveM_face m τ hτ p q k x)
  cv p q x := (nerveM m τ hτ p).d_pullC q x

theorem cls_eq_of_eq {K : Cx.{1} R} {n : ℕ} {a b : K.X n} (h : a = b) (ha : K.d n a = 0) (hb : K.d n b = 0) :
    K.cls a ha = K.cls b hb := by
  subst h; rfl

theorem dblHom_sgl {K L : DCx.{1} R} (φ : DCx.Hom K L (RingHom.id R)) (a b : ℕ) (y : K.X a b) (p q : ℕ) :
    φ.f p q (K.sgl a b y p q) = L.sgl a b (φ.f a b y) p q := by
  by_cases h : p = a ∧ q = b
  · obtain ⟨rfl, rfl⟩ := h
    rw [K.sgl_self, L.sgl_self]
  · rw [K.sgl_ne _ (by omega), L.sgl_ne _ (by omega), map_zero]

end MorDbl

theorem dbl_mor : ∀ {R : Type} [CommRing R] {C C' : Type 1} [Category.{0} C] [Category.{0} C'] (F : C ⥤ ModuleCat.{0} R)
    (F' : C' ⥤ ModuleCat.{0} R) {ι ι' : Type} (U : ι → ObjectProperty C) (U' : ι' → ObjectProperty C') (hU : ∀ α, Cosieve (U α))
    (hU' : ∀ α, Cosieve (U' α)) (m : CH.Mor F F' (RingHom.id R)) (τ : ι' → ι) (hτ : ∀ α T, U' α T → U (τ α) (m.G.obj T)),
    ∃ φ : DCx.Hom (dbl U hU F) (dbl U' hU' F') (RingHom.id R),
      (∀ n (x : CH.H F n), φ.tot.mapH n ((CH.cechAugRow (idxπ U hU) F).edge.mapH n
          ((CH.Mor.restrict F (Functor.Elements.π ((Functor.const C).obj PUnit.{1}))).hom.mapH n x)) =
        (CH.cechAugRow (idxπ U' hU') F').edge.mapH n
          ((CH.Mor.restrict F' (Functor.Elements.π ((Functor.const C').obj PUnit.{1}))).hom.mapH n (m.pull n x))) ∧
      ∀ p q (x : ((dbl U hU F).col p).H q) (i : Fin (p + 1) → ι'),
        (tupM U' hU' F' i).pull q ((φ.col p).mapH q x) =
          (morU m (U := capT U (τ ∘ i)) (U' := capT U' i) fun T hT k => hτ (i k) T (hT k)).pull q ((tupM U hU F (τ ∘ i)).pull q x) := by
  intro R _ C C' _ _ F F' ι ι' U U' hU hU' m τ hτ
  refine ⟨dblHom m τ hτ, fun n x => ?_, fun p q x i => ?_⟩
  · obtain ⟨a, ha, rfl⟩ := (P.cls_surj (CH.cx F) n).1 x
    refine cls_eq_of_eq (Subtype.ext (funext fun p => funext fun q => ?_)) _ _
    exact dblHom_sgl (dblHom m τ hτ) 0 n _ p q
  · obtain ⟨a, ha, rfl⟩ := (P.cls_surj ((dbl U hU F).col p) q).1 x
    exact cls_eq_of_eq rfl _ _

end GlobalTheory.CompanionTheory.CechSerre
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechDoubleComplexMapStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cech_double_complex_map : ∀ {R : Type} [CommRing R] {C C' : Type 1} [Category.{0} C] [Category.{0} C'] (F : C ⥤ ModuleCat.{0} R)
    (F' : C' ⥤ ModuleCat.{0} R) {ι ι' : Type} (U : ι → ObjectProperty C) (U' : ι' → ObjectProperty C') (hU : ∀ α, Cosieve (U α))
    (hU' : ∀ α, Cosieve (U' α)) (m : CH.Mor F F' (RingHom.id R)) (τ : ι' → ι) (hτ : ∀ α T, U' α T → U (τ α) (m.G.obj T)),
    ∃ φ : DCx.Hom (dbl U hU F) (dbl U' hU' F') (RingHom.id R),
      (∀ n (x : CH.H F n), φ.tot.mapH n ((CH.cechAugRow (idxπ U hU) F).edge.mapH n
          ((CH.Mor.restrict F (CategoryOfElements.π ((Functor.const C).obj PUnit.{1}))).hom.mapH n x)) =
        (CH.cechAugRow (idxπ U' hU') F').edge.mapH n
          ((CH.Mor.restrict F' (CategoryOfElements.π ((Functor.const C').obj PUnit.{1}))).hom.mapH n (m.pull n x))) ∧
      ∀ p q (x : ((dbl U hU F).col p).H q) (i : Fin (p + 1) → ι'),
        (tupM U' hU' F' i).pull q ((φ.col p).mapH q x) =
          (morU m (U := capT U (τ ∘ i)) (U' := capT U' i) fun T hT k => hτ (i k) T (hT k)).pull q ((tupM U hU F (τ ∘ i)).pull q x) := by
  first | exact @GlobalTheory.CompanionTheory.CechSerre.dbl_mor | exact GlobalTheory.CompanionTheory.CechSerre.dbl_mor | (intros; apply GlobalTheory.CompanionTheory.CechSerre.dbl_mor <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleComplexMapLeadCompat
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleComplexMapLeadCompat
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

noncomputable section

namespace GlobalTheory.CompanionTheory.CechSerre

theorem leadE_map : ∀ {R : Type} [CommRing R] (K L : DCx.{1} R) (φ : DCx.Hom K L (RingHom.id R)) (a j : ℕ) (z : Zf K (a + j) j),
    ∃ z' : Zf L (a + j) j, clsZ L (a + j) j z' = φ.tot.mapH (a + j) (clsZ K (a + j) j z) ∧
      ∃ (y : (L.col j).H a) (hy : (colH L a).d j y = 0) (y₀ : (K.col j).H a) (hy₀ : (colH K a).d j y₀ = 0),
        leadE K j a z = (colH K a).cls y₀ hy₀ ∧ leadE L j a z' = (colH L a).cls y hy ∧ y = (φ.col j).mapH a y₀ := by
  intro R _ K L φ a j z
  have hc : L.tot.d (a + j) (φ.tot.f (a + j) z.1.1) = 0 := by
    rw [φ.tot.comm, show K.tot.d (a + j) z.1.1 = 0 from z.1.2, map_zero]
  have hvan : ∀ p q, p < j → (φ.tot.f (a + j) z.1.1).1 p q = 0 := by
    intro p q hp
    change φ.f p q (z.1.1.1 p q) = 0
    rw [z.2 p q hp, map_zero]
  let z' : Zf L (a + j) j := ⟨⟨φ.tot.f (a + j) z.1.1, hc⟩, hvan⟩
  have hv : (K.col j).d a (z.1.1.1 j a) = 0 := dv_lead K z.1.1.1 (D_zero K z.1) j a z.2
  have hv' : (L.col j).d a ((φ.col j).f a (z.1.1.1 j a)) = 0 := by
    rw [(φ.col j).comm, hv, map_zero]
  have hy : leadC L j a z' = (φ.col j).mapH a (leadC K j a z) := by
    rw [leadC_eq K j a z hv, P.mapH_cls _ a _ hv hv']
    rfl
  refine ⟨z', ?_, leadC L j a z', leadC_mem L j a z', leadC K j a z, leadC_mem K j a z,
    leadE_eq K j a z, leadE_eq L j a z', hy⟩
  exact (P.mapH_cls φ.tot (a + j) z.1.1 z.1.2 hc).symm

end GlobalTheory.CompanionTheory.CechSerre
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleComplexMapLeadCompatStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.double_complex_map_lead_compat : ∀ {R : Type} [CommRing R] (K L : DCx.{1} R) (φ : DCx.Hom K L (RingHom.id R)) (a j : ℕ) (z : Zf K (a + j) j),
    ∃ z' : Zf L (a + j) j, clsZ L (a + j) j z' = φ.tot.mapH (a + j) (clsZ K (a + j) j z) ∧
      ∃ (y : (L.col j).H a) (hy : (colH L a).d j y = 0) (y₀ : (K.col j).H a) (hy₀ : (colH K a).d j y₀ = 0),
        leadE K j a z = (colH K a).cls y₀ hy₀ ∧ leadE L j a z' = (colH L a).cls y hy ∧ y = (φ.col j).mapH a y₀ := by
  first | exact @GlobalTheory.CompanionTheory.CechSerre.leadE_map | exact GlobalTheory.CompanionTheory.CechSerre.leadE_map | (intros; apply GlobalTheory.CompanionTheory.CechSerre.leadE_map <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechHodgeToCohomologyIso
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

noncomputable section

namespace GlobalTheory.CompanionTheory.CechSerre

variable {R : Type} [CommRing R]

def colHMap {K L : DCx.{1} R} (φ : DCx.Hom K L (RingHom.id R)) (q : ℕ) :
    Cx.Hom (colH K q) (colH L q) (RingHom.id R) where
  f p := (φ.col p).mapH q
  comm p x := by
    obtain ⟨a, ha, rfl⟩ := (P.cls_surj (K.col p) q).1 x
    have h1 : (K.col (p + 1)).d q ((colMap K p).f q a) = 0 := by
      rw [(colMap K p).comm, ha, map_zero]
    have h2 : (L.col p).d q ((φ.col p).f q a) = 0 := by
      rw [(φ.col p).comm, ha, map_zero]
    have h3 : (L.col (p + 1)).d q ((colMap L p).f q ((φ.col p).f q a)) = 0 := by
      rw [(colMap L p).comm, h2, map_zero]
    have h4 : (L.col (p + 1)).d q ((φ.col (p + 1)).f q ((colMap K p).f q a)) = 0 := by
      rw [(φ.col (p + 1)).comm, h1, map_zero]
    change (colMap L p).mapH q ((φ.col p).mapH q _) = (φ.col (p + 1)).mapH q ((colMap K p).mapH q _)
    rw [P.mapH_cls _ q a ha h2, P.mapH_cls _ q _ h2 h3, P.mapH_cls _ q a ha h1, P.mapH_cls _ q _ h1 h4]
    have e : (colMap L p).f q ((φ.col p).f q a) = (φ.col (p + 1)).f q ((colMap K p).f q a) := φ.ch p q a
    exact ((P.cls_surj (L.col (p + 1)) q).2.2.1 _ _ h3 h4).2 (by rw [e, sub_self]; exact Submodule.zero_mem _)

variable {C : Type 1} [Category.{0} C]

theorem restr_bij (F : C ⥤ ModuleCat.{0} R) (n : ℕ) :
    Function.Bijective ((CH.Mor.restrict F (CategoryOfElements.π ((Functor.const C).obj PUnit.{1}))).hom.mapH n) := by
  let E : C ⥤ Type := (Functor.const C).obj PUnit.{1}
  let G : C ⥤ E.Elements :=
    { obj := fun T => Functor.elementsMk E T PUnit.unit
      map := fun φ => ⟨φ, rfl⟩ }
  refine P.mapH_bij _ (fun k => ⟨fun x y h => ?_, fun y => ?_⟩) n
  · funext c
    exact congrFun h (c ⋙ G)
  · exact ⟨fun c => y (c ⋙ G), funext fun s => rfl⟩

variable {ι : Type}

def eTot (F : C ⥤ ModuleCat.{0} R) (U : ι → ObjectProperty C) (hU : ∀ α, Cosieve (U α))
    (hc : ∀ T, ∃ α, U α T) (n : ℕ) : CH.H F n ≃ₗ[R] (dbl U hU F).tot.H n :=
  (LinearEquiv.ofBijective _ (restr_bij F n)).trans
    (LinearEquiv.ofBijective _ (P.cech_desc (idxπ U hU) F (fun T x => by
      obtain ⟨α, hα⟩ := hc T
      exact ⟨⟨α, hα⟩, rfl⟩) n))

theorem col_sub (F : C ⥤ ModuleCat.{0} R) (U : ι → ObjectProperty C) (hU : ∀ α, Cosieve (U α)) (a : ℕ)
    (hv : ∀ n (i : Fin (n + 1) → ι) r, r ≠ a → Subsingleton (HU F (capT U i) r)) (p q : ℕ) (hq : q ≠ a) :
    Subsingleton (((dbl U hU F).col p).H q) := by
  have := fun i => hv p i q hq
  exact (colCmp_bij U hU F p q).1.subsingleton

def eRow (F : C ⥤ ModuleCat.{0} R) (U : ι → ObjectProperty C) (hU : ∀ α, Cosieve (U α)) (a : ℕ)
    (hv : ∀ n (i : Fin (n + 1) → ι) r, r ≠ a → Subsingleton (HU F (capT U i) r)) (j : ℕ) :
    (dbl U hU F).tot.H (a + j) ≃ₗ[R] (colH (dbl U hU F) a).H j :=
  Classical.choose (GlobalTheory.T.double_complex_degenerate_column_iso (dbl U hU F) a (fun p q hq => col_sub F U hU a hv p q hq) j)

theorem eRow_clsZ (F : C ⥤ ModuleCat.{0} R) (U : ι → ObjectProperty C) (hU : ∀ α, Cosieve (U α)) (a : ℕ)
    (hv : ∀ n (i : Fin (n + 1) → ι) r, r ≠ a → Subsingleton (HU F (capT U i) r)) (j : ℕ)
    (z : Zf (dbl U hU F) (a + j) j) :
    eRow F U hU a hv j (clsZ (dbl U hU F) (a + j) j z) = leadE (dbl U hU F) j a z :=
  Classical.choose_spec (GlobalTheory.T.double_complex_degenerate_column_iso (dbl U hU F) a (fun p q hq => col_sub F U hU a hv p q hq) j) z

def eCol (F : C ⥤ ModuleCat.{0} R) (U : ι → ObjectProperty C) (hU : ∀ α, Cosieve (U α)) (a j : ℕ) :
    (colH (dbl U hU F) a).H j ≃ₗ[R] (CrystallineSemistableComparison.Pb.cechH F U a).cx.H j :=
  LinearEquiv.ofBijective _ (P.mapH_bij (colCmp U hU F a) (fun p => colCmp_bij U hU F p a) j)

theorem eCol_cls (F : C ⥤ ModuleCat.{0} R) (U : ι → ObjectProperty C) (hU : ∀ α, Cosieve (U α)) (a j : ℕ)
    (x : (colH (dbl U hU F) a).X j) (hx : (colH (dbl U hU F) a).d j x = 0)
    (h : (CrystallineSemistableComparison.Pb.cechH F U a).cx.d j ((colCmp U hU F a).f j x) = 0) :
    eCol F U hU a j ((colH (dbl U hU F) a).cls x hx) = (CrystallineSemistableComparison.Pb.cechH F U a).cx.cls _ h :=
  P.mapH_cls _ j x hx h

def eDeg (F : C ⥤ ModuleCat.{0} R) (U : ι → ObjectProperty C) (hU : ∀ α, Cosieve (U α))
    (hc : ∀ T, ∃ α, U α T) (a : ℕ)
    (hv : ∀ n (i : Fin (n + 1) → ι) r, r ≠ a → Subsingleton (HU F (capT U i) r)) (j : ℕ) :
    CH.H F (a + j) ≃ₗ[R] (CrystallineSemistableComparison.Pb.cechH F U a).cx.H j :=
  (eTot F U hU hc (a + j)).trans ((eRow F U hU a hv j).trans (eCol F U hU a j))

theorem eDeg_apply (F : C ⥤ ModuleCat.{0} R) (U : ι → ObjectProperty C) (hU : ∀ α, Cosieve (U α))
    (hc : ∀ T, ∃ α, U α T) (a : ℕ)
    (hv : ∀ n (i : Fin (n + 1) → ι) r, r ≠ a → Subsingleton (HU F (capT U i) r)) (j : ℕ) (x : CH.H F (a + j)) :
    eDeg F U hU hc a hv j x = eCol F U hU a j (eRow F U hU a hv j (eTot F U hU hc (a + j) x)) := rfl

theorem cech_deg : ∀ (R : Type) [CommRing R], ∃ e : ∀ {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R) {ι : Type}
    (U : ι → ObjectProperty C), (∀ α, Cosieve (U α)) → (∀ T, ∃ α, U α T) → ∀ a : ℕ,
    (∀ n (i : Fin (n + 1) → ι) r, r ≠ a → Subsingleton (HU F (capT U i) r)) → ∀ j : ℕ,
      CH.H F (a + j) ≃ₗ[R] (CrystallineSemistableComparison.Pb.cechH F U a).cx.H j,
    ∀ {C C' : Type 1} [Category.{0} C] [Category.{0} C'] (F : C ⥤ ModuleCat.{0} R) (F' : C' ⥤ ModuleCat.{0} R) {ι ι' : Type}
      (U : ι → ObjectProperty C) (U' : ι' → ObjectProperty C') (hU : ∀ α, Cosieve (U α)) (hc : ∀ T, ∃ α, U α T)
      (hU' : ∀ α, Cosieve (U' α)) (hc' : ∀ T, ∃ α, U' α T) (a : ℕ)
      (hv : ∀ n (i : Fin (n + 1) → ι) r, r ≠ a → Subsingleton (HU F (capT U i) r))
      (hv' : ∀ n (i : Fin (n + 1) → ι') r, r ≠ a → Subsingleton (HU F' (capT U' i) r)) (m : CH.Mor F F' (RingHom.id R))
      (τ : ι' → ι) (hτ : ∀ α T, U' α T → U (τ α) (m.G.obj T)) (j : ℕ) (c : (CrystallineSemistableComparison.Pb.cechH F U a).X j)
      (h0 : (CrystallineSemistableComparison.Pb.cechH F U a).cx.d j c = 0)
      (h1 : (CrystallineSemistableComparison.Pb.cechH F' U' a).cx.d j (fun i => (morU m (U := capT U (τ ∘ i)) (U' := capT U' i)
        fun T hT k => hτ (i k) T (hT k)).pull a (c (τ ∘ i))) = 0),
      m.pull (a + j) ((e F U hU hc a hv j).symm ((CrystallineSemistableComparison.Pb.cechH F U a).cx.cls c h0)) =
        (e F' U' hU' hc' a hv' j).symm ((CrystallineSemistableComparison.Pb.cechH F' U' a).cx.cls _ h1) := by
  intro R _
  refine ⟨fun F _ U hU hc a hv j => eDeg F U hU hc a hv j, ?_⟩
  intro C C' _ _ F F' ι ι' U U' hU hc hU' hc' a hv hv' m τ hτ j c h0 h1
  obtain ⟨φ, hφ1, hφ2⟩ := GlobalTheory.T.cech_double_complex_map F F' U U' hU hU' m τ hτ
  obtain ⟨c₁, rfl⟩ := (colCmp_bij U hU F j a).2 c
  have hd₁ : (colH (dbl U hU F) a).d j c₁ = 0 := by
    refine (colCmp_bij U hU F (j + 1) a).1 ?_
    rw [← (colCmp U hU F a).comm, h0, map_zero]
  obtain ⟨z, hz⟩ := GlobalTheory.T.double_complex_lead_surjective (dbl U hU F) a j
    (fun p q hq => col_sub F U hU a hv p q hq.ne) ((colH (dbl U hU F) a).cls c₁ hd₁)
  have hy : (eDeg F U hU hc a hv j).symm ((CrystallineSemistableComparison.Pb.cechH F U a).cx.cls _ h0) =
      (eTot F U hU hc (a + j)).symm (clsZ (dbl U hU F) (a + j) j z) := by
    rw [LinearEquiv.symm_apply_eq, eDeg_apply, LinearEquiv.apply_symm_apply, eRow_clsZ, hz, eCol_cls F U hU a j c₁ hd₁ h0]
  obtain ⟨z', hz'1, y', hy', y₀, hy₀, e1, e2, e3⟩ := GlobalTheory.T.double_complex_map_lead_compat (dbl U hU F) (dbl U' hU' F') φ a j z
  show m.pull (a + j) ((eDeg F U hU hc a hv j).symm _) = (eDeg F' U' hU' hc' a hv' j).symm _
  rw [hy, LinearEquiv.eq_symm_apply, eDeg_apply]
  have h2 : eTot F' U' hU' hc' (a + j) (m.pull (a + j) ((eTot F U hU hc (a + j)).symm (clsZ (dbl U hU F) (a + j) j z))) =
      clsZ (dbl U' hU' F') (a + j) j z' := by
    rw [hz'1, ← LinearEquiv.apply_symm_apply (eTot F U hU hc (a + j)) (clsZ (dbl U hU F) (a + j) j z)]
    simp only [LinearEquiv.symm_apply_apply]
    exact (hφ1 _ _).symm
  rw [h2, eRow_clsZ, e2]
  have h3 : (colH (dbl U hU F) a).cls y₀ hy₀ = (colH (dbl U hU F) a).cls c₁ hd₁ := e1.symm.trans hz
  have hd₂ : (colH (dbl U' hU' F') a).d j ((colHMap φ a).f j c₁) = 0 := by
    rw [(colHMap φ a).comm, hd₁, map_zero]
  have h4 : (colH (dbl U' hU' F') a).cls y' hy' = (colH (dbl U' hU' F') a).cls _ hd₂ := by
    have hd₃ : (colH (dbl U' hU' F') a).d j ((colHMap φ a).f j y₀) = 0 := by
      rw [(colHMap φ a).comm, hy₀, map_zero]
    have h5 := congrArg ((colHMap φ a).mapH j) h3
    rw [P.mapH_cls _ j _ hy₀ hd₃, P.mapH_cls _ j _ hd₁ hd₂] at h5
    subst e3
    exact h5
  have h6 : (colCmp U' hU' F' a).f j ((colHMap φ a).f j c₁) =
      fun i => (morU m (U := capT U (τ ∘ i)) (U' := capT U' i)
        fun T hT k => hτ (i k) T (hT k)).pull a ((colCmp U hU F a).f j c₁ (τ ∘ i)) := by
    funext i
    exact hφ2 j a c₁ i
  have h7 : (CrystallineSemistableComparison.Pb.cechH F' U' a).cx.d j ((colCmp U' hU' F' a).f j ((colHMap φ a).f j c₁)) = 0 := by
    rw [(colCmp U' hU' F' a).comm, hd₂, map_zero]
  rw [h4, eCol_cls F' U' hU' a j _ hd₂ h7]
  exact ((P.cls_surj (CrystallineSemistableComparison.Pb.cechH F' U' a).cx j).2.2.1 _ _ h7 h1).2 (by rw [h6, sub_self]; exact Submodule.zero_mem _)

end GlobalTheory.CompanionTheory.CechSerre
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechHodgeToCohomologyIsoStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cech_hodge_to_cohomology_iso : ∀ (R : Type) [CommRing R], ∃ e : ∀ {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R) {ι : Type}
    (U : ι → ObjectProperty C), (∀ α, Cosieve (U α)) → (∀ T, ∃ α, U α T) → ∀ a : ℕ,
    (∀ n (i : Fin (n + 1) → ι) r, r ≠ a → Subsingleton (HU F (capT U i) r)) → ∀ j : ℕ,
      CH.H F (a + j) ≃ₗ[R] (cechH F U a).cx.H j,
    ∀ {C C' : Type 1} [Category.{0} C] [Category.{0} C'] (F : C ⥤ ModuleCat.{0} R) (F' : C' ⥤ ModuleCat.{0} R) {ι ι' : Type}
      (U : ι → ObjectProperty C) (U' : ι' → ObjectProperty C') (hU : ∀ α, Cosieve (U α)) (hc : ∀ T, ∃ α, U α T)
      (hU' : ∀ α, Cosieve (U' α)) (hc' : ∀ T, ∃ α, U' α T) (a : ℕ)
      (hv : ∀ n (i : Fin (n + 1) → ι) r, r ≠ a → Subsingleton (HU F (capT U i) r))
      (hv' : ∀ n (i : Fin (n + 1) → ι') r, r ≠ a → Subsingleton (HU F' (capT U' i) r)) (m : CH.Mor F F' (RingHom.id R))
      (τ : ι' → ι) (hτ : ∀ α T, U' α T → U (τ α) (m.G.obj T)) (j : ℕ) (c : (cechH F U a).X j)
      (h0 : (cechH F U a).cx.d j c = 0)
      (h1 : (cechH F' U' a).cx.d j (fun i => (morU m (U := capT U (τ ∘ i)) (U' := capT U' i)
        fun T hT k => hτ (i k) T (hT k)).pull a (c (τ ∘ i))) = 0),
      m.pull (a + j) ((e F U hU hc a hv j).symm ((cechH F U a).cx.cls c h0)) =
        (e F' U' hU' hc' a hv' j).symm ((cechH F' U' a).cx.cls _ h1) := by
  first | exact @GlobalTheory.CompanionTheory.CechSerre.cech_deg | exact GlobalTheory.CompanionTheory.CechSerre.cech_deg | (intros; apply GlobalTheory.CompanionTheory.CechSerre.cech_deg <;> assumption)
end
