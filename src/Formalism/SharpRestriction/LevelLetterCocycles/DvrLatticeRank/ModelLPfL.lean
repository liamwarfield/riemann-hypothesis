module

public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelLPfC
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.TmulMkLMemInvLOfValAtMemFilC
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelFPfG

@[expose] public section

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelLPfJ
section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelLPfI
section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelLPfH
section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelLPfG
section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelLPfF
section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelLPfE
noncomputable section

namespace Formalism.MainNotions.N.Ln34.MLE

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

theorem exists_fin_sum {O M N' : Type*} [CommRing O] [AddCommGroup M] [Module O M] [AddCommGroup N']
    [Module O N'] (t : M ⊗[O] N') : ∃ (m : ℕ) (a : Fin m → M) (s : Fin m → N'), t = ∑ j, a j ⊗ₜ s j := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
  | tmul a s => exact ⟨1, fun _ => a, fun _ => s, by simp⟩
  | add t t' ht ht' =>
    obtain ⟨m, a, s, rfl⟩ := ht
    obtain ⟨m', a', s', rfl⟩ := ht'
    refine ⟨m + m', Fin.append a a', Fin.append s s', ?_⟩
    rw [Fin.sum_univ_add]
    simp [Fin.append_left, Fin.append_right]

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (π' Eπ : LetA O n) (h' : ℕ) (c : ZMod n)

theorem toLA_tmul (S : Submodule O (LcQ W T π' c)) (a : ↥W.AΔ) (s : ↥S) :
    toLA W T π' c S (a ⊗ₜ s) = algebraMap (LetA O n) W.EE ((letE c : LetA O n) * a) ⊗ₜ (s : LcQ W T π' c) :=
  rfl

theorem smulLA_tmul (a : LetA O n) (e : W.EE) (s : LcQ W T π' c) :
    smulLA W T π' c a (e ⊗ₜ s) = (algebraMap (LetA O n) W.EE a * e) ⊗ₜ s := rfl

theorem smulLA_smulLA (a b : LetA O n) (x : LA W T π' c) :
    smulLA W T π' c a (smulLA W T π' c b x) = smulLA W T π' c (a * b) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul e s => simp only [smulLA_tmul, map_mul, mul_assoc]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem smul_eq_smulLA (o : O) (x : LA W T π' c) :
    o • x = smulLA W T π' c (algebraMap O (LetA O n) o) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul e s =>
    rw [smulLA_tmul, TensorProduct.smul_tmul', Algebra.smul_def,
      IsScalarTower.algebraMap_apply O (LetA O n) W.EE]
  | add x y hx hy => rw [smul_add, map_add (f := _), hx, hy]

theorem rep_exists {x : LA W T π' c} (hx : x ∈ LamLA W T π' Eπ h' c ⊤) :
    ∃ (m : ℕ) (a : Fin m → ↥W.AΔ) (y : Fin m → W.DD T), IsRepL W T π' Eπ h' c x a y := by
  obtain ⟨t, ht⟩ := hx
  obtain ⟨m, a, s, rfl⟩ := exists_fin_sum t
  have hs : ∀ j, ∃ yy : ↥(NcS W T (c - 1)), Submodule.Quotient.mk yy = ((s j : ↥(⊤ : Submodule O _)) :
      LcQ W T π' c) := fun j => Submodule.Quotient.mk_surjective _ _
  choose yy hyy using hs
  refine ⟨m, a, fun j => (yy j : W.DD T), ⟨fun j => (yy j).2, ?_⟩⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← ht, map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [toLA_tmul, ← hyy j]
  rfl

theorem rep_append {x x' : LA W T π' c} {m m' : ℕ} {a : Fin m → ↥W.AΔ} {y : Fin m → W.DD T}
    {a' : Fin m' → ↥W.AΔ} {y' : Fin m' → W.DD T} (h : IsRepL W T π' Eπ h' c x a y)
    (h₂ : IsRepL W T π' Eπ h' c x' a' y') :
    IsRepL W T π' Eπ h' c (x + x') (Fin.append a a') (Fin.append y y') := by
  obtain ⟨hy, hx⟩ := h
  obtain ⟨hy', hx'⟩ := h₂
  refine ⟨fun j => ?_, ?_⟩
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · rw [Fin.append_left]; exact hy j
    · rw [Fin.append_right]; exact hy' j
  · rw [map_add (f := _), hx, hx', Fin.sum_univ_add]
    congr 1
    · refine Finset.sum_congr rfl (fun j _ => ?_)
      simp only [Fin.append_left]
    · refine Finset.sum_congr rfl (fun j _ => ?_)
      simp only [Fin.append_right]

theorem expS_append (ζ : LL) {m m' : ℕ} (a : Fin m → ↥W.AΔ) (y : Fin m → W.DD T)
    (a' : Fin m' → ↥W.AΔ) (y' : Fin m' → W.DD T) :
    expS W T c ζ (fun j => ((Fin.append a a' j : ↥W.AΔ) : LetA O n)) (Fin.append y y') =
      expS W T c ζ (fun j => (a j : LetA O n)) y + expS W T c ζ (fun j => (a' j : LetA O n)) y' := by
  funext i
  simp only [expS, Pi.add_apply, Fin.sum_univ_add, Fin.append_left, Fin.append_right]

theorem rep_smul {x : LA W T π' c} {m : ℕ} {a : Fin m → ↥W.AΔ} {y : Fin m → W.DD T}
    (h : IsRepL W T π' Eπ h' c x a y) {b : LetA O n} (hb : b ∈ W.AΔ) :
    IsRepL W T π' Eπ h' c (smulLA W T π' c b x) (fun j => ⟨b * a j, W.AΔ.mul_mem hb (a j).2⟩) y := by
  obtain ⟨hy, hx⟩ := h
  refine ⟨hy, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [smulLA_smulLA, mul_comm, ← smulLA_smulLA, hx, map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [smulLA_tmul, ← map_mul]
  congr 2
  ring

end Generic

end Formalism.MainNotions.N.Ln34.MLE

end
end

noncomputable section

namespace Formalism.MainNotions.N.Ln34.MLF

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop)
    (π' Eπ : LetA O n) (h' : ℕ) (c : ZMod n)

def WD : Prop :=
  ∀ τ ζ, Pt c ζ τ → ∀ {m m' : ℕ} (a : Fin m → LetA O n) (y : Fin m → W.DD T)
    (hy : ∀ j, y j ∈ NcS W T (c - 1)) (b : Fin m' → LetA O n) (z : Fin m' → W.DD T)
    (hz : ∀ k, z k ∈ NcS W T (c - 1)),
    ∑ j, algebraMap (LetA O n) W.EE ((letE c : LetA O n) * a j) ⊗ₜ[O] mkL W T π' c (y j) (hy j) =
      ∑ k, algebraMap (LetA O n) W.EE ((letE c : LetA O n) * b k) ⊗ₜ[O] mkL W T π' c (z k) (hz k) →
    expS W T c ζ a y = expS W T c ζ b z

theorem expS_alg_mul (ζ : LL) (o : O) {m : ℕ} (a : Fin m → LetA O n) (y : Fin m → W.DD T) :
    expS W T c ζ (fun j => algebraMap O (LetA O n) o * a j) y = algebraMap O LL o • expS W T c ζ a y := by
  funext i
  simp only [expS, serC, Pi.smul_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  split_ifs
  · rw [map_mul, AlgHom.commutes, PowerSeries.algebraMap_apply, PowerSeries.coeff_C_mul, mul_smul]
  · rw [smul_zero]

theorem good_all (hwd : WD W T Pt π' c) {x : LA W T π' c} (hx : x ∈ NL W T Pt π' Eπ h' c)
    {m : ℕ} {a : Fin m → ↥W.AΔ} {y : Fin m → W.DD T} (hr : IsRepL W T π' Eπ h' c x a y) :
    ∀ τ ζ, Pt c ζ τ → ∀ i : ℤ, expS W T c ζ (fun j => (a j : LetA O n)) y i ∈
      Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (h' - i) := by
  have hrep : x ∈ NLset W T Pt π' Eπ h' c := by
    clear hr
    induction hx using Submodule.span_induction with
    | mem x hx => exact hx
    | zero =>
      refine ⟨0, Fin.elim0, Fin.elim0, ⟨fun j => j.elim0, by simp⟩, fun τ ζ _ i => ?_⟩
      simp [expS]
    | add x₁ x₂ _ _ h₁ h₂ =>
      obtain ⟨m₁, a₁, y₁, ⟨hy₁, he₁⟩, hg₁⟩ := h₁
      obtain ⟨m₂, a₂, y₂, ⟨hy₂, he₂⟩, hg₂⟩ := h₂
      let z : Fin (m₁ + m₂) → ↥(NcS W T (c - 1)) :=
        Fin.append (fun j => ⟨y₁ j, hy₁ j⟩) (fun j => ⟨y₂ j, hy₂ j⟩)
      refine ⟨m₁ + m₂, Fin.append a₁ a₂, fun j => z j, ⟨fun j => (z j).2, ?_⟩, fun τ ζ hpt i => ?_⟩
      · rw [map_add (f := _), he₁, he₂, Fin.sum_univ_add]
        simp only [z, Fin.append_left, Fin.append_right]
      · simpa only [expS, Fin.sum_univ_add, z, Fin.append_left, Fin.append_right] using
          Submodule.add_mem _ (hg₁ τ ζ hpt i) (hg₂ τ ζ hpt i)
    | smul o x _ hx =>
      obtain ⟨m, a, y, ⟨hy, he⟩, hg⟩ := hx
      refine ⟨m, fun j => o • a j, y, ⟨hy, ?_⟩, fun τ ζ hpt i => ?_⟩
      · rw [map_smul, he, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [TensorProduct.smul_tmul', Subalgebra.coe_smul, mul_smul_comm]
        simp only [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply O (LetA O n) W.EE]
      · simp only [Subalgebra.coe_smul]
        simpa only [Algebra.smul_def, expS_alg_mul, Pi.smul_apply] using
          Submodule.smul_mem _ (algebraMap O LL o) (hg τ ζ hpt i)
  obtain ⟨m', a', y', ⟨hy', hx'⟩, hg⟩ := hrep
  obtain ⟨hy, hxr⟩ := hr
  intro τ ζ hpt i
  rw [hwd τ ζ hpt _ y hy _ y' hy' (hxr.symm.trans hx')]
  exact hg τ ζ hpt i

theorem nl_le : NL W T Pt π' Eπ h' c ≤ LamLA W T π' Eπ h' c ⊤ := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨m, a, y, ⟨hy, hx⟩, -⟩
  refine ⟨∑ j, a j ⊗ₜ ⟨mkL W T π' c (y j) (hy j), Submodule.mem_top⟩, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, hx]
  rfl

theorem nl_smulA {b : LetA O n} (hb : b ∈ W.AΔ) {x : LA W T π' c} (hx : x ∈ NL W T Pt π' Eπ h' c) :
    smulLA W T π' c b x ∈ NL W T Pt π' Eπ h' c := by
  have htmul (a : LetA O n) (e : W.EE) (z : LcQ W T π' c) :
      smulLA W T π' c a (e ⊗ₜ z) = (algebraMap (LetA O n) W.EE a * e) ⊗ₜ z := rfl
  have hcomm (x : LA W T π' c) :
      smulLA W T π' c (Eπ ^ h') (smulLA W T π' c b x) =
        smulLA W T π' c b (smulLA W T π' c (Eπ ^ h') x) := by
    induction x using TensorProduct.inductionOn with
    | tmul e z => simp only [htmul, mul_left_comm]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, a, y, ⟨hy, he⟩, hg⟩ := hx
    refine Submodule.subset_span
      ⟨m, fun j => ⟨b * a j, W.AΔ.mul_mem hb (a j).2⟩, y, ⟨hy, ?_⟩, fun τ ζ hpt => ?_⟩
    · set_option synthInstance.maxHeartbeats 100000 in
        rw [hcomm, he, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [htmul, ← map_mul]
      congr 2
      ring
    · exact MLB.goodF_mul W T c ζ τ h' b _ y (hg τ ζ hpt)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul o x _ hx => rw [LinearMap.map_smul]; exact Submodule.smul_mem _ _ hx

theorem nl_sat (hwd : WD W T Pt π' c) (hp : algebraMap O LL ((PD.p : ℕ) : O) ≠ 0)
    {x : LA W T π' c} (hx : x ∈ LamLA W T π' Eπ h' c ⊤) (k : ℕ)
    (hk : ((PD.p : ℕ) : O) ^ k • x ∈ NL W T Pt π' Eπ h' c) : x ∈ NL W T Pt π' Eπ h' c := by
  have hrep : ∃ (m : ℕ) (a : Fin m → ↥W.AΔ) (y : Fin m → W.DD T), IsRepL W T π' Eπ h' c x a y := by
    obtain ⟨t, ht⟩ := hx
    obtain ⟨m, a, s, rfl⟩ := MLE.exists_fin_sum t
    have hs : ∀ j, ∃ z : ↥(NcS W T (c - 1)), Submodule.Quotient.mk z =
        ((s j : ↥(⊤ : Submodule O _)) : LcQ W T π' c) := fun j => Submodule.Quotient.mk_surjective _ _
    choose z hz using hs
    refine ⟨m, a, fun j => z j, ⟨fun j => (z j).2, ?_⟩⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← ht, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    change algebraMap (LetA O n) W.EE ((letE c : LetA O n) * a j) ⊗ₜ
      ((s j : ↥(⊤ : Submodule O _)) : LcQ W T π' c) = _
    rw [← hz j]
    rfl
  obtain ⟨m, a, y, hy, he⟩ := hrep
  let o : O := ((PD.p : ℕ) : O) ^ k
  have hr' : IsRepL W T π' Eπ h' c (o • x) (fun j => o • a j) y := by
    refine ⟨hy, ?_⟩
    rw [map_smul, he, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [TensorProduct.smul_tmul', Subalgebra.coe_smul, mul_smul_comm]
    simp only [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply O (LetA O n) W.EE]
  have hg := good_all W T Pt π' Eπ h' c hwd hk hr'
  refine Submodule.subset_span ⟨m, a, y, ⟨hy, he⟩, fun τ ζ hpt i => ?_⟩
  have h1 := hg τ ζ hpt i
  simp only [Subalgebra.coe_smul] at h1
  simp only [Algebra.smul_def, expS_alg_mul, Pi.smul_apply] at h1
  have ho : algebraMap O LL o ≠ 0 := by simpa only [o, map_pow] using pow_ne_zero k hp
  exact (Submodule.smul_mem_iff _ ho).1 h1

end Generic

end Formalism.MainNotions.N.Ln34.MLF

end
end

noncomputable section

namespace Formalism.MainNotions.N.Ln34.MLG

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

variable {LL V' : Type} [Field LL] [AddCommGroup V'] [Module LL V']

def Bdd (F : ℤ → V') (m₀ : ℤ) : Prop := ∀ i < m₀, F i = 0

theorem serMul_eq_sum (P : PowerSeries LL) {F : ℤ → V'} {m₀ : ℤ} (hF : Bdd F m₀) (i : ℤ) (M : ℕ)
    (hM : (i - m₀).toNat + 1 ≤ M) :
    serMul P F i = ∑ k ∈ Finset.range M, PowerSeries.coeff k P • F (i - k) := by
  unfold serMul
  apply finsum_eq_sum_of_support_subset
  intro k hk
  rw [Function.mem_support] at hk
  rw [Finset.mem_coe, Finset.mem_range]
  by_contra hkM
  apply hk
  rw [hF (i - k) (by omega), smul_zero]

theorem serMul_bdd (P : PowerSeries LL) {F : ℤ → V'} {m₀ : ℤ} (hF : Bdd F m₀) : Bdd (serMul P F) m₀ := by
  intro i hi
  unfold serMul
  apply finsum_eq_zero_of_forall_eq_zero
  intro k
  rw [hF (i - k) (by omega), smul_zero]

theorem serMul_serMul (P Q : PowerSeries LL) {F : ℤ → V'} {m₀ : ℤ} (hF : Bdd F m₀) (i : ℤ) :
    serMul P (serMul Q F) i = serMul (P * Q) F i := by
  set N := (i - m₀).toNat + 1 with hN
  rw [serMul_eq_sum P (serMul_bdd Q hF) i N le_rfl, serMul_eq_sum (P * Q) hF i N le_rfl]
  have hL : ∀ k ∈ Finset.range N, PowerSeries.coeff k P • serMul Q F (i - k) =
      ∑ j ∈ Finset.range (N - k), (PowerSeries.coeff k P * PowerSeries.coeff j Q) • F (i - (k + j : ℕ)) := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [serMul_eq_sum Q hF (i - k) (N - k) (by omega), Finset.smul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [mul_smul]
    congr 2
    push_cast
    ring
  rw [Finset.sum_congr rfl hL]
  have hR : ∀ s ∈ Finset.range N, PowerSeries.coeff s (P * Q) • F (i - s) =
      ∑ k ∈ Finset.Ico 0 (s + 1), (PowerSeries.coeff k P * PowerSeries.coeff (s - k) Q) • F (i - s) := by
    intro s _
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_smul,
      Finset.range_eq_Ico]
  rw [Finset.sum_congr rfl hR, Finset.range_eq_Ico, ← Finset.sum_Ico_Ico_comm]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [Finset.mem_Ico] at hk
  rw [Finset.sum_Ico_eq_sum_range]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Nat.add_sub_cancel_left]

theorem serMul_X_pow (h : ℕ) (F : ℤ → V') (i : ℤ) :
    serMul (PowerSeries.X ^ h : PowerSeries LL) F i = F (i - h) := by
  unfold serMul
  rw [finsum_eq_single _ h (fun k hk => by rw [PowerSeries.coeff_X_pow, if_neg hk, zero_smul])]
  rw [PowerSeries.coeff_X_pow, if_pos rfl, one_smul]

theorem serMul_rescale (u : LL) (hu : u ≠ 0) (P : PowerSeries LL) (F : ℤ → V') (i : ℤ) :
    u ^ i • serMul P F i = serMul (PowerSeries.rescale u P) (fun j => u ^ j • F j) i := by
  unfold serMul
  rw [smul_finsum]
  refine finsum_congr (fun k => ?_)
  rw [PowerSeries.coeff_rescale, smul_smul, smul_smul]
  congr 1
  rw [show u ^ i = u ^ (k : ℤ) * u ^ (i - k) by rw [← zpow_add₀ hu]; ring_nf, zpow_natCast]
  ring

end Formalism.MainNotions.N.Ln34.MLG

end
end

noncomputable section

namespace Formalism.MainNotions.N.Ln34.MLH

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop)
    (π' Eπ : LetA O n) (h' : ℕ) (c : ZMod n)

theorem γLA_smulLA (b : LetA O n) (z : LA W T π' c) :
    γLA W T π' c (smulLA W T π' c b z) = smulLA W T π' c (W.γA W.gamK b) (γLA W T π' c z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul e s =>
    show W.γE W.gamK (algebraMap (LetA O n) W.EE b * e) ⊗ₜ s =
      (algebraMap (LetA O n) W.EE (W.γA W.gamK b) * W.γE W.gamK e) ⊗ₜ s
    rw [map_mul, W.γE_ext]
    rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem γA_mem_AΔ {a : LetA O n} (ha : a ∈ W.AΔ) : W.γA W.gamK a ∈ W.AΔ := by
  intro δ hδ
  have e1 : W.γA δ (W.γA W.gamK a) = W.γA (δ * W.gamK) a := by
    simp only [LocWach.γA, map_mul]
    rfl
  have e2 : W.γA W.gamK (W.γA δ a) = W.γA (W.gamK * δ) a := by
    simp only [LocWach.γA, map_mul]
    rfl
  rw [e1, mul_comm, ← e2, ha δ hδ]

theorem rep_γ {u₀ : LetA O n} (hu₀ : u₀ ∈ W.AΔ) (hΛ : u₀ * W.γA W.gamK (Eπ ^ h') = Eπ ^ h')
    (hlet : W.γA W.gamK (letE c : LetA O n) = letE c)
    {x : LA W T π' c} {m : ℕ} {a : Fin m → ↥W.AΔ} {y : Fin m → W.DD T}
    (hr : IsRepL W T π' Eπ h' c x a y) :
    IsRepL W T π' Eπ h' c (γLA W T π' c x)
      (fun j => ⟨u₀ * W.γA W.gamK (a j), W.AΔ.mul_mem hu₀ (γA_mem_AΔ W (a j).2)⟩) y := by
  obtain ⟨hy, hx⟩ := hr
  refine ⟨hy, ?_⟩
  have e : smulLA W T π' c (Eπ ^ h') (γLA W T π' c x) =
      smulLA W T π' c u₀ (γLA W T π' c (smulLA W T π' c (Eπ ^ h') x)) := by
    rw [γLA_smulLA, MLE.smulLA_smulLA, hΛ]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, hx, map_sum, map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  show (algebraMap (LetA O n) W.EE u₀ * W.γE W.gamK (algebraMap (LetA O n) W.EE
      ((letE c : LetA O n) * a j))) ⊗ₜ mkL W T π' c (y j) (hy j) = _
  rw [W.γE_ext, ← map_mul]
  congr 2
  show u₀ * W.γA W.gamK ((letE c : LetA O n) * a j) = (letE c : LetA O n) * (u₀ * W.γA W.gamK (a j))
  rw [map_mul, hlet]
  ring

theorem expS_γ (ζ : LL) (u : LL) (hlev : ∀ a, W.lev c ζ (W.γA W.gamK a) = PowerSeries.rescale u (W.lev c ζ a))
    {m : ℕ} (a : Fin m → LetA O n) (y : Fin m → W.DD T) (i : ℤ) :
    expS W T c ζ (fun j => W.γA W.gamK (a j)) y i = u ^ i.toNat • expS W T c ζ a y i := by
  simp only [expS, serC, hlev, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  split_ifs
  · rw [PowerSeries.coeff_rescale, mul_smul]
  · rw [smul_zero]

theorem nl_γ {u₀ : LetA O n} (hu₀ : u₀ ∈ W.AΔ) (hΛ : u₀ * W.γA W.gamK (Eπ ^ h') = Eπ ^ h')
    (hlet : W.γA W.gamK (letE c : LetA O n) = letE c) (u : LL)
    (hlev : ∀ τ ζ, Pt c ζ τ → ∀ a, W.lev c ζ (W.γA W.gamK a) = PowerSeries.rescale u (W.lev c ζ a))
    {x : LA W T π' c} (hx : x ∈ NL W T Pt π' Eπ h' c) : γLA W T π' c x ∈ NL W T Pt π' Eπ h' c := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, a, y, hr, hg⟩ := hx
    refine Submodule.subset_span ⟨m, _, y, rep_γ W T π' Eπ h' c hu₀ hΛ hlet hr, fun τ ζ hpt => ?_⟩
    refine MLB.goodF_mul W T c ζ τ h' u₀ (fun j => W.γA W.gamK (a j)) y (fun i => ?_)
    rw [expS_γ W T c ζ u (hlev τ ζ hpt)]
    exact Submodule.smul_mem _ _ (hg τ ζ hpt i)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul o x _ hx => rw [LinearMap.map_smul]; exact Submodule.smul_mem _ _ hx

end Generic

end Formalism.MainNotions.N.Ln34.MLH

end
end

noncomputable section

namespace Formalism.MainNotions.N.Ln34.MLI

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop)
    (π' Eπ : LetA O n) (h' : ℕ) (c : ZMod n)

theorem expS_neg (ζ : LL) {m : ℕ} (a : Fin m → LetA O n) (y : Fin m → W.DD T) {i : ℤ} (hi : i < 0) :
    expS W T c ζ a y i = 0 := by
  simp [expS, serC, if_neg (show ¬ (0 ≤ i) by omega)]

theorem ind_fil (τ : K →ₐ[Qp] LL) (U : PowerSeries LL) (hU : PowerSeries.constantCoeff U ≠ 0)
    {g : ℤ → T.V ⊗[Qp] BdR} {m₀ : ℤ} (hg : MLG.Bdd g m₀)
    (hH : ∀ j, serMul U g j ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (-j)) :
    ∀ j, g j ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (-j) := by
  have key : ∀ N : ℕ, ∀ j, j < m₀ + N → g j ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (-j) := by
    intro N
    induction N with
    | zero => intro j hj; rw [hg j (by omega)]; exact Submodule.zero_mem _
    | succ N ih =>
      intro j hj
      by_cases hjN : j < m₀ + N
      · exact ih j hjN
      · have hj' : j = m₀ + N := by push_cast at hj; omega
        have hs := hH j
        rw [MLG.serMul_eq_sum U hg j ((j - m₀).toNat + 1) le_rfl, Finset.sum_range_succ'] at hs
        have hrest : ∑ k ∈ Finset.range (j - m₀).toNat, PowerSeries.coeff (k + 1) U • g (j - ((k + 1 : ℕ) : ℤ)) ∈
            Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (-j) := by
          refine Submodule.sum_mem _ (fun k hk => Submodule.smul_mem _ _ ?_)
          rw [Finset.mem_range] at hk
          exact u3upPf_FilC_anti (PD := PD) T τ (by push_cast; omega) (ih _ (by push_cast; omega))
        have h0 := Submodule.sub_mem _ hs hrest
        rw [add_sub_cancel_left, PowerSeries.coeff_zero_eq_constantCoeff_apply, Nat.cast_zero, sub_zero] at h0
        exact (Submodule.smul_mem_iff _ hU).1 h0
  intro j
  exact key ((j - m₀).toNat + 1) j (by omega)

end Generic

end Formalism.MainNotions.N.Ln34.MLI

end
end

noncomputable section

namespace Formalism.MainNotions.N.Ln34.MLJ

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop)
    (π' Eπ : LetA O n) (h' : ℕ) (c : ZMod n)

theorem local_form (hwd : MLF.WD W T Pt π' c) {u₀ : LetA O n} (hu₀ : u₀ ∈ W.AΔ)
    (hΛ : u₀ * W.γA W.gamK (Eπ ^ h') = Eπ ^ h') (hlet : W.γA W.gamK (letE c : LetA O n) = letE c)
    (u : LL) (hu : u ≠ 0) (hu1 : ∀ i : ℤ, i ≠ 0 → u ^ i ≠ 1)
    (hlev : ∀ τ ζ, Pt c ζ τ → ∀ a, W.lev c ζ (W.γA W.gamK a) = PowerSeries.rescale u (W.lev c ζ a))
    (hsimp : ∀ τ ζ, Pt c ζ τ → ∃ U : PowerSeries LL, W.lev c ζ (Eπ ^ h') = PowerSeries.X ^ h' * U ∧
      PowerSeries.constantCoeff U ≠ 0)
    {x : LA W T π' c} (hx : x ∈ LamLA W T π' Eπ h' c ⊤)
    (hγ : γLA W T π' c x - x ∈ NL W T Pt π' Eπ h' c) :
    ∀ τ ζ, Pt c ζ τ → ∀ f, ExpL W T π' Eπ h' c ζ x f → ∀ i : ℤ, i ≠ 0 →
      f i ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (-i) := by
  intro τ ζ hpt f hf i hi
  obtain ⟨⟨m₀, hf0⟩, m, a, y, hr, hfe⟩ := hf
  have hfb : MLG.Bdd f m₀ := hf0

  have hrγ := MLH.rep_γ W T π' Eπ h' c hu₀ hΛ hlet hr
  have hrn := MLE.rep_smul W T π' Eπ h' c hr (W.AΔ.algebraMap_mem (-1 : O))
  rw [← MLE.smul_eq_smulLA, neg_one_smul] at hrn
  have hra := MLE.rep_append W T π' Eπ h' c hrγ hrn
  rw [← sub_eq_add_neg] at hra
  have hgood := MLF.good_all W T Pt π' Eπ h' c hwd hγ hra τ ζ hpt
  rw [MLE.expS_append] at hgood
  set e := expS W T c ζ (fun j => (a j : LetA O n)) y with he
  have heb : MLG.Bdd e 0 := fun j hj => MLI.expS_neg W T c ζ _ y hj

  have hneg : expS W T c ζ (fun j => ((⟨algebraMap O (LetA O n) (-1) * a j,
      W.AΔ.mul_mem (W.AΔ.algebraMap_mem _) (a j).2⟩ : ↥W.AΔ) : LetA O n)) y = -e := by
    show expS W T c ζ (fun j => algebraMap O (LetA O n) (-1) * (a j : LetA O n)) y = -e
    rw [MLF.expS_alg_mul, map_neg, map_one, neg_one_smul]
  obtain ⟨U, hU, hU0⟩ := hsimp τ ζ hpt
  have hfu : MLG.Bdd (fun s => u ^ s • f s) m₀ := fun s hs => by simp only [hfb s hs, smul_zero]
  have hγpart : ∀ j, expS W T c ζ (fun k => ((⟨u₀ * W.γA W.gamK (a k), W.AΔ.mul_mem hu₀
      (MLH.γA_mem_AΔ W (a k).2)⟩ : ↥W.AΔ) : LetA O n)) y j =
      serMul (W.lev c ζ (Eπ ^ h')) (fun s => u ^ s • f s) j := by
    intro j
    show expS W T c ζ (fun k => u₀ * W.γA W.gamK (a k)) y j = _
    have hLdec : W.lev c ζ (Eπ ^ h') = W.lev c ζ u₀ * PowerSeries.rescale u (W.lev c ζ (Eπ ^ h')) := by
      rw [← hlev τ ζ hpt, ← map_mul, hΛ]
    rw [MLB.expS_mul, hLdec, ← MLG.serMul_serMul _ _ hfu]
    have hin : serMul (PowerSeries.rescale u (W.lev c ζ (Eπ ^ h'))) (fun s => u ^ s • f s) =
        fun s => u ^ s • e s := by
      funext s
      rw [← MLG.serMul_rescale u hu, hfe s]
    rw [hin, MLG.serMul_eq_sum (m₀ := 0) _ (fun s hs => by simp only [heb s hs, smul_zero]) j (j.toNat + 1) (by omega)]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [MLH.expS_γ W T c ζ u (hlev τ ζ hpt)]
    congr 1
    by_cases hjk : 0 ≤ j - (k : ℤ)
    · rw [← zpow_natCast, Int.toNat_of_nonneg hjk]
    · rw [MLI.expS_neg W T c ζ _ y (by omega), heb _ (by omega), smul_zero, smul_zero]

  set g : ℤ → T.V ⊗[Qp] BdR := fun s => u ^ s • f s - f s with hgdef
  have hgb : MLG.Bdd g m₀ := fun s hs => by simp [hgdef, hfb s hs]
  have hGg : ∀ j, serMul (W.lev c ζ (Eπ ^ h')) g j ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (h' - j) := by
    intro j
    have h1 := hgood j
    rw [Pi.add_apply, hγpart j, hneg, Pi.neg_apply, ← hfe j, ← sub_eq_add_neg] at h1
    convert h1 using 1
    rw [MLG.serMul_eq_sum _ hgb j _ le_rfl, MLG.serMul_eq_sum _ hfu j _ le_rfl,
      MLG.serMul_eq_sum _ hfb j _ le_rfl, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hgdef, smul_sub]
  have hH : ∀ j, serMul U g j ∈ Formalism.MainNotions.DeltaInvariantLattices.FilC (PD := PD) T τ (-j) := by
    intro j
    have h1 := hGg (j + h')
    rw [hU, ← MLG.serMul_serMul _ _ hgb, MLG.serMul_X_pow, add_sub_cancel_right] at h1
    convert h1 using 2
    ring
  have hgi := MLI.ind_fil T τ U hU0 hgb hH i
  have e1 : g i = (u ^ i - 1) • f i := by rw [hgdef, sub_smul, one_smul]
  rw [e1] at hgi
  exact (Submodule.smul_mem_iff _ (sub_ne_zero.2 (hu1 i hi))).1 hgi

end Generic

end Formalism.MainNotions.N.Ln34.MLJ

end
end

noncomputable section

namespace Formalism.MainNotions.N.Ln34.MLL

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct Formalism.MainNotions.N.Ln34.ModelFPf

theorem rec_WD (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (CA CB CK : ℝ) (hA : Adm1 D HW F Cm CA CB CK) (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) (K LL : FinExt l)
    (hG : Good K 1 LL) (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K)))
    (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL))
    (hr : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (hT : IsCrys ((D.loc l).PD K) T.ρ)
    (c : ZMod (finrank ℚ_[l] ↥(K0 K))) :
    MLF.WD ((HW l).W K 1 LL hG) T (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) π' c := by
  intro τ ζ hpt m m' a y hy b z hz h
  have hs : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hprim : IsPrimitiveRoot ζ l := framepf_pt_prim D HW hG c ζ τ hpt
  have hprim' : IsPrimitiveRoot ζ ((D.loc l).PD K).p := by rw [hp]; exact hprim
  haveI : IsDiscreteValuationRing ↥(OL LL) := GenPf.isDVR (D.loc l) LL
  have hinj : Function.Injective (algebraMap ↥(OL LL) ↥LL.1) := Subtype.val_injective
  obtain ⟨-, -, -, h4W, -⟩ := hA.1 l K 1 LL hG
  have hone : ∃ j : ℕ, IsPrimitiveRoot (1 : ↥LL.1) (((D.loc l).PD K).p ^ j) := ⟨0, by simp⟩
  have hπ1 : PowerSeries.constantCoeff (((HW l).W K 1 LL hG).lev (c - 1) 1 letπ) = 0 := by
    rw [CrystallineExponents.cc_lev_pi ((HW l).W K 1 LL hG) (c - 1) 1 hone, sub_self]
  have hX : ((HW l).W K 1 LL hG).X = letπ := by simp [LocWach.X, hs]
  have hd := Formalism.MainNotions.N.Ln34.DvdPf.dvdCondition l hl K LL hG
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have he : 0 < eK K := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, zero_dvd_iff] at hd
    omega
  have hsK : 1 ≤ sK l K := Nat.div_pos (Nat.le_of_dvd (by omega) hd) he
  have hπ : PowerSeries.constantCoeff (((HW l).W K 1 LL hG).lev (c - 1) 1 π') = 0 := by
    obtain ⟨w, hw⟩ := hr.2.2.1
    rw [hw, map_mul, map_pow, map_mul, map_pow, hπ1, zero_pow (by omega), mul_zero]
  have hQ := framepf_Q_at ((HW l).W K 1 LL hG) hs c ζ hprim'
  have hP : MLA.PtHyp (W := (HW l).W K 1 LL hG) T c ζ := by
    refine ⟨hT, ⟨1, by rw [pow_one]; exact hprim'⟩, hprim'.pow_eq_one, hQ.1, hQ.2, ?_, ?_⟩
    · intro x k hk
      have h4 := ((h4W T hT).1 (c - 1) 1 ⟨0, by simp⟩ (by rw [hX]; exact hπ1)).1 x k
      exact h4.2 hk
    · intro x hx
      exact ((HW l).W K 1 LL hG).N_φ T x hx
  exact MLA.expS_wd ((Cm l).C K 1 LL hG).tie T hinj hP π' hπ a y hy b z hz h

set_option maxHeartbeats 1000000 in
theorem exists_mul_gamma_Eat_pow_eq_Eat_pow (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (CA CB CK : ℝ) (hA : Adm1 D HW F Cm CA CB CK) (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) (K LL : FinExt l)
    (hG : Good K 1 LL) (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K)))
    (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL))
    (hr : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E) (h' : ℕ) :
    ∃ u₀ ∈ ((HW l).W K 1 LL hG).AΔ, u₀ * ((HW l).W K 1 LL hG).γA ((HW l).W K 1 LL hG).gamK
      (Formalism.MainNotions.DeltaInvariantLattices.Eat E π' ^ h') = Formalism.MainNotions.DeltaInvariantLattices.Eat E π' ^ h' := by
  have hs : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hgam : ((HW l).W K 1 LL hG).gamK = ((HW l).W K 1 LL hG).gam :=
    ((HW l).W K 1 LL hG).gamK_eq_one hs (by rw [hp]; exact hl)
  obtain ⟨hπΔ, -, ⟨w0, hw0⟩, -, ⟨w, hw⟩, -, ⟨w2, hw2⟩, -⟩ := hr
  have hd := Formalism.MainNotions.N.Ln34.DvdPf.dvdCondition l hl K LL hG
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have he : 0 < eK K := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, zero_dvd_iff] at hd
    omega
  have hsK : 1 ≤ sK l K := Nat.div_pos (Nat.le_of_dvd (by omega) hd) he
  have hEΔ : Formalism.MainNotions.DeltaInvariantLattices.Eat E π' ∈ ((HW l).W K 1 LL hG).AΔ := by
    intro δ hδ
    funext i
    show ((HW l).W K 1 LL hG).γ₀ δ (Polynomial.aeval (π' i) (E i)) = Polynomial.aeval (π' i) (E i)
    rw [← Polynomial.aeval_algHom_apply]
    exact congrArg (fun t => Polynomial.aeval t (E i)) (congrFun (hπΔ δ hδ) i)
  obtain ⟨u, hu, hγ⟩ := gam_unit ((HW l).W K 1 LL hG) π' E hsK w2 hw2 w0 hw0
  have hpO : (((D.loc l).PD K).p : ↥(OL LL)) ≠ 0 := fun h0 => by
    apply p_ne_zero ((HW l).W K 1 LL hG)
    rw [← map_natCast (algebraMap ↥(OL LL) ↥LL.1), h0, map_zero]
  have hnz := Eπ_nzd ((HW l).W K 1 LL hG) hw (q0_ne_two_and_ne_q_and_ne_d ((HW l).W K 1 LL hG) hpO)
  have huΔ := u_mem_AΔ ((HW l).W K 1 LL hG) hEΔ hnz hγ
  have hu'Δ := inv_mem_AΔ ((HW l).W K 1 LL hG) huΔ hu.val_inv_mul
  refine ⟨((hu.unit⁻¹ : (LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K)))ˣ) : LetA _ _) ^ h', Subalgebra.pow_mem _ hu'Δ h', ?_⟩
  rw [hgam, map_pow, hγ, mul_pow, ← mul_assoc, ← mul_pow, hu.val_inv_mul, one_pow, one_mul]

set_option maxHeartbeats 1000000 in
theorem rec_lev (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) (K LL : FinExt l) (hG : Good K 1 LL)
    (c : ZMod (finrank ℚ_[l] ↥(K0 K))) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (ζ : ↥LL.1)
    (hpt : Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ) (a : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K))) :
    ((HW l).W K 1 LL hG).lev c ζ (((HW l).W K 1 LL hG).γA ((HW l).W K 1 LL hG).gamK a) =
      PowerSeries.rescale (algebraMap ↥(OL LL) ↥LL.1
        ((((HW l).W K 1 LL hG).χΓ ((HW l).W K 1 LL hG).gamK : (↥(OL LL))ˣ) : ↥(OL LL)))
        (((HW l).W K 1 LL hG).lev c ζ a) := by
  have hs : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hgam : ((HW l).W K 1 LL hG).gamK = ((HW l).W K 1 LL hG).gam :=
    ((HW l).W K 1 LL hG).gamK_eq_one hs (by rw [hp]; exact hl)
  have hprim : IsPrimitiveRoot ζ (((D.loc l).PD K).p ^ 1) := by
    rw [pow_one, hp]; exact framepf_pt_prim D HW hG c ζ τ hpt
  have hv : ((1 : ℕ) : WithTop ℚ) ≤ (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1
      ((((HW l).W K 1 LL hG).χΓ ((HW l).W K 1 LL hG).gamK : (↥(OL LL))ˣ) : ↥(OL LL)) - ((1 : ℕ) : ↥LL.1)) := by
    rw [hgam, Nat.cast_one (R := ↥LL.1), ((HW l).W K 1 LL hG).gam_gen, hs]
  have := ((Cm l).C K 1 LL hG).tie.lev_Γ ((HW l).W K 1 LL hG).gamK c ζ ζ 1 1 hprim hv (by rw [pow_one]) a
  exact this

set_option maxHeartbeats 1000000 in
theorem rec_u (D : D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) (K LL : FinExt l)
    (hG : Good K 1 LL) :
    algebraMap ↥(OL LL) ↥LL.1 ((((HW l).W K 1 LL hG).χΓ ((HW l).W K 1 LL hG).gamK : (↥(OL LL))ˣ) :
      ↥(OL LL)) ≠ 0 ∧
    ∀ i : ℤ, i ≠ 0 → (algebraMap ↥(OL LL) ↥LL.1 ((((HW l).W K 1 LL hG).χΓ
      ((HW l).W K 1 LL hG).gamK : (↥(OL LL))ˣ) : ↥(OL LL))) ^ i ≠ 1 := by
  have hs : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hgam : ((HW l).W K 1 LL hG).gamK = ((HW l).W K 1 LL hG).gam :=
    ((HW l).W K 1 LL hG).gamK_eq_one hs (by rw [hp]; exact hl)
  have hd := Formalism.MainNotions.N.Ln34.DvdPf.dvdCondition l hl K LL hG
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have he : 0 < eK K := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, zero_dvd_iff] at hd
    omega
  have hsK : 1 ≤ sK l K := Nat.div_pos (Nat.le_of_dvd (by omega) hd) he
  have har := (framepf_hyp_arith D HW l hl K LL hG 1 hsK).1
  rw [hgam]
  set χ := ((((HW l).W K 1 LL hG).χΓ ((HW l).W K 1 LL hG).gam : (↥(OL LL))ˣ) : ↥(OL LL)) with hχ
  have hnat : ∀ k : ℕ, 1 ≤ k → (algebraMap ↥(OL LL) ↥LL.1 χ) ^ k ≠ 1 := by
    intro k hk h1
    have h2 : χ ^ k = 1 := by
      apply Subtype.val_injective
      have := h1
      rw [← map_pow] at this
      simpa using this
    apply har k hk
    rw [← pow_mul, mul_comm, pow_mul, h2, one_pow]
  refine ⟨((Units.isUnit _).map (algebraMap ↥(OL LL) ↥LL.1)).ne_zero, fun i hi h1 => ?_⟩
  rcases lt_or_gt_of_ne hi with hneg | hpos
  · apply hnat (-i).toNat (by omega)
    have : (algebraMap ↥(OL LL) ↥LL.1 χ) ^ (-i) = 1 := by rw [zpow_neg, h1, inv_one]
    rwa [← zpow_natCast, Int.toNat_of_nonneg (by omega)]
  · apply hnat i.toNat (by omega)
    rwa [← zpow_natCast, Int.toNat_of_nonneg (by omega)]

end Formalism.MainNotions.N.Ln34.MLL

end
