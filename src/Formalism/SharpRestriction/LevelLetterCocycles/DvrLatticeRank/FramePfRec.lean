module

public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.ModelFPf
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfLocC
public import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfAlpha

@[expose] public section

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfDat
section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfHH
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {T : LocLat G Qp LL O}
    (Bs : FramepfBas W T) (π' : LetA O n) (c : ZMod n)
    (hπ0 : ∀ j, PowerSeries.constantCoeff (π' j) = 0)
    (hΔπ : ∀ δ ∈ W.DelF, W.γA δ π' = π')
    (hR2 : ∀ a : LetA O n, a ∈ W.AΔ → ∃! f : ZMod n → PowerSeries O,
      ∀ j, a j = PowerSeries.subst (π' j) (f j))
    (γ0 : ∀ δ ∈ W.DelF, PowerSeries.constantCoeff (W.γ₀ δ PowerSeries.X) = 0)
    (hu : IsUnit (algebraMap (LetA O n) W.EE π'))

include hπ0 hΔπ γ0 in
theorem framepf_hhx_ι_Δ (i : ZMod n) (g : PowerSeries O) (δ : W.Gam) (hδ : δ ∈ W.DelF) :
    W.γA δ (framepf_ι π' i g) = framepf_ι π' i g := by
  have h := framepf_ι_letγ π' i (hπ0 i) (W.γ₀ δ) (γ0 δ hδ) PowerSeries.X (by simp)
    (by rw [PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero' (hπ0 i))];
        exact congrFun (hΔπ δ hδ) i) g
  rw [PowerSeries.X_subst] at h
  exact h

include hπ0 hΔπ γ0 in
theorem framepf_hhx_vec_mem (H : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) (k : Fin Bs.r) :
    framepf_vec Bs π' (c - 1) H k ∈ NcS W T (c - 1) := by
  unfold framepf_vec
  refine Submodule.sum_mem _ fun m _ => ?_
  rw [mem_NcS]
  obtain ⟨hN, hΔ⟩ := Bs.mem m
  refine ⟨(W.N T).smul_mem _ hN, fun δ hδ => ?_, ?_⟩
  · rw [gradNPf_γD_smul, framepf_hhx_ι_Δ π' hπ0 hΔπ γ0 _ _ δ hδ, hΔ δ hδ]
  · rw [smul_smul, framepf_letE_ι π' (c - 1) hπ0]

theorem framepf_hhx_mem (H : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) (ℓ : LcQ W T π' c) :
    framepf_hh Bs π' c hπ0 hΔπ hR2 γ0 hu H ℓ ∈ NcS W T (c - 1) := by
  unfold framepf_hh
  rw [LinearMap.comp_apply, Fintype.linearCombination_apply]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (framepf_hhx_vec_mem Bs π' c hπ0 hΔπ γ0 H k)

include hπ0 in
theorem framepf_hhx_vec_pow (i : ZMod n) (Hm : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) (M : ℕ)
    (k : Fin Bs.r) :
    framepf_vec Bs π' i ((PowerSeries.X : PowerSeries O) ^ M • Hm) k =
      π' ^ M • framepf_vec Bs π' i Hm k := by
  induction M with
  | zero => rw [pow_zero, pow_zero, one_smul, one_smul]
  | succ M ih => rw [pow_succ', mul_smul, framepf_vec_X_smul Bs π' i hπ0, ih, smul_smul, ← pow_succ']

theorem framepf_hhx_apply (H : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) (ℓ : LcQ W T π' c) :
    framepf_hh Bs π' c hπ0 hΔπ hR2 γ0 hu H ℓ =
      ∑ k, framepf_Lbas Bs π' c hπ0 hΔπ hR2 γ0 hu ℓ k • framepf_vec Bs π' (c - 1) H k := by
  unfold framepf_hh
  rw [LinearMap.comp_apply, Fintype.linearCombination_apply]
  rfl

theorem framepf_hhx_γ (Gs : PowerSeries O) (hGs0 : PowerSeries.constantCoeff Gs = 0)
    (hGs : W.γ₀ W.gam (π' (c - 1)) = PowerSeries.subst (π' (c - 1)) Gs)
    (Γ : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O))
    (hΓ : ∀ m, W.γD T W.gam ((letE (c - 1) : LetA O n) • Bs.b m) = framepf_vec Bs π' (c - 1) Γ m)
    (H Km : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) (M : ℕ)
    (hH : Γ * H.map (PowerSeries.subst Gs) - H = (PowerSeries.X : PowerSeries O) ^ M • Km)
    (ℓ : LcQ W T π' c) :
    W.γD T W.gam (framepf_hh Bs π' c hπ0 hΔπ hR2 γ0 hu H ℓ) - framepf_hh Bs π' c hπ0 hΔπ hR2 γ0 hu H ℓ ∈
      PiNS W T π' M := by
  have e : W.γD T W.gam (framepf_hh Bs π' c hπ0 hΔπ hR2 γ0 hu H ℓ) -
      framepf_hh Bs π' c hπ0 hΔπ hR2 γ0 hu H ℓ = π' ^ M • framepf_hh Bs π' c hπ0 hΔπ hR2 γ0 hu Km ℓ := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [framepf_hhx_apply, framepf_hhx_apply, map_sum, ← Finset.sum_sub_distrib, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, framepf_γ_vec Bs π' (c - 1) hπ0 Gs hGs0 hGs Γ hΓ, sub_eq_iff_eq_add.1 hH,
      framepf_vec_add Bs π' (c - 1) hπ0, framepf_hhx_vec_pow Bs π' hπ0, smul_add, add_sub_cancel_right,
      smul_comm]
  have hm := (mem_NcS W T (c - 1) _).1 (framepf_hhx_mem Bs π' c hπ0 hΔπ hR2 γ0 hu Km ℓ)
  rw [e, mem_PiNS]
  refine ⟨⟨_, hm.1, rfl⟩, fun δ hδ => ?_⟩
  rw [gradNPf_γD_smul, map_pow, hΔπ δ hδ, hm.2.1 δ hδ]

theorem framepf_hhx_mod (lσ : O) (H Km : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O))
    (hH : H = PowerSeries.C lσ • (1 : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) +
      (PowerSeries.X : PowerSeries O) • Km)
    (z : W.DD T) (hz : z ∈ NcS W T (c - 1)) :
    framepf_hh Bs π' c hπ0 hΔπ hR2 γ0 hu H (mkL W T π' c z hz) - lσ • z ∈ PiNS W T π' 1 := by
  set ℓ := mkL W T π' c z hz with hℓ
  have hv : ∀ k, framepf_coordL Bs π' c hπ0 hΔπ hR2 γ0
      ⟨_, framepf_hhx_vec_mem Bs π' c hπ0 hΔπ γ0 H k⟩ = lσ • Pi.single k 1 := by
    intro k
    have e := framepf_gco_eq Bs π' c hπ0 hΔπ hR2 γ0 ⟨_, framepf_hhx_vec_mem Bs π' c hπ0 hΔπ γ0 H k⟩
      (fun m => H m k) rfl
    funext m
    rw [framepf_coordL_apply, e, hH]
    by_cases hmk : m = k
    · subst hmk; simp
    · simp [Matrix.one_apply_ne hmk, Pi.single_eq_of_ne hmk]
  have hsum : (⟨_, framepf_hhx_mem Bs π' c hπ0 hΔπ hR2 γ0 hu H ℓ⟩ : ↥(NcS W T (c - 1))) =
      ∑ k, framepf_Lbas Bs π' c hπ0 hΔπ hR2 γ0 hu ℓ k •
        (⟨_, framepf_hhx_vec_mem Bs π' c hπ0 hΔπ γ0 H k⟩ : ↥(NcS W T (c - 1))) := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    exact framepf_hhx_apply Bs π' c hπ0 hΔπ hR2 γ0 hu H ℓ
  have key := (framepf_coordL_ker Bs π' c hπ0 hΔπ hR2 γ0 hu
    (⟨_, framepf_hhx_mem Bs π' c hπ0 hΔπ hR2 γ0 hu H ℓ⟩ - lσ • ⟨z, hz⟩)).1 (by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, map_smul, hsum, map_sum, ← framepf_Lbas_mk Bs π' c hπ0 hΔπ hR2 γ0 hu ⟨z, hz⟩]
      simp only [map_smul, hv]
      have : Submodule.Quotient.mk (⟨z, hz⟩ : ↥(NcS W T (c - 1))) = ℓ := rfl
      rw [this, sub_eq_zero]
      funext m
      simp [Finset.sum_apply, Pi.single_apply, mul_comm])
  exact key

end Local

end Formalism.MainNotions.N.Ln34

end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FramePfMat
section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.FrameAbs
namespace DualFramesAlt.FrameAbs

open Matrix

variable {A : Type*} [CommRing A] {d : ℕ}

def MatIn (I : Ideal A) (H : Matrix (Fin d) (Fin d) A) : Prop := by
  first | exact @Bl.FirstLemmaO.goal1 A ‹_› d I H | exact @Bl.FirstLemmaO.goal1 A ‹_› d I | exact @Bl.FirstLemmaO.goal1 A ‹_› d | exact @Bl.FirstLemmaO.goal1 A ‹_› | exact @Bl.FirstLemmaO.goal1 A | exact @Bl.FirstLemmaO.goal1

def IsFrame (σ : A →+* A) (Γ : Matrix (Fin d) (Fin d) A) (π c : A) (M : ℕ)
    (H : Matrix (Fin d) (Fin d) A) : Prop :=
  MatIn (Ideal.span {π}) (H - c • (1 : Matrix (Fin d) (Fin d) A)) ∧
    MatIn (Ideal.span {π ^ M}) (Γ * H.map σ - H)

def IsDualFrame (σ : A →+* A) (Γ : Matrix (Fin d) (Fin d) A) (π c : A) (M : ℕ)
    (F : Matrix (Fin d) (Fin d) A) : Prop :=
  MatIn (Ideal.span {π}) (F - c • (1 : Matrix (Fin d) (Fin d) A)) ∧
    MatIn (Ideal.span {π ^ M}) (F * Γ - F.map σ)

structure Hyp (O : Type*) [CommRing O] [Algebra O A] (σ : A →+* A) (Γ : Matrix (Fin d) (Fin d) A)
    (π : A) (ev : ℕ → A) : Prop where
  hσ : ∀ a : A, σ a - a ∈ (Ideal.span {π} : Ideal A)
  hΓ : MatIn (Ideal.span {π}) (Γ - 1)
  hΓunit : IsUnit Γ.det
  hπ : π ∈ nonZeroDivisors A
  hσπ : ∀ y : ℕ, σ (π ^ y) - (ev y + 1) * π ^ y ∈ (Ideal.span {π ^ (y + 1)} : Ideal A)
  hσev : ∀ y : ℕ, σ (ev y) = ev y
  hnzd : ∀ (y : ℕ) (a : A), 1 ≤ y → ev y * a ∈ (Ideal.span {π} : Ideal A) → a ∈ (Ideal.span {π} : Ideal A)
  hO : ∀ o : O, σ (algebraMap O A o) = algebraMap O A o
  hdec : ∀ a : A, ∃ o : O, a - algebraMap O A o ∈ (Ideal.span {π} : Ideal A)
  hinj : ∀ o : O, algebraMap O A o ∈ (Ideal.span {π} : Ideal A) → o = 0
  hev : ∀ y : ℕ, ∃ o : O, ev y = algebraMap O A o

section SlopeTestRemainingChoices

variable {I J : Ideal A} {X Y : Matrix (Fin d) (Fin d) A}

theorem MatIn.zero : MatIn I (0 : Matrix (Fin d) (Fin d) A) := fun _ _ => I.zero_mem

theorem MatIn.add (hX : MatIn I X) (hY : MatIn I Y) : MatIn I (X + Y) :=
  fun i j => I.add_mem (hX i j) (hY i j)

theorem MatIn.neg (hX : MatIn I X) : MatIn I (-X) := fun i j => I.neg_mem (hX i j)

theorem MatIn.sub (hX : MatIn I X) (hY : MatIn I Y) : MatIn I (X - Y) :=
  fun i j => I.sub_mem (hX i j) (hY i j)

theorem MatIn.mul_left (hY : MatIn I Y) : MatIn I (X * Y) := fun i j => by
  rw [Matrix.mul_apply]; exact I.sum_mem fun k _ => I.mul_mem_left _ (hY k j)

theorem MatIn.mul_right (hX : MatIn I X) : MatIn I (X * Y) := fun i j => by
  rw [Matrix.mul_apply]; exact I.sum_mem fun k _ => I.mul_mem_right _ (hX i k)

theorem MatIn.smul (hX : MatIn I X) (a : A) : MatIn I (a • X) := fun i j => by
  rw [Matrix.smul_apply, smul_eq_mul]; exact I.mul_mem_left a (hX i j)

theorem MatIn.mono (hIJ : I ≤ J) (hX : MatIn I X) : MatIn J X := fun i j => hIJ (hX i j)

theorem MatIn.transpose (hX : MatIn I X) : MatIn I Xᵀ := fun i j => hX j i

theorem MatIn.exists_smul {p : A} (h : MatIn (Ideal.span {p}) X) :
    ∃ K : Matrix (Fin d) (Fin d) A, X = p • K := by
  choose K hK using fun i j => Ideal.mem_span_singleton'.mp (h i j)
  refine ⟨Matrix.of K, ?_⟩
  ext i j
  rw [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
  exact (hK i j).symm.trans (mul_comm _ _)

theorem MatIn.smul_self (p : A) (K : Matrix (Fin d) (Fin d) A) : MatIn (Ideal.span {p}) (p • K) :=
  fun i j => by
    rw [Matrix.smul_apply, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self p)

theorem matIn_sub_iff : MatIn I (X - Y) ↔ X.map (Ideal.Quotient.mk I) = Y.map (Ideal.Quotient.mk I) := by
  constructor
  · intro h
    ext i j
    rw [Matrix.map_apply, Matrix.map_apply, Ideal.Quotient.eq]
    exact h i j
  · intro h i j
    have := congr_fun (congr_fun h i) j
    rw [Matrix.map_apply, Matrix.map_apply, Ideal.Quotient.eq] at this
    exact this

theorem span_pow_mono (π : A) {m n : ℕ} (h : m ≤ n) :
    Ideal.span {π ^ n} ≤ Ideal.span ({π ^ m} : Set A) :=
  Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π h)

theorem span_pow_le (π : A) {n : ℕ} (h : 1 ≤ n) : Ideal.span {π ^ n} ≤ Ideal.span ({π} : Set A) :=
  Ideal.span_singleton_le_span_singleton.mpr (dvd_pow_self π (by omega))

theorem map_smul_ring (σ : A →+* A) (a : A) (X : Matrix (Fin d) (Fin d) A) :
    (a • X).map σ = σ a • X.map σ := by
  first | exact Bl.MatrixMapSmul.goal1 .. | (apply Bl.MatrixMapSmul.goal1 <;> assumption) | (intros; apply Bl.MatrixMapSmul.goal1 <;> assumption) | (apply @Bl.MatrixMapSmul.goal1 <;> assumption) | (intros; apply @Bl.MatrixMapSmul.goal1 <;> assumption) | (apply @Bl.MatrixMapSmul.goal1 <;> first | assumption | infer_instance) | exact @Bl.MatrixMapSmul.goal1 A ‹_› d σ a X | exact @Bl.MatrixMapSmul.goal1 A ‹_› d σ a | exact @Bl.MatrixMapSmul.goal1 A ‹_› d σ | exact @Bl.MatrixMapSmul.goal1 A ‹_› d | exact @Bl.MatrixMapSmul.goal1 A ‹_› | exact @Bl.MatrixMapSmul.goal1 A

theorem map_sub_ring (σ : A →+* A) (X Y : Matrix (Fin d) (Fin d) A) :
    (X - Y).map σ = X.map σ - Y.map σ := by
  first | exact Bl.MatrixMapSub.goal1 .. | (apply Bl.MatrixMapSub.goal1 <;> assumption) | (intros; apply Bl.MatrixMapSub.goal1 <;> assumption) | (apply @Bl.MatrixMapSub.goal1 <;> assumption) | (intros; apply @Bl.MatrixMapSub.goal1 <;> assumption) | (apply @Bl.MatrixMapSub.goal1 <;> first | assumption | infer_instance) | exact @Bl.MatrixMapSub.goal1 A ‹_› d σ X Y | exact @Bl.MatrixMapSub.goal1 A ‹_› d σ X | exact @Bl.MatrixMapSub.goal1 A ‹_› d σ | exact @Bl.MatrixMapSub.goal1 A ‹_› d | exact @Bl.MatrixMapSub.goal1 A ‹_› | exact @Bl.MatrixMapSub.goal1 A

theorem cancel_pow {π x : A} (hπ : π ∈ nonZeroDivisors A) {y : ℕ}
    (hx : π ^ y * x ∈ Ideal.span ({π ^ (y + 1)} : Set A)) : x ∈ Ideal.span ({π} : Set A) := by
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp hx
  have h0 : (x - t * π) * π ^ y = 0 := by linear_combination (-1 : A) * ht
  have h1 := (mem_nonZeroDivisors_iff.mp (pow_mem hπ y)).2 _ h0
  exact Ideal.mem_span_singleton'.mpr ⟨t, (sub_eq_zero.mp h1).symm⟩

end SlopeTestRemainingChoices

section Core

variable {σ : A →+* A} {π : A} {ev : ℕ → A}

theorem scalar_core (hσ : ∀ a : A, σ a - a ∈ (Ideal.span {π} : Ideal A))
    (hσπ : ∀ y : ℕ, σ (π ^ y) - (ev y + 1) * π ^ y ∈ (Ideal.span {π ^ (y + 1)} : Ideal A))
    (y : ℕ) (b : A) : ∃ r : A, σ (π ^ y * b) - π ^ y * b = π ^ y * (ev y * b + π * r) := by
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp (hσπ y)
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp (hσ b)
  refine ⟨(ev y + 1) * s + t * b + t * s * π, ?_⟩
  have e1 : σ (π ^ y) = (ev y + 1) * π ^ y + t * π ^ (y + 1) := by rw [ht]; ring
  have e2 : σ b = b + s * π := by rw [hs]; ring
  rw [map_mul, e1, e2]; ring

theorem mat_core {Γ : Matrix (Fin d) (Fin d) A} (hσ : ∀ a : A, σ a - a ∈ (Ideal.span {π} : Ideal A))
    (hΓ : MatIn (Ideal.span {π}) (Γ - 1))
    (hσπ : ∀ y : ℕ, σ (π ^ y) - (ev y + 1) * π ^ y ∈ (Ideal.span {π ^ (y + 1)} : Ideal A))
    (y : ℕ) (U : Matrix (Fin d) (Fin d) A) : ∃ R : Matrix (Fin d) (Fin d) A,
      Γ * (π ^ y • U).map σ - π ^ y • U = π ^ y • (ev y • U + π • R) := by
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp (hσπ y)
  have hK : MatIn (Ideal.span {π}) (Γ * U.map σ - U) := by
    have e : Γ * U.map σ - U = (Γ - 1) * U.map σ + (U.map σ - U) := by
      rw [Matrix.sub_mul, Matrix.one_mul]; abel
    rw [e]
    refine (MatIn.mul_right hΓ).add (fun i j => ?_)
    rw [Matrix.sub_apply, Matrix.map_apply]
    exact hσ (U i j)
  obtain ⟨K, hK'⟩ := hK.exists_smul
  refine ⟨(ev y + 1) • K + t • U + (π * t) • K, ?_⟩
  have e1 : σ (π ^ y) = (ev y + 1) * π ^ y + t * π ^ (y + 1) := by rw [ht]; ring
  have e2 : Γ * U.map σ = U + π • K := by rw [← hK']; abel
  rw [map_smul_ring, Matrix.mul_smul, e2, e1]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem frame_exists_of_eigenvalues {Γ : Matrix (Fin d) (Fin d) A}
    (hσ : ∀ a : A, σ a - a ∈ (Ideal.span {π} : Ideal A))
    (hΓ : MatIn (Ideal.span {π}) (Γ - 1))
    (hσπ : ∀ y : ℕ, σ (π ^ y) - (ev y + 1) * π ^ y ∈ (Ideal.span {π ^ (y + 1)} : Ideal A))
    (hσev : ∀ y : ℕ, σ (ev y) = ev y) (n : ℕ) (hn : 1 ≤ n) :
    ∃ H : Matrix (Fin d) (Fin d) A,
      MatIn (Ideal.span {π}) (H - (∏ y ∈ Finset.Ico 1 n, ev y) • (1 : Matrix (Fin d) (Fin d) A)) ∧
      MatIn (Ideal.span {π ^ n}) (Γ * H.map σ - H) := by
  induction n, hn using Nat.le_induction with
  | base =>
    refine ⟨1, ?_, ?_⟩
    · rw [Finset.Ico_self, Finset.prod_empty, one_smul, sub_self]
      exact MatIn.zero
    · rw [Matrix.map_one σ (map_zero σ) (map_one σ), Matrix.mul_one, pow_one]
      exact hΓ
  | succ n hn ih =>
    obtain ⟨H, h1, h2⟩ := ih
    obtain ⟨W, hW⟩ := h2.exists_smul
    obtain ⟨R, hR⟩ := mat_core hσ hΓ hσπ n W
    refine ⟨ev n • H - π ^ n • W, ?_, ?_⟩
    · rw [Finset.prod_Ico_succ_top hn]
      have e : ev n • H - π ^ n • W - ((∏ y ∈ Finset.Ico 1 n, ev y) * ev n) •
          (1 : Matrix (Fin d) (Fin d) A) =
          ev n • (H - (∏ y ∈ Finset.Ico 1 n, ev y) • (1 : Matrix (Fin d) (Fin d) A)) - π ^ n • W := by
        ext i j
        simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
        ring
      rw [e]
      exact (h1.smul _).sub ((MatIn.smul_self _ W).mono (span_pow_le π hn))
    · have hX : Γ * H.map σ = H + π ^ n • W := by rw [← hW]; abel
      have hY : Γ * (π ^ n • W).map σ = π ^ n • W + π ^ n • (ev n • W + π • R) := by
        rw [← hR]; abel
      have e : Γ * (ev n • H - π ^ n • W).map σ - (ev n • H - π ^ n • W) = π ^ (n + 1) • (-R) := by
        rw [map_sub_ring, map_smul_ring, hσev, Matrix.mul_sub, Matrix.mul_smul, hX, hY]
        ext i j
        simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply, smul_eq_mul]
        ring
      rw [e]
      exact MatIn.smul_self _ _

theorem frame_unique_of_eigenvalues {Γ : Matrix (Fin d) (Fin d) A}
    (hσ : ∀ a : A, σ a - a ∈ (Ideal.span {π} : Ideal A))
    (hΓ : MatIn (Ideal.span {π}) (Γ - 1)) (hπ : π ∈ nonZeroDivisors A)
    (hσπ : ∀ y : ℕ, σ (π ^ y) - (ev y + 1) * π ^ y ∈ (Ideal.span {π ^ (y + 1)} : Ideal A))
    (hnzd : ∀ (y : ℕ) (a : A), 1 ≤ y → ev y * a ∈ (Ideal.span {π} : Ideal A) →
      a ∈ (Ideal.span {π} : Ideal A))
    (M : ℕ) (hM : 1 ≤ M) (D : Matrix (Fin d) (Fin d) A) (h1 : MatIn (Ideal.span {π}) D)
    (h2 : MatIn (Ideal.span {π ^ M}) (Γ * D.map σ - D)) : MatIn (Ideal.span {π ^ M}) D := by
  suffices key : ∀ n, 1 ≤ n → n ≤ M → MatIn (Ideal.span {π ^ n}) D from key M hM le_rfl
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => intro _; rw [pow_one]; exact h1
  | succ n hn ih =>
    intro hle
    obtain ⟨U, hU⟩ := (ih (by omega)).exists_smul
    obtain ⟨R, hR⟩ := mat_core hσ hΓ hσπ n U
    have h2' : MatIn (Ideal.span {π ^ (n + 1)}) (π ^ n • (ev n • U + π • R)) := by
      rw [← hR, ← hU]; exact h2.mono (span_pow_mono π hle)
    intro i j
    have e1 := h2' i j
    simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul] at e1
    have e2 := cancel_pow hπ e1
    have e3 : ev n * U i j ∈ (Ideal.span {π} : Ideal A) := by
      have := Ideal.sub_mem _ e2 (Ideal.mul_mem_right (R i j) _ (Ideal.mem_span_singleton_self π))
      rwa [add_sub_cancel_right] at this
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp (hnzd n (U i j) hn e3)
    rw [hU, Matrix.smul_apply, smul_eq_mul, ← hs]
    exact Ideal.mem_span_singleton'.mpr ⟨s, by ring⟩

end Core

section Const

variable {O : Type*} [CommRing O] [Algebra O A] {σ : A →+* A} {Γ : Matrix (Fin d) (Fin d) A}
  {π : A} {ev : ℕ → A}

theorem invariants_const (h : Hyp O σ Γ π ev) (M : ℕ) (hM : 1 ≤ M) (a : A)
    (ha : σ a - a ∈ (Ideal.span {π ^ M} : Ideal A)) :
    ∃ o : O, a - algebraMap O A o ∈ (Ideal.span {π ^ M} : Ideal A) := by
  obtain ⟨o, ho⟩ := h.hdec a
  refine ⟨o, ?_⟩
  suffices key : ∀ n, 1 ≤ n → n ≤ M → a - algebraMap O A o ∈ (Ideal.span {π ^ n} : Ideal A) from
    key M hM le_rfl
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => intro _; rw [pow_one]; exact ho
  | succ n hn ih =>
    intro hle
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp (ih (by omega))
    obtain ⟨r, hr⟩ := scalar_core h.hσ h.hσπ n b
    have ea : a = algebraMap O A o + π ^ n * b := by linear_combination -hb
    have e : σ a - a = π ^ n * (ev n * b + π * r) := by
      rw [← hr, ea, map_add (f := _), h.hO]; ring
    have hin : π ^ n * (ev n * b + π * r) ∈ (Ideal.span {π ^ (n + 1)} : Ideal A) := by
      rw [← e]; exact span_pow_mono π hle ha
    have e2 := cancel_pow h.hπ hin
    have e3 : ev n * b ∈ (Ideal.span {π} : Ideal A) := by
      have := Ideal.sub_mem _ e2 (Ideal.mul_mem_right r _ (Ideal.mem_span_singleton_self π))
      rwa [add_sub_cancel_right] at this
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp (h.hnzd n b hn e3)
    exact Ideal.mem_span_singleton'.mpr ⟨s, by rw [← hb, ← hs]; ring⟩

theorem rigid (h : Hyp O σ Γ π ev) (M : ℕ) (hM : 1 ≤ M) (a : A) (o' : O)
    (ha : σ a - a ∈ (Ideal.span {π ^ M} : Ideal A))
    (hb : a - algebraMap O A o' ∈ (Ideal.span {π} : Ideal A)) :
    a - algebraMap O A o' ∈ (Ideal.span {π ^ M} : Ideal A) := by
  obtain ⟨o, ho⟩ := invariants_const h M hM a ha
  have hoo : o = o' := by
    apply sub_eq_zero.mp
    apply h.hinj
    have := Ideal.sub_mem _ hb (span_pow_le π hM ho)
    rwa [sub_sub_sub_cancel_left, ← map_sub] at this
  rw [← hoo]; exact ho

end Const

theorem mul_comm_of_mul_eq_smul {R : Type*} [CommRing R] {n : ℕ} (P Q : Matrix (Fin n) (Fin n) R)
    (c : R) (hc : c ∈ nonZeroDivisors R) (h : Q * P = c • (1 : Matrix (Fin n) (Fin n) R)) :
    P * Q = c • (1 : Matrix (Fin n) (Fin n) R) := by
  first | exact Bl.FirstLemmaB.goal1 .. | (apply Bl.FirstLemmaB.goal1 <;> assumption) | (intros; apply Bl.FirstLemmaB.goal1 <;> assumption) | (apply @Bl.FirstLemmaB.goal1 <;> assumption) | (intros; apply @Bl.FirstLemmaB.goal1 <;> assumption) | (apply @Bl.FirstLemmaB.goal1 <;> first | assumption | infer_instance) | exact @Bl.FirstLemmaB.goal1 R ‹_› n P Q c hc h | exact @Bl.FirstLemmaB.goal1 R ‹_› n P Q c hc | exact @Bl.FirstLemmaB.goal1 R ‹_› n P Q c | exact @Bl.FirstLemmaB.goal1 R ‹_› n P Q | exact @Bl.FirstLemmaB.goal1 R ‹_› n P | exact @Bl.FirstLemmaB.goal1 R ‹_› n | exact @Bl.FirstLemmaB.goal1 R ‹_› | exact @Bl.FirstLemmaB.goal1 R

theorem quot_sq_nzd {I : Ideal A} {c : A} (hc : ∀ a : A, c * a ∈ I → a ∈ I) :
    Ideal.Quotient.mk I (c ^ 2) ∈ nonZeroDivisors (A ⧸ I) := by
  have aux : ∀ x : A ⧸ I, x * Ideal.Quotient.mk I (c ^ 2) = 0 → x = 0 := by
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem] at hx
    rw [Ideal.Quotient.eq_zero_iff_mem]
    apply hc; apply hc
    convert hx using 1; ring
  exact mem_nonZeroDivisors_iff.mpr ⟨fun x hx => aux x (by rwa [mul_comm]), aux⟩

section Main

variable {O : Type*} [CommRing O] [Algebra O A] {σ : A →+* A} {Γ : Matrix (Fin d) (Fin d) A}
  {π : A} {ev : ℕ → A}

theorem prod_ev_mem (h : Hyp O σ Γ π ev) (M : ℕ) :
    ∃ o : O, (∏ y ∈ Finset.Ico 1 M, ev y) = algebraMap O A o := by
  choose f hf using h.hev
  exact ⟨∏ y ∈ Finset.Ico 1 M, f y, by
    rw [map_prod]; exact Finset.prod_congr rfl fun y _ => hf y⟩

theorem dual_frame_products (h : Hyp O σ Γ π ev) (M : ℕ) (hM : 1 ≤ M) (c : A)
    (hcO : ∃ o : O, c = algebraMap O A o) (H F : Matrix (Fin d) (Fin d) A)
    (hH : IsFrame σ Γ π c M H) (hF : IsDualFrame σ Γ π c M F)
    (hc : ∀ a : A, c * a ∈ (Ideal.span {π ^ M} : Ideal A) → a ∈ (Ideal.span {π ^ M} : Ideal A)) :
    MatIn (Ideal.span {π ^ M}) (F * H - c ^ 2 • (1 : Matrix (Fin d) (Fin d) A)) ∧
    MatIn (Ideal.span {π ^ M}) (H * F - c ^ 2 • (1 : Matrix (Fin d) (Fin d) A)) := by
  have hG1 : MatIn (Ideal.span {π ^ M}) ((F * H).map σ - F * H) := by
    have e : (F * H).map σ - F * H = -(F * Γ - F.map σ) * H.map σ + F * (Γ * H.map σ - H) := by
      rw [Matrix.map_mul, neg_sub]
      simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
      abel
    rw [e]
    exact (MatIn.mul_right hF.2.neg).add (MatIn.mul_left hH.2)
  have hG2 : MatIn (Ideal.span {π}) (F * H - c ^ 2 • (1 : Matrix (Fin d) (Fin d) A)) := by
    have e : F * H - c ^ 2 • (1 : Matrix (Fin d) (Fin d) A) =
        (F - c • (1 : Matrix (Fin d) (Fin d) A)) * H + c • (H - c • (1 : Matrix (Fin d) (Fin d) A)) := by
      simp only [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, smul_sub, smul_smul, pow_two]
      abel
    rw [e]
    exact (MatIn.mul_right hF.1).add (hH.1.smul c)
  obtain ⟨oc, hoc⟩ := hcO
  have hFH : MatIn (Ideal.span {π ^ M}) (F * H - c ^ 2 • (1 : Matrix (Fin d) (Fin d) A)) := by
    intro i j
    obtain ⟨o', ho'⟩ : ∃ o' : O, (c ^ 2 • (1 : Matrix (Fin d) (Fin d) A)) i j = algebraMap O A o' := by
      by_cases hij : i = j
      · refine ⟨oc ^ 2, ?_⟩
        subst hij
        rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, hoc, map_pow]
      · refine ⟨0, ?_⟩
        rw [Matrix.smul_apply, Matrix.one_apply_ne hij, smul_zero, map_zero]
    rw [Matrix.sub_apply, ho']
    apply rigid h M hM
    · have := hG1 i j
      rwa [Matrix.sub_apply, Matrix.map_apply] at this
    · rw [← ho', ← Matrix.sub_apply]
      exact hG2 i j
  refine ⟨hFH, ?_⟩
  have h1 := matIn_sub_iff.mp hFH
  apply matIn_sub_iff.mpr
  have hsm : (c ^ 2 • (1 : Matrix (Fin d) (Fin d) A)).map (Ideal.Quotient.mk (Ideal.span {π ^ M})) =
      Ideal.Quotient.mk (Ideal.span {π ^ M}) (c ^ 2) • (1 : Matrix (Fin d) (Fin d) _) := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  rw [Matrix.map_mul, hsm] at h1 ⊢
  exact mul_comm_of_mul_eq_smul _ _ _ (quot_sq_nzd hc) h1

theorem frame_products {O : Type*} [CommRing O] [Algebra O A] {σ : A →+* A}
    {Γ : Matrix (Fin d) (Fin d) A} {π : A} {ev : ℕ → A} (h : Hyp O σ Γ π ev) (M : ℕ) (hM : 1 ≤ M)
    (H F : Matrix (Fin d) (Fin d) A)
    (hH : IsFrame σ Γ π (∏ y ∈ Finset.Ico 1 M, ev y) M H)
    (hF : IsDualFrame σ Γ π (∏ y ∈ Finset.Ico 1 M, ev y) M F)
    (hc : ∀ a : A, (∏ y ∈ Finset.Ico 1 M, ev y) * a ∈ (Ideal.span {π ^ M} : Ideal A) →
      a ∈ (Ideal.span {π ^ M} : Ideal A)) :
    MatIn (Ideal.span {π ^ M}) (F * H - (∏ y ∈ Finset.Ico 1 M, ev y) ^ 2 • (1 : Matrix (Fin d) (Fin d) A)) ∧
    MatIn (Ideal.span {π ^ M}) (H * F - (∏ y ∈ Finset.Ico 1 M, ev y) ^ 2 • (1 : Matrix (Fin d) (Fin d) A)) :=
  dual_frame_products h M hM _ (prod_ev_mem h M) H F hH hF hc

theorem exists_frame {O : Type*} [CommRing O] [Algebra O A] {σ : A →+* A}
    {Γ : Matrix (Fin d) (Fin d) A} {π : A} {ev : ℕ → A} (h : Hyp O σ Γ π ev) (M : ℕ) (hM : 1 ≤ M) :
    (∃ H, IsFrame σ Γ π (∏ y ∈ Finset.Ico 1 M, ev y) M H) ∧
    (∀ H H', IsFrame σ Γ π (∏ y ∈ Finset.Ico 1 M, ev y) M H →
      IsFrame σ Γ π (∏ y ∈ Finset.Ico 1 M, ev y) M H' → MatIn (Ideal.span {π ^ M}) (H - H')) := by
  refine ⟨frame_exists_of_eigenvalues h.hσ h.hΓ h.hσπ h.hσev M hM, fun H H' hH hH' => ?_⟩
  apply frame_unique_of_eigenvalues h.hσ h.hΓ h.hπ h.hσπ h.hnzd M hM
  · have := hH.1.sub hH'.1
    rwa [sub_sub_sub_cancel_right] at this
  · have e : Γ * (H - H').map σ - (H - H') = (Γ * H.map σ - H) - (Γ * H'.map σ - H') := by
      rw [map_sub_ring, Matrix.mul_sub]; abel
    rw [e]
    exact hH.2.sub hH'.2

theorem exists_dualFrame {O : Type*} [CommRing O] [Algebra O A] {σ : A →+* A}
    {Γ : Matrix (Fin d) (Fin d) A} {π : A} {ev : ℕ → A} (h : Hyp O σ Γ π ev) (M : ℕ) (hM : 1 ≤ M) :
    ∃ F, IsDualFrame σ Γ π (∏ y ∈ Finset.Ico 1 M, ev y) M F := by
  have hinv : Γ⁻¹ * Γ = 1 := Matrix.nonsing_inv_mul Γ h.hΓunit
  have hΓ' : MatIn (Ideal.span {π}) ((Γ⁻¹)ᵀ - 1) := by
    have e : (Γ⁻¹)ᵀ - 1 = (Γ⁻¹ * (-(Γ - 1)))ᵀ := by
      rw [Matrix.mul_neg, Matrix.mul_sub, hinv, Matrix.mul_one, neg_sub, Matrix.transpose_sub,
        Matrix.transpose_one]
    rw [e]
    exact (MatIn.mul_left h.hΓ.neg).transpose
  obtain ⟨H', h1, h2⟩ := frame_exists_of_eigenvalues h.hσ hΓ' h.hσπ h.hσev M hM
  refine ⟨H'ᵀ, ?_, ?_⟩
  · have := h1.transpose
    rwa [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one] at this
  · have hΓΓ : Γᵀ * (Γ⁻¹)ᵀ = 1 := by
      rw [← Matrix.transpose_mul, hinv, Matrix.transpose_one]
    have key : (H'ᵀ * Γ - H'ᵀ.map σ)ᵀ = -(Γᵀ * ((Γ⁻¹)ᵀ * H'.map σ - H')) := by
      rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_transpose,
        Matrix.transpose_map, Matrix.transpose_transpose, Matrix.mul_sub, ← Matrix.mul_assoc, hΓΓ,
        Matrix.one_mul, neg_sub]
    have := ((MatIn.mul_left (X := Γᵀ) h2).neg).transpose
    rwa [← key, Matrix.transpose_transpose] at this

end Main

end DualFramesAlt.FrameAbs
end

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open PowerSeries DualFramesAlt.FrameAbs

variable {O : Type} [CommRing O] [IsDomain O] {d : ℕ}

theorem framepf_cc_subst (Fs g : PowerSeries O) :
    constantCoeff (subst ((X : PowerSeries O) * Fs) g) = constantCoeff g := by
  have h0 : PowerSeries.constantCoeff ((X : PowerSeries O) * Fs) = 0 := by simp
  have ha : PowerSeries.HasSubst ((X : PowerSeries O) * Fs) :=
    PowerSeries.HasSubst.of_constantCoeff_zero h0
  refine (PowerSeries.constantCoeff_subst (R := O) ha g).trans ?_
  rw [finsum_eq_single _ 0]
  · simp
  · intro n hn
    rw [map_pow]
    change coeff n g • (PowerSeries.constantCoeff ((X : PowerSeries O) * Fs)) ^ n = 0
    rw [h0, zero_pow hn, smul_zero]

theorem framepf_mem_span_X (a : PowerSeries O) :
    a ∈ Ideal.span {(X : PowerSeries O)} ↔ constantCoeff a = 0 := by
  rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff]

theorem framepf_mats (c₀ : O) (hc : ∀ y : ℕ, 1 ≤ y → c₀ ^ y ≠ 1) (Fs : PowerSeries O)
    (hF : constantCoeff Fs = c₀) (R : Matrix (Fin d) (Fin d) (PowerSeries O)) (M : ℕ) (hM : 1 ≤ M)
    (aσ lσ : O) (hl : lσ = aσ * ∏ y ∈ Finset.Ico 1 M, (c₀ ^ y - 1)) :
    ∃ H H' : Matrix (Fin d) (Fin d) (PowerSeries O),
      (∃ K, H = C lσ • 1 + (X : PowerSeries O) • K) ∧
      (∃ K, (1 + (X : PowerSeries O) • R) * H.map (subst ((X : PowerSeries O) * Fs)) - H =
        (X : PowerSeries O) ^ M • K) ∧
      (∃ K, H' = C lσ • 1 + (X : PowerSeries O) • K) ∧
      (∃ K, H' * (1 + (X : PowerSeries O) • R) - H'.map (subst ((X : PowerSeries O) * Fs)) =
        (X : PowerSeries O) ^ M • K) ∧
      (∃ K, H' * H = C (lσ ^ 2) • 1 + (X : PowerSeries O) ^ M • K) ∧
      (∃ K, H * H' = C (lσ ^ 2) • 1 + (X : PowerSeries O) ^ M • K) := by
  classical
  have hG : HasSubst ((X : PowerSeries O) * Fs) := HasSubst.of_constantCoeff_zero' (by simp)
  set σr : PowerSeries O →+* PowerSeries O := (substAlgHom hG).toRingHom with hσr
  have hσ : ∀ g, σr g = subst ((X : PowerSeries O) * Fs) g := fun g => by
    simp [σr, coe_substAlgHom]
  set Γ : Matrix (Fin d) (Fin d) (PowerSeries O) := 1 + (X : PowerSeries O) • R with hΓ
  set ev : ℕ → PowerSeries O := fun y => C (c₀ ^ y - 1) with hev
  have hAC : ∀ o : O, algebraMap O (PowerSeries O) o = C o := fun o => by
    rw [PowerSeries.algebraMap_apply]; rfl
  have hyp : Hyp O σr Γ X ev := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro a
      rw [framepf_mem_span_X, map_sub, hσ, framepf_cc_subst, sub_self]
    · rw [hΓ, add_sub_cancel_left]
      exact MatIn.smul_self _ _
    · rw [PowerSeries.isUnit_iff_constantCoeff, RingHom.map_det]
      have : (constantCoeff : PowerSeries O →+* O).mapMatrix Γ = 1 := by
        ext p q
        simp [hΓ, Matrix.one_apply]
      rw [this, Matrix.det_one]
      exact isUnit_one
    · exact mem_nonZeroDivisors_of_ne_zero X_ne_zero
    · intro y
      rw [hσ, subst_pow hG, subst_X hG, hev]
      rw [Ideal.mem_span_singleton]
      obtain ⟨t, ht⟩ := sub_dvd_pow_sub_pow Fs (C c₀) y
      have hX : (X : PowerSeries O) ∣ Fs - C c₀ := by
        rw [X_dvd_iff, map_sub, constantCoeff_C, hF, sub_self]
      obtain ⟨u, hu⟩ := hX
      refine ⟨u * t, ?_⟩
      have e : C (c₀ ^ y - 1) + 1 = (C c₀) ^ y := by simp
      rw [e, mul_pow, mul_comm ((C c₀) ^ y), ← mul_sub, ht, hu, pow_succ]
      ring
    · intro y
      rw [hσ, hev, subst_C]
      rfl
    · intro y a hy h
      rw [framepf_mem_span_X] at h ⊢
      rw [map_mul, constantCoeff_C] at h
      exact (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 (hc y hy))
    · intro o
      rw [hσ, ← PowerSeries.coe_substAlgHom hG, AlgHom.commutes]
    · intro a
      refine ⟨constantCoeff a, ?_⟩
      rw [framepf_mem_span_X, map_sub, hAC, constantCoeff_C, sub_self]
    · intro o h
      rw [framepf_mem_span_X, hAC, constantCoeff_C] at h
      exact h
    · intro y
      exact ⟨c₀ ^ y - 1, by rw [hAC]⟩
  have hD : ∏ y ∈ Finset.Ico 1 M, ev y = C (∏ y ∈ Finset.Ico 1 M, (c₀ ^ y - 1)) := by
    rw [hev, map_prod]
  have hc' : ∀ a : PowerSeries O, (∏ y ∈ Finset.Ico 1 M, ev y) * a ∈ Ideal.span {(X : PowerSeries O) ^ M} →
      a ∈ Ideal.span {(X : PowerSeries O) ^ M} := by
    intro a h
    rw [Ideal.mem_span_singleton, X_pow_dvd_iff] at h ⊢
    intro j hj
    have := h j hj
    rw [hD, coeff_C_mul] at this
    exact (mul_eq_zero.1 this).resolve_left
      (Finset.prod_ne_zero_iff.2 fun y hy => sub_ne_zero.2 (hc y (Finset.mem_Ico.1 hy).1))
  obtain ⟨⟨H, hH⟩, -⟩ := exists_frame hyp M hM
  obtain ⟨F, hF'⟩ := exists_dualFrame hyp M hM
  obtain ⟨hFH, hHF⟩ := frame_products hyp M hM H F hH hF' hc'
  have hmap : ∀ Z : Matrix (Fin d) (Fin d) (PowerSeries O), Z.map σr = Z.map (subst ((X : PowerSeries O) * Fs)) := by
    intro Z; ext p q; simp [hσ]
  obtain ⟨K1, hK1⟩ := hH.1.exists_smul
  obtain ⟨K2, hK2⟩ := hH.2.exists_smul
  obtain ⟨K3, hK3⟩ := hF'.1.exists_smul
  obtain ⟨K4, hK4⟩ := hF'.2.exists_smul
  obtain ⟨K5, hK5⟩ := hFH.exists_smul
  obtain ⟨K6, hK6⟩ := hHF.exists_smul
  have hσa : σr (C aσ) = C aσ := by rw [hσ, subst_C]; rfl
  rw [hD] at hK1 hK3 hK5 hK6
  have e1 := (sub_eq_iff_eq_add.1 hK1).trans (add_comm _ _)
  have e3 := (sub_eq_iff_eq_add.1 hK3).trans (add_comm _ _)
  have e5 := (sub_eq_iff_eq_add.1 hK5).trans (add_comm _ _)
  have e6 := (sub_eq_iff_eq_add.1 hK6).trans (add_comm _ _)
  have hsc : ∀ Z : Matrix (Fin d) (Fin d) (PowerSeries O), (C aσ • Z).map σr = C aσ • Z.map σr := by
    intro Z; ext p q; simp [hσa]
  have hsq : C aσ * C aσ * C (∏ y ∈ Finset.Ico 1 M, (c₀ ^ y - 1)) ^ 2 = C (lσ ^ 2) := by
    rw [hl, ← map_mul, ← map_pow, ← map_mul]; ring_nf
  refine ⟨C aσ • H, C aσ • F, ⟨C aσ • K1, ?_⟩, ⟨C aσ • K2, ?_⟩, ⟨C aσ • K3, ?_⟩, ⟨C aσ • K4, ?_⟩,
    ⟨(C aσ * C aσ) • K5, ?_⟩, ⟨(C aσ * C aσ) • K6, ?_⟩⟩
  · rw [e1, smul_add, smul_smul, ← map_mul, ← hl, smul_comm (C aσ) (X : PowerSeries O) K1]
  · rw [← hmap, hsc, Matrix.mul_smul, ← smul_sub, hK2, smul_comm]
  · rw [e3, smul_add, smul_smul, ← map_mul, ← hl, smul_comm (C aσ) (X : PowerSeries O) K3]
  · rw [← hmap, hsc, Matrix.smul_mul, ← smul_sub, hK4, smul_comm]
  · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, e5, smul_add, smul_smul, smul_comm _ _ K5, hsq]
  · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, e6, smul_add, smul_smul, smul_comm _ _ K6, hsq]

end Formalism.MainNotions.N.Ln34

end
end

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n}
    {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O] [Algebra Zl Ai]
    {RW : Type} [CommRing RW] [Algebra O RW]
    {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai}
    {E : EtTie W (O ⊗[Zl] Ai) RW inclR φR gR πA} {ιdR : Ai →+* BdR} {p1 : Ai} {tS zS : BdR}
    (Ct : CmpTie W E ιdR p1 tS zS) (T : LocLat G Qp LL O)

def FramepfBack {T : LocLat G Qp LL O} (Bs : FramepfBas W T) (π' : LetA O n) (c : ZMod n)
    (hπ0 : ∀ j, PowerSeries.constantCoeff (π' j) = 0)
    (hΔπ : ∀ δ ∈ W.DelF, W.γA δ π' = π')
    (hR2 : ∀ a : LetA O n, a ∈ W.AΔ → ∃! f : ZMod n → PowerSeries O,
      ∀ j, a j = PowerSeries.subst (π' j) (f j))
    (γ0 : ∀ δ ∈ W.DelF, PowerSeries.constantCoeff (W.γ₀ δ PowerSeries.X) = 0)
    (hu : IsUnit (algebraMap (LetA O n) W.EE π')) (Eπ : LetA O n) (h' M : ℕ) : Prop :=
  ∀ (H H' K₁ K₂ : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) (lam : O),
    H' * H = PowerSeries.C lam • (1 : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) +
      (PowerSeries.X : PowerSeries O) ^ M • K₁ →
    H * H' = PowerSeries.C lam • (1 : Matrix (Fin Bs.r) (Fin Bs.r) (PowerSeries O)) +
      (PowerSeries.X : PowerSeries O) ^ M • K₂ →
    ∃ Φ : W.DD T →ₗ[W.EE] W.EE ⊗[O] LcQ W T π' c,
      (∀ y ∈ LamPS W T Eπ h' c, Φ y ∈ LamLA W T π' Eπ h' c ⊤) ∧
      (∀ y ∈ JP W T π' Eπ h' M c, Φ y ∈ JLA W T π' Eπ h' M c) ∧
      (∀ x ∈ LamLA W T π' Eπ h' c ⊤,
        Φ (framepf_Ψα Bs π' c hπ0 hΔπ hR2 γ0 hu H x) - lam • x ∈ JLA W T π' Eπ h' M c) ∧
      ∀ y ∈ LamPS W T Eπ h' c,
        framepf_Ψα Bs π' c hπ0 hΔπ hR2 γ0 hu H (Φ y) - lam • y ∈ JP W T π' Eπ h' M c


include Ct in
set_option maxHeartbeats 1000000 in
theorem framepf_data [IsDomain O] (hι : Function.Injective (algebraMap O LL)) (hT : IsCrys PD T.ρ)
    (hs : W.s = 1) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (c : ZMod n)
    (hprim : ∀ τ ζ, Pt c ζ τ → IsPrimitiveRoot ζ PD.p) (h4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T)
    {e s' : ℕ} {π' : LetA O n} {Ep : ZMod n → Polynomial O} (hR : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W e s' π' Ep)
    (hs' : 1 ≤ s') (h' M σ : ℕ) (hM1 : 1 ≤ M) (hM : 4 * h' ≤ s' * M) (hK : W.gamK = W.gam)
    (Bs : FramepfBas W T) (hπ0 : ∀ j, PowerSeries.constantCoeff (π' j) = 0)
    (hΔπ : ∀ δ ∈ W.DelF, W.γA δ π' = π')
    (hR2 : ∀ a : LetA O n, a ∈ W.AΔ → ∃! f : ZMod n → PowerSeries O,
      ∀ j, a j = PowerSeries.subst (π' j) (f j))
    (γ0 : ∀ δ ∈ W.DelF, PowerSeries.constantCoeff (W.γ₀ δ PowerSeries.X) = 0)
    (hu : IsUnit (algebraMap (LetA O n) W.EE π'))
    (hγN : ∀ y ∈ W.NΔ T, ∃ d ∈ W.N T, W.γD T W.gam y - y = π' • d)
    (Fs : PowerSeries O)
    (hFs : W.γ₀ W.gam (π' (c - 1)) = PowerSeries.subst (π' (c - 1)) (PowerSeries.X * Fs))
    (hF0 : PowerSeries.constantCoeff Fs = ((W.χΓ W.gam : Oˣ) : O) ^ s')
    (hne : ∀ y : ℕ, 1 ≤ y → (((W.χΓ W.gam : Oˣ) : O) ^ s') ^ y ≠ 1) (aσ : O)
    (haσ : ((PD.p : ℕ) : O) ^ σ = aσ * ∏ y ∈ Finset.Ico 1 M, ((((W.χΓ W.gam : Oˣ) : O) ^ s') ^ y - 1))
    (hB : FramepfBack Bs π' c hπ0 hΔπ hR2 γ0 hu (Formalism.MainNotions.DeltaInvariantLattices.Eat Ep π') h' M) :
    ∃ (hh : LcQ W T π' c →ₗ[O] W.DD T)
      (Ψ : W.EE ⊗[O] LcQ W T π' c →ₗ[W.EE] W.DD T) (Φ : W.DD T →ₗ[W.EE] W.EE ⊗[O] LcQ W T π' c),
      (∀ x ∈ LamLA W T π' (Formalism.MainNotions.DeltaInvariantLattices.Eat Ep π') h' c ⊤, Ψ x ∈ LamPS W T (Formalism.MainNotions.DeltaInvariantLattices.Eat Ep π') h' c) ∧
      (∀ y ∈ LamPS W T (Formalism.MainNotions.DeltaInvariantLattices.Eat Ep π') h' c, Φ y ∈ LamLA W T π' (Formalism.MainNotions.DeltaInvariantLattices.Eat Ep π') h' c ⊤) ∧
      FramepfData W Pt π' (Formalism.MainNotions.DeltaInvariantLattices.Eat Ep π') h' M σ c T hh Ψ Φ := by
  have huE := framepf_E_unit hR hs
  have hEΔ := framepf_E_Δ hR
  obtain ⟨Γ, hΓ, R, hΓR⟩ := framepf_Γ Bs π' (c - 1) hπ0 hΔπ hR2 hu hγN
  obtain ⟨H, H', ⟨K1, hK1⟩, ⟨K2, hK2⟩, -, -, ⟨K5, hK5⟩, ⟨K6, hK6⟩⟩ :=
    framepf_mats _ hne Fs hF0 R M hM1 aσ _ haσ
  rw [← pow_mul, mul_comm σ 2] at hK5 hK6
  obtain ⟨Φ, hΦL, hΦJ, hβα, hαβ⟩ := hB H H' K5 K6 _ hK5 hK6
  have hγ := framepf_hhx_γ Bs π' c hπ0 hΔπ hR2 γ0 hu (PowerSeries.X * Fs) (by simp) hFs Γ hΓ H K2 M
    (by rw [hΓR]; exact hK2)
  have hmod := framepf_hhx_mod Bs π' c hπ0 hΔπ hR2 γ0 hu _ H K1 hK1
  have hp0 : ((PD.p : ℕ) : O) ≠ 0 := by
    intro h
    have h1 := congrArg (algebraMap O LL) h
    rw [map_natCast, map_zero] at h1
    have := W.v_l
    rw [h1, AddValuation.map_zero] at this
    exact absurd this (by simp)
  obtain ⟨w, hw⟩ := hR.2.2.1
  obtain ⟨w', hw'⟩ := hR.2.2.2.2.1
  refine ⟨_, framepf_Ψα Bs π' c hπ0 hΔπ hR2 γ0 hu H, Φ,
    framepf_Ψα_Lam Bs π' c hπ0 hΔπ hR2 γ0 hu _ huE hEΔ h' H, hΦL, hγ, hmod,
    framepf_Ψα_tmul Bs π' c hπ0 hΔπ hR2 γ0 hu H, framepf_Ψα_J Bs π' c hπ0 hΔπ hR2 γ0 hu _ h' M H,
    hΦJ, hβα, hαβ, fun x hx hj => ?_, fun x hx hgx => ?_, fun τ ζ hpt x y hxy m a z hrep k hk i hi => ?_⟩
  · exact framepf_JLA_sat π' c (framepf_Lbas Bs π' c hπ0 hΔπ hR2 γ0 hu) _ h' M hu huE
      (fun o ho => (mul_eq_zero.1 ho).resolve_left hp0) _ x hx hj
  · obtain ⟨f, hfΔ, hf⟩ := framepf_γπ hR
    obtain ⟨Ff, hFf, -⟩ := hR2 f hfΔ
    obtain ⟨t, ht⟩ := gradNPf_expand π' f hπ0 Ff hFf _ (gradNPf_cc_f W s' w π' f hw hf)
    refine invLiftPf_inj W T π' f t _ hf ht hu hΔπ hγN hK M (fun y hy _ r₀ hr₀ d hd hrd => ?_) x hx
      (by rw [hK]; exact hgx)
    exact invLiftPf_nzd W T π' w s' w.isUnit hw _
      (fun o ho => (mul_eq_zero.1 ho).resolve_left (sub_ne_zero.2 (hne y hy))) Bs.r Bs.b
      (fun j => (Bs.mem j).1) Bs.uniq 1 r₀ d hr₀ hd (by rw [pow_one]; exact hrd)
  · refine framepf_locC Ct T hT hs c ζ (hprim τ ζ hpt) (fun x k hk => ?_) ?_ (fun r hr h => ?_)
      π' _ w w' s' h' M σ hs' hw w'.isUnit hw' hM _
      (fun ℓ => ((mem_NcS W T (c - 1) _).1 (framepf_hhx_mem Bs π' c hπ0 hΔπ hR2 γ0 hu H ℓ)).1) hγ hmod
      _ (framepf_Ψα_tmul Bs π' c hπ0 hΔπ hR2 γ0 hu H) x y hxy m a z hrep k hk i hi
    · exact ((h4.1 (c - 1) 1 ⟨0, one_pow _⟩
        (by rw [Formalism.MainNotions.LiftingTheory.wmap_X_one W hs]; exact framepf_lev_π_one _)).1 x k).2 hk
    · rw [W.gam_gen]
      rw [hs, Nat.cast_one]
      exact zero_le_one
    · obtain ⟨y, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ r by omega)
      rw [zpow_natCast, ← map_pow, ← map_one (algebraMap O LL)] at h
      apply hne y (by omega)
      rw [← pow_mul, mul_comm, pow_mul, hι h, one_pow]

end Local

end Formalism.MainNotions.N.Ln34

end
end

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules TensorProduct

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n}
    {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O] [Algebra Zl Ai]
    {RW : Type} [CommRing RW] [Algebra O RW]
    {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai}
    {E : EtTie W (O ⊗[Zl] Ai) RW inclR φR gR πA} {ιdR : Ai →+* BdR} {p1 : Ai} {tS zS : BdR}
    (Ct : CmpTie W E ιdR p1 tS zS) (T : LocLat G Qp LL O)


include Ct in
theorem framepf_data' [IsDomain O] (hι : Function.Injective (algebraMap O LL)) (hT : IsCrys PD T.ρ)
    (hs : W.s = 1) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (c : ZMod n)
    (hprim : ∀ τ ζ, Pt c ζ τ → IsPrimitiveRoot ζ PD.p) (h4 : Formalism.MainNotions.DeltaInvariantLattices.p4 W Pt T)
    {e s' : ℕ} {π' : LetA O n} {Ep : ZMod n → Polynomial O} (hR : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W e s' π' Ep)
    (hs' : 1 ≤ s') (h' M σ : ℕ) (hM1 : 1 ≤ M) (hM : 4 * h' ≤ s' * M) (l : ℕ) (hl : PD.p = l)
    (hyp : Nonempty (FramepfBas W T) ∧ (∀ j, PowerSeries.constantCoeff (π' j) = 0) ∧
      (∀ δ ∈ W.DelF, W.γA δ π' = π') ∧
      (∀ a ∈ W.AΔ, ∃! f : ZMod n → PowerSeries O, ∀ j, a j = PowerSeries.subst (π' j) (f j)) ∧
      (∀ δ ∈ W.DelF, PowerSeries.constantCoeff (W.γ₀ δ PowerSeries.X) = 0) ∧
      IsUnit (algebraMap (LetA O n) W.EE π') ∧
      (∀ y ∈ W.NΔ T, ∃ d ∈ W.N T, W.γD T W.gam y - y = π' • d) ∧ W.gamK = W.gam ∧
      ∃ Fs : PowerSeries O,
        W.γ₀ W.gam (π' (c - 1)) = PowerSeries.subst (π' (c - 1)) (PowerSeries.X * Fs) ∧
        PowerSeries.constantCoeff Fs = ((W.χΓ W.gam : Oˣ) : O) ^ s' ∧
        (∀ y : ℕ, 1 ≤ y → (((W.χΓ W.gam : Oˣ) : O) ^ s') ^ y ≠ 1) ∧
        ∃ aσ : O, (l : O) ^ σ = aσ * ∏ y ∈ Finset.Ico 1 M, ((((W.χΓ W.gam : Oˣ) : O) ^ s') ^ y - 1))
    (hB : ∀ (Bs : FramepfBas W T) hπ0 hΔπ hR2 γ0 hu,
      FramepfBack Bs π' c hπ0 hΔπ hR2 γ0 hu (Formalism.MainNotions.DeltaInvariantLattices.Eat Ep π') h' M) :
    ∃ (hh : LcQ W T π' c →ₗ[O] W.DD T)
      (Ψ : W.EE ⊗[O] LcQ W T π' c →ₗ[W.EE] W.DD T) (Φ : W.DD T →ₗ[W.EE] W.EE ⊗[O] LcQ W T π' c),
      (∀ x ∈ LamLA W T π' (Formalism.MainNotions.DeltaInvariantLattices.Eat Ep π') h' c ⊤, Ψ x ∈ LamPS W T (Formalism.MainNotions.DeltaInvariantLattices.Eat Ep π') h' c) ∧
      (∀ y ∈ LamPS W T (Formalism.MainNotions.DeltaInvariantLattices.Eat Ep π') h' c, Φ y ∈ LamLA W T π' (Formalism.MainNotions.DeltaInvariantLattices.Eat Ep π') h' c ⊤) ∧
      FramepfData W Pt π' (Formalism.MainNotions.DeltaInvariantLattices.Eat Ep π') h' M σ c T hh Ψ Φ := by
  obtain ⟨⟨Bs⟩, hπ0, hΔπ, hR2, γ0, hu, hγN, hK, Fs, hFs, hF0, hne, aσ, haσ⟩ := hyp
  exact framepf_data Ct T hι hT hs Pt c hprim h4 hR hs' h' M σ hM1 hM hK
    Bs hπ0 hΔπ hR2 γ0 hu hγN Fs hFs hF0 hne aσ (by rw [hl]; exact haσ) (hB Bs hπ0 hΔπ hR2 γ0 hu)

end Local


set_option maxHeartbeats 1000000 in
theorem framepf_rec (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (h1 : adm1 D HW F Cm) (l : ℕ) [Fact l.Prime] (hl : l ≠ 2)
    (K LL : FinExt l) (hG : Good K 1 LL) (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K)))
    (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL))
    (hR : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E) (h' : ℕ) (hh' : 1 ≤ h')
    (c : ZMod (finrank ℚ_[l] ↥(K0 K)))
    (hB : ∀ (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys ((D.loc l).PD K) T.ρ →
      ∀ (Bs : FramepfBas ((HW l).W K 1 LL hG) T) hπ0 hΔπ hR2 γ0 hu,
        IsUnit (algebraMap _ ((HW l).W K 1 LL hG).EE (Formalism.MainNotions.DeltaInvariantLattices.Eat E π')) →
        Formalism.MainNotions.DeltaInvariantLattices.Eat E π' ∈ ((HW l).W K 1 LL hG).AΔ → ∀ u ∈ ((HW l).W K 1 LL hG).AΔ,
        ((HW l).W K 1 LL hG).φA π' ^ MK l K h' = π' ^ MK l K h' * Formalism.MainNotions.DeltaInvariantLattices.Eat E π' ^ (4 * h') * u →
        FramepfBack Bs π' c hπ0 hΔπ hR2 γ0 hu (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' (MK l K h')) :
    FrameA ((HW l).W K 1 LL hG) (Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG) π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' (MK l K h')
      (sigA l (sK l K) h') c := by
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have hp2 : ((D.loc l).PD K).p ≠ 2 := by rw [hpl]; exact hl
  have hs : ((HW l).W K 1 LL hG).s = 1 := (HW l).W_s K 1 LL hG
  have hK : ((HW l).W K 1 LL hG).gamK = ((HW l).W K 1 LL hG).gam := ((HW l).W K 1 LL hG).gamK_eq_one hs hp2
  have hs' := ramification_quotient_pos l hl K LL hG
  have hM : 4 * h' ≤ sK l K * MK l K h' := by
    have hsR : (0 : ℝ) < (sK l K : ℝ) := by exact_mod_cast hs'
    have hc : (4 * h' : ℝ) / (sK l K : ℝ) ≤ (MK l K h' : ℝ) := Nat.le_ceil _
    rw [div_le_iff₀ hsR] at hc
    have h4 : ((4 * h' : ℕ) : ℝ) ≤ ((sK l K * MK l K h' : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast h4
  have hM1 : 1 ≤ MK l K h' := by
    rcases Nat.eq_zero_or_pos (MK l K h') with h0 | h0
    · rw [h0, mul_zero] at hM
      omega
    · exact h0
  have hprim : ∀ τ ζ, Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hG c ζ τ → IsPrimitiveRoot ζ ((D.loc l).PD K).p := by
    intro τ ζ hpt
    rw [hpl]
    exact framepf_pt_prim D HW hG c ζ τ hpt
  have hι : Function.Injective (algebraMap ↥(OL LL) ↥LL.1) := Subtype.val_injective
  obtain ⟨u, huΔ, hφ⟩ := framepf_φπ hR hs h' _ hM
  obtain ⟨f, hfΔ, hf⟩ := framepf_γπ hR
  obtain ⟨t, htΔ, ht⟩ := framepf_γE hR hs ((HW l).W K 1 LL hG).gamK
  obtain ⟨t', ht'Δ, ht'⟩ := framepf_γE' hR hs ((HW l).W K 1 LL hG).gamK
  have huE := framepf_E_unit hR hs
  refine framepf_frameA _ _ π' _ h' _ _ c hK (framepf_π_unit hR) huE hR.1 u huΔ hφ hfΔ
    (by rw [hK]; exact hf) htΔ ht ht'Δ ht' fun T hT => ?_
  exact framepf_data' ((Cm l).C K 1 LL hG).tie T hι hT hs _ c hprim ((h1 l K 1 LL hG).2.2.2.1 T hT) hR
    hs' h' _ _ hM1 hM l hpl (framepf_hyps D HW F Cm h1 l hl K LL hG π' E hR T hT c h')
    fun Bs hπ0 hΔπ hR2 γ0 hu => hB T hT Bs hπ0 hΔπ hR2 γ0 hu huE (framepf_E_Δ hR) u huΔ hφ

end Formalism.MainNotions.N.Ln34

end
