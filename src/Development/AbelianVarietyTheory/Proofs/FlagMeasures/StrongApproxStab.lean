module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegerAddStarEqOneOfIsCMUnram
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianStabiliserRationalUnitriangularPairs
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameMatrixCloseGivesLatticeCloseIntegral

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BlockUnitriangularRationalFromCommonStabiliser
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BlockUnitriangularRationalFromCommonStabiliser
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.RatPat

noncomputable def rhoL {R : Type} [CommRing R] : List (Rˣ × ℕ+) → ℕ → ℕ
  | [], a => a
  | (_, s) :: bs, a => if a < (s : ℕ) then (s : ℕ) - 1 - a else (s : ℕ) + rhoL bs (a - s)

theorem sum_cons' {R : Type} [CommRing R] (t : Rˣ) (s : ℕ+) (bs : List (Rˣ × ℕ+)) :
    (((t, s) :: bs).map (fun b => (b.2 : ℕ))).sum = (s : ℕ) + (bs.map (fun b => (b.2 : ℕ))).sum := by
  simp

theorem rhoL_lt {R : Type} [CommRing R] (bs : List (Rˣ × ℕ+)) (a : ℕ)
    (ha : a < (bs.map (fun b => (b.2 : ℕ))).sum) : rhoL bs a < (bs.map (fun b => (b.2 : ℕ))).sum := by
  induction bs generalizing a with
  | nil => simp at ha
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    rw [sum_cons'] at ha ⊢
    simp only [rhoL]
    split_ifs with h
    · omega
    · have := ih (a - s) (by omega); omega

theorem rhoL_rhoL {R : Type} [CommRing R] (bs : List (Rˣ × ℕ+)) (a : ℕ)
    (ha : a < (bs.map (fun b => (b.2 : ℕ))).sum) : rhoL bs (rhoL bs a) = a := by
  induction bs generalizing a with
  | nil => rfl
  | cons b bs ih =>
    obtain ⟨t, s⟩ := b
    rw [sum_cons'] at ha
    by_cases h : a < (s : ℕ)
    · have e : rhoL ((t, s) :: bs) a = (s : ℕ) - 1 - a := by simp [rhoL, h]
      rw [e]; simp only [rhoL]; rw [if_pos (by omega)]; omega
    · have e : rhoL ((t, s) :: bs) a = (s : ℕ) + rhoL bs (a - s) := by simp [rhoL, h]
      rw [e]; simp only [rhoL]
      rw [if_neg (by omega), Nat.add_sub_cancel_left, ih (a - s) (by omega)]; omega

theorem entry_ne_zero_iff {R : Type} [CommRing R] [Nontrivial R] (bs : List (Rˣ × ℕ+)) (a b : ℕ)
    (ha : a < (bs.map (fun b => (b.2 : ℕ))).sum) :
    ptEntryL bs a b ≠ 0 ↔ b = rhoL bs a := by
  induction bs generalizing a b with
  | nil => simp at ha
  | cons c bs ih =>
    obtain ⟨t, s⟩ := c
    rw [sum_cons'] at ha
    simp only [ptEntryL, rhoL]
    by_cases h1 : a < (s : ℕ)
    · rw [if_pos h1]
      by_cases h2 : b < (s : ℕ)
      · rw [if_pos ⟨h1, h2⟩]
        split_ifs with h3
        · simp only [ne_eq, Units.ne_zero, not_false_eq_true, true_iff]; omega
        · simp only [ne_eq, not_true_eq_false, false_iff]; omega
      · rw [if_neg (fun h => h2 h.2), if_neg (fun h => by omega)]
        simp only [ne_eq, not_true_eq_false, false_iff]; omega
    · rw [if_neg h1, if_neg (fun h => h1 h.1)]
      by_cases h2 : (s : ℕ) ≤ b
      · rw [if_pos ⟨by omega, h2⟩, ih (a - s) (b - s) (by omega)]
        omega
      · rw [if_neg (fun h => h2 h.2)]
        simp only [ne_eq, not_true_eq_false, false_iff]; omega

theorem rhoL_rev {R : Type} [CommRing R] (bs : List (Rˣ × ℕ+)) (x y : ℕ) (hxy : x < y)
    (hy : y < (bs.map (fun b => (b.2 : ℕ))).sum)
    (hB : ∀ l : ℕ, x < l → l ≤ y → ¬ ∀ a, a < l → rhoL bs a < l) : rhoL bs y < rhoL bs x := by
  induction bs generalizing x y with
  | nil => simp at hy
  | cons c bs ih =>
    obtain ⟨t, s⟩ := c
    rw [sum_cons'] at hy
    simp only [rhoL] at hB ⊢
    by_cases h1 : y < (s : ℕ)
    · rw [if_pos h1, if_pos (by omega)]; omega
    · by_cases h2 : x < (s : ℕ)
      · exfalso
        refine hB s h2 (by omega) fun a ha => ?_
        rw [if_pos ha]; omega
      · rw [if_neg h1, if_neg h2]
        have := ih (x - s) (y - s) (by omega) (by omega) fun l hl1 hl2 hcl => by
          refine hB (s + l) (by omega) (by omega) fun a ha => ?_
          by_cases h : a < (s : ℕ)
          · rw [if_pos h]; omega
          · rw [if_neg h]; have := hcl (a - s) (by omega); omega
        omega

theorem pt_shape {R : Type} [CommRing R] [Nontrivial R] {n : ℕ} (w : Pt R n) :
    ∃ ρ : Fin n → Fin n, Function.Involutive ρ ∧ (∀ a b, w.mat a b ≠ 0 ↔ b = ρ a) ∧
      ∀ x y : Fin n, x < y → (∀ l : ℕ, (x : ℕ) < l → l ≤ (y : ℕ) →
        ¬ ∀ a : Fin n, (a : ℕ) < l → ((ρ a : Fin n) : ℕ) < l) → ρ y < ρ x := by
  have hn : ∀ a : Fin n, (a : ℕ) < (w.blocks.map (fun b => (b.2 : ℕ))).sum := fun a => by rw [w.size]; exact a.2
  let ρ : Fin n → Fin n := fun a => ⟨rhoL w.blocks a, by have := rhoL_lt _ _ (hn a); rwa [w.size] at this⟩
  refine ⟨ρ, fun a => Fin.ext (rhoL_rhoL _ _ (hn a)), fun a b => ?_, fun x y hxy hB => ?_⟩
  · show ptEntryL w.blocks a b ≠ 0 ↔ b = ρ a
    rw [entry_ne_zero_iff _ _ _ (hn a), Fin.ext_iff]
  · show rhoL w.blocks y < rhoL w.blocks x
    refine rhoL_rev _ _ _ hxy (hn y) fun l h1 h2 hcl => hB l h1 h2 fun a ha => hcl a ha

end GlobalTheory.HL.RatPat

namespace GlobalTheory.HL.RatPat

theorem det_ne_zero_of_monomial {K : Type} [Field K] {m : ℕ} (M : Matrix (Fin m) (Fin m) K)
    (σ : Equiv.Perm (Fin m)) (hM : ∀ a b, M a b ≠ 0 ↔ b = σ a) : M.det ≠ 0 := by
  rw [Matrix.det_apply, Finset.sum_eq_single σ⁻¹]
  · have hp : ∏ i, M ((σ⁻¹ : Equiv.Perm (Fin m)) i) i ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro i _
      rw [hM]
      simp
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ⁻¹) with h | h <;> rw [h] <;> simpa using hp
  · intro τ _ hτ
    have : ∃ i, σ (τ i) ≠ i := by
      by_contra h
      push_neg at h
      apply hτ
      refine Equiv.ext fun i => ?_
      show τ i = σ⁻¹ i
      rw [Equiv.Perm.eq_inv_iff_eq]
      exact h i
    obtain ⟨i, hi⟩ := this
    rw [Finset.prod_eq_zero (Finset.mem_univ i), smul_zero]
    by_contra h
    exact hi ((hM _ _).1 h).symm
  · simp

theorem exists_upper {K : Type} [Field K] {n : ℕ} (Z u : Matrix (Fin n) (Fin n) K) (ρ : Fin n → Fin n)
    (B : Fin n → Fin n → Prop) (hρ : Function.Involutive ρ) (hZ : ∀ a b, Z a b ≠ 0 ↔ b = ρ a)
    (hB : ∀ x y, x < y → B x y → ρ y < ρ x) (hu1 : ∀ a, u a a = 1)
    (hu0 : ∀ a b, a ≠ b → ¬ (b < a ∧ B b a) → u a b = 0) :
    ∃ s : Matrix (Fin n) (Fin n) K, ((∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1)) ∧ u * Z * s = Z := by
  have hZd : ∀ a, Z a (ρ a) ≠ 0 := fun a => (hZ a _).2 rfl
  have hZd' : ∀ b, Z (ρ b) b ≠ 0 := fun b => (hZ _ _).2 (hρ b).symm
  let M : Matrix (Fin n) (Fin n) K := fun a b => u (ρ a) (ρ b) * Z (ρ b) b / Z (ρ a) a
  have hMup : M.BlockTriangular id := by
    intro i j hij
    simp only [id] at hij
    show u (ρ i) (ρ j) * Z (ρ j) j / Z (ρ i) i = 0
    rw [hu0 (ρ i) (ρ j) (fun h => (ne_of_gt hij) (hρ.injective h)) ?_]
    · simp
    · rintro ⟨h1, h2⟩
      have := hB _ _ h1 h2
      rw [hρ, hρ] at this
      exact absurd hij (not_lt.2 this.le)
  have hMd : ∀ i, M i i = 1 := by
    intro i
    show u (ρ i) (ρ i) * Z (ρ i) i / Z (ρ i) i = 1
    rw [hu1, one_mul, div_self (hZd' i)]
  have hdet : M.det = 1 := by
    rw [Matrix.det_of_upperTriangular hMup]
    simp [hMd]
  have hZM : Z * M = u * Z := by
    ext a b
    rw [Matrix.mul_apply, Matrix.mul_apply, Finset.sum_eq_single (ρ a), Finset.sum_eq_single (ρ b)]
    · show Z a (ρ a) * (u (ρ (ρ a)) (ρ b) * Z (ρ b) b / Z (ρ (ρ a)) (ρ a)) = u a (ρ b) * Z (ρ b) b
      rw [hρ a]
      field_simp [hZd a]
    · intro c _ hc
      have : Z c b = 0 := by
        by_contra h
        apply hc
        rw [(hZ c b).1 h, hρ]
      rw [this, mul_zero]
    · simp
    · intro c _ hc
      have : Z a c = 0 := by
        by_contra h
        exact hc ((hZ a c).1 h)
      rw [this, zero_mul]
    · simp
  haveI : Invertible M := Matrix.invertibleOfIsUnitDet M (by rw [hdet]; exact isUnit_one)
  refine ⟨M⁻¹, ⟨fun i j hij => Matrix.blockTriangular_inv_of_blockTriangular hMup hij, fun i => ?_⟩, ?_⟩
  · have h1 : (M⁻¹ * M) i i = 1 := by rw [Matrix.inv_mul_of_invertible]; simp
    rw [Matrix.mul_apply, Finset.sum_eq_single i] at h1
    · rwa [hMd, mul_one] at h1
    · intro c _ hc
      rcases lt_or_gt_of_ne hc with h | h
      · rw [Matrix.blockTriangular_inv_of_blockTriangular hMup h, zero_mul]
      · rw [hMup h, mul_zero]
    · simp
  · rw [← hZM, Matrix.mul_assoc, Matrix.mul_inv_of_invertible, Matrix.mul_one]

end GlobalTheory.HL.RatPat

namespace GlobalTheory.HL.RatPat

theorem hf_smul {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (α β : F) (x y : Fin n → E) :
    hf L Hm (algebraMap F E α • x) (algebraMap F E β • y) =
      algebraMap F E α * algebraMap F E β * hf L Hm x y := by
  unfold hf
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, AlgEquiv.commutes, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem nonempty_places (F : Type) [Field F] [NumberField F] : Nonempty (HeightOneSpectrum (𝓞 F)) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 F)
  exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField F)⟩⟩

theorem main : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
    (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), ∀ t : Matrix (Fin (r + 1)) (Fin (r + 1)) E,
    (∀ i j, ¬ (i < j ∧ ∀ l : Fin (r + 2), ((i : Fin (r + 1)) : ℕ) < l → (l : ℕ) ≤ ((j : Fin (r + 1)) : ℕ) →
      G.D l = 0) → t i j = if i = j then 1 else 0) →
    ∃ g ∈ G.St, ∀ j, g (G.f j) = ∑ i, t i j • G.f i := by
  intro F E _ _ _ _ _ sig A r k G t ht
  obtain ⟨p⟩ := nonempty_places F
  haveI : Nontrivial (A.loc p).Ep :=
    Module.nontrivial_of_finrank_pos (R := (A.loc p).Fp) (by rw [(A.loc p).rank]; norm_num)
  have hinj : Function.Injective (A.loc p).ιE := (A.loc p).ιE.injective

  have hZ : ∀ a b, (A.loc p).ιE (G.Zh a b) =
      algebraMap (A.loc p).Fp (A.loc p).Ep (((G.c p : (A.loc p).Fp)) ^ (r - (b : ℕ))) *
      algebraMap (A.loc p).Fp (A.loc p).Ep (((G.c p : (A.loc p).Fp)) ^ (r - (a : ℕ))) *
      ((G.S p).w.mat a b * (-1) ^ (r - (b : ℕ))) := by
    intro a b
    have hform := (GlobalTheory.HL.RatExt.rational_extend A (k + 2 * r + 1) p).2.2.2.2.1 G.Hm (G.f' b) (G.f a)
    have e1 : G.Zh a b = ∑ i, ∑ j, G.f' b i * G.Hm i j * sig (G.f a j) := rfl
    rw [e1, ← hform, ← G.Hm_eq p, ← G.f_eq p a, ← G.f'_eq p b, hf_smul, ← (G.S p).relevant]
  have hne : ∀ a b, G.Zh a b ≠ 0 ↔ (G.S p).w.mat a b ≠ 0 := by
    intro a b
    have hu : IsUnit (algebraMap (A.loc p).Fp (A.loc p).Ep (((G.c p : (A.loc p).Fp)) ^ (r - (b : ℕ))) *
        algebraMap (A.loc p).Fp (A.loc p).Ep (((G.c p : (A.loc p).Fp)) ^ (r - (a : ℕ)))) :=
      (((G.c p).isUnit.pow _).map _).mul (((G.c p).isUnit.pow _).map _)
    have hs : IsUnit ((-1 : (A.loc p).Ep) ^ (r - (b : ℕ))) := (isUnit_one.neg).pow _
    rw [ne_eq, ne_eq, ← map_eq_zero_iff _ hinj, hZ, hu.mul_right_eq_zero, hs.mul_left_eq_zero]
  obtain ⟨ρ, hρ, hρw, hρB⟩ := pt_shape (G.S p).w
  have hZρ : ∀ a b, G.Zh a b ≠ 0 ↔ b = ρ a := fun a b => (hne a b).trans (hρw a b)

  have hD : ∀ l : Fin (r + 2), (∀ a : Fin (r + 1), (a : ℕ) < l → ((ρ a : Fin (r + 1)) : ℕ) < l) → G.D l ≠ 0 := by
    intro l hl
    let e : Fin l → Fin (r + 1) := Fin.castLE (Nat.lt_succ_iff.mp l.2)
    let σ' : Fin l → Fin l := fun i => ⟨ρ (e i), hl (e i) i.2⟩
    have he : ∀ i, ρ (e (σ' i)) = e i := fun i => by
      show ρ (ρ (e i)) = e i
      exact hρ _
    have hσ : Function.Involutive σ' := fun i => Fin.ext (by
      show ((ρ (e (σ' i)) : Fin (r + 1)) : ℕ) = i
      rw [he]; rfl)
    refine det_ne_zero_of_monomial _ hσ.toPerm fun a b => ?_
    show G.Zh (e a) (e b) ≠ 0 ↔ b = σ' a
    rw [hZρ]
    constructor
    · intro h; exact Fin.ext (by rw [show (b : ℕ) = (e b : ℕ) from rfl, h])
    · intro h; subst h; rfl
  obtain ⟨s', hs'up, hs'⟩ := exists_upper G.Zh (t.map sig).transpose ρ
    (fun x y => ∀ l : Fin (r + 2), (x : ℕ) < l → (l : ℕ) ≤ (y : ℕ) → G.D l = 0) hρ hZρ
    (fun x y hxy hB => hρB x y hxy fun l h1 h2 hcl =>
      hD ⟨l, by have := y.2; omega⟩ hcl (hB ⟨l, by have := y.2; omega⟩ h1 h2))
    (fun a => by simp [ht a a (fun h => lt_irrefl _ h.1)])
    (fun a b hab hB => by
      simp only [Matrix.transpose_apply, Matrix.map_apply]
      rw [ht b a hB, if_neg (Ne.symm hab), map_zero])
  have htup : (∀ i j, j < i → t i j = 0) ∧ ∀ i, t i i = 1 :=
    ⟨fun i j hij => by rw [ht i j (fun h => lt_asymm h.1 hij), if_neg (ne_of_gt hij)],
      fun i => by rw [ht i i (fun h => lt_irrefl _ h.1), if_pos rfl]⟩
  obtain ⟨h, hh, hf1, -⟩ := (GlobalTheory.T.hermitianStabiliser_rational_unitriangular_pairs A r k G t s' htup hs'up).1 hs'
  exact ⟨h, hh, hf1⟩

end GlobalTheory.HL.RatPat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BlockUnitriangularRationalFromCommonStabiliserStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockUnitriangular_rational_from_commonStabiliser : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), ∀ t : Matrix (Fin (r + 1)) (Fin (r + 1)) E, (∀ i j, ¬ (i < j ∧ ∀ l : Fin (r + 2), ((i : Fin (r + 1)) : ℕ) < l → (l : ℕ) ≤ ((j : Fin (r + 1)) : ℕ) → G.D l = 0) → t i j = if i = j then 1 else 0) → ∃ g ∈ G.St, ∀ j, g (G.f j) = ∑ i, t i j • G.f i := by
  first | exact @GlobalTheory.HL.RatPat.main | exact GlobalTheory.HL.RatPat.main | (intros; apply GlobalTheory.HL.RatPat.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalCommonStabiliserBlockUnitriangularOnFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalCommonStabiliserBlockUnitriangularOnFrame
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.LocPattern
open GlobalTheory.HL.Eichler

section Local
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem zh_split (l : Fin (r + 2)) (hl : S.D l ≠ 0) (x y : Fin (r + 1))
    (hxy : ((x : ℕ) < l ∧ (l : ℕ) ≤ y) ∨ ((y : ℕ) < l ∧ (l : ℕ) ≤ x)) : S.Zh x y = 0 := by
  have hZ : ∀ a b : Fin (r + 1), S.Zh a b = ptEntryL S.w.blocks a b * (-1) ^ (r - (b : ℕ)) :=
    fun a b => S.relevant a b
  have hA : ∀ a : Fin (r + 1), (a : ℕ) < l → GlobalTheory.FrameBasic.sig S.w.blocks a < l := by
    intro a ha
    by_contra hc
    push_neg at hc
    apply hl
    unfold Frames.D lead
    apply Matrix.det_eq_zero_of_row_eq_zero (⟨a, ha⟩ : Fin l)
    intro j
    simp only [Matrix.submatrix_apply]
    rw [hZ]
    have hj := j.2
    have : ((Fin.castLE (Nat.lt_succ_iff.mp l.2) j : Fin (r + 1)) : ℕ) ≠
        GlobalTheory.FrameBasic.sig S.w.blocks (Fin.castLE (Nat.lt_succ_iff.mp l.2) (⟨a, ha⟩ : Fin l) : Fin (r + 1)) := by
      simp only [Fin.coe_castLE]; omega
    rw [GlobalTheory.FrameBasic.entry_zero _ _ _ this, zero_mul]
  rw [hZ]
  rcases hxy with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [GlobalTheory.FrameBasic.entry_zero _ _ _ (by have := hA x h1; omega), zero_mul]
  · rw [GlobalTheory.FrameBasic.entry_zero _ _ _ ?_, zero_mul]
    intro he
    have h3 := hA y h1
    rw [he, GlobalTheory.FrameBasic.sig_sig] at h3
    omega

theorem m_zero [IsNonarchimedeanLocalField F] [CharZero F]
    (m m' : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hm' : (∀ i j, j < i → m' i j = 0) ∧ (∀ i, m' i i = 1))
    (heq : cT L m * S.Zh * m' = S.Zh) (l : Fin (r + 2)) (hl : S.D l ≠ 0) (a b : Fin (r + 1))
    (ha : (a : ℕ) < l) (hb : (l : ℕ) ≤ b) : m a b = 0 := by
  obtain ⟨-, -, -, hU, -⟩ := GlobalTheory.FrameBasic.main L r k S
  have hU' : IsUnit S.Zh.det := hU
  have hbt : m'.BlockTriangular id := by
    intro i j hij; exact hm'.1 i j hij
  have hdet : IsUnit m'.det := by
    rw [Matrix.det_of_upperTriangular hbt]; simp [hm'.2]
  letI := Matrix.invertibleOfIsUnitDet m' hdet
  have hN : (m'⁻¹).BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hbt
  have h1 : cT L m * S.Zh = S.Zh * m'⁻¹ := by
    calc cT L m * S.Zh = cT L m * S.Zh * m' * m'⁻¹ := by
          rw [Matrix.mul_assoc (cT L m * S.Zh) m', Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
      _ = S.Zh * m'⁻¹ := by rw [heq]
  let v : Fin (r + 1) → E := fun x => if (x : ℕ) < l then L.cj (m x b) else 0
  have hv : Matrix.vecMul v S.Zh = 0 := by
    funext y
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply]
    by_cases hy : (y : ℕ) < l
    · have h2 := congrFun (congrFun h1 b) y
      rw [Matrix.mul_apply, Matrix.mul_apply] at h2
      have h3 : ∑ z, S.Zh b z * m'⁻¹ z y = 0 := Finset.sum_eq_zero fun z _ => by
        by_cases hz : (z : ℕ) ≤ y
        · rw [zh_split S l hl b z (Or.inr ⟨by omega, hb⟩), zero_mul]
        · rw [hN (show y < z from Fin.lt_def.2 (by omega)), mul_zero]
      rw [h3] at h2
      rw [← h2]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [v, cT]
      split_ifs with hx
      · rfl
      · simp [zh_split S l hl x y (Or.inr ⟨hy, by omega⟩)]
    · refine Finset.sum_eq_zero fun x _ => ?_
      simp only [v]
      split_ifs with hx
      · rw [zh_split S l hl x y (Or.inl ⟨hx, by omega⟩), mul_zero]
      · rw [zero_mul]
  have hv0 : v = 0 := Matrix.vecMul_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det _).2 hU')
    (hv.trans (Matrix.zero_vecMul _).symm)
  have := congrFun hv0 a
  simp only [v, if_pos ha, Pi.zero_apply] at this
  exact (map_eq_zero_iff L.cj L.cj.injective).1 this

end Local

section Scal
variable {K B : Type} [Field K] [CommRing B] [Algebra K B]

theorem ab_one (c : Kˣ) (n : ℕ) : algebraMap K B ((c : K) ^ n) * algebraMap K B (((c⁻¹ ^ n : Kˣ)) : K) = 1 := by
  rw [← map_mul, Units.val_pow_eq_pow_val, ← mul_pow, Units.mul_inv, one_pow, map_one]

theorem ba_one (c : Kˣ) (n : ℕ) : algebraMap K B (((c⁻¹ ^ n : Kˣ)) : K) * algebraMap K B ((c : K) ^ n) = 1 := by
  rw [mul_comm, ab_one]

end Scal

section Global
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {A : Places F E sig} {r k : ℕ} (G : GFrames A r k) (p : HeightOneSpectrum (𝓞 F))

theorem f_loc (a : Fin (r + 1)) : (G.S p).f a =
    algebraMap (A.loc p).Fp (A.loc p).Ep ((((G.c p)⁻¹ ^ (r - (a : ℕ)) : ((A.loc p).Fp)ˣ)) : (A.loc p).Fp) •
      A.bc p (G.f a) := by
  rw [← G.f_eq p a, smul_smul, ba_one, one_smul]

theorem f'_loc (a : Fin (r + 1)) : (G.S p).f' a =
    algebraMap (A.loc p).Fp (A.loc p).Ep ((((G.c p)⁻¹ ^ (r - (a : ℕ)) : ((A.loc p).Fp)ˣ)) : (A.loc p).Fp) •
      A.bc p (G.f' a) := by
  rw [← G.f'_eq p a, smul_smul, ba_one, one_smul]

theorem zh_loc (a b : Fin (r + 1)) : (G.S p).Zh a b =
    algebraMap (A.loc p).Fp (A.loc p).Ep ((((G.c p)⁻¹ ^ (r - (b : ℕ)) : ((A.loc p).Fp)ˣ)) : (A.loc p).Fp) *
    algebraMap (A.loc p).Fp (A.loc p).Ep ((((G.c p)⁻¹ ^ (r - (a : ℕ)) : ((A.loc p).Fp)ˣ)) : (A.loc p).Fp) *
      (A.loc p).ιE (G.Zh a b) := by
  show hf (A.L p) (G.S p).Hm ((G.S p).f' b) ((G.S p).f a) = _
  rw [f_loc, f'_loc, hf_smul_l, hf_smul_r, AlgEquiv.commutes, G.Hm_eq p,
    (GlobalTheory.HL.RatExt.rational_extend A (k + 2 * r + 1) p).2.2.2.2.1 G.Hm (G.f' b) (G.f a)]
  simp only [GFrames.Zh, Matrix.of_apply]
  ring

theorem D_ne (l : Fin (r + 2)) (h : G.D l ≠ 0) : (G.S p).D l ≠ 0 := by
  haveI : Nontrivial (A.loc p).Ep :=
    Module.nontrivial_of_finrank_pos (R := (A.loc p).Fp) (by rw [(A.loc p).rank]; norm_num)
  set e : Fin l → Fin (r + 1) := Fin.castLE (Nat.lt_succ_iff.mp l.2) with he
  let d : Fin l → (A.loc p).Ep := fun i =>
    algebraMap (A.loc p).Fp (A.loc p).Ep ((((G.c p)⁻¹ ^ (r - (e i : ℕ)) : ((A.loc p).Fp)ˣ)) : (A.loc p).Fp)
  have hsub : (G.S p).Zh.submatrix e e =
      Matrix.diagonal d * (G.Zh.submatrix e e).map (A.loc p).ιE * Matrix.diagonal d := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.map_apply, zh_loc, d]
    ring
  have hmap : ((G.Zh.submatrix e e).map (A.loc p).ιE).det = (A.loc p).ιE (G.D l) :=
    (RingHom.map_det _ _).symm
  have hD : (G.S p).D l = (∏ i, d i) * (A.loc p).ιE (G.D l) * (∏ i, d i) := by
    show ((G.S p).Zh.submatrix e e).det = _
    rw [hsub, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, hmap]
  have hu : IsUnit (∏ i, d i) := by
    rw [IsUnit.prod_univ_iff]
    intro i
    exact (Units.isUnit _).map _
  rw [hD]
  intro h0
  rw [hu.mul_left_eq_zero, hu.mul_right_eq_zero] at h0
  exact h ((map_eq_zero_iff _ (A.loc p).ιE.injective).1 h0)

end Global

theorem local_pattern : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), ∀ (p : HeightOneSpectrum (𝓞 F)) (h : (G.S p).GLV), h ∈ (G.S p).St → ∃ s : Matrix (Fin (r + 1)) (Fin (r + 1)) (A.loc p).Ep, (∀ i j, ¬ (i < j ∧ ∀ l : Fin (r + 2), ((i : Fin (r + 1)) : ℕ) < l → (l : ℕ) ≤ ((j : Fin (r + 1)) : ℕ) → G.D l = 0) → s i j = if i = j then 1 else 0) ∧ (∀ j, h (A.bc p (G.f j)) = ∑ i, s i j • A.bc p (G.f i)) ∧ ((∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = G.c p) → h ∈ (G.S p).K0 → IsIntM (A.L p) s) := by
  intro F E _ _ _ _ _ sig A r k G p h hh
  haveI := (A.loc p).lf
  haveI := (A.loc p).char0
  obtain ⟨hN1, hN2, -⟩ := GlobalTheory.HL.FrameOnto.unipotent_onto (A.L p) r k (G.S p)
  obtain ⟨m, hm, hmf⟩ := hN1 h hh.1
  obtain ⟨m', hm', hmf'⟩ := hN2 h hh.2
  have heq : cT (A.L p) m * (G.S p).Zh * m' = (G.S p).Zh :=
    ((GlobalTheory.HL.FrameStab.stab_eq (A.L p) r k (G.S p)).2 m m' hm hm').2 ⟨h, hh, hmf, hmf'⟩
  refine ⟨fun i j => algebraMap (A.loc p).Fp (A.loc p).Ep (((G.c p : (A.loc p).Fp)) ^ (r - (j : ℕ))) * m i j *
    algebraMap (A.loc p).Fp (A.loc p).Ep ((((G.c p)⁻¹ ^ (r - (i : ℕ)) : ((A.loc p).Fp)ˣ)) : (A.loc p).Fp),
    ?_, ?_, ?_⟩
  · intro i j hij
    beta_reduce
    rcases lt_trichotomy i j with hlt | rfl | hgt
    · have hex : ∃ l : Fin (r + 2), (i : ℕ) < l ∧ (l : ℕ) ≤ j ∧ G.D l ≠ 0 := by
        by_contra hc
        push_neg at hc
        exact hij ⟨hlt, fun l h1 h2 => hc l h1 h2⟩
      obtain ⟨l, h1, h2, h3⟩ := hex
      rw [if_neg hlt.ne, m_zero (G.S p) m m' hm' heq l (D_ne G p l h3) i j h1 h2]
      simp
    · rw [if_pos rfl, hm.2, mul_one, ab_one]
    · rw [if_neg hgt.ne', hm.1 i j hgt]
      simp
  · intro j
    beta_reduce
    rw [← G.f_eq p j, map_smul, hmf j, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← G.f_eq p i, smul_smul, smul_smul, mul_assoc (_ * m i j), ba_one, mul_one]
  · rintro ⟨u, hu⟩ hK i j
    have hli : LinearIndependent (A.loc p).Ep (G.S p).f :=
      (GlobalTheory.FrameBasic.main (A.L p) r k (G.S p)).1.comp Sum.inl Sum.inl_injective
    have hmem : h ((G.S p).f j) ∈ Submodule.span (A.L p).O (Set.range (G.S p).f) := by
      have h1 : h • Submodule.span (A.L p).O (Set.range (G.S p).f) =
          Submodule.span (A.L p).O (Set.range (G.S p).f) := hK.1.2
      rw [← h1]
      exact Submodule.smul_mem_pointwise_smul _ _ _ (Submodule.subset_span ⟨j, rfl⟩)
    obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hmem
    have hb' : ∑ i, ((b i : (A.L p).O) : (A.loc p).Ep) • (G.S p).f i = h ((G.S p).f j) := by
      rw [← hb]
      exact Finset.sum_congr rfl fun i _ => (Subring.smul_def _ _).symm
    have hmb : m i j = b i := by
      have := Fintype.linearIndependent_iff.1 hli (fun i => ((b i : (A.L p).O) : (A.loc p).Ep) - m i j) (by
        simp only [sub_smul, Finset.sum_sub_distrib, hb', hmf j, sub_self])
      exact (sub_eq_zero.1 (this i)).symm
    have hO : ∀ (y : 𝒪[(A.loc p).Fp]) (n : ℕ),
        algebraMap (A.loc p).Fp (A.loc p).Ep ((y : (A.loc p).Fp) ^ n) ∈ (A.L p).O := by
      intro y n
      rw [map_pow]
      refine pow_mem (((A.L p).O_def _).2 ?_) n
      rw [show (y : (A.loc p).Fp) = algebraMap 𝒪[(A.loc p).Fp] (A.loc p).Fp y from rfl,
        ← IsScalarTower.algebraMap_apply]
      exact isIntegral_algebraMap
    have hinv : (((G.c p)⁻¹ : ((A.loc p).Fp)ˣ) : (A.loc p).Fp) = (((u⁻¹ : (𝒪[(A.loc p).Fp])ˣ) : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) := by
      rw [Units.val_inv_eq_inv_val, ← hu]
      symm
      apply eq_inv_of_mul_eq_one_left
      exact congrArg (fun x : 𝒪[(A.loc p).Fp] => (x : (A.loc p).Fp)) (Units.inv_mul u)
    refine Subring.mul_mem _ (Subring.mul_mem _ ?_ (hmb ▸ (b i).2)) ?_
    · rw [← hu]; exact hO u _
    · rw [Units.val_pow_eq_pow_val, hinv]; exact hO _ _

end GlobalTheory.HL.LocPattern
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalCommonStabiliserBlockUnitriangularOnFrameStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localCommonStabiliser_blockUnitriangular_on_frame : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), ∀ (p : HeightOneSpectrum (𝓞 F)) (h : (G.S p).GLV), h ∈ (G.S p).St → ∃ s : Matrix (Fin (r + 1)) (Fin (r + 1)) (A.loc p).Ep, (∀ i j, ¬ (i < j ∧ ∀ l : Fin (r + 2), ((i : Fin (r + 1)) : ℕ) < l → (l : ℕ) ≤ ((j : Fin (r + 1)) : ℕ) → G.D l = 0) → s i j = if i = j then 1 else 0) ∧ (∀ j, h (A.bc p (G.f j)) = ∑ i, s i j • A.bc p (G.f i)) ∧ ((∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = G.c p) → h ∈ (G.S p).K0 → IsIntM (A.L p) s) := by
  first | exact @GlobalTheory.HL.LocPattern.local_pattern | exact GlobalTheory.HL.LocPattern.local_pattern | (intros; apply GlobalTheory.HL.LocPattern.local_pattern <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrongApproxStab
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.StrongSt

theorem mat_step {K V : Type} [CommRing K] [AddCommGroup V] [Module K V] {m : ℕ} (v : Fin m → V)
    (n g' : V ≃ₗ[K] V) (s t : Matrix (Fin m) (Fin m) K) (hs : IsUnit s.det)
    (hn : ∀ j, n (v j) = ∑ i, s i j • v i) (hg : ∀ j, g' (v j) = ∑ i, t i j • v i) :
    ∀ j, (n⁻¹ * g') (v j) = ∑ i, (s⁻¹ * t) i j • v i := by
  have hw : ∀ i, n.symm (v i) = ∑ k, s⁻¹ k i • v k := by
    intro i
    apply n.injective
    set_option synthInstance.maxHeartbeats 100000 in
      rw [LinearEquiv.apply_symm_apply, map_sum]
    simp_rw [map_smul, hn, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    have h1 : s * s⁻¹ = 1 := Matrix.mul_nonsing_inv s hs
    have : ∀ l, ∑ k, s⁻¹ k i * s l k = (s * s⁻¹) l i := by
      intro l; rw [Matrix.mul_apply]; exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    simp_rw [← Finset.sum_smul, this, h1, Matrix.one_apply, ite_smul, one_smul, zero_smul]
    simp
  intro j
  change n.symm (g' (v j)) = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hg, map_sum]
  simp_rw [map_smul, hw, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun k _ => by congr 1; exact Finset.sum_congr rfl fun i _ => mul_comm _ _

end GlobalTheory.HL.StrongSt

namespace GlobalTheory.HL.StrongSt

theorem bc_sum {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {sig : E →ₐ[F] E} (A : Places F E sig) (p : HeightOneSpectrum (𝓞 F)) {n m : ℕ}
    (a : Fin m → E) (x : Fin m → Fin n → E) :
    A.bc p (∑ i, a i • x i) = ∑ i, (A.loc p).ιE (a i) • A.bc p (x i) := by
  funext l
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Places.bc, Finset.sum_apply, map_sum, map_mul]

theorem unit_of_pat {K : Type} [CommRing K] {m : ℕ} (P : Fin m → Fin m → Prop)
    (hP : ∀ i j, P i j → i < j) (s : Matrix (Fin m) (Fin m) K)
    (hs : ∀ i j, ¬ P i j → s i j = if i = j then 1 else 0) : IsUnit s.det := by
  have hup : s.BlockTriangular id := by
    intro i j hij
    have := hs i j (fun h => absurd (hP i j h) (not_lt.mpr (le_of_lt hij)))
    rw [this, if_neg (ne_of_gt (show j < i from hij))]
  rw [Matrix.det_of_upperTriangular hup]
  have : ∀ i, s i i = 1 := fun i => by rw [hs i i (fun h => absurd (hP i i h) (lt_irrefl _)), if_pos rfl]
  simp [this]

end GlobalTheory.HL.StrongSt

namespace GlobalTheory.HL.StrongSt

theorem strong_approx_stab : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), ∀ Λ : G.Lt, Submodule.IsFullLattice E Λ → ∀ c : ∀ p, ((A.loc p).Fp)ˣ, {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = c p}.Finite → ∀ n : ∀ p, (G.S p).GLV, (∀ p, n p ∈ (G.S p).St) → {p | n p ∉ (G.S p).K0}.Finite → ∃ g ∈ G.St, ∀ p g', A.Ext p g g' → (n p)⁻¹ * g' ∈ (G.S p).K0 ∧ ∀ x ∈ A.lat p Λ, ∃ y ∈ A.lat p Λ, (n p).symm (g' x) - x = algebraMap (A.loc p).Fp (A.loc p).Ep (c p) • y := by
  intro F E _ _ _ _ _ sig A r k G Λ hΛ c₁ hc₁ n hnSt hnK
  let c : ∀ p, ((A.loc p).Fp)ˣ := fun p => if ((c₁ p : (A.loc p).Fp) ∈ 𝒪[(A.loc p).Fp]) then c₁ p else 1
  have hcO : ∀ p, ((c p : (A.loc p).Fp) ∈ 𝒪[(A.loc p).Fp]) := by
    intro p
    by_cases h : ((c₁ p : (A.loc p).Fp) ∈ 𝒪[(A.loc p).Fp])
    · simp only [c, if_pos h]; exact h
    · simp only [c, if_neg h]; exact one_mem _
  have hc : {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = c p}.Finite := by
    refine hc₁.subset fun p hp => ?_
    rintro ⟨u, hu⟩
    have h : ((c₁ p : (A.loc p).Fp) ∈ 𝒪[(A.loc p).Fp]) := hu ▸ (u : 𝒪[(A.loc p).Fp]).2
    exact hp ⟨u, by simp only [c, if_pos h]; exact hu⟩
  have hq : ∀ p, ∃ a ∈ 𝒪[(A.loc p).Fp], (c p : (A.loc p).Fp) = c₁ p * a := by
    intro p
    by_cases h : ((c₁ p : (A.loc p).Fp) ∈ 𝒪[(A.loc p).Fp])
    · exact ⟨1, one_mem _, by simp only [c, if_pos h, mul_one]⟩
    · refine ⟨(c₁ p : (A.loc p).Fp)⁻¹, ?_, by simp only [c, if_neg h]; simp⟩
      have h' : ¬ valuation (A.loc p).Fp (c₁ p : (A.loc p).Fp) ≤ 1 := h
      show valuation (A.loc p).Fp (c₁ p : (A.loc p).Fp)⁻¹ ≤ 1
      rw [map_inv₀]
      exact inv_le_one_of_one_le₀ (le_of_lt (not_le.1 h'))
  have hclose := by
    first
    | exact GlobalTheory.T.frameMatrix_close_gives_lattice_close_integral A r k G Λ hΛ
    | exact GlobalTheory.T.frameMatrix_close_gives_lattice_close_integral A r k G Λ hΛ.toIsLattice
  obtain ⟨d, hd0, hdfin, hd⟩ := hclose
  choose s hsP hsf hsI using fun p => GlobalTheory.T.localCommonStabiliser_blockUnitriangular_on_frame A r k G p (n p) (hnSt p)
  let c' : ∀ p, ((A.loc p).Fp)ˣ := fun p => c p * Units.mk0 (d p) (hd0 p)
  have hc' : {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = c' p}.Finite := by
    refine (hc.union hdfin).subset fun p hp => ?_
    by_contra hq
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hq
    obtain ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ := hq
    exact hp ⟨u * v, by simp [c', hu, hv]⟩
  have hsI' : {p | ¬ IsIntM (A.L p) (s p)}.Finite := by
    refine (hnK.union G.c_unit).subset fun p hp => ?_
    by_contra hq
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hq
    exact hp (hsI p hq.2 hq.1)
  obtain ⟨t, htP, htc⟩ := GlobalTheory.T.pattern_unitriangular_strong_approximation A (r + 1) _ (fun i j h => h.1)
    (fun i j l hij hjl => ⟨hij.1.trans hjl.1, fun m h1 h2 => by
      by_cases hm : (m : ℕ) ≤ (j : ℕ)
      · exact hij.2 m h1 hm
      · exact hjl.2 m (by omega) h2⟩) c' hc' s hsP hsI'
  obtain ⟨g, hgSt, hgf⟩ := GlobalTheory.T.blockUnitriangular_rational_from_commonStabiliser A r k G t htP
  refine ⟨g, hgSt, fun p g' hg' => ?_⟩
  obtain ⟨g'', hg''St, hg''⟩ := hgSt p
  have hgg : g' = g'' := ((GlobalTheory.HL.RatExt.rational_extend A _ p).2.2.1 g).unique hg' hg''
  subst hgg
  have hh : (n p)⁻¹ * g' ∈ (G.S p).St := (G.S p).St.mul_mem ((G.S p).St.inv_mem (hnSt p)) hg''St
  have hgv : ∀ j, g' (A.bc p (G.f j)) = ∑ i, (t.map (A.loc p).ιE) i j • A.bc p (G.f i) := by
    intro j
    rw [hg' (G.f j), hgf j, bc_sum]
    rfl
  have hM := mat_step (fun j => A.bc p (G.f j)) (n p) g' (s p) (t.map (A.loc p).ιE)
    (unit_of_pat _ (fun i j h => h.1) (s p) (hsP p)) (hsf p) hgv
  obtain ⟨hK, hL⟩ := hd p (c p) _ _ (Units.ne_zero _) (hcO p) hh hM fun i j => by
    obtain ⟨o, ho, he⟩ := htc p i j
    exact ⟨o, ho, by rw [he]; simp [c']⟩
  refine ⟨hK, fun x hx => ?_⟩
  obtain ⟨y, hy, he⟩ := hL x hx
  obtain ⟨a, ha, hae⟩ := hq p
  have haO : algebraMap (A.loc p).Fp (A.loc p).Ep a ∈ (A.L p).O := by
    rw [(A.L p).O_def]
    exact isIntegral_algebraMap (R := 𝒪[(A.loc p).Fp]) (x := (⟨a, ha⟩ : 𝒪[(A.loc p).Fp]))
  refine ⟨(⟨_, haO⟩ : (A.L p).O) • y, Submodule.smul_mem _ _ hy, ?_⟩
  refine he.trans ?_
  rw [hae, map_mul, mul_smul]
  rfl

end GlobalTheory.HL.StrongSt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrongApproxStabStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mem_St_approximating_local_elements : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig), ∀ (r k : ℕ) (G : GFrames A r k), ∀ Λ : G.Lt, Submodule.IsFullLattice E Λ → ∀ c : ∀ p, ((A.loc p).Fp)ˣ, {p | ¬ ∃ u : (𝒪[(A.loc p).Fp])ˣ, ((u : 𝒪[(A.loc p).Fp]) : (A.loc p).Fp) = c p}.Finite → ∀ n : ∀ p, (G.S p).GLV, (∀ p, n p ∈ (G.S p).St) → {p | n p ∉ (G.S p).K0}.Finite → ∃ g ∈ G.St, ∀ p g', A.Ext p g g' → (n p)⁻¹ * g' ∈ (G.S p).K0 ∧ ∀ x ∈ A.lat p Λ, ∃ y ∈ A.lat p Λ, (n p).symm (g' x) - x = algebraMap (A.loc p).Fp (A.loc p).Ep (c p) • y := by
  first | exact @GlobalTheory.HL.StrongSt.strong_approx_stab | exact GlobalTheory.HL.StrongSt.strong_approx_stab | (intros; apply GlobalTheory.HL.StrongSt.strong_approx_stab <;> first | assumption | exact (show Submodule.IsFullLattice _ _ from by assumption).toIsLattice)
end
