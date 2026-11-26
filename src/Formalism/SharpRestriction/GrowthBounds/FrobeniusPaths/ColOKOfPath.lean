module

public import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.ColumnKernelComponentsIntegral

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.LiftedColumnCongruence
section -- merged from Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.ColStepFactor
noncomputable section

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

namespace Formalism.MainNotions.LemmaBAlt

section Sym

variable {N r K : ℕ}

def condUS (LL : LiftLetters (Fin N)) (i : Fin N) (b : Fin (r + K)) : Prop :=
  (LL.vec i = true ∧ r ≤ b.val) ∨ (LL.vec i = false ∧ b.val < r)


open Classical in
def nomL (R : Type) [CommRing R] (LL : LiftLetters (Fin N)) (mu : Fin (N + 1) → Fin (r + K) → ℤ) (c : ℤ) (i : Fin N) :
    Fin (r + K) → MvPolynomial (Fin N × Fin (r + K)) R :=
  fun b => if (condUS LL i b ↔ IsCostly mu c i) then X (i, b) else 0

def SgW (R : Type) [CommRing R] (LL : LiftLetters (Fin N)) (mu : Fin (N + 1) → Fin (r + K) → ℤ) (c : ℤ) :
    ℕ → Finset (Fin (r + K)) → MvPolynomial (Fin N × Fin (r + K)) R
  | 0 => extOne
  | j + 1 =>
    if h : j < N then
      colStep c (colH (mu ⟨j, by omega⟩) c) (colH (mu ⟨j + 1, by omega⟩) c) (nomL R LL mu c ⟨j, h⟩) (SgW R LL mu c j)
    else SgW R LL mu c j


open Classical in
def oS (p : ℕ) (pos : Fin N → ℤ) (mu : Fin (N + 1) → Fin (r + K) → ℤ) (c : ℤ) (j : ℕ) (s : ℤ) : ℕ :=
  ∑ i : Fin N, if i.val < j ∧ IsCostly mu c i then p ^ (s - pos i).toNat else 0

lemma oS_zero (p : ℕ) (pos : Fin N → ℤ) (mu : Fin (N + 1) → Fin (r + K) → ℤ) (c : ℤ) (s : ℤ) :
    oS p pos mu c 0 s = 0 := by simp [oS]

open Classical in
lemma oS_succ (p : ℕ) (pos : Fin N → ℤ) (mu : Fin (N + 1) → Fin (r + K) → ℤ) (c : ℤ) (s : ℤ) (j : ℕ) (h : j < N) :
    oS p pos mu c (j + 1) s = oS p pos mu c j s +
      (if IsCostly mu c ⟨j, h⟩ then p ^ (s - pos ⟨j, h⟩).toNat else 0) := by
  unfold oS
  have key : ∀ i : Fin N, (if i.val < j + 1 ∧ IsCostly mu c i then p ^ (s - pos i).toNat else 0) =
      (if i.val < j ∧ IsCostly mu c i then p ^ (s - pos i).toNat else 0) +
      (if i = ⟨j, h⟩ then (if IsCostly mu c ⟨j, h⟩ then p ^ (s - pos ⟨j, h⟩).toNat else 0) else 0) := by
    intro i
    by_cases hi : i = ⟨j, h⟩
    · subst hi; simp
    · have hne : i.val ≠ j := fun e => hi (Fin.ext e)
      have e1 : (i.val < j + 1) ↔ (i.val < j) := by omega
      simp [hi, e1]
  rw [Finset.sum_congr rfl (fun i _ => key i), Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

lemma oS_pow (p : ℕ) (pos : Fin N → ℤ) (mu : Fin (N + 1) → Fin (r + K) → ℤ) (c : ℤ) (j : ℕ) (s s' : ℤ)
    (hs : s ≤ s') (hpos : ∀ i : Fin N, i.val < j → IsUsed mu c i → pos i ≤ s) :
    oS p pos mu c j s' = oS p pos mu c j s * p ^ (s' - s).toNat := by
  classical
  unfold oS
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hi
  · have := hpos i hi.1 (costly_used mu c i hi.2)
    rw [← pow_add]; congr 1; omega
  · simp

lemma oS_top (p : ℕ) (pos : Fin N → ℤ) (mu : Fin (N + 1) → Fin (r + K) → ℤ) (c : ℤ) (z : ℤ) :
    oS p pos mu c N z = oc (fun i => p ^ (z - pos i).toNat) mu c := by
  classical
  unfold oS oc
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [i.isLt]

lemma SgW_supported (LL : LiftLetters (Fin N)) (mu : Fin (N + 1) → Fin (r + K) → ℤ) (c : ℤ) (j : ℕ) :
    ∀ J, SgW ℤ LL mu c j J ∈ supported ℤ {v : Fin N × Fin (r + K) | v.1.val < j ∧ IsUsed mu c v.1} := by
  induction j with
  | zero =>
    intro J; simp only [SgW]; unfold extOne; split_ifs
    · exact Subalgebra.one_mem _
    · exact Subalgebra.zero_mem _
  | succ j ih =>
    intro J
    have mono : supported ℤ {v : Fin N × Fin (r + K) | v.1.val < j ∧ IsUsed mu c v.1} ≤
        supported ℤ {v : Fin N × Fin (r + K) | v.1.val < j + 1 ∧ IsUsed mu c v.1} :=
      supported_mono fun v hv => ⟨by have := hv.1; omega, hv.2⟩
    simp only [SgW]
    split_ifs with h
    · by_cases hu : colH (mu ⟨j, by omega⟩) c = colH (mu ⟨j + 1, by omega⟩) c
      · have : colStep c (colH (mu ⟨j, by omega⟩) c) (colH (mu ⟨j + 1, by omega⟩) c) (nomL ℤ LL mu c ⟨j, h⟩)
            (SgW ℤ LL mu c j) = SgW ℤ LL mu c j := by
          unfold colStep; rw [hu]; simp
        rw [this]; exact mono (ih J)
      · refine colStep_mem _ _ _ _ _ _ (fun b => ?_) (fun J => mono (ih J)) J
        unfold nomL; split_ifs
        · exact X_mem_supported.mpr ⟨by simp, hu⟩
        · exact Subalgebra.zero_mem _
    · exact mono (ih J)

end Sym

section Fac

variable {R R' : Type*} [CommRing R] [CommRing R'] {k : ℕ}

lemma sum_factor {ι' : Type*} (W : R) (π : R →+* R') (s : Finset ι') (e : ι' → ℕ) (a v : ι' → R) (a' v' : ι' → R')
    (H : ∀ m ∈ s, ∃ u, a m * v m = W * u ∧ π u = a' m * v' m) :
    ∃ Y, ∑ m ∈ s, (-1 : R) ^ e m * a m * v m = W * Y ∧ π Y = ∑ m ∈ s, (-1 : R') ^ e m * a' m * v' m := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp, by simp⟩
  | insert m s hm ih =>
    obtain ⟨Y, h1, h2⟩ := ih fun m' hm' => H m' (Finset.mem_insert_of_mem hm')
    obtain ⟨u, h3, h4⟩ := H m (Finset.mem_insert_self m s)
    refine ⟨(-1) ^ e m * u + Y, ?_, ?_⟩
    · rw [Finset.sum_insert hm, h1, mul_assoc, h3]; ring
    · rw [Finset.sum_insert hm, ← h2, map_add (f := _), map_mul, h4, map_pow, map_neg, map_one]; ring

lemma colStep_factor (W : R) (π : R →+* R') (c : ℤ) (hP hN : ℕ) (hne : hP ≠ hN) (y : Fin k → R)
    (V : Finset (Fin k) → R) (n' : Fin k → R') (S' : Finset (Fin k) → R')
    (H : ∀ m J, (((hP < hN ∧ 1 ≤ c) ∨ (hN < hP ∧ ¬ 1 ≤ c)) → m ∈ J →
          ∃ u, y m * V (J.erase m) = W * u ∧ π u = n' m * S' (J.erase m)) ∧
        (((hP < hN ∧ ¬ 1 ≤ c) ∨ (hN < hP ∧ 1 ≤ c)) → m ∉ J →
          ∃ u, y m * V (insert m J) = W * u ∧ π u = n' m * S' (insert m J))) (J : Finset (Fin k)) :
    ∃ Y, colStep c hP hN y V J = W * Y ∧ π Y = colStep c hP hN n' S' J := by
  unfold colStep
  split_ifs with h1 h2 h3 h4
  · exact sum_factor W π _ _ _ _ _ _ fun m hm => (H m J).1 (Or.inl ⟨h1, h2⟩) hm
  · exact sum_factor W π _ _ _ _ _ _ fun m hm => (H m J).2 (Or.inl ⟨h1, h2⟩) (by simpa using hm)
  · exact sum_factor W π _ _ _ _ _ _ fun m hm => (H m J).2 (Or.inr ⟨h3, h4⟩) (by simpa using hm)
  · exact sum_factor W π _ _ _ _ _ _ fun m hm => (H m J).1 (Or.inr ⟨h3, h4⟩) hm
  · omega

end Fac

section Ana

variable (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {N r K : ℕ}

lemma piR_ker {σ : Type} (S : UniformizedDVR p O) (Y : MvPolynomial σ O)
    (h : MvPolynomial.map (IsLocalRing.residue O) Y = 0) : ∃ T, Y = C S.w * T := by
  have : C S.w ∣ Y := by
    rw [MvPolynomial.C_dvd_iff_dvd_coeff]
    intro m
    have h1 : IsLocalRing.residue O (Y.coeff m) = 0 := by rw [← coeff_map, h]; simp
    rw [IsLocalRing.residue_eq_zero_iff, S.w_irr.maximalIdeal_eq, Ideal.mem_span_singleton] at h1
    exact h1
  exact this

lemma piR_w {σ : Type} (S : UniformizedDVR p O) :
    MvPolynomial.map (IsLocalRing.residue O) (C S.w : MvPolynomial σ O) = 0 := by
  have : IsLocalRing.residue O S.w = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, S.w_irr.maximalIdeal_eq]; exact Ideal.mem_span_singleton_self _
  rw [map_C, this, C_0]

def piS (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (pos : Fin N → ℤ) (s : ℤ) :
    MvPolynomial (Fin N × Fin (r + K)) ℤ →+* MvPolynomial (Fin N × Fin (r + K)) (FF O) :=
  eval₂Hom (Int.castRingHom _) (fun v => X v ^ p ^ (s - pos v.1).toNat)

lemma piS_frob [CharP (FF O) p] (pos : Fin N → ℤ) (s s' : ℤ) (hs : s ≤ s') (V : Set (Fin N × Fin (r + K)))
    (hV : ∀ v ∈ V, pos v.1 ≤ s) (f : MvPolynomial (Fin N × Fin (r + K)) ℤ) (hf : f ∈ supported ℤ V) :
    (piS p O pos s f) ^ (p ^ (s' - s).toNat) = piS p O pos s' f := by
  have key : ((iterateFrobenius (MvPolynomial (Fin N × Fin (r + K)) (FF O)) p (s' - s).toNat).comp (piS p O pos s)) f =
      piS p O pos s' f := by
    refine MvPolynomial.hom_congr_vars (RingHom.ext_int _ _) (fun v hv _ => ?_) rfl
    have hv' := hV v ((mem_supported.mp hf) hv)
    simp only [RingHom.comp_apply, iterateFrobenius_def, piS, eval₂Hom_X']
    rw [← pow_mul, ← pow_add]; congr 2; omega
  simpa [iterateFrobenius_def] using key

def yO (w : O) (LL : LiftLetters (Fin N)) (i : Fin N) (b : Fin (r + K)) : MvPolynomial (Fin N × Fin (r + K)) O :=
  C (dW O w LL r i b) * X (i, b)

lemma yO_cond (w : O) (LL : LiftLetters (Fin N)) (i : Fin N) (b : Fin (r + K)) (h : condUS LL i b) :
    yO w LL i b = C w * X (i, b) := by
  unfold condUS at h; unfold yO dW; rw [if_pos h]

lemma yO_ncond (w : O) (LL : LiftLetters (Fin N)) (i : Fin N) (b : Fin (r + K)) (h : ¬ condUS LL i b) :
    yO w LL i b = X (i, b) := by
  unfold condUS at h; unfold yO dW; rw [if_neg h]; simp

def SgVanish (LL : LiftLetters (Fin N)) (mu : Fin (N + 1) → Fin (r + K) → ℤ) (c : ℤ) : Prop :=
  ∀ (j : ℕ) (h : j < N), IsCostly mu c ⟨j, h⟩ → ∀ m, ¬ condUS LL ⟨j, h⟩ m → ∀ J : Finset (Fin (r + K)),
    (((colH (mu ⟨j, by omega⟩) c < colH (mu ⟨j + 1, by omega⟩) c ∧ 1 ≤ c) ∨
        (colH (mu ⟨j + 1, by omega⟩) c < colH (mu ⟨j, by omega⟩) c ∧ ¬ 1 ≤ c)) → m ∈ J →
      SgW ℤ LL mu c j (J.erase m) = 0) ∧
    (((colH (mu ⟨j, by omega⟩) c < colH (mu ⟨j + 1, by omega⟩) c ∧ ¬ 1 ≤ c) ∨
        (colH (mu ⟨j + 1, by omega⟩) c < colH (mu ⟨j, by omega⟩) c ∧ 1 ≤ c)) → m ∉ J →
      SgW ℤ LL mu c j (insert m J) = 0)

theorem Inv_main [CharP (FF O) p] (S : UniformizedDVR p O) (LL : LiftLetters (Fin N))
    (mu : Fin (N + 1) → Fin (r + K) → ℤ) (c : ℤ) (hmono : Monotone LL.pos)
    (hposc : ∀ i j : Fin N, i < j → IsUsed mu c i → IsCostly mu c j → LL.pos i < LL.pos j)
    (HV : SgVanish LL mu c) (j : ℕ) (hj : j ≤ N) :
    ∀ s : ℤ, (∀ i : Fin N, i.val < j → IsUsed mu c i → LL.pos i ≤ s) → ∀ J, ∃ Y : MvPolynomial (Fin N × Fin (r + K)) O,
      ZZ p (yO S.w LL) LL.pos mu c j s J = C S.w ^ oS p LL.pos mu c j s * Y ∧
      MvPolynomial.map (IsLocalRing.residue O) Y = piS p O LL.pos s (SgW ℤ LL mu c j J) := by
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  induction j with
  | zero =>
    intro s _ J
    refine ⟨extOne J, by rw [ZZ_zero, oS_zero]; simp, ?_⟩
    simp only [SgW]
    rw [extOne_map, extOne_map]
  | succ j ih =>
    intro s hs J
    have h : j < N := hj
    have ih' := ih (by omega)
    by_cases hu : colH (mu ⟨j, by omega⟩) c = colH (mu ⟨j + 1, by omega⟩) c
    · have hnc : ¬ IsCostly mu c ⟨j, h⟩ := fun hc => costly_used mu c _ hc hu
      obtain ⟨Y, h1, h2⟩ := ih' s (fun i hi => hs i (by omega)) J
      refine ⟨Y, ?_, ?_⟩
      · rw [ZZ_unused p _ _ mu c s j h hu, oS_succ p _ mu c s j h, if_neg hnc, add_zero]; exact h1
      · rw [h2]; simp only [SgW, dif_pos h]
        congr 1
        unfold colStep; rw [hu]; simp
    · set s0 := LL.pos ⟨j, h⟩ with hs0
      have hs0s : s0 ≤ s := hs ⟨j, h⟩ (by simp) hu
      have hprev : ∀ i : Fin N, i.val < j → IsUsed mu c i → LL.pos i ≤ s0 := fun i hi _ =>
        hmono (show i ≤ ⟨j, h⟩ from Fin.le_def.mpr (by simp; omega))

      have stepA : ∀ J, ∃ Y : MvPolynomial (Fin N × Fin (r + K)) O,
          colStep c (colH (mu ⟨j, by omega⟩) c) (colH (mu ⟨j + 1, by omega⟩) c) (yO S.w LL ⟨j, h⟩)
            (ZZ p (yO S.w LL) LL.pos mu c j s0) J = C S.w ^ oS p LL.pos mu c (j + 1) s0 * Y ∧
          MvPolynomial.map (IsLocalRing.residue O) Y = piS p O LL.pos s0 (SgW ℤ LL mu c (j + 1) J) := by
        intro J
        have eS : piS p O LL.pos s0 (SgW ℤ LL mu c (j + 1) J) =
            colStep c (colH (mu ⟨j, by omega⟩) c) (colH (mu ⟨j + 1, by omega⟩) c)
              (fun b => piS p O LL.pos s0 (nomL ℤ LL mu c ⟨j, h⟩ b))
              (fun J => piS p O LL.pos s0 (SgW ℤ LL mu c j J)) J := by
          simp only [SgW, dif_pos h, colStep_map]
        have eX : ∀ b : Fin (r + K), piS p O LL.pos s0 (X (⟨j, h⟩, b)) = X (⟨j, h⟩, b) := by
          intro b; simp [piS, hs0]
        rw [eS]
        by_cases hc : IsCostly mu c ⟨j, h⟩
        ·
          have hs1 : ∀ i : Fin N, i.val < j → IsUsed mu c i → LL.pos i ≤ s0 - 1 := fun i hi hui => by
            have := hposc i ⟨j, h⟩ (Fin.lt_def.mpr (by simpa using hi)) hui hc
            omega
          choose Y1 hY1 hY2 using ih' (s0 - 1) hs1
          have e1 : (s0 - (s0 - 1)).toNat = 1 := by omega
          have eZ : ZZ p (yO S.w LL) LL.pos mu c j s0 =
              fun J => C S.w ^ oS p LL.pos mu c j s0 * (Y1 J) ^ p := by
            rw [ZZ_pow p hp0 _ _ mu c j (by omega) (s0 - 1) s0 (by omega) hs1,
              oS_pow p _ mu c j (s0 - 1) s0 (by omega) hs1, e1, pow_one]
            funext J; simp only [powC]; rw [hY1, mul_pow, ← pow_mul]
          have eV : ∀ J, MvPolynomial.map (IsLocalRing.residue O) ((Y1 J) ^ p) =
              piS p O LL.pos s0 (SgW ℤ LL mu c j J) := by
            intro J
            rw [map_pow, hY2, ← piS_frob p LL.pos (s0 - 1) s0 (by omega) {v : Fin N × Fin (r + K) | v.1.val < j ∧ IsUsed mu c v.1} (fun v hv => hs1 v.1 hv.1 hv.2) _
              (SgW_supported LL mu c j J), e1, pow_one]
          have pair : ∀ m J', (condUS LL ⟨j, h⟩ m ∨ SgW ℤ LL mu c j J' = 0) →
              ∃ u, yO S.w LL ⟨j, h⟩ m * (Y1 J') ^ p = C S.w * u ∧
                MvPolynomial.map (IsLocalRing.residue O) u =
                  piS p O LL.pos s0 (nomL ℤ LL mu c ⟨j, h⟩ m) * piS p O LL.pos s0 (SgW ℤ LL mu c j J') := by
            intro m J' hm
            by_cases hcm : condUS LL ⟨j, h⟩ m
            · refine ⟨X (⟨j, h⟩, m) * (Y1 J') ^ p, by rw [yO_cond _ _ _ _ hcm]; ring, ?_⟩
              rw [map_mul, eV, map_X]
              have : nomL ℤ LL mu c ⟨j, h⟩ m = X (⟨j, h⟩, m) := by
                unfold nomL; rw [if_pos (iff_of_true hcm hc)]
              rw [this, eX]
            · have hz : SgW ℤ LL mu c j J' = 0 := hm.resolve_left hcm
              obtain ⟨T, hT⟩ := piR_ker p S (Y1 J') (by rw [hY2, hz, map_zero])
              have hp1 : p - 1 ≠ 0 := by have := (Fact.out : p.Prime).two_le; omega
              refine ⟨X (⟨j, h⟩, m) * (C S.w ^ (p - 1) * T ^ p), ?_, ?_⟩
              · rw [yO_ncond _ _ _ _ hcm, hT, mul_pow]
                have e : (C S.w : MvPolynomial (Fin N × Fin (r + K)) O) ^ p = C S.w ^ (p - 1) * C S.w := by
                  rw [← pow_succ, Nat.sub_add_cancel (Fact.out : p.Prime).one_le]
                rw [e]; ring
              · rw [map_mul, map_mul, map_pow, piR_w p S, zero_pow hp1, hz, map_zero]; simp
          obtain ⟨Y, hYa, hYb⟩ := colStep_factor (C S.w) (MvPolynomial.map (IsLocalRing.residue O)) c _ _ hu
            (yO S.w LL ⟨j, h⟩) (fun J => (Y1 J) ^ p) (fun b => piS p O LL.pos s0 (nomL ℤ LL mu c ⟨j, h⟩ b))
            (fun J => piS p O LL.pos s0 (SgW ℤ LL mu c j J))
            (fun m J => ⟨fun hw hmJ => pair m _ (by
                by_cases hcm : condUS LL ⟨j, h⟩ m
                · exact Or.inl hcm
                · exact Or.inr ((HV j h hc m hcm J).1 hw hmJ)),
              fun hw hmJ => pair m _ (by
                by_cases hcm : condUS LL ⟨j, h⟩ m
                · exact Or.inl hcm
                · exact Or.inr ((HV j h hc m hcm J).2 hw hmJ))⟩) J
          refine ⟨Y, ?_, hYb⟩
          rw [eZ, colStep_smul, hYa, oS_succ p _ mu c s0 j h, if_pos hc, ← hs0]
          simp only [sub_self, Int.toNat_zero, pow_zero]
          ring
        ·
          choose Y hY1 hY2 using ih' s0 hprev
          have eZ : ZZ p (yO S.w LL) LL.pos mu c j s0 = fun J => C S.w ^ oS p LL.pos mu c j s0 * Y J :=
            funext hY1
          refine ⟨colStep c (colH (mu ⟨j, by omega⟩) c) (colH (mu ⟨j + 1, by omega⟩) c) (yO S.w LL ⟨j, h⟩) Y J, ?_, ?_⟩
          · rw [eZ, colStep_smul, oS_succ p _ mu c s0 j h, if_neg hc, add_zero]
          · rw [colStep_map]
            congr 1
            · funext b
              by_cases hcm : condUS LL ⟨j, h⟩ b
              · rw [yO_cond _ _ _ _ hcm, map_mul, piR_w p S, zero_mul]
                have : nomL ℤ LL mu c ⟨j, h⟩ b = 0 := by
                  unfold nomL; rw [if_neg (fun e => hc (e.mp hcm))]
                rw [this, map_zero]
              · rw [yO_ncond _ _ _ _ hcm, map_X]
                have : nomL ℤ LL mu c ⟨j, h⟩ b = X (⟨j, h⟩, b) := by
                  unfold nomL; rw [if_pos (iff_of_false hcm hc)]
                rw [this, eX]
            · funext J'; exact hY2 J'

      obtain ⟨Y, hYa, hYb⟩ := stepA J
      refine ⟨Y ^ (p ^ (s - s0).toNat), ?_, ?_⟩
      · rw [ZZ_used p _ _ mu c s j h hu]
        simp only [powC]
        rw [← hs0, hYa, mul_pow, ← pow_mul, oS_pow p _ mu c (j + 1) s0 s hs0s]
        intro i hi hui
        exact hmono (show i ≤ ⟨j, h⟩ from Fin.le_def.mpr (by simp; omega))
      · rw [map_pow, hYb]
        exact piS_frob p LL.pos s0 s hs0s _
          (fun v hv => hmono (show v.1 ≤ ⟨j, h⟩ from Fin.le_def.mpr (by have := hv.1; simp; omega))) _
          (SgW_supported LL mu c (j + 1) J)

end Ana

end Formalism.MainNotions.LemmaBAlt
end
end

noncomputable section

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

namespace Formalism.MainNotions.LemmaBAlt

section LinkG

variable (p f : ℕ) [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Algebra (WF p f) O] {N r K : ℕ}

lemma lift_letG (w : O) (LL : LiftLetters (Fin N)) (g : Matrix (Fin (r + K)) (Fin (r + K)) (WF p f)) (hg : IsGLW g)
    (i : Fin N) (b : Fin (r + K)) :
    liftSubst p f O w r LL g (letG p f (O := O) LL g i b) =
      MvPolynomial.map (algebraMap O (KK O)) (yO w LL i b) := by
  have hinv : sigMat p f O g⁻¹ (LL.pos i) * sigMat p f O g (LL.pos i) = 1 := by
    rw [← sigMat_mul, Matrix.nonsing_inv_mul g hg, sigMat_one]
  have hC : ∀ x : KK O, liftSubst p f O w r LL g (C x) = C x := fun x => (liftSubst p f O w r LL g).commutes x
  simp only [yO, map_mul, map_C, map_X]
  by_cases hv : LL.vec i = true
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [letG, hv, if_true, map_sum, map_mul, hC, liftSubst_X_vec p f O w LL r g hg i _ hv]
      simp_rw [Finset.sum_mul, mul_assoc, ← map_mul]
      rw [Finset.sum_comm]
      set_option synthInstance.maxHeartbeats 100000 in
        simp_rw [← Finset.mul_sum, ← map_sum, ← Matrix.mul_apply, hinv, Matrix.one_apply, apply_ite C, map_one, map_zero,
        mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · have hv' : LL.vec i = false := by simpa using hv
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [letG, hv', Bool.false_eq_true, if_false, map_sum, map_mul, hC,
      liftSubst_X_cov p f O w LL r g i _ hv', sigMat_inv p f O g hg]
    simp_rw [Finset.sum_mul, mul_assoc, ← map_mul]
    rw [Finset.sum_comm]
    set_option synthInstance.maxHeartbeats 100000 in
      simp_rw [← Finset.mul_sum, ← map_sum, mul_comm (sigMat p f O g (LL.pos i) _ _), ← Matrix.mul_apply, hinv,
      Matrix.one_apply, apply_ite C, map_one, map_zero, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]

lemma lift_KKc (w : O) (LL : LiftLetters (Fin N)) (g : Matrix (Fin (r + K)) (Fin (r + K)) (WF p f)) (hg : IsGLW g)
    (z : ℤ) (mu : Fin (N + 1) → Fin (r + K) → ℤ) (c : ℤ) (J : Finset (Fin (r + K))) :
    liftSubst p f O w r LL g (KKc p f (O := O) LL g z mu c J) =
      MvPolynomial.map (algebraMap O (KK O)) (ZZ p (yO w LL) LL.pos mu c N z J) := by
  rw [KKc_eq (O := O) p f LL g z mu c]
  have h1 := ZZ_map (liftSubst p f O w r LL g).toRingHom p (letG p f (O := O) LL g) LL.pos mu c N le_rfl z J
  have h2 := ZZ_map (MvPolynomial.map (algebraMap O (KK O))) p (yO w LL) LL.pos mu c N le_rfl z J
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h1
  rw [h1, h2]
  congr 1
  funext i b
  exact lift_letG p f w LL g hg i b

end LinkG

section MapSg

variable {N r K : ℕ}

lemma SgW_map {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (LL : LiftLetters (Fin N))
    (mu : Fin (N + 1) → Fin (r + K) → ℤ) (c : ℤ) (j : ℕ) :
    ∀ J, MvPolynomial.map φ (SgW R LL mu c j J) = SgW R' LL mu c j J := by
  induction j with
  | zero => intro J; simp only [SgW]; exact extOne_map _ J
  | succ j ih =>
    intro J
    simp only [SgW]
    split_ifs with h
    · rw [colStep_map]
      congr 1
      · funext b
        simp only [nomL]
        split_ifs <;> simp
      · funext J'
        exact ih J'
    · exact ih J

end MapSg

section Clause4

variable (p f : ℕ) [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Algebra (WF p f) O] {N r K : ℕ}

theorem lifted_column_congruence (S : UniformizedDVR p O) (LL : LiftLetters (Fin N)) (g : Matrix (Fin (r + K)) (Fin (r + K)) (WF p f))
    (hg : IsGLW g) (z : ℤ) (mu : Fin (N + 1) → Fin (r + K) → ℤ) (c : ℤ) (hmono : Monotone LL.pos)
    (hz : ∀ i, LL.pos i ≤ z)
    (hposc : ∀ i j : Fin N, i < j → IsUsed mu c i → IsCostly mu c j → LL.pos i < LL.pos j)
    (HV : SgVanish LL mu c) (hS2 : ∀ J, plTanCol O mu c J = SgW O LL mu c N J) (J : Finset (Fin (r + K))) :
    InWj S.w (liftSubst p f O S.w r LL g (KKc p f (O := O) LL g z mu c J) -
        C (algebraMap O (KK O) S.w ^ oc (fun i => p ^ (z - LL.pos i).toNat) mu c) *
          powSubst p LL z (plTanCol O mu c J))
      (oc (fun i => p ^ (z - LL.pos i).toNat) mu c + 1) := by
  have : CharP (FF O) p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).2 (by
    rw [← map_natCast (IsLocalRing.residue O), IsLocalRing.residue_eq_zero_iff]; exact S.p_mem)
  obtain ⟨Y, hY, hYres⟩ := Inv_main p S LL mu c hmono hposc HV N le_rfl z (fun i _ _ => hz i) J
  rw [oS_top] at hY
  set o := oc (fun i => p ^ (z - LL.pos i).toNat) mu c with ho
  let P : Fin N × Fin (r + K) → MvPolynomial (Fin N × Fin (r + K)) O := fun v => X v ^ p ^ (z - LL.pos v.1).toNat
  have hps : ∀ F : MvPolynomial (Fin N × Fin (r + K)) O,
      powSubst p LL z F = MvPolynomial.map (algebraMap O (KK O)) (aeval P F) := by
    intro F
    induction F using MvPolynomial.induction_on with
    | C a => simp [powSubst, MvPolynomial.algebraMap_eq]
    | add F G hF hG => simp only [map_add (f := _), hF, hG]
    | mul_X F v hF => simp [powSubst, hF, P] at hF ⊢
  have hres : ∀ F : MvPolynomial (Fin N × Fin (r + K)) ℤ,
      MvPolynomial.map (IsLocalRing.residue O) (aeval P (MvPolynomial.map (Int.castRingHom O) F)) =
        piS p O LL.pos z F := by
    intro F
    induction F using MvPolynomial.induction_on with
    | C a => simp [piS]
    | add F G hF hG => simp only [map_add (f := _), hF, hG]
    | mul_X F v hF => simp [piS, hF, P] at hF ⊢
  set Q := aeval P (SgW O LL mu c N J) with hQ
  have hQres : MvPolynomial.map (IsLocalRing.residue O) Q = piS p O LL.pos z (SgW ℤ LL mu c N J) := by
    rw [hQ, ← SgW_map (Int.castRingHom O) LL mu c N J, hres]
  obtain ⟨T, hT⟩ := piR_ker p S (Y - Q) (by rw [map_sub, hYres, hQres, sub_self])
  have key : liftSubst p f O S.w r LL g (KKc p f (O := O) LL g z mu c J) -
      C (algebraMap O (KK O) S.w ^ o) * powSubst p LL z (plTanCol O mu c J) =
      MvPolynomial.map (algebraMap O (KK O)) (C (S.w ^ (o + 1)) * T) := by
    rw [lift_KKc p f S.w LL g hg z mu c J, hY, hS2 J, hps, ← hQ, ← map_pow]
    have e : (C ((algebraMap O (KK O)) S.w ^ o) : MvPolynomial (Fin N × Fin (r + K)) (KK O)) =
        MvPolynomial.map (algebraMap O (KK O)) (C (S.w ^ o)) := by
      rw [map_C, map_pow (algebraMap O (KK O))]
    rw [e, ← map_mul, ← map_sub, ← mul_sub, hT, ← mul_assoc, ← C_mul, ← pow_succ]
  intro m
  refine ⟨T.coeff m, ?_⟩
  rw [key, coeff_map, coeff_C_mul]

end Clause4

end Formalism.MainNotions.LemmaBAlt
end
end

noncomputable section

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

namespace Formalism.MainNotions.LemmaBAlt

section Strip

lemma colH_strip {n : ℕ} (nu mu' : Fin n → ℤ) (b : ℕ) (h : HStrip nu mu' b) (c : ℤ) :
    colH nu c ≤ colH mu' c ∧ colH mu' c ≤ colH nu c + 1 := by
  classical
  obtain ⟨h1, h2, _⟩ := h
  constructor
  · unfold colH
    refine Finset.card_le_card fun m hm => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm ⊢
    exact hm.trans (h1 m)
  · unfold colH
    set A := univ.filter fun m : Fin n => c ≤ mu' m with hA
    have e : A.card = (A.filter fun m => m.val = 0).card + (A.filter fun m => ¬ m.val = 0).card :=
      (Finset.card_filter_add_card_filter_not _).symm
    have e1 : (A.filter fun m => m.val = 0).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      simp only [Finset.mem_filter] at ha hb
      exact Fin.ext (by omega)
    have e2 : (A.filter fun m => ¬ m.val = 0).card ≤ (univ.filter fun m : Fin n => c ≤ nu m).card := by
      refine Finset.card_le_card_of_injOn (fun m => ⟨m.val - 1, by have := m.isLt; omega⟩) ?_ ?_
      · intro m hm
        simp only [Finset.coe_filter, Finset.mem_filter, hA, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hm ⊢
        have hlt : (m.val - 1) + 1 < n := by have := m.isLt; omega
        have := h2 ⟨m.val - 1, by have := m.isLt; omega⟩ hlt
        have em : (⟨(m.val - 1) + 1, hlt⟩ : Fin n) = m := Fin.ext (by simp; omega)
        simp only [em] at this
        exact hm.1.trans this
      · intro a ha b hb hab
        simp only [Finset.coe_filter, Finset.mem_filter, Set.mem_ofPred_eq] at ha hb
        simp only [Fin.mk.injEq] at hab
        exact Fin.ext (by omega)
    omega

end Strip

section Col

variable {N r K : ℕ}

structure ColOK (LL : LiftLetters (Fin N)) (mu : Fin (N + 1) → Fin (r + K) → ℤ) (c : ℤ) : Prop where
  rise : ∀ (j : ℕ) (h : j < N), colH (mu ⟨j, by omega⟩) c < colH (mu ⟨j + 1, by omega⟩) c →
    LL.vec ⟨j, h⟩ = true ∧ colH (mu ⟨j + 1, by omega⟩) c = colH (mu ⟨j, by omega⟩) c + 1
  fall : ∀ (j : ℕ) (h : j < N), colH (mu ⟨j + 1, by omega⟩) c < colH (mu ⟨j, by omega⟩) c →
    LL.vec ⟨j, h⟩ = false ∧ colH (mu ⟨j, by omega⟩) c = colH (mu ⟨j + 1, by omega⟩) c + 1
  start : 1 ≤ c → colH (mu ⟨0, by omega⟩) c = 0
  dual : ¬ 1 ≤ c → ∀ (j : ℕ) (h : j ≤ N), r < colH (mu ⟨j, by omega⟩) c

lemma colOK_of_path [NeZero r] (LL : LiftLetters (Fin N)) (B : Fin N → ℕ) (hK : N + r ≤ K)
    (P : PPath (r + K) N LL.toLetters B) (c : ℤ) : ColOK LL P.mu c := by
  have step : ∀ (j : ℕ) (h : j < N),
      (LL.vec ⟨j, h⟩ = true ∧ colH (P.mu ⟨j, by omega⟩) c ≤ colH (P.mu ⟨j + 1, by omega⟩) c ∧
        colH (P.mu ⟨j + 1, by omega⟩) c ≤ colH (P.mu ⟨j, by omega⟩) c + 1) ∨
      (LL.vec ⟨j, h⟩ = false ∧ colH (P.mu ⟨j + 1, by omega⟩) c ≤ colH (P.mu ⟨j, by omega⟩) c ∧
        colH (P.mu ⟨j, by omega⟩) c ≤ colH (P.mu ⟨j + 1, by omega⟩) c + 1) := by
    intro j h
    have hs := P.step ⟨j, h⟩
    by_cases hv : LL.vec ⟨j, h⟩ = true
    · rw [if_pos hv] at hs
      exact Or.inl ⟨hv, colH_strip _ _ _ hs c⟩
    · rw [if_neg hv] at hs
      exact Or.inr ⟨by simpa using hv, colH_strip _ _ _ hs c⟩
  have hz : P.mu ⟨0, by omega⟩ = 0 := P.zero
  refine ⟨fun j h hlt => ?_, fun j h hlt => ?_, fun hc => ?_, fun hc => ?_⟩
  · rcases step j h with ⟨hv, h1, h2⟩ | ⟨hv, h1, h2⟩
    · exact ⟨hv, by omega⟩
    · omega
  · rcases step j h with ⟨hv, h1, h2⟩ | ⟨hv, h1, h2⟩
    · omega
    · exact ⟨hv, by omega⟩
  · rw [hz]; unfold colH
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro m _; simp only [Pi.zero_apply]; omega
  · have h0 : colH (P.mu ⟨0, by omega⟩) c = r + K := by
      rw [hz]; unfold colH
      rw [Finset.filter_true_of_mem (fun m _ => by simp only [Pi.zero_apply]; omega)]
      simp
    have hind : ∀ (j : ℕ) (h : j ≤ N), r + K ≤ colH (P.mu ⟨j, by omega⟩) c + j := by
      intro j
      induction j with
      | zero => intro _; omega
      | succ j ih =>
        intro h
        have := ih (by omega)
        rcases step j h with ⟨_, h1, h2⟩ | ⟨_, h1, h2⟩ <;> omega
    intro j h
    have := hind j h
    have := NeZero.pos r
    omega

lemma plane_card : (univ.filter fun a : Fin (r + K) => a.val < r).card = r := by
  classical
  rw [show (univ.filter fun a : Fin (r + K) => a.val < r) = (univ : Finset (Fin r)).image (Fin.castAdd K) from ?_,
    Finset.card_image_of_injective _ (Fin.castAdd_injective r K), Finset.card_fin]
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro h; exact ⟨⟨a.val, h⟩, Fin.ext rfl⟩
  · rintro ⟨b, rfl⟩; exact b.isLt

lemma costly_iff (mu : Fin (N + 1) → Fin (r + K) → ℤ) (c : ℤ) (j : ℕ) (h : j < N) :
    IsCostly mu c ⟨j, h⟩ ↔
      (colH (mu ⟨j, by omega⟩) c < colH (mu ⟨j + 1, by omega⟩) c ∧ r ≤ colH (mu ⟨j, by omega⟩) c) ∨
      (colH (mu ⟨j + 1, by omega⟩) c < colH (mu ⟨j, by omega⟩) c ∧ colH (mu ⟨j, by omega⟩) c ≤ r) := Iff.rfl

lemma nomL_ne {R : Type} [CommRing R] (LL : LiftLetters (Fin N)) (mu : Fin (N + 1) → Fin (r + K) → ℤ) (c : ℤ)
    (i : Fin N) (m : Fin (r + K)) (h : nomL R LL mu c i m ≠ 0) : condUS LL i m ↔ IsCostly mu c i := by
  classical
  by_contra hh
  exact h (by unfold nomL; rw [if_neg hh])

lemma wedgeR_ne {R : Type} [CommRing R] {k : ℕ} (x : Fin k → R) (Kv : Finset (Fin k) → R) (J : Finset (Fin k))
    (h : wedgeR x Kv J ≠ 0) : ∃ m ∈ J, x m ≠ 0 ∧ Kv (J.erase m) ≠ 0 := by
  obtain ⟨m, hm, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  refine ⟨m, hm, fun e => hne (by rw [e]; simp), fun e => hne (by rw [e]; simp)⟩

lemma contrR_ne {R : Type} [CommRing R] {k : ℕ} (x : Fin k → R) (Kv : Finset (Fin k) → R) (J : Finset (Fin k))
    (h : contrR x Kv J ≠ 0) : ∃ m, m ∉ J ∧ x m ≠ 0 ∧ Kv (insert m J) ≠ 0 := by
  obtain ⟨m, hm, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  refine ⟨m, by simpa using hm, fun e => hne (by rw [e]; simp), fun e => hne (by rw [e]; simp)⟩

lemma SgW_supp {R : Type} [CommRing R] (LL : LiftLetters (Fin N)) (mu : Fin (N + 1) → Fin (r + K) → ℤ) (c : ℤ)
    (H : ColOK LL mu c) (j : ℕ) (hj : j ≤ N) :
    ∀ J, SgW R LL mu c j J ≠ 0 →
      (1 ≤ c → J.card = colH (mu ⟨j, by omega⟩) c ∧
        (r ≤ colH (mu ⟨j, by omega⟩) c → ∀ a : Fin (r + K), a.val < r → a ∈ J) ∧
        (colH (mu ⟨j, by omega⟩) c ≤ r → ∀ a ∈ J, a.val < r)) ∧
      (¬ 1 ≤ c → ∀ a ∈ J, r ≤ a.val) := by
  classical
  induction j with
  | zero =>
    intro J hJ
    have : J = ∅ := by
      by_contra hne; exact hJ (by simp only [SgW]; unfold extOne; rw [if_neg hne])
    subst this
    refine ⟨fun hc => ⟨by rw [H.start hc]; simp, fun hr a ha => ?_, by simp⟩, by simp⟩
    rw [H.start hc] at hr; omega
  | succ j ih =>
    intro J hJ
    have h : j < N := hj
    have ih' := ih (by omega)
    simp only [SgW, dif_pos h] at hJ
    unfold colStep at hJ
    have hci := costly_iff mu c j h
    split_ifs at hJ with h1 h2 h3 h4
    ·
      obtain ⟨hv, hN⟩ := H.rise j h h1
      obtain ⟨m, hm, hn, hK⟩ := wedgeR_ne _ _ _ hJ
      have hc := nomL_ne LL mu c _ m hn
      obtain ⟨hcard, hA, hB⟩ := (ih' _ hK).1 h2
      have hmr : r ≤ m.val ↔ r ≤ colH (mu ⟨j, by omega⟩) c := by
        rw [hci] at hc; unfold condUS at hc; simp only [hv, true_and] at hc
        constructor
        · intro hh; rcases hc.mp (Or.inl hh) with ⟨_, x⟩ | ⟨x, _⟩ <;> omega
        · intro hh; rcases hc.mpr (Or.inl ⟨h1, hh⟩) with x | ⟨x, _⟩
          · exact x
          · exact absurd x (by simp)
      have hcJ : J.card = colH (mu ⟨j + 1, by omega⟩) c := by
        rw [Finset.card_erase_of_mem hm] at hcard
        have := Finset.card_pos.mpr ⟨m, hm⟩; omega
      have hsub : colH (mu ⟨j, by omega⟩) c < r → ∀ a ∈ J, a.val < r := by
        intro hlt a ha
        by_cases ham : a = m
        · subst ham; by_contra hh; have := hmr.mp (by omega); omega
        · exact hB (by omega) a (Finset.mem_erase.mpr ⟨ham, ha⟩)
      refine ⟨fun _ => ⟨hcJ, fun hr a ha => ?_, fun hr => hsub (by omega)⟩, fun hc' => absurd h2 hc'⟩
      by_cases hr' : r ≤ colH (mu ⟨j, by omega⟩) c
      · exact Finset.mem_of_mem_erase (hA hr' a ha)
      · have hs := hsub (by omega)
        have : J = univ.filter fun a : Fin (r + K) => a.val < r := by
          refine Finset.eq_of_subset_of_card_le (fun a ha => by simpa using hs a ha) ?_
          rw [plane_card]; omega
        rw [this]; simpa using ha
    ·
      obtain ⟨hv, hN⟩ := H.rise j h h1
      obtain ⟨m, hm, hn, hK⟩ := contrR_ne _ _ _ hJ
      exact ⟨fun hc' => absurd hc' h2, fun _ a ha => (ih' _ hK).2 h2 a (Finset.mem_insert_of_mem ha)⟩
    ·
      obtain ⟨hv, hP⟩ := H.fall j h h3
      obtain ⟨m, hm, hn, hK⟩ := contrR_ne _ _ _ hJ
      have hc := nomL_ne LL mu c _ m hn
      obtain ⟨hcard, hA, hB⟩ := (ih' _ hK).1 h4
      have hmr : m.val < r ↔ colH (mu ⟨j, by omega⟩) c ≤ r := by
        rw [hci] at hc; unfold condUS at hc; simp only [hv, true_and] at hc
        constructor
        · intro hh; rcases hc.mp (Or.inr hh) with ⟨x, _⟩ | ⟨_, x⟩ <;> omega
        · intro hh; rcases hc.mpr (Or.inr ⟨h3, hh⟩) with ⟨x, _⟩ | x
          · exact absurd x (by simp)
          · exact x
      have hcJ : J.card = colH (mu ⟨j + 1, by omega⟩) c := by
        rw [Finset.card_insert_of_notMem hm] at hcard; omega
      have hsup : r < colH (mu ⟨j, by omega⟩) c → ∀ a : Fin (r + K), a.val < r → a ∈ J := by
        intro hlt a ha
        have := hA (by omega) a ha
        rcases Finset.mem_insert.mp this with e | e
        · subst e; have := hmr.mp ha; omega
        · exact e
      refine ⟨fun _ => ⟨hcJ, fun hr => hsup (by omega), fun hr a ha => ?_⟩, fun hc' => absurd h4 hc'⟩
      by_cases hr' : colH (mu ⟨j, by omega⟩) c ≤ r
      · exact hB hr' a (Finset.mem_insert_of_mem ha)
      · have hs := hsup (by omega)
        have : (univ.filter fun a : Fin (r + K) => a.val < r) = J := by
          refine Finset.eq_of_subset_of_card_le (fun a ha => hs a (by simpa using ha)) ?_
          rw [plane_card]; omega
        rw [← this] at ha; simpa using ha
    ·
      obtain ⟨hv, hP⟩ := H.fall j h h3
      obtain ⟨m, hm, hn, hK⟩ := wedgeR_ne _ _ _ hJ
      have hc := nomL_ne LL mu c _ m hn
      have hd := H.dual h4 j (by omega)
      refine ⟨fun hc' => absurd hc' h4, fun _ a ha => ?_⟩
      by_cases ham : a = m
      · subst ham
        by_contra hh
        rw [hci] at hc; unfold condUS at hc
        rcases hc.mp (Or.inr ⟨hv, by omega⟩) with ⟨x, _⟩ | ⟨_, x⟩ <;> omega
      · exact (ih' _ hK).2 h4 a (Finset.mem_erase.mpr ⟨ham, ha⟩)
    ·
      have e : colH (mu ⟨j + 1, by omega⟩) c = colH (mu ⟨j, by omega⟩) c := by omega
      rw [e]; exact ih' J hJ

lemma SgVanish_of (LL : LiftLetters (Fin N)) (mu : Fin (N + 1) → Fin (r + K) → ℤ) (c : ℤ)
    (H : ColOK LL mu c) : SgVanish LL mu c := by
  intro j h hc m hm J
  rw [costly_iff] at hc
  unfold condUS at hm
  refine ⟨fun hw hmJ => ?_, fun hw hmJ => ?_⟩
  · by_contra hne
    have hs := SgW_supp LL mu c H j (by omega) _ hne
    rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain ⟨hv, _⟩ := H.rise j h h1
      have hmr : m.val < r := by by_contra hh; exact hm (Or.inl ⟨hv, by omega⟩)
      have hr : r ≤ colH (mu ⟨j, by omega⟩) c := by rcases hc with ⟨_, x⟩ | ⟨x, _⟩ <;> omega
      exact (Finset.notMem_erase m J) ((hs.1 h2).2.1 hr m hmr)
    · have := H.dual h2 j (by omega)
      rcases hc with ⟨x, _⟩ | ⟨_, x⟩ <;> omega
  · by_contra hne
    have hs := SgW_supp LL mu c H j (by omega) _ hne
    rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · obtain ⟨hv, _⟩ := H.rise j h h1
      have hmr : m.val < r := by by_contra hh; exact hm (Or.inl ⟨hv, by omega⟩)
      have := hs.2 h2 m (Finset.mem_insert_self m J); omega
    · obtain ⟨hv, _⟩ := H.fall j h h1
      have hmr : ¬ m.val < r := fun hh => hm (Or.inr ⟨hv, hh⟩)
      have hr : colH (mu ⟨j, by omega⟩) c ≤ r := by rcases hc with ⟨x, _⟩ | ⟨_, x⟩ <;> omega
      exact hmr ((hs.1 h2).2.2 hr m (Finset.mem_insert_self m J))

end Col

end Formalism.MainNotions.LemmaBAlt
