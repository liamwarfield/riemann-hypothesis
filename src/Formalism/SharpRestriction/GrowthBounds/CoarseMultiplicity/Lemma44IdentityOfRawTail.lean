module

public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.FTDefs
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SymmetricFamilySpan

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Lemma44IdentityOfRawTail
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

section Basic

variable {O : Type} [CommRing O] [IsDomain O] {σ : Type}

def wjSub (w : O) (j : ℕ) : Submodule O (MvPolynomial σ (KK O)) where
  carrier := {P | InWj w P j}
  add_mem' := by
    intro P Q hP hQ m
    obtain ⟨a, ha⟩ := hP m
    obtain ⟨b, hb⟩ := hQ m
    exact ⟨a + b, by rw [MvPolynomial.coeff_add, ha, hb, ← map_add (f := _), mul_add]⟩
  zero_mem' := fun m => ⟨0, by simp⟩
  smul_mem' := by
    intro c P hP m
    obtain ⟨a, ha⟩ := hP m
    exact ⟨c * a, by rw [coeff_smul, ha, Algebra.smul_def, ← map_mul]; congr 1; ring⟩

theorem inA_iff_wj (w : O) {P : MvPolynomial σ (KK O)} : InA (O := O) P ↔ InWj w P 0 := by
  unfold InA InWj
  simp only [pow_zero, one_mul]

theorem wj_smul_pow {w : O} {j : ℕ} {P : MvPolynomial σ (KK O)} (h : InWj w P j) (e : ℕ) :
    InWj w ((w ^ e) • P) (j + e) := by
  intro m
  obtain ⟨a, ha⟩ := h m
  exact ⟨a, by rw [coeff_smul, ha, Algebra.smul_def, ← map_mul]; congr 1; ring⟩

theorem wj_mono {w : O} {j j' : ℕ} (hj : j' ≤ j) {P : MvPolynomial σ (KK O)} (h : InWj w P j) : InWj w P j' := by
  intro m
  obtain ⟨a, ha⟩ := h m
  refine ⟨w ^ (j - j') * a, ?_⟩
  rw [ha, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hj]

theorem C_mul_eq_smul (a : O) (P : MvPolynomial σ (KK O)) : C (algebraMap O (KK O) a) * P = a • P := by
  rw [← smul_eq_C_mul, algebraMap_smul]

end Basic

section Clean

variable (X : Loc) [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [Algebra (WF X.p X.n') O] (w : O)
  (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'))

def cleanSub (o : ℕ) : Submodule O (MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) (KK O)) where
  carrier := {F | IsCleanAwayFromPlane X O w g o F}
  add_mem' := by
    rintro F G ⟨h1, h2, h3⟩ ⟨k1, k2, k3⟩
    refine ⟨Submodule.add_mem _ h1 k1, ?_, fun g' hg' hne => ?_⟩
    · rw [mul_add, inA_iff_wj w]
      exact (wjSub w 0).add_mem ((inA_iff_wj w).1 h2) ((inA_iff_wj w).1 k2)
    · unfold InWjRg
      rw [map_add (f := _)]
      exact (wjSub w X.c).add_mem (h3 g' hg' hne) (k3 g' hg' hne)
  zero_mem' := by
    refine ⟨Submodule.zero_mem _, ?_, fun g' _ _ => ?_⟩
    · rw [mul_zero]; exact fun m => ⟨0, by simp⟩
    · unfold InWjRg
      rw [map_zero]
      exact (wjSub w X.c).zero_mem
  smul_mem' := by
    rintro a F ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, fun g' hg' hne => ?_⟩
    · rw [← algebraMap_smul (KK O) a F]
      exact Submodule.smul_mem _ _ h1
    · rw [mul_smul_comm, inA_iff_wj w]
      exact (wjSub w 0).smul_mem a ((inA_iff_wj w).1 h2)
    · unfold InWjRg
      rw [AlgHom.map_smul_of_tower]
      exact (wjSub w X.c).smul_mem a (h3 g' hg' hne)

variable {X O w g}

theorem clean_mono {o o' : ℕ} (h : o ≤ o') {F : MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) (KK O)}
    (hF : IsCleanAwayFromPlane X O w g o F) : IsCleanAwayFromPlane X O w g o' F := by
  refine ⟨hF.1, ?_, hF.2.2⟩
  have h2 := hF.2.1
  rw [C_mul_eq_smul, inA_iff_wj w] at h2 ⊢
  have : (w ^ o') • F = (w ^ (o' - o)) • ((w ^ o) • F) := by
    rw [smul_smul, ← pow_add, Nat.sub_add_cancel h]
  rw [this]
  exact (wjSub w 0).smul_mem _ h2

theorem clean_smul_pow {o e : ℕ} {F : MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) (KK O)}
    (hF : IsCleanAwayFromPlane X O w g (o + e) F) : IsCleanAwayFromPlane X O w g o ((w ^ e) • F) := by
  refine ⟨?_, ?_, fun g' hg' hne => ?_⟩
  · rw [← algebraMap_smul (KK O) (w ^ e) F]
    exact Submodule.smul_mem _ _ hF.1
  · have h2 := hF.2.1
    rw [C_mul_eq_smul] at h2 ⊢
    rwa [smul_smul, ← pow_add]
  · unfold InWjRg
    rw [AlgHom.map_smul_of_tower]
    exact (wjSub w X.c).smul_mem _ (hF.2.2 g' hg' hne)

end Clean

section Multi

variable {O : Type} [CommRing O] [IsDomain O] {C0 CE1 CE2 : ℝ} {X : Loc}

theorem ioBlock_add (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m)
    (u v : MvPolynomial (BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t) (KK O)) :
    ioBlock (KK O) X.p C0 CE1 CE2 X j b (u + v) =
      ioBlock (KK O) X.p C0 CE1 CE2 X j b u + ioBlock (KK O) X.p C0 CE1 CE2 X j b v := by
  unfold ioBlock
  rw [map_add (f := _), mul_add]

theorem symFam_span (β : GlobalTheory X)
    (G : ∀ j : Fin (numSeg X.TT), Set (MvPolynomial (BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t) (KK O)))
    (M : Submodule O (MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) (KK O)))
    (hM : ∀ s : Syms O C0 CE1 CE2 X, (∀ j, s j ∈ G j) → symFam (KK O) X.p C0 CE1 CE2 X β s ∈ M)
    (s : Syms O C0 CE1 CE2 X) (hs : ∀ j, s j ∈ Submodule.span O (G j)) :
    symFam (KK O) X.p C0 CE1 CE2 X β s ∈ M :=
  _root_.UpperTheory.Reformulated.B.SymmetricFamilySpan.symFam_span β G M hM s hs

end Multi

theorem ssg_int {O : Type} [CommRing O] [IsDomain O] {C0 Cde CE1 CE2 : ℝ} {X : Loc} [NeZero X.m] {mu E : ℝ} {o : ℕ}
    (w : O) {σ : MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) (KK O)} (h : σ ∈ SSg O C0 Cde CE1 CE2 X mu E o) :
    InWj w σ 0 := by
  have : SSg O C0 Cde CE1 CE2 X mu E o ≤ wjSub w 0 := by
    refine Submodule.span_le.2 ?_
    rintro σ ⟨β, _, _, s, hs, rfl⟩
    exact (inA_iff_wj w).1 (symIntAt C0 CE1 CE2 X O mu β s fun j => Submodule.subset_span (hs j))
  exact this h

theorem t44 {C0 Cde CE1 CE2 : ℝ}
    (X : Loc) [NeZero X.m] [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O) (mm : ℝ)
    (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n')) (hRT : RawTailBody C0 Cde CE1 CE2 X O S.w mm g) :
    ∀ n : ℕ, n ≤ X.c → ∀ (o : ℕ),
      ∀ σ ∈ SSg O C0 Cde CE1 CE2 X (mm + (n : ℝ) * ka1 X) (((X.c - n : ℕ) : ℝ) * ka1 X) o,
      ∃ F, IsCleanAwayFromPlane X O S.w g o F ∧ InWj S.w (liftSubst X.p X.n' O S.w 1 (hhLetters X.TT) g F - σ) n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn o σ hσ
    rcases Nat.eq_zero_or_pos n with rfl | hn1
    · refine ⟨0, (cleanSub X O S.w g o).zero_mem, ?_⟩
      rw [map_zero, zero_sub]
      exact (wjSub S.w 0).neg_mem (ssg_int S.w hσ)
    ·
      let M : Submodule O (MvPolynomial ((X.TT × Bool) × Fin (X.m + 1)) (KK O)) :=
        { carrier := {σ | ∃ F, IsCleanAwayFromPlane X O S.w g o F ∧
            InWj S.w (liftSubst X.p X.n' O S.w 1 (hhLetters X.TT) g F - σ) n}
          add_mem' := by
            rintro σ σ' ⟨F, hF, hFσ⟩ ⟨F', hF', hFσ'⟩
            refine ⟨F + F', (cleanSub X O S.w g o).add_mem hF hF', ?_⟩
            rw [map_add (f := _), add_sub_add_comm]
            exact (wjSub S.w n).add_mem hFσ hFσ'
          zero_mem' := by
            refine ⟨0, (cleanSub X O S.w g o).zero_mem, ?_⟩
            rw [map_zero, sub_zero]
            exact (wjSub S.w n).zero_mem
          smul_mem' := by
            rintro a σ ⟨F, hF, hFσ⟩
            refine ⟨a • F, (cleanSub X O S.w g o).smul_mem a hF, ?_⟩
            rw [AlgHom.map_smul_of_tower, ← smul_sub]
            exact (wjSub S.w n).smul_mem a hFσ }
      have hle : SSg O C0 Cde CE1 CE2 X (mm + (n : ℝ) * ka1 X) (((X.c - n : ℕ) : ℝ) * ka1 X) o ≤ M := by
        refine Submodule.span_le.2 ?_
        rintro σ ⟨β, hβ, ho, s, hs, rfl⟩
        obtain ⟨raw, τ, hraw, hτ, hcong⟩ := hRT n hn1 hn β hβ s hs
        have hF : ∀ ε ∈ Finset.Ico 1 n, ∃ F, IsCleanAwayFromPlane X O S.w g (ordFam C0 CE1 CE2 X β + ε) F ∧
            InWj S.w (liftSubst X.p X.n' O S.w 1 (hhLetters X.TT) g F - τ ε) (n - ε) := by
          intro ε hε
          have h1 := (Finset.mem_Ico.1 hε).1
          have h2 := (Finset.mem_Ico.1 hε).2
          exact ih (n - ε) (by omega) (by omega) _ _ (hτ ε hε)
        choose! Fe hFe1 hFe2 using hF
        refine ⟨raw - ∑ ε ∈ Finset.Ico 1 n, (S.w ^ ε) • Fe ε, ?_, ?_⟩
        · refine clean_mono ho ((cleanSub X O S.w g _).sub_mem hraw ?_)
          exact (cleanSub X O S.w g _).sum_mem fun ε hε => clean_smul_pow (hFe1 ε hε)
        · have e1 : liftSubst X.p X.n' O S.w 1 (hhLetters X.TT) g (raw - ∑ ε ∈ Finset.Ico 1 n, (S.w ^ ε) • Fe ε) -
              symFam (KK O) X.p C0 CE1 CE2 X β s =
              (liftSubst X.p X.n' O S.w 1 (hhLetters X.TT) g raw - symFam (KK O) X.p C0 CE1 CE2 X β s -
                ∑ ε ∈ Finset.Ico 1 n, (S.w ^ ε) • τ ε) -
              ∑ ε ∈ Finset.Ico 1 n, (S.w ^ ε) • (liftSubst X.p X.n' O S.w 1 (hhLetters X.TT) g (Fe ε) - τ ε) := by
            set_option synthInstance.maxHeartbeats 100000 in
              rw [map_sub, map_sum]
            simp only [AlgHom.map_smul_of_tower, smul_sub, Finset.sum_sub_distrib]
            ring
          rw [e1]
          refine (wjSub S.w n).sub_mem hcong ((wjSub S.w n).sum_mem fun ε hε => ?_)
          have h2 := (Finset.mem_Ico.1 hε).2
          have := wj_smul_pow (hFe2 ε hε) ε
          rwa [Nat.sub_add_cancel h2.le] at this
      exact hle hσ

theorem lemma44_at_body {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ} (hK : KeptBLAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc)
    (X : Loc) [NeZero X.m] [Fact X.p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra (WF X.p X.n') O] (S : UniformizedDVR X.p O) (hD : D1num X) (hH : HIext C0 CYb Cde Ck CD Cb X)
    (hc : CBound Cc X) (mm : ℝ) (g : Matrix (Fin (X.m + 1)) (Fin (X.m + 1)) (WF X.p X.n'))
    (hRT : RawTailBody C0 Cde CE1 CE2 X O S.w mm g) (β : GlobalTheory X) (hβ : KeptAll C0 CE1 CE2 X β)
    (s : Syms O C0 CE1 CE2 X) (hs : InSSZ O C0 CE1 CE2 (13 * X.k * X.N1 * X.Q * (X.c : ℝ) + mm) X β s) :
    ∃ F, IsCleanAwayFromPlane X O S.w g (ordFam C0 CE1 CE2 X β) F ∧
      InWj S.w (liftSubst X.p X.n' O S.w 1 (hhLetters X.TT) g F - symFam (KK O) X.p C0 CE1 CE2 X β s) X.c := by
  have hmar : 13 * X.k * X.N1 * X.Q * (X.c : ℝ) + mm = mm + (X.c : ℝ) * ka1 X := by
    unfold ka1; ring
  rw [hmar] at hs
  have hσ : symFam (KK O) X.p C0 CE1 CE2 X β s ∈ SSg O C0 Cde CE1 CE2 X (mm + (X.c : ℝ) * ka1 X)
      (((X.c - X.c : ℕ) : ℝ) * ka1 X) (ordFam C0 CE1 CE2 X β) := by
    refine symFam_span β (fun j => genSet O (r := X.m)
      (blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j)
        (mm + (X.c : ℝ) * ka1 X) (β j))) _ (fun s' hs' => ?_) s hs
    refine Submodule.subset_span ⟨β, fun j => ?_, le_rfl, s', hs', rfl⟩
    rw [Nat.sub_self, Nat.cast_zero, zero_mul]
    exact hK X hD hH hc j (β j) (hβ j)
  exact t44 X O S mm g hRT X.c le_rfl _ _ hσ

theorem lemma44_identity_of_raw_tail {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ} (hRT : RawTailAt1 C0 CYb Cde Ck CD Cb CE1 CE2 Cc)
    (hK : KeptBLAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) : CoarseMultiplicityAtIdentity C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  intro X _ _ O _ _ _ _ S hSq hD hH hc mm hmm β hβ s hs
  obtain ⟨F, hF, hcong⟩ := lemma44_at_body hK X O S hD hH hc mm 1 (hRT X O S hSq hD hH hc mm hmm) β hβ s hs
  exact ⟨F, hF.1, hF.2.1, hcong, hF.2.2⟩

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.FtFockZeroLeft
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory MvPolynomial

theorem ft_fock_zero_left {K : Type} [CommSemiring K] {σ : Type} (G : MvPolynomial σ K) :
    fock (0 : MvPolynomial σ K) G = 0 := by
  simp [fock]

theorem fock_add_left {K : Type} [Field K] {σ : Type} (F F' G : MvPolynomial σ K) :
    fock (F + F') G = fock F G + fock F' G := by
  classical
  have key : ∀ (H : MvPolynomial σ K) (s : Finset (σ →₀ ℕ)), H.support ⊆ s →
      fock H G = ∑ m ∈ s, H.coeff m * G.coeff m * (expFact m : K) := by
    intro H s hs
    unfold fock
    refine Finset.sum_subset hs fun m _ hm => ?_
    rw [MvPolynomial.notMem_support_iff.1 hm, zero_mul, zero_mul]
  have hsub : (F + F').support ⊆ F.support ∪ F'.support := MvPolynomial.support_add
  rw [key _ _ hsub, key F (F.support ∪ F'.support) Finset.subset_union_left,
    key F' (F.support ∪ F'.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_add]
  ring

theorem prod_add_mul {O ι : Type} [CommRing O] (s : Finset ι) (a x : ι → O) (t : O) :
    ∃ Y : O, ∏ i ∈ s, (a i + t * x i) = ∏ i ∈ s, a i + t * Y := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert j s hj ih =>
    obtain ⟨Y, hY⟩ := ih
    refine ⟨x j * ∏ i ∈ s, a i + a j * Y + t * x j * Y, ?_⟩
    rw [Finset.prod_insert hj, Finset.prod_insert hj, hY]
    ring

theorem segForm_single {O : Type} [CommRing O] [IsDomain O] (p r : ℕ) {s : ℕ} (S : SegData s)
    (u u' : SegVs O r s S.t) (b0 : SegBlock s r) (h : ∀ b, b ≠ b0 → u b = 0) :
    segForm O p r S u u' = ((specConst p S b0 : ℕ) : KK O) * fock (u b0) (u' b0) := by
  unfold segForm
  rw [finsum_eq_single _ b0]
  intro b hb
  rw [h b hb, ft_fock_zero_left, mul_zero]

theorem vLEO_mono {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {p : ℕ} {x : O} {D D' : ℝ}
    (h : vLEO p x D) (hD : D ≤ D') : vLEO p x D' := by
  obtain ⟨q, hq, hqD⟩ := h
  exact ⟨q, hq, hqD.trans hD⟩

theorem vLEO_one {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {p : ℕ} {w : O} (hw : Irreducible w)
    (h2 : w ^ 2 = (p : O)) {D : ℝ} (hD : 0 ≤ D) : vLEO p (1 : O) D := by
  refine ⟨0, ?_, by simpa using hD⟩
  unfold vO vK ordW
  rw [map_one, if_neg one_ne_zero]
  have hspec := Classical.choose_spec (IsLocalization.surj (nonZeroDivisors O) (1 : KK O))
  rw [one_mul] at hspec
  have heq : ((Classical.choose (IsLocalization.surj (nonZeroDivisors O) (1 : KK O))).2 : O) =
      (Classical.choose (IsLocalization.surj (nonZeroDivisors O) (1 : KK O))).1 :=
    IsFractionRing.injective O (KK O) hspec
  dsimp only
  rw [heq, sub_self]
  simp

theorem famOK_mem {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {C0 CE1 CE2 Cm : ℝ} {X : Loc}
    [NeZero X.m] {β : GlobalTheory X} {u : Vecs O C0 CE1 CE2 X} (hβ : KeptAll C0 CE1 CE2 X β) (hu : FamOK O C0 CE1 CE2 Cm X β u)
    (j : Fin (numSeg X.TT)) :
    u j (β j) ∈ blockLat O X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (X.m0 Cm) (β j) := by
  have h := (Submodule.mem_pi.1 (hu j).1) (β j) (Set.mem_univ _)
  rwa [if_pos (hβ j)] at h

theorem formAt_of {C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc : ℝ}
    (hstd : ∀ X : Loc, D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X → Std C0 Cde CE1 CE2 1 X)
    (hB : BlockFormAt C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc) (h1 : OrthAt C0 CE1 CE2) (h2 : ProdAt C0 CE1 CE2)
    (h3 : SymPolAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) (h4 : IntAt) (h5 : NumAt C0 Cde CE1 CE2) (h6 : ZProdAt) :
    FormAt C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc := by
  classical
  intro X _ W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ jO w hS hH hc hc1
  have hD1 : D1num X := ⟨hS.1.prime, hS.1.five_le, hS.1.two_le, hS.1.even⟩
  have St := hstd X hD1 hH hc
  have hw : Irreducible w := hS.2.1
  have hw2 : w ^ 2 = (X.p : O) := hS.1.w_sq
  have hBX := hB X W Qq O Kf ι σ jO w hS hH hc hc1
  have hex : ∀ (j : Fin (numSeg X.TT)) (b : SegBlock (segS X.TT j) X.m),
      ∃ (κ : O) (s s' : MvPolynomial (BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t) (KK O) →
          MvPolynomial (BVar (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t) (KK O)),
        κ ≠ 0 ∧ vLEO X.p κ (((X.m + 2) * lgSeg X j : ℕ) : ℝ) ∧
        (Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b →
        (∀ u ∈ blockLat O X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (X.m0 Cm) b,
          s u ∈ (blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (X.m0 13) b).SSZ O
            (r := X.m) ∧
          s' u ∈ (blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (X.m0 13) b).SSZ O
            (r := X.m)) ∧
        ∀ u ∈ blockLat O X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (X.m0 Cm) b,
        ∀ u' ∈ blockLat O X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (X.m0 Cm) b,
        ∀ a : O, ((specConst X.p (X.seg C0 CE1 CE2 j) b : ℕ) : KK O) * fock u u' = algebraMap O (KK O) a →
          ∃ x : O, zSeg (KK O) X j * fock (ioBlock (KK O) X.p C0 CE1 CE2 X j b (s u))
              (ioBlock (KK O) X.p C0 CE1 CE2 X j b (s' u')) = algebraMap O (KK O) (κ * (a + w ^ X.c * x))) := by
    intro j b
    by_cases hk : Kept X.p X.m (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) b
    · obtain ⟨κ, s, s', a1, a2, a3, a4⟩ := hBX j b hk
      exact ⟨κ, s, s', a1, a2, fun _ => ⟨a3, a4⟩⟩
    · exact ⟨1, id, id, one_ne_zero, vLEO_one hw hw2 (Nat.cast_nonneg _), fun h => absurd h hk⟩
  choose κb sb sb' hκ0 hκv hK using hex
  refine ⟨fun β => ∏ j, κb j (β j), fun β u j => sb j (β j) (u j (β j)), fun β u j => sb' j (β j) (u j (β j)),
    ?_, ?_, ?_⟩
  · intro β
    have hp := vLEO_prod hw hw2 Finset.univ (fun j => κb j (β j)) (fun j => (((X.m + 2) * lgSeg X j : ℕ) : ℝ))
      fun j _ => ⟨hκ0 j (β j), hκv j (β j)⟩
    exact ⟨hp.1, vLEO_mono hp.2 (h5 X St)⟩
  · intro β u hβ hu
    exact ⟨fun j => ((hK j (β j) (hβ j)).1 _ (famOK_mem hβ hu j)).1,
      fun j => ((hK j (β j) (hβ j)).1 _ (famOK_mem hβ hu j)).2⟩
  · intro β u β' u' hβ hβ' hu hu' a ha P hP Q hQ hPc hQc
    have hs1 : InSSZ O C0 CE1 CE2 (X.m0 13) X β (fun j => sb j (β j) (u j (β j))) :=
      fun j => ((hK j (β j) (hβ j)).1 _ (famOK_mem hβ hu j)).1
    have hs2 : InSSZ O C0 CE1 CE2 (X.m0 13) X β' (fun j => sb' j (β' j) (u' j (β' j))) :=
      fun j => ((hK j (β' j) (hβ' j)).1 _ (famOK_mem hβ' hu' j)).2
    set σ₁ := symFam (KK O) X.p C0 CE1 CE2 X β (fun j => sb j (β j) (u j (β j))) with hσ₁
    set σ₂ := symFam (KK O) X.p C0 CE1 CE2 X β' (fun j => sb' j (β' j) (u' j (β' j))) with hσ₂
    have hσ1P := h3 X O hD1 hH hc _ β hβ _ hs1
    have hσ2P := h3 X O hD1 hH hc _ β' hβ' _ hs2
    have hσ1I : InA (O := O) σ₁ := symIntAt C0 CE1 CE2 X O _ β _ hs1
    have hσ2I : InA (O := O) σ₂ := symIntAt C0 CE1 CE2 X O _ β' _ hs2
    have hPI : InA (O := O) P := by
      intro mm
      obtain ⟨c1, e1⟩ := hσ1I mm
      obtain ⟨c2, e2⟩ := hPc mm
      refine ⟨c1 + w ^ X.c * c2, ?_⟩
      rw [map_add (f := _), ← e1, ← e2, coeff_sub]
      ring
    obtain ⟨y1, hy1⟩ := h4 X.p O hS.1.prime (dvrOfStd hS) w X.n' X.m X.TT X.aT X.bT (P - σ₁)
      (Submodule.sub_mem _ hP hσ1P) σ₂ X.c hPc hσ2I
    obtain ⟨y2, hy2⟩ := h4 X.p O hS.1.prime (dvrOfStd hS) w X.n' X.m X.TT X.aT X.bT (Q - σ₂)
      (Submodule.sub_mem _ hQ hσ2P) P X.c hQc hPI
    have hdec : fock P Q = fock σ₁ σ₂ + fock (P - σ₁) σ₂ + fock (Q - σ₂) P := by
      have e1 : fock P Q = fock P σ₂ + fock P (Q - σ₂) := by
        rw [← fock_form_add_right]
        congr 1
        ring
      have e2 : fock P σ₂ = fock σ₁ σ₂ + fock (P - σ₁) σ₂ := by
        rw [← fock_add_left]
        congr 1
        ring
      rw [e1, e2, fock_form_symm P (Q - σ₂)]
    have hmain : ∃ ν0 : O, zTen (KK O) X.p X.m X.TT X.aT X.bT * fock σ₁ σ₂ =
        algebraMap O (KK O) ((if β = β' then (∏ j, κb j (β j)) * ∏ j, a j else 0) + w ^ X.c * ν0) := by
      rw [hσ₁, hσ₂, h2 X (KK O) St.seg2 β β' _ _, h6 X (KK O) St.seg2, ← Finset.prod_mul_distrib]
      by_cases hββ : β = β'
      · subst hββ
        have hx : ∀ j, ∃ x : O, zSeg (KK O) X j * fock (ioBlock (KK O) X.p C0 CE1 CE2 X j (β j) (sb j (β j) (u j (β j))))
            (ioBlock (KK O) X.p C0 CE1 CE2 X j (β j) (sb' j (β j) (u' j (β j)))) =
            algebraMap O (KK O) (κb j (β j) * (a j + w ^ X.c * x)) := fun j =>
          (hK j (β j) (hβ j)).2 _ (famOK_mem hβ hu j) _ (famOK_mem hβ hu' j) (a j) (by
            rw [← ha j, segForm_single X.p X.m (X.seg C0 CE1 CE2 j) (u j) (u' j) (β j) (hu j).2])
        choose x hx using hx
        obtain ⟨Y, hY⟩ := prod_add_mul Finset.univ a x (w ^ X.c)
        refine ⟨(∏ j, κb j (β j)) * Y, ?_⟩
        rw [Finset.prod_congr rfl (fun j _ => hx j), ← map_prod, Finset.prod_mul_distrib, hY, if_pos rfl]
        congr 1
        ring
      · obtain ⟨j0, hj0⟩ := Function.ne_iff.mp hββ
        refine ⟨0, ?_⟩
        rw [Finset.prod_eq_zero (Finset.mem_univ j0) (by
          rw [h1 X O _ hD1 j0 _ _ (hβ j0) (hβ' j0) hj0 _ (hs1 j0) _ (hs2 j0), mul_zero]), if_neg hββ]
        simp
    obtain ⟨ν0, h0⟩ := hmain
    refine ⟨ν0 + y1 + y2, ?_⟩
    rw [hdec, mul_add, mul_add, h0, hy1, hy2, ← map_add (f := _), ← map_add (f := _)]
    congr 1
    ring

def RestSymPol : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => SymPolAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc

theorem restForm_of' (hB : RestBlockForm) (h1 : ∀ C0 CE1 CE2, OrthAt C0 CE1 CE2) (h2 : ∀ C0 CE1 CE2, ProdAt C0 CE1 CE2)
    (h3 : RestSymPol) (h4 : IntAt) (h5 : ∀ C0 Cde CE1 CE2, NumAt C0 Cde CE1 CE2) (h6 : ZProdAt) : RestForm := by
  intro Cc hCc
  obtain ⟨A0, hA0, hA⟩ := thr_std Cc hCc
  obtain ⟨B0, hB0, hBB⟩ := hB Cc hCc
  obtain ⟨S0, hS0, hS⟩ := h3 Cc hCc
  refine ⟨max A0 (max B0 S0), lt_max_of_lt_left hA0, fun C0 hC0 => ?_⟩
  obtain ⟨A1, hA1, hA'⟩ := hA C0 ((le_max_left _ _).trans hC0)
  obtain ⟨B1, hB1, hBB'⟩ := hBB C0 (((le_max_left _ _).trans (le_max_right _ _)).trans hC0)
  obtain ⟨S1, hS1, hS'⟩ := hS C0 (((le_max_right _ _).trans (le_max_right _ _)).trans hC0)
  refine ⟨max A1 (max B1 S1), lt_max_of_lt_left hA1, fun CE1 CE2 Cm hE1 hE2 hm => ?_⟩
  have l1 : A1 ≤ max A1 (max B1 S1) := le_max_left _ _
  have l2 : B1 ≤ max A1 (max B1 S1) := (le_max_left _ _).trans (le_max_right _ _)
  have l3 : S1 ≤ max A1 (max B1 S1) := (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨A2, hA2, hA''⟩ := hA' CE1 CE2 Cm (l1.trans hE1) (l1.trans hE2) (l1.trans hm)
  obtain ⟨B2, hB2, hBB''⟩ := hBB' CE1 CE2 Cm (l2.trans hE1) (l2.trans hE2) (l2.trans hm)
  obtain ⟨S2, hS2, hS''⟩ := hS' CE1 CE2 Cm (l3.trans hE1) (l3.trans hE2) (l3.trans hm)
  refine ⟨max A2 (max B2 S2), lt_max_of_lt_left hA2, fun CYb Cde Ck CD Cb h₁ h₂ h₃ h₄ h₅ => ?_⟩
  have m1 : A2 ≤ max A2 (max B2 S2) := le_max_left _ _
  have m2 : B2 ≤ max A2 (max B2 S2) := (le_max_left _ _).trans (le_max_right _ _)
  have m3 : S2 ≤ max A2 (max B2 S2) := (le_max_right _ _).trans (le_max_right _ _)
  have hstd := (hA'' CYb Cde Ck CD Cb (m1.trans h₁) (m1.trans h₂) (m1.trans h₃) (m1.trans h₄) (m1.trans h₅)).2
  have hblk := hBB'' CYb Cde Ck CD Cb (m2.trans h₁) (m2.trans h₂) (m2.trans h₃) (m2.trans h₄) (m2.trans h₅)
  have hsym := hS'' CYb Cde Ck CD Cb (m3.trans h₁) (m3.trans h₂) (m3.trans h₃) (m3.trans h₄) (m3.trans h₅)
  exact formAt_of hstd hblk (h1 C0 CE1 CE2) (h2 C0 CE1 CE2) hsym h4 (h5 C0 Cde CE1 CE2) h6

end Formalism.MainNotions.ColumnSystems.Pf
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.DegSplit
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

theorem wh_smulO {O : Type} [CommRing O] [IsDomain O] {σ : Type} {ω : σ → ℕ} {x : MvPolynomial σ (KK O)} {n : ℕ} (c : O)
    (h : IsWeightedHomogeneous ω x n) : IsWeightedHomogeneous ω (c • x) n := by
  intro d hd
  apply h
  intro h0
  apply hd
  rw [MvPolynomial.coeff_smul, h0, smul_zero]

theorem wh_congr {K : Type} [CommRing K] {σ : Type} {ω : σ → ℕ} {x : MvPolynomial σ K} {n n' : ℕ}
    (h : IsWeightedHomogeneous ω x n) (e : n = n') : IsWeightedHomogeneous ω x n' := by
  exact e ▸ h

theorem wh_chain {K : Type} [CommRing K] {N r t : ℕ} (ω : BVar N r t → ℕ) (ωL : Fin (N + 1) → ℕ)
    (h1 : ∀ a c, ω (Sum.inl (a, c)) = ωL a) (deg : Fin N → ℕ) (y : MvPolynomial (Fin N × Fin r) K)
    (hy : y ∈ Pol K r deg) :
    IsWeightedHomogeneous ω (rename (chainEmb N r t) y) (∑ a, deg a * ωL (Fin.castSucc a)) := by
  classical
  have hinj : Function.Injective (chainEmb N r t) := by
    intro x y h
    simp only [chainEmb, Sum.inl.injEq, Prod.mk.injEq, Fin.castSucc_inj] at h
    exact Prod.ext h.1 h.2
  intro d hd
  have hd' : d ∈ (rename (chainEmb N r t) y).support := MvPolynomial.mem_support_iff.mpr hd
  rw [MvPolynomial.support_rename_of_injective hinj] at hd'
  obtain ⟨m1, hm1, rfl⟩ := Finset.mem_image.mp hd'
  unfold Pol at hy
  rw [MvPolynomial.mem_restrictSupport_iff] at hy
  have hdeg := hy hm1
  rw [Finsupp.weight_apply, Finsupp.sum_mapDomain_index (h := fun i (c : ℕ) => c • ω i) (fun _ => zero_smul _ _)
      (fun _ _ _ => add_smul _ _ _),
    Finsupp.sum_fintype m1 (fun a (m : ℕ) => m • ω (chainEmb N r t a)) (fun _ => zero_smul _ _), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← hdeg a]
  unfold multideg
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [smul_eq_mul]
  congr 1
  exact h1 _ _

theorem wh_xi {O : Type} [CommRing O] [IsDomain O] {N r t b' : ℕ} (ω : BVar N r t → ℕ) (ωL : Fin (N + 1) → ℕ)
    (h1 : ∀ a c, ω (Sum.inl (a, c)) = ωL a) (g : MvPolynomial (BVar N r t) (KK O)) (hg : g ∈ XiPolZ O N r t b') :
    IsWeightedHomogeneous ω g (b' * ωL (Fin.last N)) := by
  classical
  intro d hd
  have hg1 := (Submodule.mem_inf.mp hg).1
  rw [Submodule.restrictScalars_mem, MvPolynomial.mem_restrictSupport_iff] at hg1
  obtain ⟨hsupp, hsum⟩ := hg1 (MvPolynomial.mem_support_iff.mpr hd)
  have hinj : Function.Injective (xiVar N r t) := by
    intro a b h
    simp only [xiVar, Sum.inl.injEq, Prod.mk.injEq] at h
    exact h.2
  have hsub : d.support ⊆ Finset.univ.image (xiVar N r t) := by
    intro v hv
    obtain ⟨c, rfl⟩ := hsupp v hv
    exact Finset.mem_image_of_mem _ (Finset.mem_univ c)
  rw [Finsupp.weight_apply, Finsupp.sum_of_support_subset d hsub (fun i (c : ℕ) => c • ω i) (fun _ _ => zero_smul _ _),
    Finset.sum_image (fun a _ b _ h => hinj h), ← hsum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [smul_eq_mul]
  congr 1
  exact h1 _ _

variable {s r : ℕ}

def OmB (p : ℕ) (S : SegData s) (aTop : Fin s → ℕ) (aPlus : ℕ) (b : SegBlock s r) (ω : BVar (2 * s + 1) r S.t → ℕ)
    (ωL : Fin (2 * s + 1 + 1) → ℕ) : ℕ :=
  (∑ l : Fin S.t, (coarseA p S b (uTop S l) - b.o (uTop S l)) * ω (Sum.inr (Fin.castSucc l, false))) +
    (aPlus - b.oPlus) * ω (Sum.inr (Fin.last S.t, false)) +
    (∑ a : Fin (2 * s + 1), (segChain p S aTop b).deg a * ωL (Fin.castSucc a)) + S.bPlus * ωL (Fin.last _)

theorem deg_split (p : ℕ) (S : SegData s) (aTop : Fin s → ℕ) (aPlus : ℕ) (m : ℝ) (b : SegBlock s r)
    (jl : Fin S.t → ℕ) (jp : ℕ) (h : (blockData p S aTop aPlus m b).LevelOK jl jp) (a : Fin (2 * s + 1)) :
    (segChain p S aTop b).deg a = ((blockData p S aTop aPlus m b).lettersAt jl jp).deg a + jE S jl (a.val / 2) +
      (if a.val = 2 * s then jp else 0) := by
  have hb := level_bounds p S aTop aPlus m b jl jp h
  rw [lev_deg]
  have ha := a.2
  by_cases h2 : a.val = 2 * s
  · have q : a.val / 2 = s := by omega
    rw [if_pos h2, q, jE_top, chain_deg_U p S aTop b a h2]
    have := hb.2
    omega
  · rw [if_neg h2]
    have hi : a.val / 2 < s := by omega
    by_cases hs : a.val / 2 < S.sigma
    · rw [jE_S S jl hs]
      omega
    · have hb1 : jE S jl (a.val / 2) ≤ b.o ⟨a.val / 2, hi⟩ ∧ jE S jl (a.val / 2) ≤ coarseC p S aTop b ⟨a.val / 2, hi⟩ :=
        hb.1 ⟨a.val / 2, hi⟩ (by show S.sigma ≤ a.val / 2; omega)
      by_cases hpar : a.val % 2 = 0
      · rw [segment_chain_degree_even p S aTop b a ⟨a.val / 2, hi⟩ (by show a.val = 2 * (a.val / 2); omega), if_neg hs]
        have := hb1.1
        omega
      · rw [chain_deg_E p S aTop b a ⟨a.val / 2, hi⟩ (by show a.val = 2 * (a.val / 2) + 1; omega), if_neg hs]
        have := hb1.2
        omega

theorem tie_sum (S : SegData s) (jl : Fin S.t → ℕ) (ωL : Fin (2 * s + 1 + 1) → ℕ) :
    ∑ a : Fin (2 * s + 1), jE S jl (a.val / 2) * ωL (Fin.castSucc a) =
      ∑ l : Fin S.t, jl l * (ωL (finPos (2 * s + 1) (2 * (uTop S l : ℕ))) +
        ωL (finPos (2 * s + 1) (2 * (uTop S l : ℕ) + 1))) := by

  let e : Fin S.t × Fin 2 → Fin (2 * s + 1) := fun p =>
    ⟨2 * (S.sigma + p.1.val) + p.2.val, by
      have h1 := p.1.2
      have h2 := p.2.2
      simp only [SegData.t] at h1
      omega⟩
  have he : Function.Injective e := by
    rintro ⟨l, b⟩ ⟨l', b'⟩ h
    have hv : 2 * (S.sigma + l.val) + b.val = 2 * (S.sigma + l'.val) + b'.val := congrArg Fin.val h
    have := b.2
    have := b'.2
    exact Prod.ext (Fin.ext (show l.val = l'.val by omega)) (Fin.ext (show b.val = b'.val by omega))
  rw [← Fintype.sum_of_injective e he
    (fun p => jl p.1 * ωL (finPos (2 * s + 1) (2 * (uTop S p.1 : ℕ) + p.2.val))) _ ?_ ?_]
  · rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Fin.sum_univ_two, mul_add]
    simp
  · intro a ha
    unfold jE
    rw [dite_eq_right]
    · simp
    · rintro ⟨h1, h2⟩
      apply ha
      refine ⟨(⟨a.val / 2 - S.sigma, by simp only [SegData.t]; omega⟩, ⟨a.val % 2, by omega⟩), ?_⟩
      apply Fin.ext
      show 2 * (S.sigma + (a.val / 2 - S.sigma)) + a.val % 2 = a.val
      omega
  · rintro ⟨l, b⟩
    have hb := b.2
    have hl := l.2
    simp only [SegData.t] at hl
    have hdiv : (2 * (S.sigma + l.val) + b.val) / 2 = S.sigma + l.val := by omega
    simp only [e, hdiv]
    unfold jE
    rw [dite_eq_left ⟨by omega, by omega⟩]
    congr 1
    · congr 1
      apply Fin.ext
      simp
    · congr 1
      apply Fin.ext
      simp [finPos, uTop]
      omega

theorem ssz_wh (O : Type) [CommRing O] [IsDomain O] [NeZero r] (p : ℕ) (S : SegData s) (aTop : Fin s → ℕ) (aPlus : ℕ)
    (mm : ℝ) (b : SegBlock s r) (ω : BVar (2 * s + 1) r S.t → ℕ) (ωL : Fin (2 * s + 1 + 1) → ℕ)
    (h1 : ∀ a c, ω (Sum.inl (a, c)) = ωL a)
    (h2 : ∀ l : Fin S.t, ω (Sum.inr (Fin.castSucc l, false)) + ω (Sum.inr (Fin.castSucc l, true)) =
      ωL (finPos (2 * s + 1) (2 * (uTop S l : ℕ))) + ωL (finPos (2 * s + 1) (2 * (uTop S l : ℕ) + 1)))
    (h3 : ω (Sum.inr (Fin.last S.t, false)) + ω (Sum.inr (Fin.last S.t, true)) =
      ωL (Fin.castSucc ⟨2 * s, by omega⟩) + ωL (Fin.last _))
    (x : MvPolynomial (BVar (2 * s + 1) r S.t) (KK O)) (hx : x ∈ (blockData p S aTop aPlus mm b).SSZ O (r := r)) :
    IsWeightedHomogeneous ω x (OmB p S aTop aPlus b ω ωL) := by
  refine Submodule.span_induction (p := fun x _ => IsWeightedHomogeneous ω x (OmB p S aTop aPlus b ω ωL))
    ?_ ?_ ?_ ?_ hx
  · intro x hx
    obtain ⟨jl, hx⟩ := Set.mem_iUnion.1 hx
    obtain ⟨jp, hx⟩ := Set.mem_iUnion.1 hx
    obtain ⟨hlev, hx⟩ := Set.mem_iUnion.1 hx
    obtain ⟨y, hy, g, hg, rfl⟩ := hx
    have hE : ∀ l : Fin S.t, IsWeightedHomogeneous ω ((blockData p S aTop aPlus mm b).Ehat O (r := r) l)
        (ωL (finPos (2 * s + 1) (2 * (uTop S l : ℕ))) + ωL (finPos (2 * s + 1) (2 * (uTop S l : ℕ) + 1))) := by
      intro l
      refine IsWeightedHomogeneous.add ?_ (IsWeightedHomogeneous.sum _ _ _ fun c _ => ?_)
      · rw [← h2 l]
        exact (isWeightedHomogeneous_X _ ω _).mul (isWeightedHomogeneous_X _ ω _)
      · have := (isWeightedHomogeneous_X (KK O) ω (Sum.inl (finPos (2 * s + 1) (2 * (uTop S l : ℕ)), c))).mul
          (isWeightedHomogeneous_X (KK O) ω (Sum.inl (finPos (2 * s + 1) (2 * (uTop S l : ℕ) + 1), c)))
        rw [h1, h1] at this
        exact this
    have hEp : IsWeightedHomogeneous ω ((blockData p S aTop aPlus mm b).Eplus O (r := r))
        (ωL (Fin.castSucc ⟨2 * s, by omega⟩) + ωL (Fin.last _)) := by
      refine IsWeightedHomogeneous.add ?_ (IsWeightedHomogeneous.sum _ _ _ fun c _ => ?_)
      · rw [← h3]
        exact (isWeightedHomogeneous_X _ ω _).mul (isWeightedHomogeneous_X _ ω _)
      · have := (isWeightedHomogeneous_X (KK O) ω (Sum.inl (Fin.castSucc (⟨2 * s, by omega⟩ : Fin (2 * s + 1)), c))).mul
          (isWeightedHomogeneous_X (KK O) ω (Sum.inl (Fin.last (2 * s + 1), c)))
        rw [h1, h1] at this
        exact this
    have hA := IsWeightedHomogeneous.prod Finset.univ
      (fun l : Fin S.t => (blockData p S aTop aPlus mm b).Ehat O (r := r) l ^ jl l) _ (fun l _ => (hE l).pow (jl l))
    have hB := hEp.pow jp
    have hC := IsWeightedHomogeneous.prod Finset.univ
      (fun l : Fin S.t => (X (scalZ (2 * s + 1) r S.t (Fin.castSucc l)) : MvPolynomial (BVar (2 * s + 1) r S.t) (KK O)) ^
        (coarseA p S b (uTop S l) - b.o (uTop S l))) _ (fun l _ => (isWeightedHomogeneous_X (KK O) ω _).pow _)
    have hD := (isWeightedHomogeneous_X (KK O) ω (scalZ (2 * s + 1) r S.t (Fin.last S.t))).pow (aPlus - b.oPlus)
    have hY := wh_chain ω ωL h1 _ y hy.1.1
    have hG := wh_xi ω ωL h1 g hg
    have hall := ((((hA.mul hB).mul hC).mul hD).mul hY).mul hG
    refine wh_congr hall (Eq.symm ?_)
    have hjpB : jp ≤ S.bPlus := le_trans hlev.2 (min_le_right _ _)
    have hsplit : ∑ a : Fin (2 * s + 1), (segChain p S aTop b).deg a * ωL (Fin.castSucc a) =
        ∑ a : Fin (2 * s + 1), ((blockData p S aTop aPlus mm b).lettersAt jl jp).deg a * ωL (Fin.castSucc a) +
        ∑ l : Fin S.t, jl l * (ωL (finPos (2 * s + 1) (2 * (uTop S l : ℕ))) +
          ωL (finPos (2 * s + 1) (2 * (uTop S l : ℕ) + 1))) + jp * ωL (Fin.castSucc ⟨2 * s, by omega⟩) := by
      rw [← tie_sum S jl ωL]
      have e3 : jp * ωL (Fin.castSucc ⟨2 * s, by omega⟩) =
          ∑ a : Fin (2 * s + 1), (if a.val = 2 * s then jp else 0) * ωL (Fin.castSucc a) := by
        rw [Finset.sum_eq_single (⟨2 * s, by omega⟩ : Fin (2 * s + 1))]
        · rw [if_pos rfl]
        · intro c _ hc
          rw [if_neg (fun h => hc (Fin.ext h)), zero_mul]
        · intro h; exact absurd (Finset.mem_univ _) h
      rw [e3, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [deg_split p S aTop aPlus mm b jl jp hlev a]
      ring
    unfold OmB
    rw [hsplit]
    have hBj : S.bPlus * ωL (Fin.last _) = (S.bPlus - jp) * ωL (Fin.last _) + jp * ωL (Fin.last _) := by
      rw [← add_mul, Nat.sub_add_cancel hjpB]
    rw [hBj]
    simp only [smul_eq_mul]
    show _ = (∑ l : Fin S.t, jl l * (ωL (finPos (2 * s + 1) (2 * (uTop S l : ℕ))) +
          ωL (finPos (2 * s + 1) (2 * (uTop S l : ℕ) + 1)))) +
        jp * (ωL (Fin.castSucc ⟨2 * s, by omega⟩) + ωL (Fin.last _)) +
        (∑ l : Fin S.t, (coarseA p S b (uTop S l) - b.o (uTop S l)) * ω (Sum.inr (Fin.castSucc l, false))) +
        (aPlus - b.oPlus) * ω (Sum.inr (Fin.last S.t, false)) +
        (∑ a : Fin (2 * s + 1), ((blockData p S aTop aPlus mm b).lettersAt jl jp).deg a * ωL (Fin.castSucc a)) +
        (S.bPlus - jp) * ωL (Fin.last _)
    ring
  · exact isWeightedHomogeneous_zero _ _ _
  · intro x y _ _ hx hy
    exact hx.add hy
  · intro c x _ hx
    exact wh_smulO c hx

end Formalism.MainNotions.ColumnSystems.Pf
end
end
