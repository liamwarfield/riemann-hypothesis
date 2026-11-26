module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ValidForConstructedPointClassesEventuallyWorking
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeCoprimeSmallConductor

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ObjCOfRecExObjO
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLedPart
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemLocSub
namespace GlobalTheory.EX.Glue

open Formalism.BasicNotions NumberField IsDedekindDomain

theorem exists_clear {R : Type} [CommRing R] [IsDedekindDomain R] (c : R) (hc : c ≠ 0)
    (w₀ : HeightOneSpectrum R) :
    ∃ t : R, t ∉ w₀.asIdeal ∧ ∀ w : HeightOneSpectrum R, w ≠ w₀ → ∃ s : R, s ∉ w.asIdeal ∧ c ∣ s * t := by
  classical
  haveI := w₀.isMaximal
  have hI : Ideal.span {c} ≠ ⊥ := by simpa [Ideal.span_singleton_eq_bot] using hc
  obtain ⟨Q, hQ, hfac⟩ := Ideal.eq_prime_pow_mul_coprime hI w₀.asIdeal
  have hQn : ¬ Q ≤ w₀.asIdeal := by
    intro h
    rw [sup_eq_left.2 h] at hQ
    exact w₀.isPrime.ne_top hQ
  obtain ⟨t, htQ, ht⟩ := SetLike.not_le_iff_exists.1 hQn
  refine ⟨t, ht, fun w hw => ?_⟩
  generalize Multiset.count w₀.asIdeal _ = k at hfac
  have hP : ¬ w₀.asIdeal ^ k ≤ w.asIdeal := by
    intro h
    haveI := w.isPrime
    have h' : w₀.asIdeal ≤ w.asIdeal := Ideal.IsPrime.le_of_pow_le h
    exact hw (HeightOneSpectrum.ext (w₀.isMaximal.eq_of_le w.isPrime.ne_top h').symm)
  obtain ⟨s, hsP, hs⟩ := SetLike.not_le_iff_exists.1 hP
  refine ⟨s, hs, ?_⟩
  rw [← Ideal.mem_span_singleton, hfac]
  exact Ideal.mul_mem_mul hsP htQ

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module (𝓞 K) V]

def locSub (w : HeightOneSpectrum (𝓞 K)) (M : Submodule (𝓞 K) V) : Submodule (𝓞 K) V where
  carrier := {x | InLoc w M x}
  zero_mem' := ⟨1, (Ideal.ne_top_iff_one _).1 w.isPrime.ne_top, by simp⟩
  add_mem' := by
    rintro x y ⟨s, hs, hx⟩ ⟨t, ht, hy⟩
    refine ⟨s * t, fun h => (w.isPrime.mem_or_mem h).elim hs ht, ?_⟩
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact M.smul_mem _ hx
    · rw [mul_smul]; exact M.smul_mem _ hy
  smul_mem' := by
    rintro a x ⟨s, hs, hx⟩
    exact ⟨s, hs, by rw [smul_comm]; exact M.smul_mem _ hx⟩

theorem mem_locSub {w : HeightOneSpectrum (𝓞 K)} {M : Submodule (𝓞 K) V} {x : V} :
    x ∈ locSub w M ↔ InLoc w M x := Iff.rfl

theorem inLoc_iInf (B : HeightOneSpectrum (𝓞 K) → Submodule (𝓞 K) V)
    (hsat : ∀ w (t : 𝓞 K) (x : V), t ∉ w.asIdeal → t • x ∈ B w → x ∈ B w)
    (hden : ∀ x : V, ∃ c : 𝓞 K, c ≠ 0 ∧ ∀ w, c • x ∈ B w) (w₀ : HeightOneSpectrum (𝓞 K)) (x : V) :
    InLoc w₀ (⨅ w, B w) x ↔ x ∈ B w₀ := by
  constructor
  · rintro ⟨s, hs, hx⟩
    exact hsat w₀ s x hs ((Submodule.mem_iInf _).1 hx w₀)
  · intro hx
    obtain ⟨c, hc, hcx⟩ := hden x
    obtain ⟨t, ht, h⟩ := exists_clear c hc w₀
    refine ⟨t, ht, (Submodule.mem_iInf _).2 fun w => ?_⟩
    by_cases hw : w = w₀
    · subst hw; exact (B w).smul_mem _ hx
    · obtain ⟨s, hs, d, hd⟩ := h w hw
      refine hsat w s _ hs ?_
      rw [← mul_smul, hd, mul_comm, mul_smul]
      exact (B w).smul_mem _ (hcx w)

theorem exists_glue : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (M : Submodule (𝓞 K) V) (S : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (A : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → Submodule (𝓞 K) V), S.Finite →
    (∀ x : V, ∃ n : ℕ, n ≠ 0 ∧ n • x ∈ M) →
    (∀ w ∈ S, (∀ (t : 𝓞 K) (x : V), t ∉ w.asIdeal → t • x ∈ A w → x ∈ A w) ∧
      ∃ n : ℕ, n ≠ 0 ∧ (∀ x ∈ M, n • x ∈ A w) ∧ ∀ x ∈ A w, InLoc w M (n • x)) →
    ∃ N : Submodule (𝓞 K) V, (∀ w ∈ S, ∀ x, InLoc w N x ↔ x ∈ A w) ∧
      ∀ w ∉ S, ∀ x, InLoc w N x ↔ InLoc w M x := by
  intro K V _ _ _ _ _ _ M S A hS hM hA
  classical
  let B : HeightOneSpectrum (𝓞 K) → Submodule (𝓞 K) V := fun w => if w ∈ S then A w else locSub w M
  have hB1 : ∀ w ∈ S, B w = A w := fun w hw => if_pos hw
  have hB2 : ∀ w ∉ S, B w = locSub w M := fun w hw => if_neg hw
  have hsat : ∀ w (t : 𝓞 K) (x : V), t ∉ w.asIdeal → t • x ∈ B w → x ∈ B w := by
    intro w t x ht hx
    by_cases hw : w ∈ S
    · rw [hB1 w hw] at hx ⊢
      exact (hA w hw).1 t x ht hx
    · rw [hB2 w hw] at hx ⊢
      obtain ⟨s, hs, hx⟩ := hx
      exact ⟨s * t, fun h => (w.isPrime.mem_or_mem h).elim hs ht, by rwa [mul_smul]⟩
  have hn : ∀ w, ∃ n : ℕ, n ≠ 0 ∧ (w ∈ S → ∀ x ∈ M, n • x ∈ A w) := by
    intro w
    by_cases hw : w ∈ S
    · obtain ⟨n, hn, h, -⟩ := (hA w hw).2
      exact ⟨n, hn, fun _ => h⟩
    · exact ⟨1, one_ne_zero, fun h => absurd h hw⟩
  choose n hn0 hn using hn
  have hden : ∀ x : V, ∃ c : 𝓞 K, c ≠ 0 ∧ ∀ w, c • x ∈ B w := by
    intro x
    obtain ⟨m, hm, hx⟩ := hM x
    refine ⟨(((∏ w ∈ hS.toFinset, n w) * m : ℕ) : 𝓞 K), ?_, fun w => ?_⟩
    · exact Nat.cast_ne_zero.2 (mul_ne_zero (Finset.prod_ne_zero_iff.2 fun w _ => hn0 w) hm)
    · rw [Nat.cast_smul_eq_nsmul, mul_smul]
      by_cases hw : w ∈ S
      · rw [hB1 w hw]
        obtain ⟨d, hd⟩ := Finset.dvd_prod_of_mem n (hS.mem_toFinset.2 hw)
        rw [hd, mul_comm, mul_smul]
        exact nsmul_mem (hn w hw _ hx) d
      · rw [hB2 w hw]
        exact ⟨1, (Ideal.ne_top_iff_one _).1 w.isPrime.ne_top, by
          rw [one_smul]; exact nsmul_mem hx _⟩
  refine ⟨⨅ w, B w, fun w hw x => ?_, fun w hw x => ?_⟩
  · rw [inLoc_iInf B hsat hden, hB1 w hw]
  · rw [inLoc_iInf B hsat hden, hB2 w hw, mem_locSub]

end GlobalTheory.EX.Glue
end

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField

namespace GlobalTheory.EX.Led

open Formalism.MainNotions.G IsDedekindDomain

theorem X'_le_X'' (s : Scale) (R : Ranks) : s.X' ≤ s.X'' R.n := by
  have hx := s.one_lt_alt
  have hx0 : 0 < s.x := by linarith
  have hn : (1 : ℝ) ≤ R.n := by
    have : 1 ≤ R.n := by
      unfold Ranks.n
      have := R.two_le_m
      have := R.m_le_f
      omega
    exact_mod_cast this
  have hX : 0 < s.X' := Real.exp_pos _
  have ha : 0 < s.a := by unfold Scale.a Scale.b; positivity
  have : s.X'' R.n = s.X' * (s.x * R.n) := by
    unfold Scale.X'' Scale.w'' Scale.b'
    field_simp
  rw [this]
  exact le_mul_of_one_le_right hX.le (by nlinarith)

variable {D : D7}

theorem cand_of_VV {L : SizeData₂ D} (X : Inst D L) (K : Consts) (a b : HH D → ℤ) (p : ℕ) (h : VV X K a b p ≠ ∅) :
    Cand D L K p ∧ Sig X K a b p ≤ L.sc.x ^ (-L.sc.eps) := by
  by_contra h'
  apply h
  unfold VV
  rw [if_neg h']

theorem not_noGain {L : SizeData₂ D} (X : Inst D L) (K : Consts) (Cr : ℝ) (p : ℕ) (h : VV X K (aL L) (bL L) p ≠ ∅) :
    ¬ NoGain X K Cr p := by
  obtain ⟨hc, hs⟩ := cand_of_VV X K _ _ p h
  have hX := X'_le_X'' L.sc D.R
  rintro (⟨-, -, h1 | ⟨h1, i, hi, h2⟩ | ⟨-, h1⟩⟩ | h1 | h1 | h1)
  · exact absurd hc.2.2.2.1 (not_le.2 h1)
  · rw [abs_le] at h2
    exact hc.2.2.2.2 h1 ⟨h1, hc.2.1, i, hi, by linarith [h2.1], by linarith [h2.2]⟩
  · exact absurd hs (not_le.2 h1)
  · linarith [hc.2.1]
  · exact h1 (Or.inl hc.2.2.1)
  · exact HEv.not_isCs (UpperTheory.even_addOrderOf_hP_of_pow_le.2 D L p hc.2.2.2.1) h1

theorem locLe_iff {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module (𝓞 K) V]
    (w : HeightOneSpectrum (𝓞 K)) (A B : Submodule (𝓞 K) V) : DV.LocLe w 0 A B ↔ ∀ x ∈ A, InLoc w B x := by
  unfold DV.LocLe InLoc
  rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]

theorem inLoc_of_mem {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module (𝓞 K) V]
    (w : HeightOneSpectrum (𝓞 K)) (A : Submodule (𝓞 K) V) (x : V) (h : x ∈ A) : InLoc w A x :=
  ⟨1, fun h => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by rwa [one_smul]⟩

theorem locEq_of_iff {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module (𝓞 K) V]
    (w : HeightOneSpectrum (𝓞 K)) (A B : Submodule (𝓞 K) V) (h : ∀ x, InLoc w A x ↔ InLoc w B x) : DV.LocEq w A B :=
  ⟨(locLe_iff w A B).2 fun x hx => (h x).1 (inLoc_of_mem w A x hx),
    (locLe_iff w B A).2 fun x hx => (h x).2 (inLoc_of_mem w B x hx)⟩

theorem exists_sub {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (w : HeightOneSpectrum (𝓞 K)) (P : V → Prop) (h0 : P 0)
    (hadd : ∀ x y, P x → P y → P (x + y)) (hs : ∀ (a : K) x, w.valuation K a ≤ 1 → P x → P (a • x)) :
    ∃ A : Submodule (𝓞 K) V, (∀ x, x ∈ A ↔ P x) ∧ ∀ (t : 𝓞 K) (x : V), t ∉ w.asIdeal → t • x ∈ A → x ∈ A := by
  refine ⟨⟨⟨⟨{x | P x}, fun {x y} => hadd x y⟩, h0⟩, fun c x hx => ?_⟩, fun _ => Iff.rfl, fun t x ht hx => ?_⟩
  · show P (c • x)
    rw [← algebraMap_smul K c x]
    exact hs _ x (w.valuation_le_one c) hx
  · have hv : w.valuation K (algebraMap (𝓞 K) K t) = 1 := (w.valuation_eq_one_iff_notMem).2 ht
    have ht0 : algebraMap (𝓞 K) K t ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hv
      exact zero_ne_one hv
    have h1 := hs (algebraMap (𝓞 K) K t)⁻¹ (t • x) (by rw [map_inv₀, hv, inv_one]) hx
    rw [← algebraMap_smul K t x, smul_smul, inv_mul_cancel₀ ht0, one_smul] at h1
    exact h1

theorem exists_served {L : SizeData₂ D} (X : Inst D L) (Y : LatInst D) (K : Consts) (c : LatCmp D) (u : D.what₂.Word)
    (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    ∃ A : Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V, (∀ x, x ∈ A ↔ c.cmp u w hg (D.nuIn u x) ∈ NP X Y K u w hg) ∧
      ∀ (t : 𝓞 D.what₂.LL) x, t ∉ (D.plEq w).asIdeal → t • x ∈ A → x ∈ A := by
  refine exists_sub (D.plEq w) (fun x => c.cmp u w hg (D.nuIn u x) ∈ NP X Y K u w hg) ?_ ?_ ?_
  · simp
  · intro x y hx hy
    simp only [map_add (f := _)]
    exact Submodule.add_mem _ hx hy
  · intro a x ha hx
    obtain ⟨o, ho⟩ := (c.embW_val u w hg a).1 ha
    show c.cmp u w hg (D.nuIn u (a • x)) ∈ _
    rw [map_smul, c.cmp_smul, ← ho, algebraMap_smul]
    exact Submodule.smul_mem _ _ hx

theorem exists_atT (u : D.what₂.Word) (w : D.what₂.places.Pl) :
    ∃ A : Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V, (∀ x, x ∈ A ↔ D.nuIn u x ∈ LT.Nlam D u w) ∧
      ∀ (t : 𝓞 D.what₂.LL) x, t ∉ (D.plEq w).asIdeal → t • x ∈ A → x ∈ A := by
  refine exists_sub (D.plEq w) (fun x => D.nuIn u x ∈ LT.Nlam D u w) ?_ ?_ ?_
  · simp
  · intro x y hx hy
    simp only [map_add (f := _)]
    exact Submodule.add_mem _ hx hy
  · intro a x ha hx
    show D.nuIn u (a • x) ∈ _
    rw [map_smul]
    exact (LT.Nlam D u w).smul_mem (⟨a, (D.val_nonneg_iff w a).2 ha⟩ : intW D.what₂.places w) hx

theorem exists_lat {L : SizeData₂ D} (X : Inst D L) (Y : LatInst D) (K : Consts) (c : LatCmp D) (u : D.what₂.Word)
    (hfull : ∀ x : (D.div.Nu u).V, ∃ n : ℕ, n ≠ 0 ∧ n • x ∈ DV.MramL D u)
    (hT : ∀ w : D.what₂.places.Pl, D.what₂.places.resChar w = (D.mem u).A.T → ∃ n : ℕ, n ≠ 0 ∧
      (∀ x ∈ DV.MramL D u, D.nuIn u (n • x) ∈ LT.Nlam D u w) ∧
      ∀ x, D.nuIn u x ∈ LT.Nlam D u w → InLoc (D.plEq w) (DV.MramL D u) (n • x))
    (hS : ∀ (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
        VV X K (aL L) (bL L) (D.what₂.places.resChar w) ≠ ∅ →
        (∀ x, c.cmp u w hg (D.nuIn u x) ∈ NP X Y K u w hg → InLoc (D.plEq w) (DV.MramL D u) x) ∧
        ∃ n : ℕ, n ≠ 0 ∧ ∀ x ∈ DV.MramL D u, c.cmp u w hg (D.nuIn u (n • x)) ∈ NP X Y K u w hg) :
    ∃ N : Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V,
      (∀ (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
        VV X K (aL L) (bL L) (D.what₂.places.resChar w) ≠ ∅ →
        ∀ x, InLoc (D.plEq w) N x ↔ c.cmp u w hg (D.nuIn u x) ∈ NP X Y K u w hg) ∧
      (∀ w : D.what₂.places.Pl, D.what₂.places.resChar w = (D.mem u).A.T →
        ∀ x, InLoc (D.plEq w) N x ↔ D.nuIn u x ∈ LT.Nlam D u w) ∧
      (∀ w : D.what₂.places.Pl, D.what₂.places.resChar w ≠ (D.mem u).A.T → DV.LocLe (D.plEq w) 0 N (DV.MramL D u)) ∧
      ∀ w : D.what₂.places.Pl, D.what₂.places.resChar w ≠ (D.mem u).A.T →
        VV X K (aL L) (bL L) (D.what₂.places.resChar w) = ∅ → DV.LocEq (D.plEq w) N (DV.MramL D u) := by
  classical
  choose A1 hA1 hA1s using exists_served X Y K c u
  choose A2 hA2 hA2s using exists_atT (D := D) u
  let A : D.what₂.places.Pl → Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V := fun w =>
    if hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) then A1 w hg else A2 w
  let S : Set D.what₂.places.Pl := {w | (GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) ∧
    VV X K (aL L) (bL L) (D.what₂.places.resChar w) ≠ ∅) ∨ D.what₂.places.resChar w = (D.mem u).A.T}
  have hng : ∀ w, D.what₂.places.resChar w = (D.mem u).A.T → ¬ GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) :=
    fun w h hg => hg.2.2.2.2.2 (h ▸ dvd_rfl)
  have hSf : S.Finite := by
    refine ((GlobalTheory.Refill.finite_le D ⌈L.sc.X'⌉₊).union (GlobalTheory.Refill.finite_over D (D.mem u).A.T)).subset ?_
    rintro w (⟨-, h⟩ | h)
    · left
      have h1 := (cand_of_VV X K _ _ _ h).1.2.1
      have h2 := h1.le.trans (Nat.le_ceil _)
      exact_mod_cast h2
    · exact Or.inr h
  obtain ⟨N, hN1, hN2⟩ := GlobalTheory.EX.Glue.exists_glue D.what₂.LL (D.div.Nu u).V (DV.MramL D u) (D.plEq '' S)
    (fun v => A (D.plEq.symm v)) (hSf.image _) hfull (by
      rintro _ ⟨w, hw, rfl⟩
      simp only [Equiv.symm_apply_apply]
      rcases hw with ⟨hg, hV⟩ | hw
      · have hA : A w = A1 w hg := dif_pos hg
        rw [hA]
        obtain ⟨h1, n, hn, h2⟩ := hS w hg hV
        refine ⟨hA1s w hg, n, hn, fun x hx => (hA1 w hg _).2 (h2 x hx), fun x hx => h1 _ ?_⟩
        exact (hA1 w hg _).1 (Submodule.smul_of_tower_mem _ n hx)
      · have hA : A w = A2 w := dif_neg (hng w hw)
        rw [hA]
        obtain ⟨n, hn, h1, h2⟩ := hT w hw
        exact ⟨hA2s w, n, hn, fun x hx => (hA2 w _).2 (h1 x hx), fun x hx => h2 _ ((hA2 w _).1 hx)⟩)
  have e1 : ∀ (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
        VV X K (aL L) (bL L) (D.what₂.places.resChar w) ≠ ∅ →
        ∀ x, InLoc (D.plEq w) N x ↔ c.cmp u w hg (D.nuIn u x) ∈ NP X Y K u w hg := by
    intro w hg hV x
    have hA : A w = A1 w hg := dif_pos hg
    rw [hN1 _ ⟨w, Or.inl ⟨hg, hV⟩, rfl⟩, Equiv.symm_apply_apply, hA, hA1]
  have e2 : ∀ w, w ∉ S → DV.LocEq (D.plEq w) N (DV.MramL D u) := fun w hw =>
    locEq_of_iff _ _ _ (hN2 _ (fun h => hw ((D.plEq.injective.mem_set_image).1 h)))
  refine ⟨N, e1, fun w hw x => ?_, fun w hw => ?_, fun w hw hV => e2 w ?_⟩
  · have hA : A w = A2 w := dif_neg (hng w hw)
    rw [hN1 _ ⟨w, Or.inr hw, rfl⟩, Equiv.symm_apply_apply, hA, hA2]
  · by_cases h : w ∈ S
    · obtain ⟨hg, hV⟩ := h.resolve_right hw
      exact (locLe_iff _ _ _).2 fun x hx => (hS w hg hV).1 x ((e1 w hg hV x).1 (inLoc_of_mem _ _ _ hx))
    · exact (e2 w h).1
  · rintro (h | h)
    · exact h.2 hV
    · exact hw h

def setLat (L : SizeData₂ D) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) : SizeData₂ D :=
  { L with
    NuLat := N
    lenMN := fun u w => ((DV.lenLoc (D.plEq w) (N u) (DV.MramL D u)).toNat : ℚ) / (D.what₂.places.ramIdx w : ℚ) }

def setInst {L : SizeData₂ D} (X : Inst D L) (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) : Inst D (setLat L N) :=
  { X with }

theorem exists_ledPart : ∀ (C : FC) (cD ch : ℝ) (s : Scale) (D : D7) (Y : Lay D) (e : Formalism.HC.Frame) (a b : e.A → ℤ) (L0 : SizeData₂ D), Std C → 10 ≤ C.cX.err.g → e = D.R.toFrame → L0.sc = s → WtEq L0 a b → Val C cD ch L0 → HostArith D.host → 1 ≤ s.w'' D.R.n → (∀ u, s.X' ≤ ((D.mem u).A.T : ℝ)) → RecOK s C cD D → LedOK s C cD ch Y a b → ∃ p : LedPart C Y, p.L.sc = s ∧ WtEq p.L a b ∧ Val C cD ch p.L ∧ CanonInst p.ta.Gx := by
  intro C cD ch s D Y e a b L0 hC hg _ hs hW hV0 hA hw _ hR hL
  obtain ⟨L, X, e1, e2, e3, hV, hcan, hep, hkap, hF, hE, hs1, hs2, hfill, hdrop⟩ :=
    GlobalTheory.Refill.exists_refill C cD ch D L0 Y.errX hC hV0 hA (hs ▸ hw) (X'_le_X'' _ _) hR.fin hR.dgam (hL L0 hs hW hV0).1
  have hWL : WtEq L a b := by
    intro t t' h
    rw [e2, e3]
    exact hW t t' h
  obtain ⟨htied, heptie, hS⟩ := (hL L (e1.trans hs) hWL hV).2 X hcan hep hkap hfill
  choose N hN1 hN2 hN3 hN4 using fun u => exists_lat X Y.Gy C.GK Y.cmp u (hR.full u) (hR.atT u) (hS u)
  have hlen : ∀ u w, ∀ l : ℕ, DV.lenLoc (D.plEq w) (N u) (DV.MramL D u) = l →
      (l : ℝ) = ((setLat L N).lenMN u w : ℝ) * (D.what₂.places.ramIdx w : ℝ) := by
    intro u w l h
    have h0 : (D.what₂.places.ramIdx w : ℝ) ≠ 0 := by exact_mod_cast (D.what₂.places.ramIdx_pos w).ne'
    show _ = ((((DV.lenLoc (D.plEq w) (N u) (DV.MramL D u)).toNat : ℚ) / (D.what₂.places.ramIdx w : ℚ) : ℚ) : ℝ) * _
    rw [h, ENat.toNat_natCast]
    push_cast
    rw [div_mul_cancel₀ _ h0]
  have hnu : DV.NuDef D (setLat L N) := by
    refine ⟨hN3, fun u w hT h => hN4 u w hT ?_, hlen⟩
    by_contra hVV
    rcases h with h | h
    · exact not_noGain X C.GK C.Cr _ hVV ((hdrop _ (D.what₂.places.resChar_prime w)).1 h).1
    · exact h (Or.inr (cand_of_VV X C.GK _ _ _ hVV).1.2.2.1)
  obtain ⟨-, -, -, -, f5, f6, -⟩ := hC.1
  refine ⟨⟨setLat L N, ⟨setInst X N, Y.Gy, hs1, hs2, hfill,
      fun w u h1 h2 => LatCmp.lenMN_unserved hnu u w (hN4 u w h2 h1), htied, hdrop⟩, rfl, hnu,
      ⟨Y.vram, hN1, hN2⟩, hep, heptie, hkap, hN4,
      ⟨⟨f5.ge, f6.ge, hg⟩, Y.piG_lev, Y.piT_lev, Y.seen, Y.tauOf, Y.dgam, hE⟩, hF⟩, e1.trans hs, hWL,
    ⟨hV.ranks, hV.host, hV.hc, hV.dlog, hV.Del_eq, hV.eta_eq, hV.La_eq, hV.bT_le, hV.logFiveDepth_eq, hV.Ct_eq, hV.Cc_eq,
      hV.CGam_eq, hV.secondConstant_eq, hV.words, hV.etaF_eq⟩, hcan⟩

end GlobalTheory.EX.Led

end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField

namespace GlobalTheory.EX.OB.Bridge

theorem exists_T_of_over {D : D7} {P : PreCh} {Lv : LevCh P} (h : Over D P Lv) (u : D.what₂.Word) :
    ∃ u', (D.mem u).A.T = Lv.T u' := by
  obtain ⟨sp, hT, hY, hA, hV, hz, X, h1, rfl⟩ := h
  have key : ∀ B : Pre, B = Pre.ofCh P Lv sp hT hY hA hV hz → ∀ v : B.Word, ∃ u', B.T v = Lv.T u' := by
    rintro B rfl v
    exact ⟨v, rfl⟩
  obtain ⟨u', hu⟩ := key X.B.toPre h1 u
  exact ⟨u', (X.C.A_T u).trans hu⟩

theorem scale_X'_le_of_log (eps cs : ℝ) (he : 0 < eps) (hc : 0 < cs) : ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks) (T : ℝ),
    s.eps = eps → x0 ≤ s.x → RankVal s R → 0 < T → cs * R.m * s.L ≤ Real.log T → s.X' ≤ T := by
  refine ⟨cs⁻¹ ^ ((2 * eps / 3)⁻¹), fun s R T hs hx hR hT h => ?_⟩
  have hx1 := s.one_lt_alt
  have hx0 : 0 < s.x := by linarith
  have hel := s.eps_lt
  have hm : (1 : ℝ) ≤ R.m := by
    refine le_trans ?_ hR.2.1.1
    rw [Real.one_le_sqrt, Scale.delta1, ← Real.rpow_one_add' hx0.le (by linarith)]
    exact Real.one_le_rpow hx1.le (by linarith)
  have h1 : cs⁻¹ ≤ s.x ^ (2 * eps / 3) := by
    have := Real.rpow_le_rpow (by positivity) hx (show 0 ≤ 2 * eps / 3 by positivity)
    rwa [Real.rpow_inv_rpow (by positivity) (by positivity)] at this
  have h2 : s.L = s.x ^ (2 * eps / 3) * s.x ^ (s.eps / 3) := by
    rw [Scale.L, ← Real.rpow_add hx0, hs]; congr 1; ring
  have h3 : 1 ≤ cs * s.x ^ (2 * eps / 3) := by
    have := mul_le_mul_of_nonneg_left h1 hc.le
    rwa [mul_inv_cancel₀ hc.ne'] at this
  have h4 : 0 < s.x ^ (s.eps / 3) := by positivity
  have h5 : s.x ^ (s.eps / 3) ≤ cs * R.m * s.L := by
    have : cs * R.m * s.L = (cs * s.x ^ (2 * eps / 3) * R.m) * s.x ^ (s.eps / 3) := by rw [h2]; ring
    rw [this]
    exact le_mul_of_one_le_left h4.le (one_le_mul_of_one_le_of_one_le h3 hm)
  rw [Scale.X', ← Real.le_log_iff_exp_le hT]
  exact h5.trans h

theorem scale_one_le_w'' (eps : ℝ) (he : 0 < eps) : ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks),
    s.eps = eps → x0 ≤ s.x → RankVal s R → 1 ≤ s.w'' R.n := by
  obtain ⟨x0, h⟩ := GlobalTheory.scale_poly_comparison eps 0 1 he one_pos
  refine ⟨max x0 4, fun s R hs hx hR => ?_⟩
  have hx4 : 4 ≤ s.x := (le_max_right _ _).trans hx
  have hx0 : 0 < s.x := by linarith
  have hel := s.eps_lt
  have hn : 1 ≤ R.n := Formalism.HC.Frame.ord_pos _
  have h2 : (2 : ℝ) ≤ s.x ^ ((1 : ℝ) / 2) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.le_sqrt_of_sq_le (by linarith)
  have h3 : (R.n : ℝ) ≤ s.x ^ (3 : ℝ) := by
    have a1 : s.x ^ (2 + 8 * s.eps) ≤ s.x ^ ((5 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have a2 : s.x ^ (3 : ℝ) = s.x ^ ((1 : ℝ) / 2) * s.x ^ ((5 : ℝ) / 2) := by
      rw [← Real.rpow_add hx0]; norm_num
    rw [a2]
    exact hR.1.2.trans (mul_le_mul h2 a1 (by positivity) (by positivity))
  have := ((h s hs ((le_max_left _ _).trans hx)).2.2.2.2.2.1 R.n hn h3).1
  simpa using this

end GlobalTheory.EX.OB.Bridge
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsObjectsOfAdmissibleTwistDatum
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField

namespace GlobalTheory.Fc

theorem ObjCP.imp {Q Q' : Par → PtProp} (h : ObjCP Q) (hi : ∀ (κ : Par) (p : Pt κ.C), p.Has (Q κ) → p.Has (Q' κ)) : ObjCP Q' :=
  ParEv.mono (fun κ ⟨x0, H⟩ => ⟨x0, fun s R G q0 a b M c u0 d1 d2 d3 d4 d5 d0 d6 d7 d8 d9 =>
    let ⟨p, e1, e2, e3, e4, e5, e6⟩ := H s R G q0 a b M c u0 d1 d2 d3 d4 d5 d0 d6 d7 d8 d9
    ⟨p, e1, e2, e3, e4, e5, hi κ p e6⟩⟩) h


open GlobalTheory.EX.DC in
theorem ObjCP.and_q0Pt {Q : Par → PtProp} (h : ObjCP Q) : ObjCP (fun κ => (Q κ).and twistingGlobalPointProp) := by
  obtain ⟨ε0, h0, h⟩ := h
  refine ⟨ε0, h0, fun eps C8 C5 c6 Cb a1 a2 a3 a4 => ?_⟩
  obtain ⟨K0, h⟩ := h eps C8 C5 c6 Cb a1 a2 a3 a4
  refine ⟨K0, fun C b1 b2 b3 => ?_⟩
  obtain ⟨c1, h⟩ := h C b1 b2 b3
  obtain ⟨c1', hP⟩ := explicitConstants_parameterConditions_large eps a1 a3 C b1
  refine ⟨max c1 c1', fun cD hcD => ?_⟩
  obtain ⟨c2, h⟩ := h cD ((le_max_left _ _).trans hcD)
  obtain ⟨c2', hP⟩ := hP cD ((le_max_right _ _).trans hcD)
  refine ⟨max c2 c2', fun ch hch => ?_⟩
  obtain ⟨x0, h⟩ := h ch ((le_max_left _ _).trans hch)
  obtain ⟨x1, hP⟩ := hP ch ((le_max_right _ _).trans hch)
  obtain ⟨x2, hq⟩ := small_prime_lt eps C8 a1 a4
  obtain ⟨x3, hJ⟩ := GlobalTheory.ClassDuty.windowsAt_of eps a1 a3 C b1
  refine ⟨max (max x0 x1) (max x2 x3), fun s R H q0 a b M c u0 d1 d2 d3 d4 d5 d0 d6 d7 d8 d9 => ?_⟩
  dsimp only at d1 d4 d5 d6 d7
  rw [b2] at d5
  simp only [max_le_iff] at d2
  obtain ⟨p, e1, e2, e3, e4, e5, e6⟩ := h s R H q0 a b M c u0 d1 d2.1.1 d3 d4 (b2 ▸ d5) d0 d6 d7 d8 d9
  refine ⟨p, e1, e2, e3, e4, e5, e6, ?_⟩
  dsimp only at e2 p
  subst e1
  show GlobalTwistingFacts p.L
  obtain ⟨hv, -, -, -, -, -, -, -, -, -, -, -, ⟨-, -, hle, -⟩, hlev⟩ := d5
  have eq0 : q0Av p.D = q0 := (eq_of_from p e4 e2.host.2.2.2.2.2.2.1 hv.2.2.2.2.2.2.1).trans d0.symm
  have hX : (q0Av p.D : ℝ) < p.L.sc.X' := by
    rw [eq0]
    exact hq _ _ q0 d1 d2.2.1 (by exact_mod_cast cond_pos H) hv.log_cond_le hle
  obtain ⟨P, -⟩ := hP _ _ d1 d2.1.2 e2 e3
  have hXb := X'_le_b p.L.sc
  have hs := globalTwisting_spec_fact p.D.host
  have hg : ∀ j, q0Av p.D < p.D.host.g j := by
    intro j
    have hg := (e2.host.2.2.2.2.1 j).1
    have hk : (1 : ℝ) ≤ p.D.R.k := by
      have := p.D.R.m_add_three_le_k
      exact_mod_cast (by omega : 1 ≤ p.D.R.k)
    have hb1 : 1 ≤ p.L.sc.b := Real.one_le_exp (Real.rpow_nonneg (by linarith [p.L.sc.one_lt_alt]) _)
    have h5 : p.L.sc.b ≤ (p.D.R.k : ℝ) * p.L.sc.b := le_mul_of_one_le_left (by linarith) hk
    have h6 : (p.D.R.k : ℝ) * p.L.sc.b ≤ ((p.D.R.k : ℝ) * p.L.sc.b) ^ 8 := le_self_pow₀ (by linarith) (by norm_num)
    exact_mod_cast (show (q0Av p.D : ℝ) < p.D.host.g j by linarith)
  refine ⟨?_, hs.1, hs.2.1, ?_, hX, hX.le.trans (hJ cD ch _ _ d1 d2.2.2 e2 P).2, (q0H_ne_pde_and_ne_pde' _).1, (q0H_ne_pde_and_ne_pde' _).2,
    fun j => (hg j).ne, fun u => ((hg 0).trans (firstTypePrime_lt_rowPrime _ u)).ne⟩
  · rw [eq0]
    exact e4.2.2.2.2.2.2.2.2.1 (by rw [hlev]; simp)
  · rw [Real.log_le_iff_le_exp (by exact_mod_cast hs.1.pos)]
    exact hX.le.trans hXb


open GlobalTheory.EX.DC GlobalTheory.EX.OB.Bridge in
theorem objCP_and_of_recExP (QO : Par → ∀ D : D7, Obj D → Prop) (hLP : LevelPrime) (hRec : RecExP QO) :
    ObjCP (fun κ => (ptO (QO κ)).and (TamePt.and (MinkPt.and TwPt))) := by
  obtain ⟨ε0, h0, hRec⟩ := hRec
  refine ⟨ε0, h0, fun eps C8 C5 c6 Cb e1 e2 e3 e4 => ?_⟩
  obtain ⟨K0, hRec⟩ := hRec eps C8 C5 c6 Cb e1 e2 e3 e4
  refine ⟨⟨K0.pre, K0.t, fun l => max (K0.mid l) 10, K0.last⟩, fun C hS hC8 hL => ?_⟩
  have hL0 : C.Large K0 C.P.CF :=
    ⟨hL.1, trivial, fun c hc => (le_max_left _ _).trans (hL.2.2.1 c hc), hL.2.2.2⟩
  have hg : 10 ≤ C.cX.err.g := (le_max_right _ _).trans (hL.2.2.1 _ (by simp [FC.cMid]))
  obtain ⟨c1, hRec⟩ := hRec C hS hC8 hL0
  refine ⟨max c1 0, fun cD hcD => ?_⟩
  have hcD0 : 0 ≤ cD := (le_max_right _ _).trans hcD
  obtain ⟨c2, hRec⟩ := hRec cD ((le_max_left _ _).trans hcD)
  refine ⟨max c2 402, fun ch hch => ?_⟩
  have hch0 : 402 ≤ ch := (le_max_right _ _).trans hch
  obtain ⟨cs, x1, hcs, hRec⟩ := hRec ch ((le_max_left _ _).trans hch)
  obtain ⟨x2, h2⟩ := chGood_of_host eps C5 c6 Cb cD ch C e1 e3 hS hcD0 hch0
  obtain ⟨x3, h3⟩ := exists_levCh_of_levelPrime hLP eps cs C e1 e3 hcs hS
  obtain ⟨x4, h4⟩ := exists_sizeData_over eps cD ch C e1 e3 hS hcD0 hch0
  obtain ⟨x5, h5⟩ := scale_X'_le_of_log eps cs e1 hcs
  obtain ⟨x6, h6⟩ := scale_one_le_w'' eps e1
  refine ⟨max (max (max x1 x2) (max x3 x4)) (max x5 x6), ?_⟩
  intro s R H q0 a b M c u0 hs hx hR hCT hH hq0 hW hM hc hu
  simp only [max_le_iff] at hx
  obtain ⟨⟨⟨y1, y2⟩, y3, y4⟩, y5, y6⟩ := hx
  dsimp only at hs hCT hH hW hM
  rw [hq0] at hH
  obtain ⟨hcW, w0, k1, k2, k3, k4, k5, k6, k7, k8, hCh⟩ := h2 s R H a b M c u0 hs y2 hR hCT hH hW hM hc
  obtain ⟨du, Ds, hdu, hDs, hlog, hRec⟩ := hRec s _ _ _ _ hs y1 hCh
  obtain ⟨Lv, l1, l2, l3⟩ := h3 cD ch s _ _ _ _ _ du Ds hs y3 hCh.ok hdu hDs hlog
  obtain ⟨D, Y, hO, hRO, hLO, hTW, hQ⟩ := hRec Lv l1 l2 l3
  obtain ⟨hA, ⟨L0, m1, m2, m3⟩, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, eW, g11⟩ :=
    h4 s _ _ _ _ _ Lv D hs y4 hCh.ok l3 hO hRO
  have hDR : D.R = R := g0
  have hT : ∀ u, s.X' ≤ ((D.mem u).A.T : ℝ) := by
    intro u
    obtain ⟨u', hu'⟩ := exists_T_of_over hO u
    have w := (Lv.T_win u').1
    rw [l1, l2, l3] at w
    rw [hu']
    refine le_trans (h5 s R _ hs y5 hR ?_ (hlog u')) w
    have : (0 : ℝ) < du u' := by exact_mod_cast hdu u'
    have : 0 < GamS C s R := Real.exp_pos _
    positivity
  obtain ⟨p, n1, n2, n3, n4⟩ := Led.exists_ledPart C cD ch s D Y R.toFrame a b L0 hS hg (by rw [hDR]) m1 m2 m3 hA
    (by rw [hDR]; exact h6 s R hs y6 hR) hT hRO hLO
  exact ⟨p.pt, n1, p.pt_val n3, hA,
    ⟨hDR, g1, g2, g3, g4, g5, g6, g7, g8, g9.trans (R.toFrame.val_ofNat_of_lt hu), g10, p.pt_wtEq n2, ⟨eW, g11⟩,
      hO.field⟩, p.pt_canon n4,
    hQ p n1 n2 n3 n4, hRO.tame, hRO.mink, twAt_tr (nPrime p.L) p.ht hTW⟩

theorem objCP_of_recExP : ∀ QO : Par → ∀ D : D7, Obj D → Prop,
    LevelPrime → RecExP QO → ObjCP (fun κ => DC.withObj (ptO (QO κ))) :=
  fun QO hL hR => (objCP_and_of_recExP QO hL hR).and_q0Pt.imp fun _ _ hp => ⟨⟨hp.1.1, hp.2⟩, hp.1.2⟩

end GlobalTheory.Fc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsObjectsOfAdmissibleTwistDatumStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsObjects_of_admissibleTwistDatum : ∀ QO : Par → ∀ D : D7, Obj D → Prop, LevelPrime → RecExP QO → ObjCP (fun κ => DC.withObj (ptO (QO κ))) := by
  first | exact @GlobalTheory.Fc.objCP_of_recExP | exact GlobalTheory.Fc.objCP_of_recExP | (intros; apply GlobalTheory.Fc.objCP_of_recExP <;> assumption)
end
