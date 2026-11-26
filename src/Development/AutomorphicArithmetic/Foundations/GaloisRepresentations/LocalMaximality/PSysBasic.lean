module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.LiftFactorization

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PSysBasic
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private lemma lft_uni' (hU : WdUni) {β κ : Type} [LinearOrder β] [LinearOrder κ] (b : Finset β)
    (L : Finset κ) : lft (uni b L) = b := by
  exact (hU β κ ℂ (fun _ => 0) (fun _ => 0) b L).2.1

private lemma rgt_uni' (hU : WdUni) {β κ : Type} [LinearOrder β] [LinearOrder κ] (b : Finset β)
    (L : Finset κ) : rgt (uni b L) = L := by
  exact (hU β κ ℂ (fun _ => 0) (fun _ => 0) b L).2.2.1

private lemma card_uni' (hU : WdUni) {β κ : Type} [LinearOrder β] [LinearOrder κ] (b : Finset β)
    (L : Finset κ) : (uni b L).card = b.card + L.card := by
  exact (hU β κ ℂ (fun _ => 0) (fun _ => 0) b L).2.2.2.1

private lemma uni_lr' (hU : WdUni) {β κ : Type} [LinearOrder β] [LinearOrder κ]
    (s : Finset (β ⊕ₗ κ)) : uni (lft s) (rgt s) = s := by
  exact (hU β κ ℂ (fun _ => 0) (fun _ => 0) ∅ ∅).2.2.2.2 s

private lemma mem_acxC {σ E : Type} [LinearOrder σ] [AddCommGroup E] [Module ℂ E]
    (A : Finset σ → Submodule ℂ E) (w : σ → Module.End ℂ E) (n : ℤ) (c : Finset σ → E) :
    c ∈ (acx A w).C n ↔ ∀ s, c s ∈ (if (s.card : ℤ) = n then A s else ⊥) := by
  show c ∈ Submodule.pi Set.univ _ ↔ _
  simp only [Submodule.mem_pi, Set.mem_univ, true_implies]

private lemma wd_eq_zero {σ E : Type} [LinearOrder σ] [AddCommGroup E] [Module ℂ E]
    (w : σ → Module.End ℂ E) (f : Finset σ → E) (t : Finset σ)
    (h : ∀ i ∈ t, f (t.erase i) = 0) : wd w f t = 0 := by
  simp only [wd, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, LinearMap.proj_apply]
  exact Finset.sum_eq_zero fun i hi => by rw [h i hi]; simp

section
variable {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E]
  (T : Sys d S E) {κ : Type} [LinearOrder κ]

private lemma col_iff (n : κ → ℕ × ℕ) (z : κ → S) (I J : Finset (Fin (d + 1))) (m : ℤ)
    (x : Finset κ → E) : x ∈ (T.colCx n z I J).C m ↔ ∀ L, x L ∈ (if (L.card : ℤ) = m then
      (T.M I J).map (T.act ((∏ l ∈ L, T.u n (pk I) (pk J) l : Sˣ) : S)) else ⊥) :=
  mem_acxC _ _ _ _

private lemma cx_iff (hU : WdUni) (n : κ → ℕ × ℕ) (z : κ → S) (N : ℤ)
    (c : Finset (Two d ⊕ₗ κ) → E) : c ∈ (T.cx n z).C N ↔ ∀ I J L, c (uni (uni I J) L) ∈
      (if I.Nonempty ∧ J.Nonempty ∧ ((I.card + J.card + L.card : ℕ) : ℤ) = N then
        (T.M I J).map (T.act ((∏ l ∈ L, T.u n (pk I) (pk J) l : Sˣ) : S)) else ⊥) := by
  have key : ∀ (I J : Finset (Fin (d + 1))) (L : Finset κ),
      (if (((uni (uni I J) L).card : ℕ) : ℤ) = N then
        mixF (fun I' J' => Submodule.map (T.act ((∏ l ∈ rgt (uni (uni I J) L),
          T.u n (pk I') (pk J') l : Sˣ) : S)) (T.M I' J')) (lft (uni (uni I J) L)) else ⊥) =
      (if I.Nonempty ∧ J.Nonempty ∧ ((I.card + J.card + L.card : ℕ) : ℤ) = N then
        (T.M I J).map (T.act ((∏ l ∈ L, T.u n (pk I) (pk J) l : Sˣ) : S)) else ⊥) := by
    intro I J L
    simp only [lft_uni' hU, rgt_uni' hU, card_uni' hU, mixF]
    split_ifs <;> first | rfl | (exfalso; tauto)
  refine (mem_acxC _ _ N c).trans ?_
  constructor
  · intro h I J L
    rw [← key]
    exact h _
  · intro h s
    obtain ⟨I, J, L, rfl⟩ : ∃ I J L, s = uni (uni I J) L :=
      ⟨_, _, _, by rw [uni_lr' hU, uni_lr' hU]⟩
    rw [key]
    exact h I J L

private lemma top_C (hU : WdUni) (n : κ → ℕ × ℕ) (z : κ → S) (N : ℤ)
    (c : Finset (Two d ⊕ₗ κ) → E) (hc : c ∈ (T.cx n z).C N) : top c ∈ T.mix.C N := by
  refine (mem_acxC _ _ N _).mpr ?_
  intro b
  obtain ⟨I, J, rfl⟩ : ∃ I J, b = uni I J := ⟨lft b, rgt b, (uni_lr' hU b).symm⟩
  have h1 := (cx_iff T hU n z N c).mp hc I J ∅
  simp only [top, mixF, lft_uni' hU, rgt_uni' hU, card_uni' hU, Finset.prod_empty,
    Finset.card_empty, add_zero, Units.val_one, map_one] at h1 ⊢
  rw [Module.End.one_eq_id, Submodule.map_id] at h1
  split_ifs at h1 ⊢ <;> first | exact h1 | (exfalso; tauto) | simp_all

private lemma top_D (hU : WdUni) (z : κ → S) (c : Finset (Two d ⊕ₗ κ) → E) :
    top (wd (T.wt z) c) = wd (fun _ : Two d => (1 : Module.End ℂ E)) (top c) := by
  funext b
  simp only [top]
  rw [(hU _ _ _ (T.wt z) c b ∅).1]
  have h0 : wd (fun l => T.wt z (inrE l)) (fun L' => c (uni b L')) ∅ = 0 := by
    simp [wd]
  rw [h0, smul_zero, add_zero]
  have hw : (fun i => T.wt z (inlE i)) = fun _ : Two d => (1 : Module.End ℂ E) := by
    funext i
    simp [Sys.wt, inlE]
  rw [hw]
  rfl

end

private theorem wd_wt_resK_eq_zero_of_wd_eq_zero (hU : WdUni) (hB : WdBasic) {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S]
    [AddCommGroup E] [Module ℂ E] (T : Sys d S E) {κ : Type} [LinearOrder κ] [Fintype κ]
    (z : κ → S) {κ' : Type} [LinearOrder κ'] (e : κ' ↪o κ) (c : Finset (Two d ⊕ₗ κ) → E)
    (hD : wd (T.wt z) c = 0) : wd (T.wt fun l => z (e l)) (resK e c) = 0 := by
  have hwl : ∀ {κ₀ : Type} [LinearOrder κ₀] (z₀ : κ₀ → S) (i : Two d), T.wt z₀ (inlE i) = 1 := by
    intro κ₀ _ z₀ i
    simp [Sys.wt, inlE]
  have hwr : ∀ {κ₀ : Type} [LinearOrder κ₀] (z₀ : κ₀ → S) (l : κ₀), T.wt z₀ (inrE l) = T.act (z₀ l) := by
    intro κ₀ _ z₀ l
    simp [Sys.wt, inrE]
  funext s
  obtain ⟨b, L, rfl⟩ : ∃ b L, s = uni b L := ⟨lft s, rgt s, (uni_lr' hU s).symm⟩
  rw [(hU _ _ _ _ (resK e c) b L).1]
  have hres : ∀ b' L', resK e c (uni b' L') = c (uni b' (L'.map e.toEmbedding)) := by
    intro b' L'
    simp only [resK, lft_uni' hU, rgt_uni' hU]
  have hmap : wd (fun l => T.act (z (e l))) (fun L' => c (uni b (L'.map e.toEmbedding))) L =
      wd (fun l => T.act (z l)) (fun L' => c (uni b L')) (L.map e.toEmbedding) :=
    (hB κ E (fun _ => ⊥) (fun l => T.act (z l))).2.2.2.2.2 κ' e (fun L' => c (uni b L')) L
  have e2 := (hU _ _ _ (T.wt z) c b (L.map e.toEmbedding)).1
  rw [hD] at e2
  simp only [hres, hwl, hwr]
  rw [hmap]
  simp only [hwl, hwr] at e2
  rw [← e2]
  rfl

theorem UpperTheory.Gal.productCup_of_system.sysBasic_of :
    WdUni → WdBasic → SysBasic := by
  intro hU hB d S E _ _ _ _ T κ _ _ n z N
  have hmem : ∀ c, c ∈ (T.cx n z).C N → ∀ (I J : Finset (Fin (d + 1))) (L : Finset κ),
      ¬ (I.Nonempty ∧ J.Nonempty ∧ ((I.card + J.card + L.card : ℕ) : ℤ) = N) →
      c (uni (uni I J) L) = 0 := by
    intro c hc I J L h
    have := (cx_iff T hU n z N c).mp hc I J L
    rw [if_neg h] at this
    exact (Submodule.mem_bot ℂ).mp this
  have h2 : ∀ c : Finset (Two d ⊕ₗ κ) → E, c ∈ (T.cx n z).C N ↔
      ∀ (I J : Finset (Fin (d + 1))), col c (uni I J) ∈
        (if I.Nonempty ∧ J.Nonempty then (T.colCx n z I J).C (N - I.card - J.card) else ⊥) := by
    intro c
    rw [cx_iff T hU]
    refine forall_congr' fun I => forall_congr' fun J => ?_
    by_cases hIJ : I.Nonempty ∧ J.Nonempty
    · rw [if_pos hIJ, col_iff]
      refine forall_congr' fun L => ?_
      simp only [col]
      by_cases hL : (L.card : ℤ) = N - I.card - J.card
      · rw [if_pos hL, if_pos ⟨hIJ.1, hIJ.2, by push_cast; omega⟩]
      · rw [if_neg hL, if_neg (fun h => hL (by have := h.2.2; push_cast at this; omega))]
    · rw [if_neg hIJ, Submodule.mem_bot, funext_iff]
      refine forall_congr' fun L => ?_
      rw [if_neg (fun h => hIJ ⟨h.1, h.2.1⟩), Submodule.mem_bot]
      rfl
  have hwr : ∀ {κ₀ : Type} [LinearOrder κ₀] (z₀ : κ₀ → S) (l : κ₀), T.wt z₀ (inrE l) = T.act (z₀ l) := by
    intro κ₀ _ z₀ l
    simp [Sys.wt, inrE]
  refine ⟨?_, h2, ?_, ?_, ?_, ?_⟩
  · intro c hc I J L h
    apply hmem c hc I J L
    rintro ⟨hI, hJ, hN⟩
    rcases h with h | h | h
    · subst h; exact Finset.not_nonempty_empty hI
    · subst h; exact Finset.not_nonempty_empty hJ
    · exact h hN
  · intro c hc
    obtain ⟨hC, hD⟩ := Submodule.mem_inf.mp hc
    refine Submodule.mem_inf.mpr ⟨top_C T hU n z N c hC, ?_⟩
    rw [LinearMap.mem_ker] at hD ⊢
    change wd (fun _ : Two d => (1 : Module.End ℂ E)) (top c) = 0
    rw [← top_D T hU z c]
    change wd (T.wt z) c = 0 at hD
    rw [hD]
    rfl
  · intro c hc
    obtain ⟨c', hc', rfl⟩ := Submodule.mem_map.mp hc
    exact Submodule.mem_map.mpr ⟨top c', top_C T hU n z (N - 1) c' hc', (top_D T hU z c').symm⟩
  · intro c hc I J hI hJ hlow
    obtain ⟨hC, hD⟩ := Submodule.mem_inf.mp hc
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · have := (h2 c).mp hC I J
      rwa [if_pos ⟨hI, hJ⟩] at this
    · rw [LinearMap.mem_ker] at hD ⊢
      change wd (fun l => T.act (z l)) (col c (uni I J)) = 0
      change wd (T.wt z) c = 0 at hD
      funext L
      have e1 := (hU _ _ _ (T.wt z) c (uni I J) L).1
      rw [hD] at e1
      have key : ∀ t : Finset (Two d), t.card < (uni I J).card → c (uni t L) = 0 := by
        intro t ht
        rw [← uni_lr' hU t]
        apply hlow
        have h3 := card_uni' hU (lft t) (rgt t)
        rw [uni_lr' hU] at h3
        rw [card_uni' hU] at ht
        omega
      have hz1 : wd (fun b => T.wt z (inlE b)) (fun b' => c (uni b' L)) (uni I J) = 0 := by
        apply wd_eq_zero
        intro i hi
        exact key _ (Finset.card_erase_lt_of_mem hi)
      rw [hz1, zero_add] at e1
      simp only [hwr, Pi.zero_apply] at e1 ⊢
      rcases neg_one_pow_eq_or ℤ (uni I J).card with h | h <;> rw [h] at e1 <;> simp at e1 <;>
        first | exact e1.symm | exact e1 | exact neg_eq_zero.mp e1.symm
  · intro κ' _ _ e c hc
    obtain ⟨hC, hD⟩ := Submodule.mem_inf.mp hc
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · rw [cx_iff T hU]
      intro I J L
      have := (cx_iff T hU n z N c).mp hC I J (L.map e.toEmbedding)
      simp only [resK, lft_uni' hU, rgt_uni' hU]
      rw [Finset.card_map, Finset.prod_map] at this
      exact this
    · rw [LinearMap.mem_ker] at hD ⊢
      exact wd_wt_resK_eq_zero_of_wd_eq_zero hU hB T z e c hD
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.KoszulExactWeaklyRegular
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.RelativeK1Module
noncomputable def UpperTheory.Reformulated.B.KoszulComplexHomotopy.Stab :
    {S E : Type} →
      [inst : CommRing S] →
        [inst_1 : Algebra ℂ S] →
          [inst_2 : AddCommGroup E] →
            [inst_3 : _root_.Module ℂ E] → (S →ₐ[ℂ] Module.End ℂ E) → Subalgebra ℂ S → Submodule ℂ E → Prop :=
    fun {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [_root_.Module ℂ E] (act : S →ₐ[ℂ] Module.End ℂ E)
        (R : Subalgebra ℂ S) (M : Submodule ℂ E) ↦
      ∀ r ∈ R, ∀ m ∈ M, ((act : S → Module.End ℂ E) r : E → E) m ∈ M

noncomputable def UpperTheory.Reformulated.B.KoszulComplexHomotopy.wd :
    {k : Type} →
      [inst : Field k] →
        {ι : Type} →
          [LinearOrder ι] →
            {E : Type} →
              [inst_2 : AddCommGroup E] →
                [inst_3 : _root_.Module k E] → (ι → Module.End k E) → (Finset ι → E) →ₗ[k] Finset ι → E :=
    fun {k : Type} [Field k] {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E] [_root_.Module k E]
        (w : ι → Module.End k E) ↦
      LinearMap.pi fun (t : Finset ι) ↦ ∑ i ∈ t, GlobalTheory.cubeSign t i • w i ∘ₗ LinearMap.proj (t.erase i)

noncomputable def UpperTheory.Reformulated.B.KoszulComplexHomotopy.acx :
    {k : Type} →
      [inst : Field k] →
        {ι : Type} →
          [LinearOrder ι] →
            {E : Type} →
              [inst_2 : AddCommGroup E] →
                [inst_3 : _root_.Module k E] →
                  (Finset ι → Submodule k E) → (ι → Module.End k E) → GlobalTheory.PD.Cx k (Finset ι → E) :=
    fun {k : Type} [Field k] {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E] [_root_.Module k E]
        (A : Finset ι → Submodule k E) (w : ι → Module.End k E) ↦
      { C := fun (n : ℤ) ↦ Submodule.pi Set.univ fun (s : Finset ι) ↦ if (↑s.card : ℤ) = n then A s else ⊥,
        D := UpperTheory.Reformulated.B.KoszulComplexHomotopy.wd w : GlobalTheory.PD.Cx k (Finset ι → E) }

noncomputable def UpperTheory.Reformulated.B.KoszulComplexHomotopy.kos :
    {S E : Type} →
      [inst : CommRing S] →
        [inst_1 : Algebra ℂ S] →
          [inst_2 : AddCommGroup E] →
            [inst_3 : _root_.Module ℂ E] →
              (S →ₐ[ℂ] Module.End ℂ E) → {κ : Type} → [LinearOrder κ] → Submodule ℂ E → (κ → S) → GlobalTheory.PD.Cx ℂ (Finset κ → E) :=
    fun {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [_root_.Module ℂ E] (act : S →ₐ[ℂ] Module.End ℂ E)
        {κ : Type} [LinearOrder κ] (M : Submodule ℂ E) (r : κ → S) ↦
      UpperTheory.Reformulated.B.KoszulComplexHomotopy.acx (fun (x : Finset κ) ↦ M) fun (l : κ) ↦ (act : S → Module.End ℂ E) (r l)

noncomputable def UpperTheory.Reformulated.B.KoszulComplexHomotopy.InSp :
    {S κ : Type} → [inst : CommRing S] → [inst_1 : Algebra ℂ S] → [Fintype κ] → Subalgebra ℂ S → (κ → S) → S → Prop :=
    fun {S κ : Type} [CommRing S] [Algebra ℂ S] [Fintype κ] (R : Subalgebra ℂ S) (r : κ → S) (g : S) ↦
      ∃ (a : κ → S), (∀ (l : κ), a l ∈ R) ∧ g = ∑ l : κ, a l * r l

noncomputable def UpperTheory.Reformulated.B.KoszulComplexHomotopy.Htpy :
    Prop :=
    ∀ (S E : Type) [inst : CommRing S] [inst_1 : Algebra ℂ S] [inst_2 : AddCommGroup E] [inst_3 : _root_.Module ℂ E]
      (act : S →ₐ[ℂ] Module.End ℂ E) (κ : Type) [inst_4 : LinearOrder κ] [inst_5 : Fintype κ] (R : Subalgebra ℂ S)
      (M : Submodule ℂ E) (r : κ → S),
      UpperTheory.Reformulated.B.KoszulComplexHomotopy.Stab act R M →
        ∀ (n : ℤ),
          ∀ c ∈ (UpperTheory.Reformulated.B.KoszulComplexHomotopy.kos act M r).Z n,
            ∀ (g : S),
              UpperTheory.Reformulated.B.KoszulComplexHomotopy.InSp R r g →
                (fun (L : Finset κ) ↦ ((act : S → Module.End ℂ E) g : E → E) (c L)) ∈ (UpperTheory.Reformulated.B.KoszulComplexHomotopy.kos act M r).B n

noncomputable def UpperTheory.Reformulated.B.KoszulComplexHomotopy.KE :
    {M : Type} → [inst : AddCommGroup M] → [inst_1 : _root_.Module ℂ M] → GlobalTheory.PD.Cx ℂ M → ℤ → Prop :=
    fun {M : Type} [AddCommGroup M] [_root_.Module ℂ M] (C : GlobalTheory.PD.Cx ℂ M) (d : ℤ) ↦ ∀ m < d, C.Z m ≤ C.B m

noncomputable def UpperTheory.Reformulated.B.KoszulComplexHomotopy.KoszulExactBelowLengthOfWeaklyRegular :
    Prop :=
    ∀ (d : ℕ) (R N : Type) [inst : CommRing R] [inst_1 : Algebra ℂ R] [inst_2 : AddCommGroup N] [inst_3 : _root_.Module R N]
      [inst_4 : _root_.Module ℂ N] [inst_5 : IsScalarTower ℂ R N] (κ : Type) [inst_6 : LinearOrder κ] [inst_7 : Fintype κ]
      (r : κ → R) (f : List R),
      f.length = d →
        RingTheory.Sequence.IsWeaklyRegular N f →
          (∀ g ∈ f, UpperTheory.Reformulated.B.KoszulComplexHomotopy.InSp ⊤ r g) →
            UpperTheory.Reformulated.B.KoszulComplexHomotopy.KE (UpperTheory.Reformulated.B.KoszulComplexHomotopy.kos (Algebra.lsmul ℂ ℂ N) ⊤ r) (↑d : ℤ)

namespace UpperTheory.Reformulated.B.KoszulComplexHomotopy

section Helpers

variable {R N : Type} [CommRing R] [AddCommGroup N] [Module R N] {κ : Type} [LinearOrder κ]

private def dd (r : κ → R) (c : Finset κ → N) : Finset κ → N :=
  fun t => ∑ i ∈ t, GlobalTheory.cubeSign t i • r i • c (t.erase i)

private theorem dd_map {N' : Type} [AddCommGroup N'] [Module R N'] (φ : N →ₗ[R] N') (r : κ → R)
    (c : Finset κ → N) (t : Finset κ) : dd r (fun s => φ (c s)) t = φ (dd r c t) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [dd, map_sum]

private theorem dd_add (r : κ → R) (a b : Finset κ → N) (t : Finset κ) :
    dd r (fun s => a s + b s) t = dd r a t + dd r b t := by
  simp [dd, Finset.sum_add_distrib]

private theorem dd_deg (r : κ → R) (c : Finset κ → N) (n : ℤ)
    (hc : ∀ s : Finset κ, (s.card : ℤ) ≠ n - 1 → c s = 0) (t : Finset κ) (ht : (t.card : ℤ) ≠ n) :
    dd r c t = 0 := by
  refine Finset.sum_eq_zero fun i hi => ?_
  have h := Finset.card_erase_add_one hi
  rw [hc _ (by omega), smul_zero, smul_zero]

private theorem dd_dd [Module ℂ N] (r : κ → R) (c : Finset κ → N) (t : Finset κ) :
    dd r (dd r c) t = 0 := by
  let F : κ → κ → N := fun i j =>
    if j ≠ i then (GlobalTheory.cubeSign t i * GlobalTheory.cubeSign (t.erase i) j) • (r i * r j) • c ((t.erase i).erase j)
    else 0
  have h1 : dd r (dd r c) t = ∑ i ∈ t, ∑ j ∈ t, F i j := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [F]
    rw [← Finset.sum_filter, Finset.filter_ne', dd, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_smul, mul_smul, smul_comm (r i)]
  have h2 : ∀ i ∈ t, ∀ j ∈ t, F i j + F j i = 0 := by
    intro i hi j hj
    by_cases h : j = i
    · simp [F, h]
    · simp only [F]
      rw [if_pos h, if_pos (Ne.symm h), GlobalTheory.cubeSign_mul_erase hi hj (Ne.symm h), mul_comm (r j),
        Finset.erase_right_comm (a := j), neg_smul, neg_add_cancel]
  have h3 : (∑ i ∈ t, ∑ j ∈ t, F i j) + ∑ i ∈ t, ∑ j ∈ t, F j i = 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_eq_zero fun j hj => h2 i hi j hj
  rw [Finset.sum_comm (f := fun i j => F j i), ← two_smul ℂ] at h3
  rw [h1]
  exact (smul_eq_zero.1 h3).resolve_left two_ne_zero

variable [Algebra ℂ R] [Module ℂ N] [IsScalarTower ℂ R N]

private theorem kos_D (r : κ → R) (c : Finset κ → N) :
    (kos (Algebra.lsmul ℂ ℂ N) ⊤ r).D c = dd r c := by
  funext t
  simp [kos, acx, wd, dd]

private theorem kos_C (r : κ → R) (c : Finset κ → N) (n : ℤ) :
    c ∈ (kos (Algebra.lsmul ℂ ℂ N) ⊤ r).C n ↔ ∀ s : Finset κ, (s.card : ℤ) ≠ n → c s = 0 := by
  simp only [kos, acx, Submodule.mem_pi, Set.mem_univ, true_imp_iff]
  refine forall_congr' fun s => ?_
  by_cases h : (s.card : ℤ) = n <;> simp [h]

private theorem kos_Z (r : κ → R) (c : Finset κ → N) (n : ℤ) :
    c ∈ (kos (Algebra.lsmul ℂ ℂ N) ⊤ r).Z n ↔
      (∀ s : Finset κ, (s.card : ℤ) ≠ n → c s = 0) ∧ dd r c = 0 := by
  rw [GlobalTheory.PD.Cx.Z, Submodule.mem_inf, kos_C, LinearMap.mem_ker, kos_D]

private theorem kos_B (r : κ → R) (c : Finset κ → N) (n : ℤ) :
    c ∈ (kos (Algebra.lsmul ℂ ℂ N) ⊤ r).B n ↔
      ∃ b : Finset κ → N, (∀ s : Finset κ, (s.card : ℤ) ≠ n - 1 → b s = 0) ∧ dd r b = c := by
  simp only [GlobalTheory.PD.Cx.B, Submodule.mem_map, kos_C, kos_D]

end Helpers

end UpperTheory.Reformulated.B.KoszulComplexHomotopy

open scoped Pointwise in
theorem UpperTheory.Reformulated.B.KoszulComplexHomotopy.koszulExactBelowLengthOfWeaklyRegular_of_htpy :
    UpperTheory.Reformulated.B.KoszulComplexHomotopy.Htpy → UpperTheory.Reformulated.B.KoszulComplexHomotopy.KoszulExactBelowLengthOfWeaklyRegular := by
  intro H d
  induction d with
  | zero =>
    intro R N _ _ _ _ _ _ κ _ _ r f _ _ _ m hm c hc
    have h0 : c = 0 := funext fun s => ((kos_Z r c m).1 hc).1 s (by omega)
    rw [h0]
    exact Submodule.zero_mem _
  | succ d ih =>
    intro R N _ _ _ _ _ _ κ _ _ r f hlen hreg hsp m hm c hc
    obtain _ | ⟨g, f⟩ := f
    · simp at hlen
    rw [RingTheory.Sequence.isWeaklyRegular_cons_iff] at hreg
    obtain ⟨hg, hf⟩ := hreg
    have hB := H R N (Algebra.lsmul ℂ ℂ N) κ ⊤ ⊤ r (fun _ _ _ _ => Submodule.mem_top) m c hc g
      (hsp g List.mem_cons_self)
    obtain ⟨b, hb, hbc⟩ := (kos_B r _ m).1 hB
    have hbc' : ∀ s, dd r b s = g • c s := fun s => congrFun hbc s
    let P : Submodule R N := g • (⊤ : Submodule R N)
    have hP : ∀ x : N, P.mkQ x = 0 ↔ ∃ y, g • y = x := by
      intro x
      simp [P, Submodule.mem_smul_pointwise_iff_exists]
    have IH := ih R (N ⧸ P) κ r f (by simpa using hlen) hf
      (fun x hx => hsp x (List.mem_cons_of_mem _ hx)) (m - 1) (by omega)
    have hZ : (fun s => P.mkQ (b s)) ∈ (kos (Algebra.lsmul ℂ ℂ (N ⧸ P)) ⊤ r).Z (m - 1) := by
      rw [kos_Z]
      refine ⟨fun s hs => by rw [hb s hs, map_zero], funext fun s => ?_⟩
      rw [dd_map, hbc']
      exact (hP _).2 ⟨_, rfl⟩
    obtain ⟨a, ha, hab⟩ := (kos_B r _ _).1 (IH hZ)
    have hlift : ∀ s : Finset κ, ∃ x : N, P.mkQ x = a s ∧ ((s.card : ℤ) ≠ m - 1 - 1 → x = 0) := by
      intro s
      by_cases hs : (s.card : ℤ) = m - 1 - 1
      · obtain ⟨x, hx⟩ := P.mkQ_surjective (a s)
        exact ⟨x, hx, fun h => absurd hs h⟩
      · exact ⟨0, by rw [ha s hs, map_zero], fun _ => rfl⟩
    choose a' ha' ha0 using hlift
    have hdiv : ∀ s, ∃ y, g • y = b s - dd r a' s := by
      intro s
      rw [← hP, map_sub, ← dd_map, funext ha', hab, sub_self]
    choose y hy using hdiv
    rw [kos_B]
    refine ⟨y, fun s hs => hg ?_, funext fun s => hg ?_⟩
    · show g • y s = g • (0 : N)
      rw [hy, hb s hs, dd_deg r a' _ ha0 s hs, sub_zero, smul_zero]
    · show g • dd r y s = g • c s
      have e : b = fun s => dd r a' s + (LinearMap.lsmul R N g) (y s) := by
        funext s
        rw [LinearMap.lsmul_apply, hy, add_sub_cancel]
      rw [← hbc', e, dd_add, dd_dd, dd_map, zero_add, LinearMap.lsmul_apply]
end

open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct Pointwise

section
variable {σ E : Type} [LinearOrder σ] [AddCommGroup E] [Module ℂ E]

end

section
variable {R κ : Type} [CommRing R] [Algebra ℂ R] [LinearOrder κ]
  {N N' : Type} [AddCommGroup N] [Module R N] [Module ℂ N] [IsScalarTower ℂ R N]
  [AddCommGroup N'] [Module R N'] [Module ℂ N'] [IsScalarTower ℂ R N']

end

section
variable {R κ : Type} [CommRing R] [Algebra ℂ R] [LinearOrder κ] [Fintype κ]

end

theorem UpperTheory.Gal.productCup_of_system.koszulExactBelowLengthOfWeaklyRegular_of_htpy :
    Htpy → KoszulExactBelowLengthOfWeaklyRegular :=
  _root_.UpperTheory.Reformulated.B.KoszulComplexHomotopy.koszulExactBelowLengthOfWeaklyRegular_of_htpy
end
