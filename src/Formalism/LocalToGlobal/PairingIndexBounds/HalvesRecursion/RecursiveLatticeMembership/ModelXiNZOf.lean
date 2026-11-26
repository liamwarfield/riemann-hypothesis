module

public import Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.Statement
public import Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.ModelIndexPairings.GenModelXiOf

@[expose] public section

section -- merged from Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.ModelIndexPairings.FourierTransformIdentityHolds
noncomputable section
open scoped BigOperators

namespace Formalism.L2.PairingIndexBounds.Mv

variable {k : Type*} [Field k] {A B T : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup T] [Module k T]

section bichar
variable {c : B → A → k}

theorem IsBichar.map_zero_right (hc : IsBichar c) (b : B) : c b 0 = 1 := by
  have h := hc.2.2 b 0 0
  rw [add_zero] at h
  exact mul_left_cancel₀ (hc.1 b 0) (by rw [mul_one]; exact h.symm)

theorem IsBichar.map_zero_left (hc : IsBichar c) (a : A) : c 0 a = 1 := by
  have h := hc.2.1 0 0 a
  rw [add_zero] at h
  exact mul_left_cancel₀ (hc.1 0 a) (by rw [mul_one]; exact h.symm)

theorem IsBichar.map_neg_left (hc : IsBichar c) (b : B) (a : A) : c (-b) a = (c b a)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← hc.2.1, neg_add_cancel, hc.map_zero_left]

theorem IsBichar.map_sub_left (hc : IsBichar c) (b b' : B) (a : A) : c (b - b') a = c b a * (c b' a)⁻¹ := by
  rw [sub_eq_add_neg, hc.2.1, hc.map_neg_left]

end bichar

theorem ind_of_mem {S : Set A} {t : A} (h : t ∈ S) : ind (k := k) S t = 1 := by
  unfold ind; exact if_pos h

theorem ind_of_not_mem {S : Set A} {t : A} (h : t ∉ S) : ind (k := k) S t = 0 := by
  unfold ind; exact if_neg h

theorem gen_apply (c : B → A → k) (A₀ : AddSubgroup A) (a : A) (b : B) (t : A) :
    gen c A₀ a b t = c b (t + a) * ind (A₀ : Set A) (t + a) := rfl

theorem sum_reps_eq_zero {G : Type*} [AddCommGroup G] (M N : AddSubgroup G) (S : Finset G) (hS : IsRepsG M N S)
    (f : G → k) (hadd : ∀ x y, f (x + y) = f x * f y) (hM : ∀ x ∈ M, f x = 1) (g₀ : G) (hg₀ : g₀ ∈ N)
    (hne : f g₀ ≠ 1) : ∑ x ∈ S, f x = 0 := by
  obtain ⟨hSN, hSinj, hSsurj⟩ := hS
  choose! σ hσ using hSsurj
  have hfσ : ∀ y ∈ N, f (σ y) = f y := by
    intro y hy
    have h1 : y = (y - σ y) + σ y := by abel
    conv_rhs => rw [h1, hadd, hM _ (hσ y hy).2, one_mul]
  have key : ∑ x ∈ S, f g₀ * f x = ∑ x ∈ S, f x := by
    refine Finset.sum_nbij (fun x => σ (g₀ + x)) ?_ ?_ ?_ ?_
    · intro x hx
      exact (hσ _ (N.add_mem hg₀ (hSN x hx))).1
    · intro x hx y hy hxy
      have hx' := (hσ _ (N.add_mem hg₀ (hSN x hx))).2
      have hy' := (hσ _ (N.add_mem hg₀ (hSN y hy))).2
      simp only at hxy
      rw [hxy] at hx'
      apply hSinj x hx y hy
      have := M.sub_mem hx' hy'
      have e : g₀ + x - σ (g₀ + y) - (g₀ + y - σ (g₀ + y)) = x - y := by abel
      rwa [e] at this
    · intro y hy
      have hyN : y - g₀ ∈ N := N.sub_mem (hSN y hy) hg₀
      have h1 := hσ _ hyN
      refine ⟨σ (y - g₀), h1.1, ?_⟩
      have h2 := hσ _ (N.add_mem hg₀ (hSN _ h1.1))
      simp only
      symm
      apply hSinj y hy _ h2.1
      have := M.add_mem h1.2 h2.2
      have e : y - g₀ - σ (y - g₀) + (g₀ + σ (y - g₀) - σ (g₀ + σ (y - g₀))) = y - σ (g₀ + σ (y - g₀)) := by abel
      rwa [e] at this
    · intro x hx
      rw [hfσ _ (N.add_mem hg₀ (hSN x hx)), hadd]
  rw [← Finset.mul_sum] at key
  have h2 : (f g₀ - 1) * ∑ x ∈ S, f x = 0 := by rw [sub_mul, key, one_mul, sub_self]
  rcases mul_eq_zero.mp h2 with h | h
  · exact absurd (sub_eq_zero.mp h) hne
  · exact h

theorem sum_reps_ind {G : Type*} [AddCommGroup G] (M N : AddSubgroup G) (S : Finset G) (hS : IsRepsG M N S) (t : G) :
    ∑ a ∈ S, ind (k := k) (M : Set G) (t + a) * ind (k := k) (N : Set G) (t + a) = ind (k := k) (N : Set G) t := by
  obtain ⟨hSN, hSinj, hSsurj⟩ := hS
  by_cases ht : t ∈ N
  · obtain ⟨x, hxS, hx⟩ := hSsurj (-t) (N.neg_mem ht)
    have hxM : t + x ∈ M := by
      have := M.neg_mem hx
      have e : -(-t - x) = t + x := by abel
      rwa [e] at this
    rw [Finset.sum_eq_single x]
    · rw [ind_of_mem (show t + x ∈ (M : Set G) from hxM),
        ind_of_mem (show t + x ∈ (N : Set G) from N.add_mem ht (hSN x hxS)),
        ind_of_mem (show t ∈ (N : Set G) from ht), one_mul]
    · intro a haS hax
      have : t + a ∉ (M : Set G) := by
        intro h
        apply hax
        apply hSinj a haS x hxS
        have := M.add_mem h hx
        have e : t + a + (-t - x) = a - x := by abel
        rwa [e] at this
      rw [ind_of_not_mem this, zero_mul]
    · intro h; exact absurd hxS h
  · rw [ind_of_not_mem (show t ∉ (N : Set G) from ht)]
    apply Finset.sum_eq_zero
    intro a ha
    have : t + a ∉ (N : Set G) := by
      intro h
      apply ht
      have := N.sub_mem h (hSN a ha)
      rwa [add_sub_cancel_right] at this
    rw [ind_of_not_mem this, mul_zero]

theorem model_moves_hold : ModelMoves := by
  intro k _ A B _ _ c hc A₁ A₂ B₁ B₂ hB₁ h22 hA SA SB hSA hSB
  funext t
  have hL : (∑ a ∈ SA, ∑ b ∈ SB, rhoA a (rhoB c b (ind (A₁ : Set A)))) t
      = ∑ a ∈ SA, ∑ b ∈ SB, c b (t + a) * ind (A₁ : Set A) (t + a) := by
    simp only [Finset.sum_apply]; rfl
  have inner : ∀ u : A, ∑ b ∈ SB, c b u * ind (A₁ : Set A) u
      = (SB.card : k) * (ind (A₁ : Set A) u * ind (A₂ : Set A) u) := by
    intro u
    by_cases hu1 : u ∈ A₁
    · rw [ind_of_mem (show u ∈ (A₁ : Set A) from hu1)]
      by_cases hu2 : u ∈ A₂
      · rw [ind_of_mem (show u ∈ (A₂ : Set A) from hu2)]
        rw [Finset.sum_congr rfl (fun b hb => by rw [h22 b (hSB.1 b hb) u hu2])]
        simp
      · rw [ind_of_not_mem (show u ∉ (A₂ : Set A) from hu2)]
        have hex : ∃ b₀ ∈ B₂, c b₀ u ≠ 1 := by
          by_contra hcon
          push Not at hcon
          exact hu2 (hA u hu1 hcon)
        obtain ⟨b₀, hb₀, hne⟩ := hex
        have := sum_reps_eq_zero B₁ B₂ SB hSB (fun b => c b u) (fun x y => hc.2.1 x y u)
          (fun x hx => (hB₁ x).mp hx u hu1) b₀ hb₀ hne
        simp only [mul_one, mul_zero]
        exact this
    · rw [ind_of_not_mem (show u ∉ (A₁ : Set A) from hu1)]
      simp
  rw [hL, Finset.sum_congr rfl (fun a _ => inner (t + a)), ← Finset.mul_sum, sum_reps_ind A₁ A₂ SA hSA t]
  rfl

section Heisenberg₂
variable {c : B → A → k} {WA : A → T →ₗ[k] T} {WB : B → T →ₗ[k] T}

theorem IsHeis.WA_add (hW : IsHeis c WA WB) (a a' : A) (x : T) : WA (a + a') x = WA a (WA a' x) := by
  rw [hW.2.1]; rfl

theorem IsHeis.WB_add (hW : IsHeis c WA WB) (b b' : B) (x : T) : WB (b + b') x = WB b (WB b' x) := by
  rw [hW.2.2.2.1]; rfl

theorem IsHeis.comm (hW : IsHeis c WA WB) (a : A) (b : B) (x : T) : WA a (WB b x) = c b a • WB b (WA a x) :=
  LinearMap.congr_fun (hW.2.2.2.2 a b) x

end Heisenberg₂

theorem Sch_ext {c : B → A → k} {A₀ : AddSubgroup A} {f g : Sch c A₀ →ₗ[k] T}
    (h : ∀ a b, f ⟨gen c A₀ a b, gen_mem c A₀ a b⟩ = g ⟨gen c A₀ a b, gen_mem c A₀ a b⟩) : f = g := by
  ext ⟨Φ, hΦ⟩
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨a, b⟩, rfl⟩ := hx
    exact h a b
  | zero =>
    have e : (⟨0, Submodule.zero_mem _⟩ : Sch c A₀) = 0 := rfl
    rw [e, map_zero, map_zero]
  | add x y hx hy ihx ihy =>
    have e : (⟨x + y, Submodule.add_mem _ hx hy⟩ : Sch c A₀) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
    rw [e, map_add (f := _), map_add (f := _), ihx, ihy]
  | smul r x hx ih =>
    have e : (⟨r • x, Submodule.smul_mem _ r hx⟩ : Sch c A₀) = r • ⟨x, hx⟩ := rfl
    rw [e, map_smul, map_smul, ih]

def chi (c : B → A → k) (hc : IsBichar c) (A₀ : AddSubgroup A) (b : B) : Multiplicative A₀ →* k where
  toFun s := c b ((Multiplicative.toAdd s : A₀) : A)
  map_one' := hc.map_zero_right b
  map_mul' _ _ := hc.2.2 b _ _

theorem chi_apply (c : B → A → k) (hc : IsBichar c) (A₀ : AddSubgroup A) (b : B) (s : A₀) :
    chi c hc A₀ b (Multiplicative.ofAdd s) = c b (s : A) := rfl

def eFam (A₀ : AddSubgroup A) (i : (A ⧸ A₀) × (Multiplicative A₀ →* k)) : A → k := by
  classical exact fun t => if h : t + i.1.out ∈ A₀ then i.2 (Multiplicative.ofAdd ⟨t + i.1.out, h⟩) else 0

theorem eFam_of_mem (A₀ : AddSubgroup A) (i : (A ⧸ A₀) × (Multiplicative A₀ →* k)) (t : A) (h : t + i.1.out ∈ A₀) :
    eFam A₀ i t = i.2 (Multiplicative.ofAdd ⟨t + i.1.out, h⟩) := by
  unfold eFam; exact dif_pos h

theorem eFam_of_not_mem (A₀ : AddSubgroup A) (i : (A ⧸ A₀) × (Multiplicative A₀ →* k)) (t : A) (h : t + i.1.out ∉ A₀) :
    eFam A₀ i t = 0 := by
  unfold eFam; exact dif_neg h

theorem out_sub_mem (A₀ : AddSubgroup A) (a : A) : a - (QuotientAddGroup.mk a : A ⧸ A₀).out ∈ A₀ := by
  obtain ⟨h, hh⟩ := QuotientAddGroup.mk_out_eq_add A₀ a
  rw [hh]
  have e : a - (a + (h : A)) = -(h : A) := by abel
  rw [e]
  exact A₀.neg_mem h.2

theorem eq_of_out_sub_mem (A₀ : AddSubgroup A) (q q' : A ⧸ A₀) (h : q.out - q'.out ∈ A₀) : q = q' := by
  rw [← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' q']
  symm
  rw [QuotientAddGroup.eq]
  have e : -q'.out + q.out = q.out - q'.out := by abel
  rwa [e]

theorem eFam_li (A₀ : AddSubgroup A) : LinearIndependent k (eFam (k := k) A₀) := by
  classical
  rw [linearIndependent_iff']
  rintro s g hg ⟨q₀, χ₀⟩ hi₀
  have hli := linearIndependent_monoidHom (Multiplicative A₀) k
  rw [linearIndependent_iff'] at hli
  refine hli ((s.filter (fun i => i.1 = q₀)).image Prod.snd) (fun χ => g (q₀, χ)) ?_ χ₀ ?_
  · funext x
    have h1 := congrFun hg (((Multiplicative.toAdd x : A₀) : A) - q₀.out)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1 ⊢
    rw [Finset.sum_image, Finset.sum_filter]
    · refine (Finset.sum_congr rfl ?_).trans h1
      rintro ⟨q, χ⟩ _
      by_cases hq : q = q₀
      · subst hq
        have hm : ((Multiplicative.toAdd x : A₀) : A) - q.out + q.out ∈ A₀ := by
          rw [sub_add_cancel]; exact (Multiplicative.toAdd x).2
        rw [if_pos rfl, eFam_of_mem A₀ (q, χ) _ hm]
        congr 2
        apply Subtype.ext
        simp
      · have hm : ((Multiplicative.toAdd x : A₀) : A) - q₀.out + q.out ∉ A₀ := by
          intro hm
          apply hq
          apply eq_of_out_sub_mem A₀
          have := A₀.sub_mem hm (Multiplicative.toAdd x).2
          have e : ((Multiplicative.toAdd x : A₀) : A) - q₀.out + q.out - ((Multiplicative.toAdd x : A₀) : A)
              = q.out - q₀.out := by abel
          rwa [e] at this
        rw [if_neg hq, eFam_of_not_mem A₀ (q, χ) _ hm, mul_zero]
    · rintro ⟨q, χ⟩ h ⟨q', χ'⟩ h' hh
      rw [Finset.mem_coe, Finset.mem_filter] at h h'
      simp only at hh
      exact Prod.ext (h.2.trans h'.2.symm) hh
  · exact Finset.mem_image.mpr ⟨(q₀, χ₀), Finset.mem_filter.mpr ⟨hi₀, rfl⟩, rfl⟩

theorem gen_eq_eFam (c : B → A → k) (hc : IsBichar c) (A₀ : AddSubgroup A) (a : A) (b : B) :
    gen c A₀ a b = c b (a - (QuotientAddGroup.mk a : A ⧸ A₀).out) •
      eFam A₀ ((QuotientAddGroup.mk a : A ⧸ A₀), chi c hc A₀ b) := by
  funext t
  have h0 := out_sub_mem A₀ a
  rw [gen_apply, Pi.smul_apply, smul_eq_mul]
  by_cases h : t + (QuotientAddGroup.mk a : A ⧸ A₀).out ∈ A₀
  · have h' : t + a ∈ A₀ := by
      have := A₀.add_mem h h0
      have e : t + (QuotientAddGroup.mk a : A ⧸ A₀).out + (a - (QuotientAddGroup.mk a : A ⧸ A₀).out) = t + a := by abel
      rwa [e] at this
    rw [ind_of_mem (show t + a ∈ (A₀ : Set A) from h'), mul_one,
      eFam_of_mem A₀ ((QuotientAddGroup.mk a : A ⧸ A₀), chi c hc A₀ b) t h, chi_apply, ← hc.2.2]
    congr 1
    change t + a = a - (QuotientAddGroup.mk a : A ⧸ A₀).out + (t + (QuotientAddGroup.mk a : A ⧸ A₀).out)
    abel
  · have h' : t + a ∉ (A₀ : Set A) := by
      intro h'
      apply h
      have := A₀.sub_mem h' h0
      have e : t + a - (a - (QuotientAddGroup.mk a : A ⧸ A₀).out) = t + (QuotientAddGroup.mk a : A ⧸ A₀).out := by abel
      rwa [e] at this
    rw [ind_of_not_mem h', eFam_of_not_mem A₀ ((QuotientAddGroup.mk a : A ⧸ A₀), chi c hc A₀ b) t h, mul_zero, mul_zero]

def wFam (c : B → A → k) (hc : IsBichar c) (WA : A → T →ₗ[k] T) (WB : B → T →ₗ[k] T) (A₀ : AddSubgroup A) (θ : T)
    (i : (A ⧸ A₀) × (Multiplicative A₀ →* k)) : T := by
  classical exact if h : ∃ b, chi c hc A₀ b = i.2 then WA i.1.out (WB h.choose θ) else 0

theorem W_eq_wFam (c : B → A → k) (hc : IsBichar c) (WA : A → T →ₗ[k] T) (WB : B → T →ₗ[k] T) (hW : IsHeis c WA WB)
    (A₀ : AddSubgroup A) (θ : T) (hA : ∀ a ∈ A₀, WA a θ = θ) (hB : ∀ b, (∀ a ∈ A₀, c b a = 1) → WB b θ = θ)
    (a : A) (b : B) :
    WA a (WB b θ) = c b (a - (QuotientAddGroup.mk a : A ⧸ A₀).out) •
      wFam c hc WA WB A₀ θ ((QuotientAddGroup.mk a : A ⧸ A₀), chi c hc A₀ b) := by
  have h0 := out_sub_mem A₀ a
  have hex : ∃ b', chi c hc A₀ b' = chi c hc A₀ b := ⟨b, rfl⟩
  have hw : wFam c hc WA WB A₀ θ ((QuotientAddGroup.mk a : A ⧸ A₀), chi c hc A₀ b)
      = WA (QuotientAddGroup.mk a : A ⧸ A₀).out (WB hex.choose θ) := by
    unfold wFam; exact dif_pos hex
  have hb' : ∀ s ∈ A₀, c hex.choose s = c b s := by
    intro s hs
    have := DFunLike.congr_fun hex.choose_spec (Multiplicative.ofAdd (⟨s, hs⟩ : A₀))
    rwa [chi_apply, chi_apply] at this
  have hθ : WB b θ = WB hex.choose θ := by
    have e : b = hex.choose + (b - hex.choose) := by abel
    conv_lhs => rw [e, hW.WB_add]
    rw [hB (b - hex.choose)]
    intro s hs
    rw [hc.map_sub_left, hb' s hs, mul_inv_cancel₀ (hc.1 b s)]
  rw [hw, hθ]
  have e : a = (QuotientAddGroup.mk a : A ⧸ A₀).out + (a - (QuotientAddGroup.mk a : A ⧸ A₀).out) := by abel
  conv_lhs => rw [e, hW.WA_add, hW.comm, hA _ h0, map_smul, hb' _ h0]

theorem Sch_le_span_eFam (c : B → A → k) (hc : IsBichar c) (A₀ : AddSubgroup A) :
    Sch c A₀ ≤ Submodule.span k (Set.range (eFam (k := k) A₀)) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨a, b⟩, rfl⟩
  simp only
  rw [gen_eq_eFam c hc A₀ a b]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

theorem xi_existence_holds : XiExists := by
  intro k _ A B T _ _ _ _ c WA WB hc hW A₀ θ hA hB
  refine ⟨(Finsupp.linearCombination k (wFam c hc WA WB A₀ θ)) ∘ₗ (eFam_li (k := k) A₀).repr ∘ₗ
    Submodule.inclusion (Sch_le_span_eFam c hc A₀), ?_, ?_⟩
  · intro a b
    have e : Submodule.inclusion (Sch_le_span_eFam c hc A₀) ⟨gen c A₀ a b, gen_mem c A₀ a b⟩
        = c b (a - (QuotientAddGroup.mk a : A ⧸ A₀).out) •
          (⟨eFam A₀ ((QuotientAddGroup.mk a : A ⧸ A₀), chi c hc A₀ b), Submodule.subset_span ⟨_, rfl⟩⟩ :
            Submodule.span k (Set.range (eFam (k := k) A₀))) := by
      apply Subtype.ext
      exact gen_eq_eFam c hc A₀ a b
    rw [LinearMap.comp_apply, LinearMap.comp_apply, e, map_smul, map_smul,
      (eFam_li (k := k) A₀).repr_eq_single ((QuotientAddGroup.mk a : A ⧸ A₀), chi c hc A₀ b) _ rfl,
      Finsupp.linearCombination_single, one_smul]
    exact (W_eq_wFam c hc WA WB hW A₀ θ hA hB a b).symm
  · intro Xi' hXi'
    apply Sch_ext
    intro a b
    rw [hXi' a b]
    have e : Submodule.inclusion (Sch_le_span_eFam c hc A₀) ⟨gen c A₀ a b, gen_mem c A₀ a b⟩
        = c b (a - (QuotientAddGroup.mk a : A ⧸ A₀).out) •
          (⟨eFam A₀ ((QuotientAddGroup.mk a : A ⧸ A₀), chi c hc A₀ b), Submodule.subset_span ⟨_, rfl⟩⟩ :
            Submodule.span k (Set.range (eFam (k := k) A₀))) := by
      apply Subtype.ext
      exact gen_eq_eFam c hc A₀ a b
    rw [LinearMap.comp_apply, LinearMap.comp_apply, e, map_smul, map_smul,
      (eFam_li (k := k) A₀).repr_eq_single ((QuotientAddGroup.mk a : A ⧸ A₀), chi c hc A₀ b) _ rfl,
      Finsupp.linearCombination_single, one_smul]
    exact W_eq_wFam c hc WA WB hW A₀ θ hA hB a b

theorem rhoA_gen (c : B → A → k) (A₀ : AddSubgroup A) (a' a : A) (b : B) :
    rhoA a' (gen c A₀ a b) = gen c A₀ (a' + a) b := by
  funext t
  change gen c A₀ a b (t + a') = _
  rw [gen_apply, gen_apply, add_assoc]

theorem rhoB_gen (c : B → A → k) (hc : IsBichar c) (A₀ : AddSubgroup A) (b' : B) (a : A) (b : B) :
    rhoB c b' (gen c A₀ a b) = (c b' a)⁻¹ • gen c A₀ a (b' + b) := by
  funext t
  change c b' t * gen c A₀ a b t = (c b' a)⁻¹ * gen c A₀ a (b' + b) t
  rw [gen_apply, gen_apply, hc.2.1, hc.2.2 b' t a]
  have h := hc.1 b' a
  field_simp

theorem rhoA_mem (c : B → A → k) (A₀ : AddSubgroup A) (a : A) : ∀ Φ ∈ Sch c A₀, rhoA a Φ ∈ Sch c A₀ := by
  intro Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨a', b⟩, rfl⟩ := hx
    simp only
    rw [rhoA_gen]
    exact gen_mem c A₀ _ _
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ ihx ihy => rw [map_add (f := _)]; exact Submodule.add_mem _ ihx ihy
  | smul r x _ ih => rw [map_smul]; exact Submodule.smul_mem _ r ih

theorem rhoB_mem (c : B → A → k) (hc : IsBichar c) (A₀ : AddSubgroup A) (b : B) :
    ∀ Φ ∈ Sch c A₀, rhoB c b Φ ∈ Sch c A₀ := by
  intro Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨a, b'⟩, rfl⟩ := hx
    simp only
    rw [rhoB_gen c hc]
    exact Submodule.smul_mem _ _ (gen_mem c A₀ _ _)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ ihx ihy => rw [map_add (f := _)]; exact Submodule.add_mem _ ihx ihy
  | smul r x _ ih => rw [map_smul]; exact Submodule.smul_mem _ r ih

theorem xi_intersection_holds : XiInter := by
  intro k _ A B T _ _ _ _ c WA WB hc hW A₀ θ Xi hXi Φ hΦ
  constructor
  · intro a
    refine ⟨rhoA_mem c A₀ a Φ hΦ, ?_⟩
    have key : Xi ∘ₗ (rhoA a).restrict (rhoA_mem c A₀ a) = WA a ∘ₗ Xi := by
      apply Sch_ext
      intro a' b
      have e : (rhoA a).restrict (rhoA_mem c A₀ a) ⟨gen c A₀ a' b, gen_mem c A₀ a' b⟩
          = ⟨gen c A₀ (a + a') b, gen_mem c A₀ (a + a') b⟩ := Subtype.ext (rhoA_gen c A₀ a a' b)
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hXi, e, hXi, hW.WA_add]
    exact LinearMap.congr_fun key ⟨Φ, hΦ⟩
  · intro b
    refine ⟨rhoB_mem c hc A₀ b Φ hΦ, ?_⟩
    have key : Xi ∘ₗ (rhoB c b).restrict (rhoB_mem c hc A₀ b) = WB b ∘ₗ Xi := by
      apply Sch_ext
      intro a b'
      have e : (rhoB c b).restrict (rhoB_mem c hc A₀ b) ⟨gen c A₀ a b', gen_mem c A₀ a b'⟩
          = (c b a)⁻¹ • ⟨gen c A₀ a (b + b'), gen_mem c A₀ a (b + b')⟩ := Subtype.ext (rhoB_gen c hc A₀ b a b')
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hXi, e, map_smul, hXi, hW.WB_add, hW.comm, smul_smul,
        inv_mul_cancel₀ (hc.1 b a), one_smul]
    exact LinearMap.congr_fun key ⟨Φ, hΦ⟩

theorem Xi_of_eq_sum {c : B → A → k} {WA : A → T →ₗ[k] T} {WB : B → T →ₗ[k] T} {A₀ : AddSubgroup A} {θ : T}
    {Xi : Sch c A₀ →ₗ[k] T} (hXi : IsXi c WA WB A₀ θ Xi) {ι : Type*} (s : Finset ι) (r : ι → k) (a : ι → A)
    (b : ι → B) (Φ : A → k) (hΦ : Φ = ∑ i ∈ s, r i • gen c A₀ (a i) (b i)) :
    ∃ h : Φ ∈ Sch c A₀, Xi ⟨Φ, h⟩ = ∑ i ∈ s, r i • WA (a i) (WB (b i) θ) := by
  subst hΦ
  refine ⟨Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (gen_mem c A₀ _ _), ?_⟩
  have e : (⟨∑ i ∈ s, r i • gen c A₀ (a i) (b i),
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (gen_mem c A₀ _ _)⟩ : Sch c A₀)
      = ∑ i ∈ s, r i • ⟨gen c A₀ (a i) (b i), gen_mem c A₀ (a i) (b i)⟩ := by
    apply Subtype.ext
    simp
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, hXi]

theorem lattice_moves_hold : Moves := by
  intro k _ A B T _ _ _ _ c WA WB hc hW A₀ A₁ B₀ B₁ θ Xi hXi hB₀ h11 hA SA SB hSA hSB hcard
  have hM : ∑ a ∈ SA, ∑ b ∈ SB, gen c A₀ a b = (SB.card : k) • ind (A₁ : Set A) :=
    model_moves_hold k A B c hc A₀ A₁ B₀ B₁ hB₀ h11 hA SA SB hSA hSB
  have hexp : ind (A₁ : Set A) = ∑ i ∈ SA ×ˢ SB, (SB.card : k)⁻¹ • gen c A₀ i.1 i.2 := by
    rw [← Finset.smul_sum, Finset.sum_product, hM, smul_smul, inv_mul_cancel₀ hcard, one_smul]
  obtain ⟨h, hval⟩ := Xi_of_eq_sum hXi (SA ×ˢ SB) (fun _ => (SB.card : k)⁻¹) Prod.fst Prod.snd _ hexp
  refine ⟨h, ?_⟩
  rw [hval, ← Finset.smul_sum, smul_smul, mul_inv_cancel₀ hcard, one_smul, Finset.sum_product]

end Formalism.L2.PairingIndexBounds.Mv
end
end

section -- merged from Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.MovesComposeU
section -- merged from Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.ModelIndexPairings.RelIndexLeOfPairing
noncomputable section
open scoped BigOperators

namespace Formalism.L2.PairingIndexBounds.Mv

open Formalism.L2.Th1.H

section Pairing
variable {k : Type*} [Field k] {G G' : Type*} [AddCommGroup G] [AddCommGroup G']

theorem relIndex_le_of_pairing (d : G' → G → k) (hd : IsBichar d) (M N : AddSubgroup G) (M' N' : AddSubgroup G')
    (h1 : ∀ y ∈ N', ∀ x ∈ M, x ∈ N → d y x = 1) (h2 : ∀ y ∈ N', (∀ x ∈ N, d y x = 1) → y ∈ M')
    (hfin : M.relIndex N ≠ 0) : M'.relIndex N' ≠ 0 ∧ M'.relIndex N' ≤ M.relIndex N := by
  classical
  have : (M.addSubgroupOf N).FiniteIndex := ⟨hfin⟩
  have : Finite (N ⧸ M.addSubgroupOf N) := AddSubgroup.finite_quotient_of_finiteIndex
  let _ := Fintype.ofFinite (N ⧸ M.addSubgroupOf N)

  have hcl : ∀ y : N', ∀ n n' : N, (QuotientAddGroup.mk n : N ⧸ M.addSubgroupOf N) = QuotientAddGroup.mk n' →
      d y n = d y n' := by
    intro y n n' h
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at h
    have h3 := h1 y y.2 _ h (-n + n').2
    have e : (n' : G) = (n : G) + ((-n + n' : N) : G) := by
      simp
    rw [e, hd.2.2, h3, mul_one]
  let χ : (N' ⧸ M'.addSubgroupOf N') → (Multiplicative (N ⧸ M.addSubgroupOf N) →* k) := fun q' =>
    { toFun := fun q => d ((Quotient.out q' : N') : G') ((Quotient.out (Multiplicative.toAdd q) : N) : G)
      map_one' := by
        have := hcl (Quotient.out q') (Quotient.out (0 : N ⧸ M.addSubgroupOf N)) 0
          (by rw [QuotientAddGroup.out_eq']; rfl)
        simpa [IsBichar.map_zero_right hd] using this
      map_mul' := by
        intro q₁ q₂
        have := hcl (Quotient.out q') (Quotient.out (Multiplicative.toAdd q₁ + Multiplicative.toAdd q₂))
          (Quotient.out (Multiplicative.toAdd q₁) + Quotient.out (Multiplicative.toAdd q₂))
          (by rw [QuotientAddGroup.mk_add]; simp only [QuotientAddGroup.out_eq'])
        rw [AddSubgroup.coe_add, hd.2.2] at this
        exact this }
  have hχ : Function.Injective χ := by
    intro q₁ q₂ h
    have hall : ∀ x ∈ N, d (((Quotient.out q₁ : N') - Quotient.out q₂ : N') : G') x = 1 := by
      intro x hx
      have h3 := DFunLike.congr_fun h (Multiplicative.ofAdd (QuotientAddGroup.mk (⟨x, hx⟩ : N)))
      have e1 := hcl (Quotient.out q₁) (Quotient.out (QuotientAddGroup.mk (⟨x, hx⟩ : N) : N ⧸ M.addSubgroupOf N))
        ⟨x, hx⟩ (QuotientAddGroup.out_eq' _)
      have e2 := hcl (Quotient.out q₂) (Quotient.out (QuotientAddGroup.mk (⟨x, hx⟩ : N) : N ⧸ M.addSubgroupOf N))
        ⟨x, hx⟩ (QuotientAddGroup.out_eq' _)
      have h4 : d ((Quotient.out q₁ : N') : G') x = d ((Quotient.out q₂ : N') : G') x := by
        rw [← e1, ← e2]; exact h3
      rw [AddSubgroup.coe_sub, IsBichar.map_sub_left hd, h4, mul_inv_cancel₀ (hd.1 _ _)]
    have hm := h2 _ ((Quotient.out q₁ : N') - Quotient.out q₂ : N').2 hall
    rw [← QuotientAddGroup.out_eq' q₁, ← QuotientAddGroup.out_eq' q₂]
    symm
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    convert hm using 1
    simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg, AddSubgroup.coe_sub]
    abel
  have hli : LinearIndependent k (fun q' => (χ q' : Multiplicative (N ⧸ M.addSubgroupOf N) → k)) :=
    (linearIndependent_monoidHom (Multiplicative (N ⧸ M.addSubgroupOf N)) k).comp χ hχ
  have hF : Finite (N' ⧸ M'.addSubgroupOf N') := hli.finite
  let _ := Fintype.ofFinite (N' ⧸ M'.addSubgroupOf N')
  have hle := hli.fintype_card_le_finrank
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_multiplicative, ← Nat.card_eq_fintype_card,
    ← Nat.card_eq_fintype_card] at hle
  refine ⟨?_, hle⟩
  change Nat.card (N' ⧸ M'.addSubgroupOf N') ≠ 0
  exact Nat.card_pos.ne'

end Pairing

theorem index_duality_holds : IndexDual := by
  intro k _ A B _ _ c hc A₀ A₁ B₀ B₁ h1 h2 h3 hfin
  obtain ⟨hfinB, hle⟩ := relIndex_le_of_pairing c hc A₁ A₀ B₀ B₁ (fun b hb a ha _ => h2 b hb a ha)
    (fun b _ h => (h1 b).2 h) hfin
  obtain ⟨-, hge⟩ := relIndex_le_of_pairing (fun a b => c b a) (bichar_swap hc) B₀ B₁ A₁ A₀
    (fun a ha b hb _ => (h1 b).1 hb a ha) h3 hfinB
  exact le_antisymm hle hge

section Vol
variable {G : Type*} [AddCommGroup G]

theorem ratio_relIndex (X Y W : AddSubgroup G) (hW : W ≤ X ⊓ Y) (hfin : W.relIndex (X ⊓ Y) ≠ 0) :
    ((X.relIndex Y : ℕ) : ℝ) / ((Y.relIndex X : ℕ) : ℝ) = ((W.relIndex Y : ℕ) : ℝ) / ((W.relIndex X : ℕ) : ℝ) := by
  have e1 : W.relIndex (X ⊓ Y) * X.relIndex Y = W.relIndex Y := by
    rw [← AddSubgroup.inf_relIndex_right X Y]
    exact AddSubgroup.relIndex_mul_relIndex _ _ _ hW inf_le_right
  have e2 : W.relIndex (X ⊓ Y) * Y.relIndex X = W.relIndex X := by
    rw [← AddSubgroup.inf_relIndex_left X Y]
    exact AddSubgroup.relIndex_mul_relIndex _ _ _ hW inf_le_left
  rw [← e1, ← e2]
  push_cast
  have : ((W.relIndex (X ⊓ Y) : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hfin
  rw [mul_div_mul_left _ _ this]

theorem ratio_cocycle (X Y Z : AddSubgroup G) (hXY : X.relIndex Y ≠ 0) (hYX : Y.relIndex X ≠ 0)
    (hZY : Z.relIndex Y ≠ 0) :
    ((X.relIndex Y : ℕ) : ℝ) / ((Y.relIndex X : ℕ) : ℝ) * (((Y.relIndex Z : ℕ) : ℝ) / ((Z.relIndex Y : ℕ) : ℝ)) =
      ((X.relIndex Z : ℕ) : ℝ) / ((Z.relIndex X : ℕ) : ℝ) := by
  have aux : ∀ P Q R : AddSubgroup G, R.relIndex Q ≠ 0 → (X ⊓ Y ⊓ Z) = P ⊓ Q ⊓ R →
      (X ⊓ Y ⊓ Z).relIndex (P ⊓ Q) ≠ 0 := by
    intro P Q R h e
    rw [e, AddSubgroup.inf_relIndex_left]
    intro h0
    exact h (AddSubgroup.relIndex_eq_zero_of_le_right inf_le_right h0)
  have fXY : (X ⊓ Y ⊓ Z).relIndex (X ⊓ Y) ≠ 0 := aux X Y Z hZY rfl
  have fYZ : (X ⊓ Y ⊓ Z).relIndex (Y ⊓ Z) ≠ 0 := aux Z Y X hXY (by
    ext x; simp only [AddSubgroup.mem_inf]; tauto) |> fun h => by rwa [inf_comm Z Y] at h
  have wY : (X ⊓ Y ⊓ Z).relIndex Y ≠ 0 := by
    rw [← AddSubgroup.relIndex_mul_relIndex (X ⊓ Y ⊓ Z) (X ⊓ Y) Y inf_le_left inf_le_right,
      AddSubgroup.inf_relIndex_right X Y]
    exact Nat.mul_ne_zero fXY hXY
  have wX : (X ⊓ Y ⊓ Z).relIndex X ≠ 0 := by
    rw [← AddSubgroup.relIndex_mul_relIndex (X ⊓ Y ⊓ Z) (X ⊓ Y) X inf_le_left inf_le_left,
      AddSubgroup.inf_relIndex_left X Y]
    exact Nat.mul_ne_zero fXY hYX
  have fXZ : (X ⊓ Y ⊓ Z).relIndex (X ⊓ Z) ≠ 0 := by
    intro h0
    exact wX (AddSubgroup.relIndex_eq_zero_of_le_right inf_le_left h0)
  rw [ratio_relIndex X Y (X ⊓ Y ⊓ Z) inf_le_left fXY,
    ratio_relIndex Y Z (X ⊓ Y ⊓ Z) (le_inf (inf_le_left.trans inf_le_right) inf_le_right) fYZ,
    ratio_relIndex X Z (X ⊓ Y ⊓ Z) (le_inf (inf_le_left.trans inf_le_left) inf_le_right) fXZ]
  have : (((X ⊓ Y ⊓ Z).relIndex Y : ℕ) : ℝ) ≠ 0 := by exact_mod_cast wY
  field_simp

end Vol

theorem pos_div_ne {a b : ℕ} (h : 0 < (a : ℝ) / (b : ℝ)) : a ≠ 0 ∧ b ≠ 0 := by
  constructor
  · rintro rfl; simp at h
  · rintro rfl; simp at h

theorem MovesComposeU_of (hMU : MovesU) (hXE : XiExists) (hXI : XiInter) : MovesComposeU := by
  intro V _ _ H α A B Λ₀ Λ₁ Λ₂ hH hA hB g0 g1 g2 h01 h12 h02 θ hθ
  classical
  obtain ⟨hbc, hheis⟩ := heisenberg_unitary_holds V H α A B hH hA hB
  obtain ⟨hfa, hfb⟩ := fixed_of_good H α A B Λ₀ g0 θ hθ
  obtain ⟨Xi, hXi, -⟩ := hXE ℂ A B (V → ℂ) (cU H A B) (wA H α A) (wB H α B) hbc hheis
    (Λ₀.addSubgroupOf A) θ hfa hfb
  obtain ⟨Xi', hXi'⟩ := LinearMap.exists_extend Xi
  have hext : ∀ (Φ : A → ℂ) (h : Φ ∈ Sch (cU H A B) (Λ₀.addSubgroupOf A)), Xi' Φ = Xi ⟨Φ, h⟩ := by
    intro Φ h
    rw [← hXi']; rfl
  obtain ⟨m1, pos01, eq01⟩ := hMU V H α A B Λ₀ Λ₁ hH hA hB g0 g1 h01 θ hθ Xi hXi
  obtain ⟨m2, pos02, eq02⟩ := hMU V H α A B Λ₀ Λ₂ hH hA hB g0 g2 h02 θ hθ Xi hXi
  have hθ1 : inter H α Λ₀ Λ₁ θ ∈ fixedBy H α Λ₁ := interFixed V H hH Λ₀ Λ₁ α g1.1 h01 θ hθ
  let Xi1 : Sch (cU H A B) (Λ₁.addSubgroupOf A) →ₗ[ℂ] (V → ℂ) :=
    (((Real.sqrt (volA A Λ₀ Λ₁))⁻¹ : ℝ) : ℂ) • (Xi' ∘ₗ (Sch (cU H A B) (Λ₁.addSubgroupOf A)).subtype)
  have hXi1 : IsXi (cU H A B) (wA H α A) (wB H α B) (Λ₁.addSubgroupOf A) (inter H α Λ₀ Λ₁ θ) Xi1 := by
    intro a b
    obtain ⟨mb, eb⟩ := (hXI ℂ A B (V → ℂ) (cU H A B) (wA H α A) (wB H α B) hbc hheis
      (Λ₀.addSubgroupOf A) θ Xi hXi _ m1).2 b
    obtain ⟨ma, ea⟩ := (hXI ℂ A B (V → ℂ) (cU H A B) (wA H α A) (wB H α B) hbc hheis
      (Λ₀.addSubgroupOf A) θ Xi hXi _ mb).1 a
    change (((Real.sqrt (volA A Λ₀ Λ₁))⁻¹ : ℝ) : ℂ) • Xi' (gen (cU H A B) (Λ₁.addSubgroupOf A) a b) = _
    rw [eq01, map_smul, map_smul, ← eb, ← ea]
    congr 1
    exact hext _ ma
  obtain ⟨m12, pos12, eq12⟩ := hMU V H α A B Λ₁ Λ₂ hH hA hB g1 g2 h12 _ hθ1 Xi1 hXi1
  rw [eq12, eq02, ← hext _ m2]
  change _ • ((((Real.sqrt (volA A Λ₀ Λ₁))⁻¹ : ℝ) : ℂ) • Xi' (ind ((Λ₂.addSubgroupOf A : AddSubgroup A) : Set A))) = _
  rw [smul_smul, ← Complex.ofReal_mul]
  congr 2
  have hc : volA A Λ₀ Λ₁ * volA A Λ₁ Λ₂ = volA A Λ₀ Λ₂ := by
    unfold volA at pos01 pos12 ⊢
    obtain ⟨n1, n2⟩ := pos_div_ne pos01
    obtain ⟨-, n4⟩ := pos_div_ne pos12
    exact ratio_cocycle (Λ₀ ⊓ A) (Λ₁ ⊓ A) (Λ₂ ⊓ A) n1 n2 n4
  rw [← hc, Real.sqrt_mul pos01.le, mul_inv, mul_comm]

end Formalism.L2.PairingIndexBounds.Mv

namespace Formalism.L2.PairingIndexBounds.Mv
end Formalism.L2.PairingIndexBounds.Mv
end
end

section -- merged from Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.ModelIndexPairings.LinearExtensionHolds
noncomputable section
open scoped BigOperators

namespace Formalism.L2.PairingIndexBounds.Mv

theorem linear_extension_holds : ExtendLin := by
  intro k _ M T _ _ _ _ ι f g hfg
  classical
  let φ := Finsupp.linearCombination k f
  let ψ := Finsupp.linearCombination k g
  have hle : LinearMap.ker φ ≤ LinearMap.ker ψ := by
    intro c hc
    rw [LinearMap.mem_ker] at hc ⊢
    simp only [φ, ψ, Finsupp.linearCombination_apply, Finsupp.sum] at hc ⊢
    exact hfg c.support c hc
  let φ' := (LinearMap.ker φ).liftQ φ le_rfl
  let ψ' := (LinearMap.ker φ).liftQ ψ hle
  have hinj : LinearMap.ker φ' = ⊥ := by
    apply Submodule.ker_liftQ_eq_bot
    exact le_rfl
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective φ' hinj
  refine ⟨ψ'.comp L, fun i => ?_⟩
  have hfi : f i = φ' (Submodule.Quotient.mk (Finsupp.single i 1)) := by
    simp [φ', φ, Finsupp.linearCombination_single]
  have h2 : L (φ' (Submodule.Quotient.mk (Finsupp.single i 1))) = Submodule.Quotient.mk (Finsupp.single i 1) := by
    rw [← LinearMap.comp_apply, hL, LinearMap.id_apply]
  rw [LinearMap.comp_apply, hfi, h2]
  simp [ψ', ψ, Finsupp.linearCombination_single]

end Formalism.L2.PairingIndexBounds.Mv
end
end

namespace Formalism.L2.PairingIndexBounds.Mv

theorem xiExists : XiExists := xi_existence_holds
theorem xiInter : XiInter := xi_intersection_holds
theorem moves : Moves := lattice_moves_hold
theorem indexDual : IndexDual := index_duality_holds
theorem extendLin : ExtendLin := linear_extension_holds
theorem heisU : HeisU := heisenberg_unitary_holds
theorem interSelf : InterSelf := self_intersection_holds
theorem movesU : MovesU := MovesU_of moves indexDual
theorem movesComposeU : MovesComposeU := MovesComposeU_of movesU xiExists xiInter
theorem genModelXi : GenModelXi := GenModelXi_of xiExists movesU extendLin

end Formalism.L2.PairingIndexBounds.Mv
end

section -- merged from Formalism.LocalToGlobal.PairingIndexBounds.HalvesRecursion.RecursiveLatticeMembership.Bridge
noncomputable section
open scoped BigOperators

namespace Formalism.L2.PairingIndexBounds.Rec

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Formalism.L2.PairingIndexBounds.Mv Formalism.L2.Th1.H Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

theorem HfS_apply (D : D7) (T : Tor D) (N N' : ℕ) (z w : VC D N N') : HfS D T N N' z w = Hf D T z w := rfl

theorem al_pm (D : D7) (T : Tor D) {N N' : ℕ} (x : VC D N N') : al D T x = 1 ∨ al D T x = -1 := by
  unfold al
  rcases Int.even_or_odd (round (Real.sqrt D.host.d / 2 * (Hf D T x x).re)) with h | h
  · left; exact h.neg_one_zpow
  · right; exact h.neg_one_zpow

theorem exp_int_sign (b : ℤ) :
    Complex.exp (-((Real.pi : ℂ) * Complex.I * (b : ℂ))) = Complex.exp ((Real.pi : ℂ) * Complex.I * (b : ℂ)) := by
  rw [Complex.exp_eq_exp_iff_exists_int]
  exact ⟨-b, by push_cast; ring⟩

theorem local_global_comparison_holds : Bridge := by
  intro D T N N'
  refine ⟨fun x y => ?_, fun x G => rfl, fun La₁ La₂ G => ?_, fun La' G hG => ?_, fun La' hI => ?_⟩
  · show Hf D T y x = starRingEnd ℂ (Hf D T x y)
    exact Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.Hf_herm T x y
  · funext z
    simp only [Iop, inter, relIdx, AddSubgroup.relIndex]
    rfl
  · intro x hx z
    exact hG.2 x hx z
  · refine ⟨fun x _ => al_pm D T x, fun x hx y hy => ?_⟩
    have h := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.semiChar_of_HfInt T hI x hx y hy
    rw [h]
    obtain ⟨a, b, -, hab⟩ := hI x hx y hy
    have him : (Hf D T x y).im = b := by rw [hab]; simp
    simp only [Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.cf, altE, HfS_apply, him]
    have e := exp_int_sign b
    push_cast at e ⊢
    rw [e]

end Formalism.L2.PairingIndexBounds.Rec
end
end

noncomputable section
open scoped BigOperators

namespace Formalism.L2.PairingIndexBounds.Rec

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Formalism.L2.PairingIndexBounds.Mv Formalism.L2.Th1.H Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

theorem eqOff_refl (D : D7) (P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)) {N : ℕ}
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) : EqOff D P L L :=
  ⟨0, fun a b _ _ => ⟨fun x hx => L.smul_mem _ hx, fun x hx => L.smul_mem _ hx⟩⟩

theorem volP_self (D : D7) (P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)) {N N' : ℕ}
    (Y : AddSubgroup (Matrix (Fin N') (Fin N) (EP D P))) : volP Y Y = 1 := by
  simp [volP, AddSubgroup.addSubgroupOf_self]

theorem volA_pos {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (A B Λ₀ Λ₁ : AddSubgroup V)
    (hH : IsHerm H) (hA : IsSemiChar H A α) (hB : IsSemiChar H B α) (g0 : GoodLat H α A B Λ₀)
    (g1 : GoodLat H α A B Λ₁) (hfin : relIdx Λ₀ Λ₁ ≠ 0) : 0 < volA A Λ₀ Λ₁ := by
  obtain ⟨hbc, hheis⟩ := heisU V H α A B hH hA hB
  obtain ⟨hfa, hfb⟩ := fixed_of_good H α A B Λ₀ g0 0 (fixedBy H α Λ₀).zero_mem
  obtain ⟨Xi, hXi, -⟩ := xiExists ℂ A B (V → ℂ) (cU H A B) (wA H α A) (wB H α B) hbc hheis
    (Λ₀.addSubgroupOf A) 0 hfa hfb
  obtain ⟨-, hpos, -⟩ := movesU V H α A B Λ₀ Λ₁ hH hA hB g0 g1 hfin 0 (fixedBy H α Λ₀).zero_mem Xi hXi
  exact hpos

theorem modelXiNZ_of (hH : HalvesRec) (D : D7) : ModelXiNZ D := by
  intro cc δ hcc hδ hδ0 N N' L₀ L₀' hAdm P hP th hth
  classical
  obtain ⟨hHerm, -, hIop, hTh, -⟩ := local_global_comparison_holds D (tor0 D cc δ) N N'
  let ι : Type := {q : Pair D N N' // admitted D N N' q.1 q.2 ∧ EqOff D P q.1 L₀ ∧ EqOff D P q.2 L₀'}
  have hfam := genModelXi (VC D N N') (HfS D (tor0 D cc δ) N N') (al D (tor0 D cc δ))
    (La D (tor0 D cc δ) L₀ L₀') (Matrix (Fin N') (Fin N) (EP D P)) ι
    (fun i => La D (tor0 D cc δ) i.1.1 i.1.2) (fun i => (YP D P i.1.1 i.1.2 : Set _))
    (fun i => volP (YP D P L₀ L₀') (YP D P i.1.1 i.1.2)) hHerm th (hTh _ hth) ?_
  swap
  · intro s
    obtain ⟨A, B, φ, hA, hB, g0, hs⟩ := hH D cc δ hcc hδ hδ0 N N' L₀ L₀' hAdm P hP
      (s.map ⟨Subtype.val, Subtype.val_injective⟩) (by
        intro q hq
        obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hq
        exact i.2)
    refine ⟨A, B, φ, hA, hB, g0, fun i hi => ?_⟩
    exact hs i.1 (Finset.mem_map_of_mem _ hi)
  obtain ⟨Xi, hXi⟩ := hfam
  refine ⟨Xi, ?_, ?_⟩
  · have h0 := hXi ⟨(L₀, L₀'), hAdm, eqOff_refl D P L₀, eqOff_refl D P L₀'⟩
    simp only [volP_self, Real.sqrt_one, Complex.ofReal_one, one_smul] at h0
    rw [h0]
    obtain ⟨A, B, φ, hA, hB, g0, -⟩ := hH D cc δ hcc hδ hδ0 N N' L₀ L₀' hAdm P hP ∅ (by simp)
    exact interSelf (VC D N N') (HfS D (tor0 D cc δ) N N') (al D (tor0 D cc δ)) _ hHerm g0.1 th (hTh _ hth)
  · intro L L' hLL hE1 hE2
    let i : ι := ⟨(L, L'), hLL, hE1, hE2⟩
    have h1 := hXi i
    obtain ⟨A, B, φ, hA, hB, g0, hs⟩ := hH D cc δ hcc hδ hδ0 N N' L₀ L₀' hAdm P hP {(L, L')} (by simpa using ⟨hLL, hE1, hE2⟩)
    obtain ⟨g1, hfin, -, hvol⟩ := hs (L, L') (Finset.mem_singleton_self _)
    have hpos : 0 < volP (YP D P L₀ L₀') (YP D P L L') := by
      rw [hvol]; exact volA_pos _ _ A B _ _ hHerm hA hB g0 g1 hfin
    have hs0 : (Real.sqrt (volP (YP D P L₀ L₀') (YP D P L L')) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.2 hpos).ne'
    rw [hIop]
    funext z
    have h1z := congrFun h1 z
    simp only [Pi.smul_apply, smul_eq_mul] at h1z
    change Xi (Set.indicator (YP D P L L' : Set _) 1) z = _ at h1z
    rw [h1z, Complex.ofReal_inv, ← mul_assoc, inv_mul_cancel₀ hs0, one_mul]

theorem modelXi_of (hH : HalvesRec) (D : D7) (hΔ : DiscrNZ D) : modelXi D := by
  intro cc δ hcc hδ N N' L₀ L₀' hAdm P hP th hth
  have hδ0 : δ ≠ 0 := by
    intro h0
    apply hΔ cc hcc
    rw [← hδ, h0]
    norm_num
  exact modelXiNZ_of hH D cc δ hcc hδ hδ0 N N' L₀ L₀' hAdm P hP th hth

end Formalism.L2.PairingIndexBounds.Rec
