module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaSignMultiplicative
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.KappaSignMultiplicative
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem _root_.GlobalTheory.T.kappa_sign_multiplicative : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (w : Pl E) (Q₁ Q₂ Q₃ : (w.adicCompletion E)[X]) (γ g : UL n w), γ.1.val.charpoly.Separable → Q₁ * Q₂ ∣ γ.1.val.charpoly → IsCoprime Q₁ Q₂ → IsCsr w Q₁ → IsCsr w Q₂ → kapSign n w (Q₁ * Q₂) γ.1 = kapSign n w Q₁ γ.1 * kapSign n w Q₂ γ.1 ∧ kapSign n w Q₃ (g⁻¹ * γ * g).1 = kapSign n w Q₃ γ.1 ∧ (kapSign n w Q₃ γ.1 = 1 ∨ kapSign n w Q₃ γ.1 = -1) := by
  first | exact @GlobalTheory.KapSignMul.main | (intros; apply GlobalTheory.KapSignMul.main <;> assumption)
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.MonicDivisorSignSum
section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.MonicDivisorSignSum
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.DivSum

open UniqueFactorizationMonoid

variable {k : Type} [Field k]

theorem monic_of_mem_normalizedFactors {P q : k[X]} (hq : q ∈ normalizedFactors P) : q.Monic := by
  have h0 : q ≠ 0 := (irreducible_of_normalized_factor q hq).ne_zero
  rw [← normalize_normalized_factor q hq]
  exact Polynomial.monic_normalize h0

theorem monic_prod_sub {P : k[X]} (t : Finset k[X]) (ht : t ⊆ (normalizedFactors P).toFinset) :
    (∏ q ∈ t, q).Monic := by
  exact Polynomial.monic_prod_of_monic t id fun q hq => monic_of_mem_normalizedFactors (Multiset.mem_toFinset.1 (ht hq))

theorem normalizedFactors_prod_sub {P : k[X]} (t : Finset k[X]) (ht : t ⊆ (normalizedFactors P).toFinset) :
    normalizedFactors (∏ q ∈ t, q) = t.val := by
  rw [Finset.prod_eq_multiset_prod, Multiset.map_id',
    normalizedFactors_prod_eq _ fun q hq => irreducible_of_normalized_factor q (Multiset.mem_toFinset.1 (ht hq))]
  conv_rhs => rw [← Multiset.map_id t.val]
  exact Multiset.map_congr rfl fun q hq => normalize_normalized_factor q (Multiset.mem_toFinset.1 (ht hq))

theorem prod_sub_dvd {P : k[X]} (hP : P ≠ 0) (t : Finset k[X])
    (ht : t ⊆ (normalizedFactors P).toFinset) : (∏ q ∈ t, q) ∣ P := by
  have h0 : (∏ q ∈ t, q) ≠ 0 := (monic_prod_sub t ht).ne_zero
  rw [dvd_iff_normalizedFactors_le_normalizedFactors h0 hP, normalizedFactors_prod_sub t ht]
  exact (Multiset.le_iff_subset t.nodup).2 fun q hq => Multiset.mem_toFinset.1 (ht hq)

theorem eq_prod_sub {P Q : k[X]} (hP : P ≠ 0) (hsq : Squarefree P) (hQ : Q.Monic) (hQP : Q ∣ P) :
    (normalizedFactors Q).toFinset ⊆ (normalizedFactors P).toFinset ∧
      Q = ∏ q ∈ (normalizedFactors Q).toFinset, q := by
  have hQ0 := hQ.ne_zero
  have hle := (dvd_iff_normalizedFactors_le_normalizedFactors hQ0 hP).1 hQP
  refine ⟨fun a ha => Multiset.mem_toFinset.2 (Multiset.mem_of_le hle (Multiset.mem_toFinset.1 ha)), ?_⟩
  have hnd : (normalizedFactors Q).Nodup :=
    (squarefree_iff_nodup_normalizedFactors hQ0).1 (hsq.squarefree_of_dvd hQP)
  rw [Finset.prod_eq_multiset_prod, Multiset.map_id', Multiset.toFinset_val, hnd.dedup,
    prod_normalizedFactors_eq hQ0]
  exact ((Polynomial.normalize_eq_self_iff_monic hQ0).2 hQ).symm

end GlobalTheory.DivSum

namespace GlobalTheory.DivSum

open UniqueFactorizationMonoid

variable {k : Type} [Field k]

theorem isCoprime_of_sub {P q : k[X]} (t : Finset k[X]) (ht : t ⊆ (normalizedFactors P).toFinset)
    (hq : q ∈ (normalizedFactors P).toFinset) (hqt : q ∉ t) : IsCoprime q (∏ r ∈ t, r) := by
  refine IsCoprime.prod_right fun r hr => ?_
  have hqP := Multiset.mem_toFinset.1 hq
  have hrP := Multiset.mem_toFinset.1 (ht hr)
  rw [(irreducible_of_normalized_factor q hqP).coprime_iff_not_dvd]
  intro hd
  exact hqt (normalizedFactors_eq_of_dvd P q hqP r hrP hd ▸ hr)

theorem s_prod_sub {P : k[X]} (hP : P ≠ 0) (s : k[X] → ℂ)
    (hmul : ∀ Q₁ Q₂ : k[X], Q₁.Monic → Q₂.Monic → Q₁ * Q₂ ∣ P → IsCoprime Q₁ Q₂ → s (Q₁ * Q₂) = s Q₁ * s Q₂)
    (h1 : s 1 = 1) (t : Finset k[X]) (ht : t ⊆ (normalizedFactors P).toFinset) :
    s (∏ q ∈ t, q) = ∏ q ∈ t, s q := by
  induction t using Finset.induction_on with
  | empty => simp [h1]
  | insert a t ha ih =>
    have ht' : t ⊆ (normalizedFactors P).toFinset := fun x hx => ht (Finset.mem_insert_of_mem hx)
    have haP : a ∈ (normalizedFactors P).toFinset := ht (Finset.mem_insert_self a t)
    have hma : a.Monic := monic_of_mem_normalizedFactors (Multiset.mem_toFinset.1 haP)
    have hd : a * ∏ q ∈ t, q ∣ P := by
      have h := prod_sub_dvd hP _ ht
      rwa [Finset.prod_insert ha] at h
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      hmul _ _ hma (monic_prod_sub t ht') hd (isCoprime_of_sub t ht' haP ha), ih ht']

theorem finsum_monic_divisors_sign : ∀ (k : Type) [Field k] (P : k[X]), P.Monic → P.Separable → ∀ s : k[X] → ℂ,
    (∀ Q₁ Q₂ : k[X], Q₁.Monic → Q₂.Monic → Q₁ * Q₂ ∣ P → IsCoprime Q₁ Q₂ → s (Q₁ * Q₂) = s Q₁ * s Q₂) →
    (∀ Q : k[X], Q.Monic → Q ∣ P → s Q = 1 ∨ s Q = -1) →
    {Q : k[X] | Q.Monic ∧ Q ∣ P}.Finite ∧
      ∑ᶠ Q : {Q : k[X] // Q.Monic ∧ Q ∣ P}, s Q.1 =
        if ∀ Q : k[X], Q.Monic → Q ∣ P → s Q = 1 then 2 ^ nfac P else 0 := by
  intro k _ P hPm hPs s hmul hsgn
  have hP : P ≠ 0 := hPm.ne_zero
  have hsq : Squarefree P := hPs.squarefree
  set F := (normalizedFactors P).toFinset with hF
  have memF : ∀ q ∈ F, q.Monic ∧ q ∣ P := fun q hq =>
    ⟨monic_of_mem_normalizedFactors (Multiset.mem_toFinset.1 hq),
      dvd_of_mem_normalizedFactors (Multiset.mem_toFinset.1 hq)⟩
  have h1 : s 1 = 1 := by
    have hm := hmul 1 1 monic_one monic_one (by rw [one_mul]; exact one_dvd P) isCoprime_one_left
    rw [one_mul] at hm
    rcases hsgn 1 monic_one (one_dvd P) with h | h
    · exact h
    · rw [h] at hm
      norm_num at hm
  let φ : {t // t ∈ F.powerset} → {Q : k[X] // Q.Monic ∧ Q ∣ P} := fun t =>
    ⟨∏ q ∈ t.1, q, monic_prod_sub t.1 (Finset.mem_powerset.1 t.2),
      prod_sub_dvd hP t.1 (Finset.mem_powerset.1 t.2)⟩
  have hinj : Function.Injective φ := by
    intro a b hab
    have h := congrArg (fun Q : {Q : k[X] // Q.Monic ∧ Q ∣ P} => normalizedFactors Q.1) hab
    simp only [φ] at h
    rw [normalizedFactors_prod_sub a.1 (Finset.mem_powerset.1 a.2),
      normalizedFactors_prod_sub b.1 (Finset.mem_powerset.1 b.2)] at h
    exact Subtype.ext (Finset.val_injective h)
  have hsurj : Function.Surjective φ := by
    rintro ⟨Q, hQm, hQd⟩
    obtain ⟨hsub, heq⟩ := eq_prod_sub hP hsq hQm hQd
    exact ⟨⟨_, Finset.mem_powerset.2 hsub⟩, Subtype.ext heq.symm⟩
  have hs1 : ∀ q ∈ F, s q = 1 ∨ s q = -1 := fun q hq => hsgn q (memF q hq).1 (memF q hq).2
  refine ⟨?_, ?_⟩
  · have hsub : {Q : k[X] | Q.Monic ∧ Q ∣ P} ⊆ ((F.powerset.image fun t => ∏ q ∈ t, q : Finset k[X]) : Set k[X]) := by
      intro Q hQ
      obtain ⟨⟨t, ht⟩, htQ⟩ := hsurj ⟨Q, hQ⟩
      exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨t, ht, congrArg Subtype.val htQ⟩)
    exact (Finset.finite_toSet _).subset hsub
  · rw [← finsum_comp_equiv (Equiv.ofBijective φ ⟨hinj, hsurj⟩), finsum_eq_sum_of_fintype]
    have hsum : ∑ t : {t // t ∈ F.powerset}, s (Equiv.ofBijective φ ⟨hinj, hsurj⟩ t).1 = ∏ q ∈ F, (1 + s q) := by
      rw [Finset.prod_one_add, ← Finset.sum_coe_sort F.powerset]
      refine Finset.sum_congr rfl fun t _ => ?_
      exact s_prod_sub hP s hmul h1 t.1 (Finset.mem_powerset.1 t.2)
    rw [hsum]
    split_ifs with hall
    · rw [Finset.prod_congr rfl fun q hq => show 1 + s q = 2 by
        rw [hall q (memF q hq).1 (memF q hq).2]
        norm_num, Finset.prod_const]
      have hnd : (normalizedFactors P).Nodup := (squarefree_iff_nodup_normalizedFactors hP).1 hsq
      rw [hF, Multiset.card_toFinset, hnd.dedup]
      rfl
    · push_neg at hall
      obtain ⟨Q, hQm, hQd, hQs⟩ := hall
      obtain ⟨hsub, heq⟩ := eq_prod_sub hP hsq hQm hQd
      have hsQ := s_prod_sub hP s hmul h1 _ hsub
      rw [← heq] at hsQ
      by_contra hne
      apply hQs
      rw [hsQ]
      refine Finset.prod_eq_one fun q hq => ?_
      rcases hs1 q (hsub hq) with h | h
      · exact h
      · exact absurd (Finset.prod_eq_zero (hsub hq) (by rw [h]; norm_num)) hne

end GlobalTheory.DivSum
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.MonicDivisorSignSumStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monic_divisor_sign_sum : ∀ (k : Type) [Field k] (P : k[X]), P.Monic → P.Separable → ∀ s : k[X] → ℂ, (∀ Q₁ Q₂ : k[X], Q₁.Monic → Q₂.Monic → Q₁ * Q₂ ∣ P → IsCoprime Q₁ Q₂ → s (Q₁ * Q₂) = s Q₁ * s Q₂) → (∀ Q : k[X], Q.Monic → Q ∣ P → s Q = 1 ∨ s Q = -1) → {Q : k[X] | Q.Monic ∧ Q ∣ P}.Finite ∧ ∑ᶠ Q : {Q : k[X] // Q.Monic ∧ Q ∣ P}, s Q.1 = if ∀ Q : k[X], Q.Monic → Q ∣ P → s Q = 1 then 2 ^ nfac P else 0 := by
  first | exact @GlobalTheory.DivSum.finsum_monic_divisors_sign | exact GlobalTheory.DivSum.finsum_monic_divisors_sign | (intros; apply GlobalTheory.DivSum.finsum_monic_divisors_sign <;> assumption)
end
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.AdelicClassCountProduct
section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.AdelicClassCountProduct
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem finprod_mem_eq_zero_of_factor {ι : Type} (f : ι → ℂ) (S : Set ι)
    (hfin : {w | f w ≠ 1}.Finite) {w₀ : ι} (hw₀ : w₀ ∈ S) (h0 : f w₀ = 0) :
    ∏ᶠ w ∈ S, f w = 0 := by
  have hs : (S ∩ Function.mulSupport f).Finite := hfin.subset fun w hw => hw.2
  rw [finprod_mem_eq_prod f hs]
  refine Finset.prod_eq_zero (i := w₀) ?_ h0
  rw [Set.Finite.mem_toFinset]
  refine ⟨hw₀, ?_⟩
  rw [Function.mem_mulSupport, h0]
  exact zero_ne_one

theorem finsum_finprod_local_sums_expand : ∀ (ι : Type) (S : Set ι) (Cl : ι → Type) [∀ w, Finite (Cl w)] (D R : Type) [Finite D] (loc : R → ∀ w, Cl w) (O : ∀ w, Cl w → ℂ) (s : D → ∀ w, Cl w → ℂ) (good : ∀ w, Cl w → Prop) (N : ℂ), (∀ᶠ w in (cofinite : Filter ι), (∃! c, good w c) ∧ ∀ c, (O w c = if good w c then 1 else 0) ∧ (good w c → ∀ d, s d w c = 1)) → (∀ w, w ∉ S → Nonempty (Cl w)) → (∀ r, ∀ᶠ w in (cofinite : Filter ι), good w (loc r w)) → (∀ r r', (∀ w ∈ S, loc r w = loc r' w) → r = r') → (∀ x : ∀ w, Cl w, (∀ᶠ w in (cofinite : Filter ι), good w (x w)) → ∑ᶠ d : D, ∏ᶠ w ∈ S, s d w (x w) = if ∃ r, ∀ w ∈ S, loc r w = x w then N else 0) → (Function.support fun r : R => ∏ᶠ w ∈ S, O w (loc r w)).Finite ∧ (∑ᶠ r : R, ∏ᶠ w ∈ S, O w (loc r w)) * N = ∑ᶠ d : D, ∏ᶠ w ∈ S, ∑ᶠ c : Cl w, s d w c * O w c := by
  intro ι S Cl _ D R _ loc O s good N hA hB hC hD hE
  classical
  haveI : ∀ w, Fintype (Cl w) := fun w => Fintype.ofFinite _
  haveI : Fintype D := Fintype.ofFinite D
  obtain ⟨T, hTfin, hTA⟩ : ∃ T : Set ι, T.Finite ∧ ∀ w, w ∉ T →
      ((∃! c, good w c) ∧ ∀ c, (O w c = if good w c then 1 else 0) ∧ (good w c → ∀ d, s d w c = 1)) :=
    ⟨_, Filter.eventually_cofinite.1 hA, fun w hw => not_not.1 hw⟩
  have hO : ∀ w, w ∉ T → ∀ c, O w c = if good w c then 1 else 0 := fun w hw c => ((hTA w hw).2 c).1
  have hs1 : ∀ w, w ∉ T → ∀ c, good w c → ∀ d, s d w c = 1 := fun w hw c => ((hTA w hw).2 c).2
  have huniq : ∀ w, w ∉ T → ∀ c c', good w c → good w c' → c = c' :=
    fun w hw c c' hc hc' => (hTA w hw).1.unique hc hc'
  obtain ⟨F, hF⟩ : ∃ F : Finset ι, ∀ w, w ∈ F ↔ w ∈ S ∧ w ∈ T :=
    ⟨hTfin.toFinset.filter (· ∈ S), fun w => by simp [and_comm]⟩
  obtain ⟨ext, ext_F, ext_good⟩ : ∃ ext : (∀ w : F, Cl w) → ∀ w, Cl w,
      (∀ x (w : F), ext x w = x w) ∧ ∀ x w, w ∉ T → good w (ext x w) := by
    refine ⟨fun x w => if h : w ∈ F then x ⟨w, h⟩ else if hw : w ∈ T then
      (hB w (fun hS => h ((hF w).2 ⟨hS, hw⟩))).some else (hTA w hw).1.exists.choose,
      fun x w => dif_pos w.2, fun x w hw => ?_⟩
    have hwF : w ∉ F := fun h => hw ((hF w).1 h).2
    simp only [dif_neg hwF, dif_neg hw]
    exact (hTA w hw).1.exists.choose_spec
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : R → ∀ w : F, Cl w, ∀ r (w : F), ρ r w = loc r w :=
    ⟨fun r w => loc r w, fun _ _ => rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : Set R, ∀ r, r ∈ G ↔ ∀ w ∈ S, w ∉ T → good w (loc r w) :=
    ⟨{r | ∀ w ∈ S, w ∉ T → good w (loc r w)}, fun _ => Iff.rfl⟩
  have prodS : ∀ φ : ι → ℂ, (∀ w ∈ S, w ∉ T → φ w = 1) → ∏ᶠ w ∈ S, φ w = ∏ w : F, φ w := by
    intro φ hφ
    have h1 : S ∩ Function.mulSupport φ ⊆ (F : Set ι) := by
      rintro w ⟨hwS, hw1⟩
      by_contra hwF
      exact hw1 (hφ w hwS fun hT => hwF (Finset.mem_coe.2 ((hF w).2 ⟨hwS, hT⟩)))
    have h2 : (F : Set ι) ⊆ S := fun w hw => ((hF w).1 (Finset.mem_coe.1 hw)).1
    rw [finprod_mem_eq_prod_of_subset φ h1 h2, ← Finset.prod_coe_sort]
  have hR : ∀ d, ∏ᶠ w ∈ S, ∑ᶠ c, s d w c * O w c =
      ∑ x : (∀ w : F, Cl w), (∏ w : F, s d w (x w)) * ∏ w : F, O w (x w) := by
    intro d
    rw [prodS]
    · simp only [finsum_eq_sum_of_fintype]
      rw [Fintype.prod_sum]
      exact Finset.sum_congr rfl fun x _ => Finset.prod_mul_distrib
    · intro w _ hw
      obtain ⟨c0, hc0⟩ := (hTA w hw).1.exists
      rw [finsum_eq_sum_of_fintype, Finset.sum_eq_single c0]
      · rw [hO w hw c0, if_pos hc0, hs1 w hw c0 hc0 d, mul_one]
      · intro c _ hc
        rw [hO w hw c, if_neg (fun hg => hc (huniq w hw c c0 hg hc0)), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ c0) h
  have hs_ext : ∀ d x, ∏ᶠ w ∈ S, s d w (ext x w) = ∏ w : F, s d w (x w) := by
    intro d x
    rw [prodS]
    · exact Finset.prod_congr rfl fun w _ => by rw [ext_F]
    · intro w _ hw
      exact hs1 w hw _ (ext_good x w hw) d
  have hEx : ∀ x, ∑ d, ∏ w : F, s d w (x w) = if ∃ r, ∀ w ∈ S, loc r w = ext x w then N else 0 := by
    intro x
    rw [← hE (ext x) ?_, finsum_eq_sum_of_fintype]
    · exact Finset.sum_congr rfl fun d _ => (hs_ext d x).symm
    · exact Filter.eventually_cofinite.2 (hTfin.subset fun w hw => by_contra fun hwT => hw (ext_good x w hwT))
  have hρ : ∀ r ∈ G, ∀ w ∈ S, loc r w = ext (ρ r) w := by
    intro r hr w hwS
    by_cases hwF : w ∈ F
    · have h := ext_F (ρ r) ⟨w, hwF⟩
      rw [hρdef] at h
      exact h.symm
    · have hwT : w ∉ T := fun hT => hwF ((hF w).2 ⟨hwS, hT⟩)
      exact huniq w hwT _ _ ((hG r).1 hr w hwS hwT) (ext_good _ w hwT)
  have hρinj : Set.InjOn ρ G := by
    intro r hr r' hr' h
    apply hD
    intro w hwS
    rw [hρ r hr w hwS, hρ r' hr' w hwS, h]
  have hP0 : ∀ r, r ∉ G → ∏ᶠ w ∈ S, O w (loc r w) = 0 := by
    intro r hr
    rw [hG] at hr
    push_neg at hr
    obtain ⟨w, hwS, hwT, hg⟩ := hr
    refine finprod_mem_eq_zero_of_factor _ S ?_ hwS ?_
    · refine (hTfin.union (Filter.eventually_cofinite.1 (hC r))).subset fun v hv => ?_
      by_contra hcon
      simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hcon
      exact hv (by rw [hO v hcon.1, if_pos hcon.2])
    · rw [hO w hwT, if_neg hg]
  have hP1 : ∀ r ∈ G, ∏ᶠ w ∈ S, O w (loc r w) = ∏ w : F, O w (ρ r w) := by
    intro r hr
    rw [prodS]
    · exact Finset.prod_congr rfl fun w _ => by rw [hρdef]
    · intro w hwS hwT
      rw [hO w hwT, if_pos ((hG r).1 hr w hwS hwT)]
  have hGfin : G.Finite := Set.Finite.of_finite_image (Set.toFinite _) hρinj
  have hmem : ∀ x, x ∈ ρ '' G ↔ ∃ r, ∀ w ∈ S, loc r w = ext x w := by
    intro x
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact ⟨r, hρ r hr⟩
    · rintro ⟨r, hr⟩
      refine ⟨r, ?_, ?_⟩
      · rw [hG]
        intro w hwS hwT
        rw [hr w hwS]
        exact ext_good x w hwT
      · funext w
        rw [hρdef, hr w ((hF w).1 w.2).1, ext_F]
  have hsum : ∑ᶠ r, ∏ᶠ w ∈ S, O w (loc r w) =
      ∑ x : (∀ w : F, Cl w), if ∃ r, ∀ w ∈ S, loc r w = ext x w then ∏ w : F, O w (x w) else 0 := by
    calc ∑ᶠ r, ∏ᶠ w ∈ S, O w (loc r w) = ∑ᶠ r ∈ G, ∏ w : F, O w (ρ r w) := by
          rw [finsum_mem_def]
          apply finsum_congr
          intro r
          by_cases hr : r ∈ G
          · simp only [Set.indicator_apply, hr, if_true]
            exact hP1 r hr
          · simp only [Set.indicator_apply, hr, if_false]
            exact hP0 r hr
      _ = ∑ᶠ x ∈ ρ '' G, ∏ w : F, O w (x w) :=
          (finsum_mem_image (f := fun x : (∀ w : F, Cl w) => ∏ w : F, O w (x w)) hρinj).symm
      _ = _ := by
          rw [finsum_mem_def, finsum_eq_sum_of_fintype]
          refine Finset.sum_congr rfl fun x _ => ?_
          simp only [Set.indicator_apply, hmem]
  refine ⟨hGfin.subset fun r hr => by_contra fun hrG => hr (hP0 r hrG), ?_⟩
  rw [hsum, finsum_congr hR, finsum_eq_sum_of_fintype, Finset.sum_comm, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_mul, hEx x]
  split_ifs <;> ring

end GlobalTheory
end

section -- merged from Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.AdelicClassCountProductStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_class_count_product : ∀ (ι : Type) (S : Set ι) (Cl : ι → Type) [∀ w, Finite (Cl w)] (D R : Type) [Finite D] (loc : R → ∀ w, Cl w) (O : ∀ w, Cl w → ℂ) (s : D → ∀ w, Cl w → ℂ) (good : ∀ w, Cl w → Prop) (N : ℂ), (∀ᶠ w in (cofinite : Filter ι), (∃! c, good w c) ∧ ∀ c, (O w c = if good w c then 1 else 0) ∧ (good w c → ∀ d, s d w c = 1)) → (∀ w, w ∉ S → Nonempty (Cl w)) → (∀ r, ∀ᶠ w in (cofinite : Filter ι), good w (loc r w)) → (∀ r r', (∀ w ∈ S, loc r w = loc r' w) → r = r') → (∀ x : ∀ w, Cl w, (∀ᶠ w in (cofinite : Filter ι), good w (x w)) → ∑ᶠ d : D, ∏ᶠ w ∈ S, s d w (x w) = if ∃ r, ∀ w ∈ S, loc r w = x w then N else 0) → (Function.support fun r : R => ∏ᶠ w ∈ S, O w (loc r w)).Finite ∧ (∑ᶠ r : R, ∏ᶠ w ∈ S, O w (loc r w)) * N = ∑ᶠ d : D, ∏ᶠ w ∈ S, ∑ᶠ c : Cl w, s d w c * O w c := by
  first | exact @GlobalTheory.finsum_finprod_local_sums_expand | exact GlobalTheory.finsum_finprod_local_sums_expand | (intros; apply GlobalTheory.finsum_finprod_local_sums_expand <;> assumption)
end
end
