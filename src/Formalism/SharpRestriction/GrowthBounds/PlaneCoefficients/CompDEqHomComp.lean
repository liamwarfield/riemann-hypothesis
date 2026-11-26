module

public import Formalism.SharpRestriction.GrowthBounds.PolynomialLevels.LowestWeightNonposOffSet

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.PolynomialLevels.LevNMonomial
noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.NormalSetCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.Proposition5Numerics Formalism.MainNotions.PairMembershipBlocks

section Lev

variable {n' r K m : ℕ} [NeZero n'] (Fr : Frames n' r) (p : ℕ) {O : Type} [CommRing O] [IsDomain O]
  (hk : m + 1 = r + K) {J : ℕ} [NeZero J] (nL : ZMod J → ℕ)

theorem levN_add (F G : MvPolynomial (TV n' (m + 1)) (KK O)) :
    levN Fr p hk nL (F + G) = levN Fr p hk nL F + levN Fr p hk nL G := by
  unfold levN
  exact sumSupp_add (fun mo => (monomial (R := KK O) (noMon Fr p hk nL mo)).toAddMonoidHom) F G

theorem levN_monomial (mo : TV n' (m + 1) →₀ ℕ) (c : KK O) :
    levN Fr p hk nL (monomial mo c) = monomial (noMon Fr p hk nL mo) c := by
  unfold levN
  by_cases h : c = 0
  · subst h; simp
  · rw [support_monomial, if_neg h, Finset.sum_singleton, coeff_monomial, if_pos rfl]

def psiExp (a : TL J nL r × Fin K →₀ ℕ) : TV n' (m + 1) →₀ ℕ :=
  a.sum fun v e => Finsupp.single (noVar Fr hk nL v.1 v.2) (lowP Fr p v.1 * e)

def Psi : MvPolynomial (TL J nL r × Fin K) (KK O) →ₐ[KK O] MvPolynomial (TV n' (m + 1)) (KK O) :=
  aeval fun v => X (noVar Fr hk nL v.1 v.2) ^ lowP Fr p v.1

theorem Psi_monomial (a : TL J nL r × Fin K →₀ ℕ) (c : KK O) :
    Psi (O := O) Fr p hk nL (monomial a c) = monomial (psiExp Fr p hk nL a) c := by
  unfold Psi psiExp
  rw [aeval_monomial, monomial_finsupp_sum_index, MvPolynomial.algebraMap_eq]
  congr 1
  refine Finsupp.prod_congr fun v _ => ?_
  rw [← pow_mul, X_pow_eq_monomial]

variable {Fr nL}

theorem noVar_inj {L₁ N₁ : ℕ} (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (hJ : J = Fr.J)
    (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) {x x' : TL J nL r} {b b' : Fin K}
    (h : noVar Fr hk nL x b = noVar Fr hk nL x' b') : x = x' ∧ b = b' := by
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  simp only [noVar] at h1 h2
  exact ⟨dg_inj hV hr hJ hnL h1, Fin.natAdd_injective K r (Fin.cast_injective _ h2)⟩

theorem noMon_psiExp {L₁ N₁ : ℕ} (hp : 0 < p) (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (hJ : J = Fr.J)
    (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) (a : TL J nL r × Fin K →₀ ℕ) :
    noMon Fr p hk nL (psiExp Fr p hk nL a) = a := by
  ext ⟨x, b⟩
  have hP : 0 < lowP Fr p x := pow_pos hp _
  have h1 : psiExp Fr p hk nL a (noVar Fr hk nL x b) = lowP Fr p x * a (x, b) := by
    unfold psiExp
    rw [Finsupp.sum_apply, Finsupp.sum_eq_single (x, b)]
    · rw [Finsupp.single_eq_same]
    · intro v _ hv
      rw [Finsupp.single_apply, if_neg]
      intro h
      obtain ⟨e1, e2⟩ := noVar_inj hk hV hr hJ hnL h
      exact hv (Prod.ext e1 e2)
    · intro _
      rw [mul_zero, Finsupp.single_zero, Finsupp.zero_apply]
  simp only [noMon, Finsupp.coe_equivFunOnFinite_symm]
  rw [h1, Nat.mul_div_cancel_left _ hP]

theorem levN_Psi {L₁ N₁ : ℕ} (hp : 0 < p) (hV : Fr.Valid L₁ N₁) (hr : 1 ≤ r) (hJ : J = Fr.J)
    (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) (H : MvPolynomial (TL J nL r × Fin K) (KK O)) :
    levN Fr p hk nL (Psi (O := O) Fr p hk nL H) = H := by
  induction H using MvPolynomial.induction_on' with
  | monomial a c => rw [Psi_monomial, levN_monomial, noMon_psiExp p hk hp hV hr hJ hnL]
  | add F G hF hG => rw [map_add (f := _), levN_add, hF, hG]

end Lev

theorem seg_Psi (p : ℕ) {n' r K m : ℕ} [NeZero n'] [NeZero r] (O : Type) [CommRing O] [IsDomain O]
    (hk : m + 1 = r + K) (Fr : Frames n' r) (L₁ N₁ : ℕ) (hV : Fr.Valid L₁ N₁) {J : ℕ} [NeZero J] (nL : ZMod J → ℕ)
    (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) (i : ℤ)
    (hsurj : ∀ x ∈ Fr.letters i, ¬ Fr.IsW i x → ∃ t : TL J nL r, segZ t.1 = i ∧ posTL Fr t = x)
    (A : MvPolynomial (ℤ × Fin K) O) (hA : A ∈ supported O {v : ℤ × Fin K | v.1 ∈ Fr.letters i ∧ ¬ Fr.IsW i v.1}) :
    MvPolynomial.map (algebraMap O (KK O)) (rename (castV hk) (phSeg O K p Fr i (nmEmb O r K A))) =
      Psi (O := O) Fr p hk nL (Rn Fr nL A) := by
  have hr : 1 ≤ r := NeZero.one_le
  let f₁ : MvPolynomial (ℤ × Fin K) O →+* MvPolynomial (TV n' (m + 1)) (KK O) :=
    (MvPolynomial.map (algebraMap O (KK O))).comp ((rename (castV hk) : _ →ₐ[O] _).toRingHom.comp
      ((phSeg O K p Fr i).toRingHom.comp (nmEmb O r K).toRingHom))
  let f₂ : MvPolynomial (ℤ × Fin K) O →+* MvPolynomial (TV n' (m + 1)) (KK O) :=
    (Psi (O := O) Fr p hk nL).toRingHom.comp
      ((rename (fun v : ℤ × Fin K => (gT Fr nL v.1, v.2)) : _ →ₐ[KK O] _).toRingHom.comp
        (MvPolynomial.map (algebraMap O (KK O))))
  have key : f₁ A = f₂ A := by
    refine hom_congr_vars ?_ ?_ rfl
    · ext c
      simp [f₁, f₂, nmEmb, phSeg, Psi, MvPolynomial.algebraMap_eq]
    · intro v hv _
      have hv' := (mem_supported.1 hA) (Finset.mem_coe.2 hv)
      obtain ⟨t, ht1, ht2⟩ := hsurj v.1 hv'.1 hv'.2
      have hg : gT Fr nL v.1 = t := by
        rw [← ht2]
        exact Function.leftInverse_invFun (dg_posTL_inj hV hr hnL) t
      obtain ⟨x, c⟩ := v
      simp only at hg ht2
      simp only [f₁, f₂, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, nmEmb, phSeg, Psi, rename_X,
        aeval_X, map_pow, map_X, hg]
      simp only [castV, noVar, lowP, ht1, ht2]
  exact key

theorem levN_zNo (p : ℕ) [Fact p.Prime] {n' r K m : ℕ} [NeZero n'] [NeZero r] [NeZero K] (O : Type) [CommRing O]
    [IsDomain O] (hk : m + 1 = r + K) (Fr : Frames n' r) (L₁ N₁ : ℕ) (hV : Fr.Valid L₁ N₁) {J : ℕ} [NeZero J]
    (nL : ZMod J → ℕ) (hJ : J = Fr.J) (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card)
    (hsurj : ∀ i : ℕ, i < Fr.J → ∀ x ∈ Fr.letters i, ¬ Fr.IsW i x →
      ∃ t : TL J nL r, segZ t.1 = (i : ℤ) ∧ posTL Fr t = x)
    (G : ℤ → MvPolynomial (ℤ × Fin K) O)
    (hG : ∀ i : ℕ, i < Fr.J → G i ∈ supported O {v : ℤ × Fin K | v.1 ∈ Fr.letters i ∧ ¬ Fr.IsW i v.1}) :
    levN Fr p hk nL (zNo p O hk Fr G) = ∏ i ∈ Finset.range Fr.J, Rn Fr nL (G i) := by
  have hr : 1 ≤ r := NeZero.one_le
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have h1 : zNo p O hk Fr G = Psi (O := O) Fr p hk nL (∏ i ∈ Finset.range Fr.J, Rn Fr nL (G i)) := by
    unfold zNo
    rw [map_prod, map_prod, map_prod]
    refine Finset.prod_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    exact seg_Psi p O hk Fr L₁ N₁ hV nL hnL (i : ℤ) (hsurj i hi') (G i) (hG i hi')
  rw [h1, levN_Psi p hk hp hV hr hJ hnL]

end Formalism.MainNotions.NormalSetCounting
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.PolynomialLevels.MemSpanList
noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.NormalSetCounting

open Formalism.MainNotions.G Formalism.MainNotions.TestSideWords

section JU

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {ι : Type*} [Fintype ι] [DecidableEq ι]
  (E : ι → GLOps n K V) (ee : ι → (Fin n → ℤ) → Module.End K V)

theorem ee_pres (hee : ∀ i mu, IsIsoProj (E i) mu (ee i mu))
    (hdec : ∀ i (G : V), ∃ T : Finset (Fin n → ℤ), G = ∑ mu ∈ T, ee i mu G ∧ ∀ mu, ee i mu G ∈ isoSub (E i) mu)
    (hcomm : ∀ i i' mu mu', ee i mu * ee i' mu' = ee i' mu' * ee i mu)
    (i i' : ι) (mu nu : Fin n → ℤ) (x : V) (hx : x ∈ isoSub (E i') nu) : ee i mu x ∈ isoSub (E i') nu := by
  obtain ⟨_, _, h2⟩ := hdec i' (ee i mu x)
  have h1 : ee i' nu x = x := (hee i' nu).1 x hx
  have h3 : ee i mu x = ee i' nu (ee i mu x) := by
    have h4 := congrArg (fun f : Module.End K V => f x) (hcomm i i' mu nu)
    simp only [Module.End.mul_apply] at h4
    rw [← h4, h1]
  rw [h3]
  exact h2 nu

theorem mem_span_list (hee : ∀ i mu, IsIsoProj (E i) mu (ee i mu))
    (hdec : ∀ i (G : V), ∃ T : Finset (Fin n → ℤ), G = ∑ mu ∈ T, ee i mu G ∧ ∀ mu, ee i mu G ∈ isoSub (E i) mu)
    (hcomm : ∀ i i' mu mu', ee i mu * ee i' mu' = ee i' mu' * ee i mu) (l : List ι) (y : V) :
    y ∈ Submodule.span K {x : V | ∃ lam : ι → Fin n → ℤ, ∀ i ∈ l, x ∈ isoSub (E i) (lam i)} := by
  induction l generalizing y with
  | nil => exact Submodule.subset_span ⟨fun _ _ => 0, by simp⟩
  | cons i l ih =>
    have key : Submodule.span K {x : V | ∃ lam : ι → Fin n → ℤ, ∀ j ∈ l, x ∈ isoSub (E j) (lam j)} ≤
        Submodule.span K {x : V | ∃ lam : ι → Fin n → ℤ, ∀ j ∈ i :: l, x ∈ isoSub (E j) (lam j)} := by
      rw [Submodule.span_le]
      rintro x ⟨lam, hlam⟩
      obtain ⟨T, hT, hmem⟩ := hdec i x
      show x ∈ Submodule.span K {x : V | ∃ lam : ι → Fin n → ℤ, ∀ j ∈ i :: l, x ∈ isoSub (E j) (lam j)}
      rw [hT]
      refine Submodule.sum_mem _ fun mu _ => Submodule.subset_span ⟨Function.update lam i mu, ?_⟩
      intro j hj
      by_cases hji : j = i
      · subst hji
        rw [Function.update_self]
        exact hmem mu
      · rw [Function.update_of_ne hji]
        exact ee_pres E ee hee hdec hcomm i j mu (lam j) x (hlam j ((List.mem_cons.mp hj).resolve_left hji))
    exact key (ih y)

private theorem list_prod_isoProj_apply_eq_ite (hee : ∀ i mu, IsIsoProj (E i) mu (ee i mu)) (ka lam : ι → Fin n → ℤ) (x : V)
    (hx : ∀ i, x ∈ isoSub (E i) (lam i)) (l : List ι) :
    (l.map (fun i => ee i (ka i))).prod x = if ∀ i ∈ l, lam i = ka i then x else 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply, ih]
    by_cases h : ∀ i ∈ l, lam i = ka i
    · rw [if_pos h]
      by_cases ha : lam a = ka a
      · have hall : ∀ i ∈ a :: l, lam i = ka i := by
          intro i hi
          rcases List.mem_cons.mp hi with rfl | hi
          · exact ha
          · exact h i hi
        rw [if_pos hall]
        exact (hee a (ka a)).1 x (by rw [← ha]; exact hx a)
      · have hno : ¬ ∀ i ∈ a :: l, lam i = ka i := fun hh => ha (hh a (List.mem_cons.mpr (Or.inl rfl)))
        rw [if_neg hno]
        exact (hee a (ka a)).2 (lam a) ha x (hx a)
    · have hno : ¬ ∀ i ∈ a :: l, lam i = ka i := fun hh => h fun i hi => hh i (List.mem_cons.mpr (Or.inr hi))
      rw [if_neg h, if_neg hno, map_zero]

theorem jproj_eq (hee : ∀ i mu, IsIsoProj (E i) mu (ee i mu))
    (hdec : ∀ i (G : V), ∃ T : Finset (Fin n → ℤ), G = ∑ mu ∈ T, ee i mu G ∧ ∀ mu, ee i mu G ∈ isoSub (E i) mu)
    (hcomm : ∀ i i' mu mu', ee i mu * ee i' mu' = ee i' mu' * ee i mu) (ka : ι → Fin n → ℤ)
    (e : Module.End K V) (he : IsJProj E {ka} e) (y : V) : e y = jointE ee ka y := by
  have hy := mem_span_list E ee hee hdec hcomm Finset.univ.toList y
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨lam, hlam⟩ := hx
    have hx' : ∀ i, x ∈ isoSub (E i) (lam i) := fun i => hlam i (Finset.mem_toList.mpr (Finset.mem_univ i))
    have hxj : x ∈ jIso E lam := by
      simp only [jIso, Submodule.mem_iInf]
      exact hx'
    unfold jointE
    rw [list_prod_isoProj_apply_eq_ite E ee hee ka lam x hx']
    by_cases h : lam = ka
    · rw [if_pos (fun i _ => congrFun h i)]
      exact he.1 lam h x hxj
    · have hno : ¬ ∀ i ∈ (Finset.univ : Finset ι).toList, lam i = ka i :=
        fun hh => h (funext fun i => hh i (Finset.mem_toList.mpr (Finset.mem_univ i)))
      rw [if_neg hno]
      exact he.2 lam h x hxj
  | zero => simp
  | add a b _ _ ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
  | smul c a _ ha => rw [map_smul, map_smul, ha]

theorem jproj_ne (hee : ∀ i mu, IsIsoProj (E i) mu (ee i mu))
    (hdec : ∀ i (G : V), ∃ T : Finset (Fin n → ℤ), G = ∑ mu ∈ T, ee i mu G ∧ ∀ mu, ee i mu G ∈ isoSub (E i) mu)
    (hcomm : ∀ i i' mu mu', ee i mu * ee i' mu' = ee i' mu' * ee i mu) (ka : ι → Fin n → ℤ)
    (e : Module.End K V) (he : IsJProj E {ka} e) (y : V) (hy : e y ≠ 0) (i : ι) : ee i (ka i) y ≠ 0 := by
  intro h0
  apply hy
  have hfix : ∀ z : V, ee i (ka i) (jointE ee ka z) = jointE ee ka z := by
    intro z
    have hz := mem_span_list E ee hee hdec hcomm Finset.univ.toList z
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨lam, hlam⟩ := hx
      have hx' : ∀ j, x ∈ isoSub (E j) (lam j) := fun j => hlam j (Finset.mem_toList.mpr (Finset.mem_univ j))
      unfold jointE
      rw [list_prod_isoProj_apply_eq_ite E ee hee ka lam x hx']
      split_ifs with h
      · exact (hee i (ka i)).1 x (by rw [← h i (Finset.mem_toList.mpr (Finset.mem_univ i))]; exact hx' i)
      · exact map_zero _
    | zero => simp
    | add a b _ _ ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
    | smul c a _ ha => rw [map_smul, map_smul, ha]
  have hc : Commute (ee i (ka i)) (jointE ee ka) := by
    unfold jointE
    apply Commute.list_prod_right
    intro b hb
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hb
    exact hcomm i j (ka i) (ka j)
  rw [jproj_eq E ee hee hdec hcomm ka e he y, ← hfix y, ← Module.End.mul_apply, hc.eq, Module.End.mul_apply, h0, map_zero]

end JU

end Formalism.MainNotions.NormalSetCounting
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.TypeBound
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.TestSideWords

open Formalism.MainNotions.G

def TypeBound : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (ι : Type) [Fintype ι] (LL : Letters ι) (n : ℕ) [NeZero n] (S : Set ι)
    (e : (Fin n → ℤ) → Module.End K (MvPolynomial (ι × Fin n) K)),
    (∀ mu, IsIsoProj (glOps K n LL S) mu (e mu)) →
    (∀ G : MvPolynomial (ι × Fin n) K, ∃ T : Finset (Fin n → ℤ),
      G = ∑ mu ∈ T, e mu G ∧ ∀ mu, e mu G ∈ isoSub (glOps K n LL S) mu) →
    ∀ (G : MvPolynomial (ι × Fin n) K) (lam : Fin n → ℤ), e lam G ≠ 0 →
      (∀ M : ℤ, lam1S LL S G ≤ (M : WithBot ℤ) → lam 0 ≤ M) ∧
      (∀ th : ℤ, (th : WithTop ℤ) ≤ valS LL S G → th ≤ lam (lastIdx n))

end Formalism.MainNotions.TestSideWords
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.PlaneCoefficients.TypeBd
noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PairMembershipBlocks

open Formalism.MainNotions.G Formalism.MainNotions.TestSideWords Formalism.MainNotions.G.GLWeightTheory

theorem typeBound_proved (D : Formalism.BasicNotions.D7) : TypeBound := by

  have hV := Formalism.MainNotions.G.GLWeightTheory.valuation_field D
  unfold Formalism.MainNotions.CovariantDegrees.ValuationLemmaField Formalism.MainNotions.CovariantDegrees.ShaLengthVersionTwo at hV
  unfold TypeBound
  intro K _ _ ι _ LL n _ S e he _ G lam hne
  obtain ⟨hval, hlam⟩ := hV.2 K ι LL n S e he
  exact ⟨fun M hM => (hlam G M).1 hM lam hne, fun th hth => (hval G th).1 hth lam hne⟩

end Formalism.MainNotions.PairMembershipBlocks
end
end

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.PairMembershipBlocks

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.Proposition5Numerics Formalism.MainNotions.NormalSetCounting

theorem compD_eq_homComp {ι : Type} {s : ℕ} {Kf : Type} [Field Kf] (d : ι → ℕ) (H : MvPolynomial (ι × Fin s) Kf) :
    compD d H = homComp d H := rfl

theorem restN (D : Formalism.BasicNotions.D7) : RestN := by
  intro p _ n' r K m _ _ _ O _ _ _ _ S hR hk Fr L₁ N₁ hV _ J _ Dt hT G hG dNo ka e he hne j u hu M
  obtain ⟨hJ, hnL, hsgn, -, -, -⟩ := hT
  have hY := levN_zNo p O hk Fr L₁ N₁ hV Dt.nL hJ hnL (fun i hi x hx hW => tl_surj' hV hJ hnL i hi x hx hW) G hG
  rw [hY] at hne
  have key : ∀ (u' : ℕ) (hu' : u' < Dt.nL j + r + 1) (Sz : Set ℤ),
      (∀ s, (⟨j, s⟩ : TL J Dt.nL r) ∈ NSet Dt.nL j u' ↔ posTL Fr (⟨j, s⟩ : TL J Dt.nL r) ∈ Sz) →
      lam1S LZ Sz (G (segZ j)) ≤ ((M : ℤ) : WithBot ℤ) → ka j u' 0 ≤ M := by
    intro u' hu' Sz hS hM
    have h1 := jproj_ne (normE p K Dt) (eeN D K Dt) (fun i => (eeN_spec D K Dt i).1) (fun i => (eeN_spec D K Dt i).2)
      (eeN_comm D K Dt S hR) (fun i => ka i.1 i.2.val) e he _ hne ⟨j, ⟨u', hu'⟩⟩
    have h2 := (typeBound_proved D (KK O) (TL J Dt.nL r) Dt.trueLet K (NSet Dt.nL j u') (eeN D K Dt ⟨j, ⟨u', hu'⟩⟩)
      (eeN_spec D K Dt ⟨j, ⟨u', hu'⟩⟩).1 (eeN_spec D K Dt ⟨j, ⟨u', hu'⟩⟩).2 _ _ h1).1 M
    apply h2
    rw [compD_eq_homComp]
    refine le_trans (valComp (KK O) (TL J Dt.nL r) K Dt.trueLet (NSet Dt.nL j u') _ dNo).2 ?_
    exact le_trans (lam_prod_le Dt hV hJ hnL hsgn G hG j _ Sz (fun t ht => mem_NSet_fst ht) hS) hM
  exact ⟨key u (by omega) _ fun s => NSet_lt hV hnL j u hu s, key (u + 1) (by omega) _ fun s => NSet_le hV hnL j u hu s⟩

end Formalism.MainNotions.PairMembershipBlocks
