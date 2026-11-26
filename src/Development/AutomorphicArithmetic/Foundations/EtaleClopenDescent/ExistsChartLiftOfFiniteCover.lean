module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PowMulMem
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PLocForms
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.CubeDifferentialIdentityApply
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PMinorSum
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PLocMax
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PThMuLat
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PEdgeRel
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PFieldLe
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PoincareLelong
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PullbackKahlerOmegaBounded
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PPTheta
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PrBOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PRYBasic
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PSysBasic
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.KoszulTwoExactOfGl2
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PKunDec
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PLCupRel
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PLatOm
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PLocReg
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.ProductCupOfSystem
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PPLift
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.IntegralClosureMonoSubset
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.RCupOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.DeRhamRestrictionTraceDegreeOne
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.DeRhamRegulatorTrivialCase
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PRowEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PSubQEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PullbackKahlerDegree
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.YbValTensor
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PYCmpG
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PYCmpT
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.MinorsCocycle

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.UnscUnscInv
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

section
variable {S E κ : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E]
  (act : S →ₐ[ℂ] Module.End ℂ E)

private lemma act_inv_act (v : Sˣ) (m : E) : act ((v⁻¹ : Sˣ) : S) (act (v : S) m) = m := by
  rw [← Module.End.mul_apply, ← map_mul, Units.inv_mul, map_one, Module.End.one_apply]

private lemma act_act_inv (v : Sˣ) (m : E) : act (v : S) (act ((v⁻¹ : Sˣ) : S) m) = m := by
  rw [← Module.End.mul_apply, ← map_mul, Units.mul_inv, map_one, Module.End.one_apply]

private lemma prod_inv_inv (u : κ → Sˣ) (L : Finset κ) : (∏ l ∈ L, (u⁻¹) l)⁻¹ = ∏ l ∈ L, u l := by
  simp [Finset.prod_inv_distrib]

private lemma unsc_inv_unsc (u : κ → Sˣ) (c : Finset κ → E) : unsc act u⁻¹ (unsc act u c) = c := by
  funext L
  simp only [unsc]
  rw [prod_inv_inv]
  exact act_act_inv act _ _

private lemma unsc_unsc_inv (u : κ → Sˣ) (c : Finset κ → E) : unsc act u (unsc act u⁻¹ c) = c := by
  funext L
  simp only [unsc]
  rw [prod_inv_inv]
  exact act_inv_act act _ _

private lemma unsc_inj (u : κ → Sˣ) {c c' : Finset κ → E} (h : unsc act u c = unsc act u c') : c = c' := by
  rw [← unsc_inv_unsc act u c, h, unsc_inv_unsc]

variable [LinearOrder κ]

private lemma mem_C_iff (M : Submodule ℂ E) (u : κ → Sˣ) (z r : κ → S) (n : ℤ) (c : Finset κ → E) :
    c ∈ (kosT act M u z).C n ↔ unsc act u c ∈ (kos act M r).C n := by
  simp only [kosT, kos, acx, Submodule.mem_pi, Set.mem_univ, true_imp_iff]
  refine forall_congr' fun s => ?_
  by_cases h : (s.card : ℤ) = n
  · simp only [h, if_true]
    constructor
    · rintro ⟨m, hm, hc⟩
      change act _ (c s) ∈ M
      rw [← hc, act_inv_act]
      exact hm
    · intro hm
      exact ⟨_, hm, act_act_inv act _ _⟩
  · simp only [h, if_false, Submodule.mem_bot]
    constructor
    · intro h0
      simp [unsc, h0]
    · intro h0
      have h1 : act ((∏ l ∈ s, u l : Sˣ) : S) (unsc act u c s) = 0 := by rw [h0, map_zero]
      simpa only [unsc, act_act_inv] using h1

private lemma unsc_wd (u : κ → Sˣ) (z r : κ → S) (hr : ∀ l, r l = z l * ((u l)⁻¹ : Sˣ)) (c : Finset κ → E) :
    unsc act u (wd (fun l => act (z l)) c) = wd (fun l => act (r l)) (unsc act u c) := by
  funext t
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [unsc, wd, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, map_sum, map_zsmul]
  refine Finset.sum_congr rfl fun i hi => ?_
  congr 1
  have hp : (∏ l ∈ t, u l) = u i * ∏ l ∈ t.erase i, u l := (Finset.mul_prod_erase t u hi).symm
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, hr, hp, mul_inv, Units.val_mul]
  congr 2
  ring

end

theorem UpperTheory.Gal.productCup_of_system.rS_of :
    RS := by
  intro S E _ _ _ _ act κ _ _ M u r z hr n c
  have hD : ∀ c, unsc act u ((kosT act M u z).D c) = (kos act M r).D (unsc act u c) :=
    fun c => unsc_wd act u z r hr c
  have hC : ∀ n c, c ∈ (kosT act M u z).C n ↔ unsc act u c ∈ (kos act M r).C n :=
    fun n c => mem_C_iff act M u z r n c
  refine ⟨hC n c, ?_, ?_, unsc_inv_unsc act u c, unsc_unsc_inv act u c⟩
  · simp only [Cx.Z, Submodule.mem_inf, LinearMap.mem_ker]
    refine and_congr (hC n c) ?_
    rw [← hD]
    constructor
    · intro h
      rw [h]
      funext L
      simp [unsc]
    · intro h
      refine unsc_inj act u (h.trans ?_)
      funext L
      simp [unsc]
  · simp only [Cx.B, Submodule.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨unsc act u y, (hC _ y).1 hy, (hD y).symm⟩
    · rintro ⟨y, hy, h⟩
      refine ⟨unsc act u⁻¹ y, (hC _ _).2 ?_, unsc_inj act u ?_⟩
      · rwa [unsc_unsc_inv]
      · rw [hD, unsc_unsc_inv, h]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.FiltrationBoundaryCriterionOfWdBasic
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

section
variable {σ E : Type} [LinearOrder σ] [Fintype σ] [AddCommGroup E] [Module ℂ E]

private lemma wd_apply' (w : σ → Module.End ℂ E) (c : Finset σ → E) (t : Finset σ) :
    wd w c t = ∑ i ∈ t, (GlobalTheory.cubeSign t i : ℤ) • w i (c (t.erase i)) := by
  simp [wd, LinearMap.pi_apply, LinearMap.sum_apply]

private lemma wd_congr' (w : σ → Module.End ℂ E) (c c' : Finset σ → E) (t : Finset σ)
    (h : ∀ i ∈ t, w i = 0 ∨ c (t.erase i) = c' (t.erase i)) : wd w c t = wd w c' t := by
  rw [wd_apply', wd_apply']
  refine Finset.sum_congr rfl fun i hi => ?_
  rcases h i hi with h | h
  · simp [h]
  · rw [h]

private lemma card_erase_mem' {Q t : Finset σ} {i : σ} (hi : i ∈ t) (hQ : i ∈ Q) :
    (((t.erase i) ∩ Q).card : ℤ) = ((t ∩ Q).card : ℤ) - 1 := by
  have h1 : (t.erase i) ∩ Q = (t ∩ Q).erase i := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_erase]
    tauto
  have h2 : i ∈ t ∩ Q := Finset.mem_inter.2 ⟨hi, hQ⟩
  have h3 : 0 < (t ∩ Q).card := Finset.card_pos.2 ⟨i, h2⟩
  rw [h1, Finset.card_erase_of_mem h2]
  omega

private lemma card_erase_not' {Q t : Finset σ} {i : σ} (hQ : i ∉ Q) :
    (t.erase i) ∩ Q = t ∩ Q := by
  ext x
  simp only [Finset.mem_inter, Finset.mem_erase]
  constructor
  · rintro ⟨⟨_, h⟩, h'⟩
    exact ⟨h, h'⟩
  · rintro ⟨h, h'⟩
    exact ⟨⟨fun e => hQ (e ▸ h'), h⟩, h'⟩

private lemma levQ' (w : σ → Module.End ℂ E) (Q : Finset σ) {m m' : ℤ} (hm : m' = m + 1)
    {y : Finset σ → E} (hy : Lev Q (· = m) y) : Lev Q (· = m') (wd (wOn Q w) y) := by
  intro t ht
  have ht' : ¬ (((t ∩ Q).card : ℤ) = m') := ht
  have h0 : wd (wOn Q w) y t = wd (wOn Q w) 0 t := by
    refine wd_congr' _ _ _ _ fun i hi => ?_
    by_cases hiQ : i ∈ Q
    · right
      refine hy _ ?_
      have h1 := card_erase_mem' hi hiQ
      show ¬ ((((t.erase i) ∩ Q).card : ℤ) = m)
      omega
    · left
      simp [wOn, hiQ]
  rw [h0, map_zero]
  rfl

private lemma levC' (w : σ → Module.End ℂ E) (Q : Finset σ) {m : ℤ}
    {y : Finset σ → E} (hy : Lev Q (· = m) y) : Lev Q (· = m) (wd (wOn Qᶜ w) y) := by
  intro t ht
  have ht' : ¬ (((t ∩ Q).card : ℤ) = m) := ht
  have h0 : wd (wOn Qᶜ w) y t = wd (wOn Qᶜ w) 0 t := by
    refine wd_congr' _ _ _ _ fun i hi => ?_
    by_cases hiQ : i ∈ Q
    · left
      simp [wOn, hiQ]
    · right
      refine hy _ ?_
      show ¬ ((((t.erase i) ∩ Q).card : ℤ) = m)
      rw [card_erase_not' hiQ]
      exact ht'
  rw [h0, map_zero]
  rfl

private lemma wd_split' (hW : WdBasic) (A : Finset σ → Submodule ℂ E) (w : σ → Module.End ℂ E)
    (Q : Finset σ) (c : Finset σ → E) (t : Finset σ) :
    wd w c t = wd (wOn Q w) c t + wd (wOn Qᶜ w) c t := by
  have h := (hW σ E A (wOn Q w)).2.2.1 (wOn Qᶜ w)
  have h2 : wOn Q w + wOn Qᶜ w = w := by
    funext i
    by_cases hi : i ∈ Q <;> simp [wOn, hi]
  rw [h2] at h
  rw [h]
  rfl

private lemma sub_cocycle' {A : Finset σ → Submodule ℂ E} {w : σ → Module.End ℂ E}
    (hcx : (acx A w).IsCx) {n : ℤ} {c y : Finset σ → E} (hc : c ∈ (acx A w).Z n)
    (hy : y ∈ (acx A w).C (n - 1)) : c - wd w y ∈ (acx A w).Z n := by
  obtain ⟨h1, h2⟩ := hcx _ y hy
  rw [sub_add_cancel] at h1
  obtain ⟨hc1, hc2⟩ := Submodule.mem_inf.1 hc
  refine Submodule.mem_inf.2 ⟨Submodule.sub_mem _ hc1 h1, ?_⟩
  have h3 : wd w c = 0 := hc2
  have h4 : wd w (wd w y) = 0 := h2
  show wd w (c - wd w y) = 0
  rw [map_sub, h3, h4, sub_zero]

private lemma of_sub' {A : Finset σ → Submodule ℂ E} {w : σ → Module.End ℂ E} {n : ℤ}
    {c y : Finset σ → E} (hy : y ∈ (acx A w).C (n - 1)) (h : c - wd w y ∈ (acx A w).B n) :
    c ∈ (acx A w).B n := by
  have h2 : wd w y ∈ (acx A w).B n := Submodule.mem_map_of_mem hy
  simpa using add_mem h h2

private lemma low' (hW : WdBasic) {A : Finset σ → Submodule ℂ E} {w : σ → Module.End ℂ E}
    {Q : Finset σ} {d : ℤ} (hok : WOk A w) (hq : QEx A w Q d) :
    ∀ k : ℕ, k ≤ d.toNat → ∀ (n : ℤ) (c : Finset σ → E), c ∈ (acx A w).Z n →
      Lev Q (· ≤ (k : ℤ) - 1) c → c ∈ (acx A w).B n := by
  have hcx : (acx A w).IsCx := (hW σ E A w).2.1 hok
  intro k
  induction k with
  | zero =>
    intro _ n c hc hl
    have h0 : c = 0 := by
      funext s
      refine hl s ?_
      show ¬ (((s ∩ Q).card : ℤ) ≤ ((0 : ℕ) : ℤ) - 1)
      omega
    rw [h0]
    exact zero_mem _
  | succ k ih =>
    intro hk n c hc hl
    have hkd : (k : ℤ) < d := by omega
    have hl' : ∀ s, (k : ℤ) < ((s ∩ Q).card : ℤ) → c s = 0 := by
      intro s hs
      refine hl s ?_
      show ¬ (((s ∩ Q).card : ℤ) ≤ ((k + 1 : ℕ) : ℤ) - 1)
      push_cast
      omega
    obtain ⟨hc1, hc2⟩ := Submodule.mem_inf.1 hc
    have hc3 : wd w c = 0 := hc2
    let cm : Finset σ → E := fun s => if ((s ∩ Q).card : ℤ) = k then c s else 0
    have hcm : cm ∈ (acx A w).C n := by
      refine Submodule.mem_pi.2 fun s hs => ?_
      by_cases h : ((s ∩ Q).card : ℤ) = k
      · have : cm s = c s := if_pos h
        rw [this]
        exact Submodule.mem_pi.1 hc1 s hs
      · have : cm s = 0 := if_neg h
        rw [this]
        exact zero_mem _
    have hcl : Lev Q (· = (k : ℤ)) cm := fun s hs => if_neg hs
    have hkill : wd (wOn Q w) cm = 0 := by
      funext t
      by_cases ht : ((t ∩ Q).card : ℤ) = k + 1
      · have e1 : wd (wOn Q w) cm t = wd (wOn Q w) c t := by
          refine wd_congr' _ _ _ _ fun i hi => ?_
          by_cases hiQ : i ∈ Q
          · right
            have h1 := card_erase_mem' hi hiQ
            exact if_pos (by omega)
          · left
            simp [wOn, hiQ]
        have e2 : wd (wOn Qᶜ w) c t = wd (wOn Qᶜ w) 0 t := by
          refine wd_congr' _ _ _ _ fun i hi => ?_
          by_cases hiQ : i ∈ Q
          · left
            simp [wOn, hiQ]
          · right
            refine hl' _ ?_
            rw [card_erase_not' hiQ]
            omega
        have e3 := wd_split' hW A w Q c t
        rw [hc3, e2, map_zero] at e3
        rw [e1]
        simpa using e3.symm
      · exact levQ' w Q rfl hcl t ht
    obtain ⟨y, hy, hyl, hyd⟩ := hq n k hkd cm hcm hcl hkill
    refine of_sub' hy (ih (by omega) n _ (sub_cocycle' hcx hc hy) ?_)
    intro s hs
    have hs' : ¬ (((s ∩ Q).card : ℤ) ≤ (k : ℤ) - 1) := hs
    have e1 := wd_split' hW A w Q y s
    have e2 : wd (wOn Qᶜ w) y s = 0 := levC' w Q hyl s (by
      show ¬ (((s ∩ Q).card : ℤ) = (k : ℤ) - 1)
      omega)
    have e3 : wd (wOn Q w) y s = cm s := congrFun hyd s
    have e4 : cm s = c s := by
      by_cases h : ((s ∩ Q).card : ℤ) = k
      · exact if_pos h
      · have : cm s = 0 := if_neg h
        rw [this, hl' s (by omega)]
    show c s - wd w y s = 0
    rw [e1, e2, e3, e4, add_zero, sub_self]

end

theorem UpperTheory.Gal.productCup_of_system.filtrationBoundaryCriterion_of_wdBasic :
    WdBasic → FiltrationBoundaryCriterion := by
  intro hW σ E _ _ _ _ A w Q d n hok hq c hc hl hy0
  obtain ⟨y, hy, hyl, hyd⟩ := hy0
  have hcx : (acx A w).IsCx := (hW σ E A w).2.1 hok
  have hl' : ∀ s, d < ((s ∩ Q).card : ℤ) → c s = 0 := by
    intro s hs
    refine hl s ?_
    show ¬ (((s ∩ Q).card : ℤ) ≤ d)
    omega
  refine of_sub' hy (low' hW hok hq d.toNat le_rfl n _ (sub_cocycle' hcx hc hy) ?_)
  intro s hs
  have hs' : ¬ (((s ∩ Q).card : ℤ) ≤ (d.toNat : ℤ) - 1) := hs
  have hge : d ≤ ((s ∩ Q).card : ℤ) := by omega
  have e1 := wd_split' hW A w Q y s
  have e2 : wd (wOn Qᶜ w) y s = 0 := levC' w Q hyl s (by
    show ¬ (((s ∩ Q).card : ℤ) = d - 1)
    omega)
  show c s - wd w y s = 0
  rw [e1, e2, add_zero]
  by_cases h : ((s ∩ Q).card : ℤ) = d
  · rw [hyd s h, sub_self]
  · have e3 : wd (wOn Q w) y s = 0 := levQ' w Q (by ring) hyl s h
    rw [e3, hl' s (by omega), sub_self]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.CoordinateSystemDegreeTwoOfUniversalDerivation
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private theorem wd_single' {ι E : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E]
    (w : ι → Module.End ℂ E) (f : Finset ι → E) (i : ι) : wd w f {i} = w i (f ∅) := by
  have s1 : GlobalTheory.cubeSign ({i} : Finset ι) i = 1 := GlobalTheory.cubeSign_singleton i
  simp [wd, s1]

private theorem wd_pair' {ι E : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E]
    (w : ι → Module.End ℂ E) (f : Finset ι → E) {i i' : ι} (h : i < i') :
    wd w f {i, i'} = w i (f {i'}) - w i' (f {i}) := by
  have hne : i ≠ i' := ne_of_lt h
  have s1 : GlobalTheory.cubeSign {i, i'} i = 1 := by
    apply GlobalTheory.cubeSign_eq_one_of_forall_le
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact le_rfl
    · rw [Finset.mem_singleton.mp hj]; exact le_of_lt h
  have s2 : GlobalTheory.cubeSign {i, i'} i' = -1 := by
    have : ({x ∈ ({i, i'} : Finset _) | x < i'}) = {i} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | rfl, hx⟩
        · rfl
        · exact absurd hx (lt_irrefl _)
      · rintro rfl; exact ⟨Or.inl rfl, h⟩
    simp [GlobalTheory.cubeSign, this]
  have e1 : ({i, i'} : Finset _).erase i = {i'} := by
    rw [Finset.erase_insert (by simpa using hne)]
  have e2 : ({i, i'} : Finset _).erase i' = {i} := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hx, rfl | rfl⟩
      · rfl
      · exact absurd rfl hx
    · rintro rfl; exact ⟨hne, Or.inl rfl⟩
  simp only [wd, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.proj_apply]
  rw [Finset.sum_pair hne, s1, s2, e1, e2, one_smul, neg_one_smul, sub_eq_add_neg]

private theorem pair_lt' {ι : Type} [LinearOrder ι] {s : Finset ι} (h : s.card = 2) :
    ∃ x y, x < y ∧ s = {x, y} := by
  obtain ⟨x, y, hne, rfl⟩ := Finset.card_eq_two.1 h
  rcases lt_or_gt_of_ne hne with h' | h'
  · exact ⟨x, y, h', rfl⟩
  · exact ⟨y, x, h', Finset.pair_comm _ _⟩

theorem UpperTheory.Gal.productCup_of_system.coordinateSystem_degree_two_of_universalDerivation :
    L2 → SysOk → WdUni → CechKoszulSystemCocycleGluing := by
  intro hL2 hOk h d S E _ _ _ _ T κ _ _ n z hG hAd hKE c0 hZ hB1 hB2
  obtain ⟨hW, -, -⟩ := hOk d S E T κ n z hG hAd
  have lu1 : ∀ (b : Finset (Two d)) (L : Finset κ), lft (uni b L) = b :=
    fun b L => (h (Two d) κ ℂ 0 0 b L).2.1
  have ru1 : ∀ (b : Finset (Two d)) (L : Finset κ), rgt (uni b L) = L :=
    fun b L => (h (Two d) κ ℂ 0 0 b L).2.2.1
  have lu2 : ∀ (I J : Finset (Fin (d + 1))), lft (uni I J) = I :=
    fun I J => (h (Fin (d + 1)) (Fin (d + 1)) ℂ 0 0 I J).2.1
  have ru2 : ∀ (I J : Finset (Fin (d + 1))), rgt (uni I J) = J :=
    fun I J => (h (Fin (d + 1)) (Fin (d + 1)) ℂ 0 0 I J).2.2.1
  have cu2 : ∀ (I J : Finset (Fin (d + 1))), (uni I J).card = I.card + J.card :=
    fun I J => (h (Fin (d + 1)) (Fin (d + 1)) ℂ 0 0 I J).2.2.2.1
  have ul2 : ∀ (s : Finset (Two d)), uni (lft s) (rgt s) = s :=
    fun s => (h (Fin (d + 1)) (Fin (d + 1)) ℂ 0 0 ∅ ∅).2.2.2.2 s
  set A : Finset (Two d ⊕ₗ κ) → Submodule ℂ E := fun s ↦ mixF (fun I J ↦
    Submodule.map (T.act ↑(∏ l ∈ rgt s, T.u n (pk I) (pk J) l)) (T.M I J)) (lft s) with hAdef
  have hcol : ∀ I J : Finset (Fin (d + 1)), I.Nonempty → J.Nonempty →
      colA A (T.wt z) (uni I J) = T.colCx n z I J := by
    intro I J hI hJ
    simp only [colA, Sys.colCx, kosT]
    congr 1
    funext L
    simp [A, mixF, lu1, ru1, lu2, ru2, hI, hJ]
  have hbot : ∀ b : Finset (Two d), ¬ ((lft b).Nonempty ∧ (rgt b).Nonempty) → ∀ L,
      A (uni b L) = ⊥ := by
    intro b hb L
    simp only [A, mixF, lu1, ru1]
    rw [if_neg hb]
  set c0' : Finset (Two d) → Finset κ → E := fun b =>
    if (lft b).card = 1 ∧ (rgt b).card = 1 then c0 (pk (lft b)) (pk (rgt b)) else 0 with hc0'
  have pk1 : ∀ i : Fin (d + 1), pk ({i} : Finset (Fin (d + 1))) = i := by
    intro i; simp [pk]
  have c0ij : ∀ i j : Fin (d + 1), c0' (uni {i} {j}) = c0 i j := by
    intro i j; simp [c0', lu2, ru2, pk1]
  have cv : ∀ I' J' : Finset (Fin (d + 1)), c0' (uni I' J') =
      if I'.card = 1 ∧ J'.card = 1 then c0 (pk I') (pk J') else 0 := by
    intro I' J'; simp only [hc0', lu2, ru2]
  have hKEA : ∀ b : Finset (Two d), KE (colA A (T.wt z) b) d := by
    intro b
    by_cases hb : (lft b).Nonempty ∧ (rgt b).Nonempty
    · rw [← ul2 b, hcol _ _ hb.1 hb.2]
      exact hKE _ _ hb.1 hb.2
    · intro m _ x hx
      have hx0 : x = 0 := by
        funext L
        have h1 := (Submodule.mem_inf.mp hx).1
        have h2 := (Submodule.mem_pi.mp h1) L (Set.mem_univ _)
        simpa [hbot b hb L] using h2
      rw [hx0]
      exact zero_mem _
  have hZA : ∀ b : Finset (Two d), (b.card : ℤ) = (d : ℤ) + 2 - d →
      c0' b ∈ (colA A (T.wt z) b).Z d := by
    intro b hbc
    by_cases h11 : (lft b).card = 1 ∧ (rgt b).card = 1
    · obtain ⟨i, hi⟩ := Finset.card_eq_one.mp h11.1
      obtain ⟨j, hj⟩ := Finset.card_eq_one.mp h11.2
      have hb' : b = uni {i} {j} := by rw [← hi, ← hj, ul2]
      subst hb'
      rw [c0ij, hcol _ _ (Finset.singleton_nonempty i) (Finset.singleton_nonempty j)]
      exact hZ i j
    · have h0 : c0' b = 0 := by simp only [hc0', h11, if_false]
      rw [h0]
      exact zero_mem _
  have hw : (fun i : Two d => T.wt z (inlE i : Two d ⊕ₗ κ)) = fun _ => 1 := by
    funext i; simp [Sys.wt, inlE]
  have hBA : ∀ b : Finset (Two d), (b.card : ℤ) = (d : ℤ) + 2 - d + 1 →
      (fun L => (wd fun i => T.wt z (inlE i)) (fun b' => c0' b' L) b) ∈ (colA A (T.wt z) b).B d := by
    intro b hbc
    have hb3 : b.card = 3 := by omega
    rw [hw]
    obtain ⟨I, J, rfl⟩ : ∃ I J, b = uni I J := ⟨lft b, rgt b, (ul2 b).symm⟩
    have hIJ : I.card + J.card = 3 := by rw [← cu2]; exact hb3
    have dec : ∀ L, (wd fun _ : Two d => (1 : Module.End ℂ E)) (fun b' => c0' b' L) (uni I J) =
        (wd fun _ => 1) (fun I' => c0' (uni I' J) L) I +
          (-1) ^ I.card • (wd fun _ => 1) (fun J' => c0' (uni I J') L) J :=
      fun L => (h (Fin (d + 1)) (Fin (d + 1)) E (fun _ => 1) (fun b' => c0' b' L) I J).1
    have hcases : I.card = 0 ∨ I.card = 1 ∨ I.card = 2 ∨ I.card = 3 := by omega
    rcases hcases with hI | hI | hI | hI
    · have hI0 : I = ∅ := Finset.card_eq_zero.mp hI
      subst hI0
      have hf : (fun L => (wd fun _ : Two d => (1 : Module.End ℂ E)) (fun b' => c0' b' L) (uni ∅ J)) = 0 := by
        funext L
        rw [dec]
        have z1 : (fun J' => c0' (uni ∅ J') L) = 0 := by
          funext J'; simp [cv]
        rw [z1, map_zero]
        simp [wd]
      rw [hf]
      exact zero_mem _
    · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hI
      have hJ2 : J.card = 2 := by simp at hIJ; omega
      obtain ⟨j, j', hjj, rfl⟩ := pair_lt' hJ2
      have hf : (fun L => (wd fun _ : Two d => (1 : Module.End ℂ E)) (fun b' => c0' b' L) (uni {i} {j, j'})) =
          c0 i j - c0 i j' := by
        funext L
        rw [dec, wd_single', wd_pair' _ _ hjj]
        simp [cv, pk1]
      rw [hf, hcol _ _ (Finset.singleton_nonempty i) (Finset.insert_nonempty _ _)]
      exact hB2 i j j'
    · obtain ⟨i, i', hii, rfl⟩ := pair_lt' hI
      have hJ1 : J.card = 1 := by omega
      obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp hJ1
      have hf : (fun L => (wd fun _ : Two d => (1 : Module.End ℂ E)) (fun b' => c0' b' L) (uni {i, i'} {j})) =
          -(c0 i j - c0 i' j) := by
        funext L
        rw [dec, wd_single', wd_pair' _ _ hii]
        simp [cv, pk1, Finset.card_pair (ne_of_lt hii)]
      rw [hf, hcol _ _ (Finset.insert_nonempty _ _) (Finset.singleton_nonempty j)]
      exact neg_mem (hB1 i i' j)
    · have hJ0 : J = ∅ := Finset.card_eq_zero.mp (by omega)
      subst hJ0
      have hf : (fun L => (wd fun _ : Two d => (1 : Module.End ℂ E)) (fun b' => c0' b' L) (uni I ∅)) = 0 := by
        funext L
        rw [dec]
        have z1 : (fun I' => c0' (uni I' ∅) L) = 0 := by
          funext I'; simp [cv]
        rw [z1, map_zero]
        simp [wd]
      rw [hf]
      exact zero_mem _
  obtain ⟨c, hc, hcb, -⟩ := hL2 (Two d) κ E A (T.wt z) d (d + 2) hW hKEA c0' hZA hBA
  refine ⟨c, hc, fun i j => ?_⟩
  have := hcb (uni {i} {j}) (by rw [cu2]; simp)
  rw [this, c0ij]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PColQEx
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private lemma wd_zero' {ι E : Type} [LinearOrder ι] [AddCommGroup E] [Module ℂ E]
    (x : Finset ι → E) (t : Finset ι) : wd (fun _ : ι => (0 : Module.End ℂ E)) x t = 0 := by
  simp [wd]

private theorem uni_inter_map_inrE {β κ : Type} [LinearOrder β] [LinearOrder κ] [Fintype κ]
    (b : Finset β) (L : Finset κ) :
    uni b L ∩ Finset.map (inrE (β := β)).toEmbedding Finset.univ = L.map (inrE (β := β)).toEmbedding := by
  ext x
  simp [GlobalTheory.WH.uni, inrE]
  constructor
  · rintro ⟨h, a, rfl⟩
    exact ⟨a, by simpa using h, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨by simpa using ha, a, rfl⟩

theorem UpperTheory.Gal.productCup_of_system.colQEx_of :
    WdUni → ColQEx := by
  intro hU β κ E _ _ _ _ _ _ A w d hK n m hm c hc hlev hcz
  set Q := Finset.map (inrE (β := β) (κ := κ)).toEmbedding Finset.univ with hQ
  have hQc : ∀ (b : Finset β) (L : Finset κ), (uni b L ∩ Q).card = L.card := by
    intro b L
    rw [hQ, uni_inter_map_inrE]
    simp
  have hl : (fun i : β => wOn Q w (inlE i)) = fun _ => 0 := by
    funext i
    have : inlE (κ := κ) i ∉ Q := by
      simp [hQ, inlE, inrE]
    simp [wOn, this]
  have hr : (fun l : κ => wOn Q w (inrE l)) = fun l => w (inrE l) := by
    funext l
    have : inrE (β := β) l ∈ Q := by
      simp [hQ]
    simp [wOn, this]
  have hdec : ∀ (x : Finset (β ⊕ₗ κ) → E) (b : Finset β) (L : Finset κ),
      wd (wOn Q w) x (uni b L) =
        (-1 : ℤ) ^ b.card • wd (fun l => w (inrE l)) (fun L' => x (uni b L')) L := by
    intro x b L
    rw [(hU β κ E (wOn Q w) x b L).1, hl, hr, wd_zero', zero_add]
  have hmem : ∀ s, c s ∈ (if ((s.card : ℕ) : ℤ) = n then A s else ⊥) := by
    intro s
    have := hc
    simp only [acx, Submodule.mem_pi, Set.mem_univ, true_implies] at this
    exact this s
  have hY : ∀ b : Finset β, ∃ Y ∈ (colA A w b).C (m - 1),
      wd (fun l => w (inrE l)) Y = fun L => c (uni b L) := by
    intro b
    have hz : (fun L => c (uni b L)) ∈ (colA A w b).Z m := by
      refine Submodule.mem_inf.2 ⟨?_, ?_⟩
      · rw [colA, acx, Submodule.mem_pi]
        intro L _
        show c (uni b L) ∈ (if ((L.card : ℕ) : ℤ) = m then A (uni b L) else ⊥)
        by_cases hL : ((L.card : ℕ) : ℤ) = m
        · rw [if_pos hL]
          have h1 := hmem (uni b L)
          split_ifs at h1 with h2
          · exact h1
          · rw [Submodule.mem_bot] at h1
            rw [h1]
            exact Submodule.zero_mem _
        · rw [if_neg hL, Submodule.mem_bot]
          apply hlev
          show ¬ (((uni b L ∩ Q).card : ℕ) : ℤ) = m
          rwa [show (uni b L ∩ Q).card = L.card by convert hQc b L]
      · rw [LinearMap.mem_ker]
        change wd (fun l => w (inrE l)) (fun L => c (uni b L)) = 0
        funext L
        have h1 : (wd (wOn Q w)) c (uni b L) = 0 := by
          exact congrFun hcz (uni b L)
        rw [hdec] at h1
        simp only [Pi.zero_apply]
        have h2 := congrArg (fun v => (-1 : ℤ) ^ b.card • v) h1
        simp only [smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul, smul_zero] at h2
        exact h2
    obtain ⟨Y, hY1, hY2⟩ := hK b m hm hz
    exact ⟨Y, hY1, hY2⟩
  choose Y hYC hYD using hY
  have hYmem : ∀ b L, Y b L ∈ (if ((L.card : ℕ) : ℤ) = m - 1 then A (uni b L) else ⊥) := by
    intro b L
    have := hYC b
    rw [colA, acx, Submodule.mem_pi] at this
    exact this L (Set.mem_univ _)
  have hU2 := fun s => (hU β κ E w c (lft s) (rgt s)).2.2.2.2 s
  have hQs : ∀ s, (s ∩ Q).card = (rgt s).card := by
    intro s
    have := hQc (lft s) (rgt s)
    rw [hU2 s] at this
    exact this
  obtain ⟨y, hy⟩ : ∃ y : Finset (β ⊕ₗ κ) → E, ∀ s, y s = if (((lft s).card : ℕ) : ℤ) = n - m then
      (-1 : ℤ) ^ (lft s).card • Y (lft s) (rgt s) else 0 := ⟨_, fun s => rfl⟩
  refine ⟨y, ?_, ?_, ?_⟩
  · rw [acx, Submodule.mem_pi]
    intro s _
    show y s ∈ (if ((s.card : ℕ) : ℤ) = n - 1 then A s else ⊥)
    rw [hy]
    have hs := hYmem (lft s) (rgt s)
    rw [hU2 s] at hs
    have hcard := (hU β κ E w c (lft s) (rgt s)).2.2.2.1
    rw [hU2 s] at hcard
    by_cases h1 : (((lft s).card : ℕ) : ℤ) = n - m
    · rw [if_pos h1]
      by_cases h2 : ((s.card : ℕ) : ℤ) = n - 1
      · rw [if_pos h2]
        by_cases h3 : (((rgt s).card : ℕ) : ℤ) = m - 1
        · rw [if_pos h3] at hs
          exact zsmul_mem hs _
        · rw [if_neg h3, Submodule.mem_bot] at hs
          rw [hs, smul_zero]
          exact Submodule.zero_mem _
      · rw [if_neg h2, Submodule.mem_bot]
        rw [if_neg, Submodule.mem_bot] at hs
        · rw [hs, smul_zero]
        · intro h3
          apply h2
          rw [hcard]
          push_cast
          omega
    · rw [if_neg h1]
      exact Submodule.zero_mem _
  · intro s hs
    rw [hy]
    split_ifs with h1
    · have hY0 := hYmem (lft s) (rgt s)
      rw [if_neg] at hY0
      · rw [Submodule.mem_bot] at hY0
        rw [hY0, smul_zero]
      · intro h3
        apply hs
        show (((s ∩ Q).card : ℕ) : ℤ) = m - 1
        rw [hQs s]
        exact h3
    · rfl
  · funext t
    obtain ⟨b, L, rfl⟩ : ∃ b L, t = uni b L := ⟨lft t, rgt t, (hU2 t).symm⟩
    refine Eq.trans (b := (-1 : ℤ) ^ b.card • wd (fun l => w (inrE l)) (fun L' => y (uni b L')) L) ?_ ?_
    · convert hdec y b L
    have hb2 := hU β κ E w c b
    have hfun : (fun L' => y (uni b L')) =
        if (((b.card : ℕ) : ℤ) = n - m) then (-1 : ℤ) ^ b.card • Y b else 0 := by
      funext L'
      rw [hy, (hb2 L').2.1, (hb2 L').2.2.1]
      split_ifs <;> rfl
    rw [hfun]
    by_cases hb : (((b.card : ℕ) : ℤ) = n - m)
    · rw [if_pos hb, map_zsmul, Pi.smul_apply, hYD, smul_smul, ← mul_pow]
      simp
    · rw [if_neg hb, map_zero, Pi.zero_apply, smul_zero]
      symm
      by_cases hL : ((L.card : ℕ) : ℤ) = m
      · have h5 := hmem (uni b L)
        rw [if_neg] at h5
        · exact (Submodule.mem_bot _).1 h5
        · intro hn
          apply hb
          rw [(hb2 L).2.2.2.1] at hn
          push_cast at hn
          omega
      · apply hlev
        show ¬ ((((uni b L ∩ Q).card : ℕ) : ℤ) = m)
        rwa [show (uni b L ∩ Q).card = L.card by convert hQc b L]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.WdApply
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

namespace UpperTheory.Gal.productCup_of_system

private def ctrH {κ E : Type} [LinearOrder κ] [AddCommGroup E] (l : κ) (c : Finset κ → E) : Finset κ → E := fun L =>
  if l ∈ L then 0 else GlobalTheory.cubeSign (insert l L) l • c (insert l L)

private theorem wd_apply' {κ E : Type} [LinearOrder κ] [AddCommGroup E] [Module ℂ E] (w : κ → Module.End ℂ E)
    (c : Finset κ → E) (t : Finset κ) : wd w c t = ∑ i ∈ t, GlobalTheory.cubeSign t i • w i (c (t.erase i)) := by
  simp [wd, LinearMap.sum_apply]

private theorem wd_ctrH {κ E : Type} [LinearOrder κ] [AddCommGroup E] [Module ℂ E] (w : κ → Module.End ℂ E)
    (l : κ) (c : Finset κ → E) (t : Finset κ) :
    wd w (ctrH l c) t + ctrH l (wd w c) t = w l (c t) := by
  by_cases hi : l ∈ t
  · have h0 : ctrH l (wd w c) t = 0 := if_pos hi
    rw [h0, add_zero, wd_apply', Finset.sum_eq_single l]
    · have h1 : ctrH l c (t.erase l) = GlobalTheory.cubeSign t l • c t := by
        simp only [ctrH]
        rw [if_neg (by simp), Finset.insert_erase hi]
      rw [h1, map_zsmul, smul_smul, GlobalTheory.cubeSign_mul_self, one_smul]
    · intro j _ hji
      have h1 : ctrH l c (t.erase j) = 0 := if_pos (Finset.mem_erase.2 ⟨Ne.symm hji, hi⟩)
      rw [h1, map_zero, smul_zero]
    · intro h; exact absurd hi h
  · have h0 : ctrH l (wd w c) t = GlobalTheory.cubeSign (insert l t) l • wd w c (insert l t) := if_neg hi
    rw [h0, wd_apply' w c (insert l t), Finset.sum_insert hi, Finset.erase_insert hi, smul_add, smul_smul,
      GlobalTheory.cubeSign_mul_self, one_smul, Finset.smul_sum, wd_apply']
    have key : ∀ j ∈ t, GlobalTheory.cubeSign t j • w j (ctrH l c (t.erase j)) +
        GlobalTheory.cubeSign (insert l t) l • GlobalTheory.cubeSign (insert l t) j • w j (c ((insert l t).erase j)) = 0 := by
      intro j hj
      have hij : l ≠ j := fun h => hi (h ▸ hj)
      have h2 : ctrH l c (t.erase j) =
          GlobalTheory.cubeSign (insert l (t.erase j)) l • c (insert l (t.erase j)) :=
        if_neg (fun h => hi (Finset.mem_of_mem_erase h))
      rw [h2, map_zsmul, ← Finset.erase_insert_of_ne hij, smul_smul, smul_smul, ← add_smul]
      have h1 := GlobalTheory.cubeSign_mul_erase (t := insert l t) (i := l) (j := j) (Finset.mem_insert_self _ _)
        (Finset.mem_insert_of_mem hj) hij
      rw [Finset.erase_insert hi] at h1
      have ha := GlobalTheory.cubeSign_mul_self (insert l t) l
      have he := GlobalTheory.cubeSign_mul_self ((insert l t).erase j) l
      have : GlobalTheory.cubeSign t j * GlobalTheory.cubeSign ((insert l t).erase j) l +
          GlobalTheory.cubeSign (insert l t) l * GlobalTheory.cubeSign (insert l t) j = 0 := by
        linear_combination (GlobalTheory.cubeSign (insert l t) l * GlobalTheory.cubeSign ((insert l t).erase j) l) * h1
          - (GlobalTheory.cubeSign t j * GlobalTheory.cubeSign ((insert l t).erase j) l) * ha
          - (GlobalTheory.cubeSign (insert l t) l * GlobalTheory.cubeSign (insert l t) j) * he
      rw [this, zero_smul]
    rw [add_left_comm, ← Finset.sum_add_distrib, Finset.sum_eq_zero key, add_zero]

end UpperTheory.Gal.productCup_of_system

theorem UpperTheory.Gal.productCup_of_system.htpy_of :
    Htpy := by
  intro S E _ _ _ _ act κ _ _ R M r hS n c hc g hg
  obtain ⟨a, ha, rfl⟩ := hg
  obtain ⟨hcC, hcD⟩ := Submodule.mem_inf.1 hc
  have hD : wd (fun l => act (r l)) c = 0 := hcD
  have hcC' : c ∈ Submodule.pi Set.univ (fun s : Finset κ => if (s.card : ℤ) = n then M else ⊥) := hcC
  have hmem : ∀ s : Finset κ, c s ∈ (if (s.card : ℤ) = n then M else ⊥ : Submodule ℂ E) :=
    fun s => (Submodule.mem_pi.1 hcC') s (Set.mem_univ _)
  have hcomm : ∀ (p q : S) (x : E), act p (act q x) = act q (act p x) := by
    intro p q x
    rw [← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply]
  have hstep : ∀ l t, wd (fun l => act (r l)) (ctrH l c) t = act (r l) (c t) := by
    intro l t
    have := wd_ctrH (fun l => act (r l)) l c t
    rw [hD] at this
    have h0 : ctrH l (0 : Finset κ → E) t = 0 := by
      simp [ctrH]
    rw [h0, add_zero] at this
    exact this
  refine Submodule.mem_map.2 ⟨fun L => ∑ l, act (a l) (ctrH l c L), ?_, ?_⟩
  · have : (fun L => ∑ l, act (a l) (ctrH l c L)) ∈
        Submodule.pi Set.univ (fun s : Finset κ => if (s.card : ℤ) = n - 1 then M else ⊥) := by
      refine Submodule.mem_pi.2 fun s _ => ?_
      by_cases hs : (s.card : ℤ) = n - 1
      · rw [if_pos hs]
        refine Submodule.sum_mem _ fun l _ => hS _ (ha l) _ ?_
        by_cases hl : l ∈ s
        · have : ctrH l c s = 0 := if_pos hl
          rw [this]; exact M.zero_mem
        · have h1 : ctrH l c s = GlobalTheory.cubeSign (insert l s) l • c (insert l s) := if_neg hl
          rw [h1]
          have h2 := hmem (insert l s)
          rw [if_pos (by rw [Finset.card_insert_of_notMem hl]; push_cast; omega)] at h2
          exact zsmul_mem h2 _
      · rw [if_neg hs]
        refine (Submodule.mem_bot _).2 (Finset.sum_eq_zero fun l _ => ?_)
        by_cases hl : l ∈ s
        · have : ctrH l c s = 0 := if_pos hl
          rw [this, map_zero]
        · have h1 : ctrH l c s = GlobalTheory.cubeSign (insert l s) l • c (insert l s) := if_neg hl
          have h2 := hmem (insert l s)
          rw [if_neg (by rw [Finset.card_insert_of_notMem hl]; push_cast; omega),
            Submodule.mem_bot] at h2
          rw [h1, h2, smul_zero, map_zero]
    exact this
  · show wd (fun l => act (r l)) _ = _
    funext t
    rw [wd_apply']
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, Finset.smul_sum]
    rw [Finset.sum_comm]
    have : ∀ l, ∑ i ∈ t, GlobalTheory.cubeSign t i • act (r i) (act (a l) (ctrH l c (t.erase i))) =
        act (a l) (act (r l) (c t)) := by
      intro l
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hstep l t, wd_apply', map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_zsmul, hcomm]
    rw [Finset.sum_congr rfl fun l _ => this l, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, Module.End.mul_apply]
end

open GlobalTheory.WH GlobalTheory.PD GlobalTheory.W1 GlobalTheory.CechDR KaehlerDifferential
open scoped TensorProduct

private theorem field0 : UpperTheory.Gal.productCup_of_system.Field0 := by
  have hZFam : UpperTheory.Gal.productCup_of_system.ZFam := UpperTheory.Gal.productCup_of_system.zFam_of
  have hLatOm : UpperTheory.Gal.productCup_of_system.LatOm := UpperTheory.Gal.productCup_of_system.latOm_of
  have hLatA : UpperTheory.Gal.productCup_of_system.LatA := UpperTheory.Gal.productCup_of_system.latA_of
  have hDualForm : UpperTheory.Gal.productCup_of_system.DualForm := UpperTheory.Gal.productCup_of_system.dualForm_of
  have hIdJ : UpperTheory.Gal.productCup_of_system.IdJ := UpperTheory.Gal.productCup_of_system.idJ_of hLatOm hLatA hDualForm
  have hActsLin : UpperTheory.Gal.productCup_of_system.ActsLin := UpperTheory.Gal.productCup_of_system.actsLin_of
  have hGoodZ : UpperTheory.Gal.productCup_of_system.GoodZ := UpperTheory.Gal.productCup_of_system.goodZ_of
  have hIdIJ : UpperTheory.Gal.productCup_of_system.IdIJ := UpperTheory.Gal.productCup_of_system.idIJ_of hIdJ hActsLin hGoodZ
  have hReg0 : UpperTheory.Gal.productCup_of_system.Reg0 := UpperTheory.Gal.productCup_of_system.deRhamRegulator_trivial_case
  have hKer0 : UpperTheory.Gal.productCup_of_system.Ker0 := UpperTheory.Gal.productCup_of_system.kernelZero_holds
  have hRegLat : UpperTheory.Gal.productCup_of_system.RegLat := UpperTheory.Gal.productCup_of_system.regLat_of hReg0 hKer0
  have hHtpy : UpperTheory.Gal.productCup_of_system.Htpy := UpperTheory.Gal.productCup_of_system.htpy_of
  have hK1Mod : UpperTheory.Gal.productCup_of_system.KoszulExactBelowLengthOfWeaklyRegular := UpperTheory.Gal.productCup_of_system.koszulExactBelowLengthOfWeaklyRegular_of_htpy hHtpy
  have hK1 : UpperTheory.Gal.productCup_of_system.K1 := UpperTheory.Gal.productCup_of_system.firstCohomologyBound_of_boundaryBound hK1Mod
  have hRS : UpperTheory.Gal.productCup_of_system.RS := UpperTheory.Gal.productCup_of_system.rS_of
  have hLocD : UpperTheory.Gal.productCup_of_system.LocD := UpperTheory.Gal.productCup_of_system.locD_of hRS hHtpy
  have hColZ : UpperTheory.Gal.productCup_of_system.ColZ := UpperTheory.Gal.productCup_of_system.colZ_of hRegLat hLatOm hDualForm hK1 hLocD hGoodZ
  have hWdBasic : UpperTheory.Gal.productCup_of_system.WdBasic := UpperTheory.Gal.productCup_of_system.wdBasic_of
  have hGL2 : UpperTheory.Gal.productCup_of_system.FiltrationCocycleLiftCriterion := UpperTheory.Gal.productCup_of_system.filtrationCocycleLiftCriterion_of_wdBasic hWdBasic
  have hSubQEx : UpperTheory.Gal.productCup_of_system.SubQEx := UpperTheory.Gal.productCup_of_system.subQEx_of hRS hWdBasic
  have hK2Ex : UpperTheory.Gal.productCup_of_system.KoszulCocycleExistsWithPrescribedComponent := UpperTheory.Gal.productCup_of_system.koszulTwoExact_of_gl2 hGL2 hSubQEx
  have hGL1 : UpperTheory.Gal.productCup_of_system.FiltrationBoundaryCriterion := UpperTheory.Gal.productCup_of_system.filtrationBoundaryCriterion_of_wdBasic hWdBasic
  have hK2Inj : UpperTheory.Gal.productCup_of_system.KoszulBoundaryOfComponentMemIdeal := UpperTheory.Gal.productCup_of_system.koszulTwoInjective_of_gl1 hGL1 hSubQEx
  have hKSub : UpperTheory.Gal.productCup_of_system.KSub := UpperTheory.Gal.productCup_of_system.kSub_of hGL1 hSubQEx
  have hDet : UpperTheory.Gal.productCup_of_system.Det := UpperTheory.Gal.productCup_of_system.det_of
  have hThMu : UpperTheory.Gal.productCup_of_system.ThMu := UpperTheory.Gal.productCup_of_system.thMu_of hDet
  have hThMuLat : UpperTheory.Gal.productCup_of_system.ThMuLat := UpperTheory.Gal.productCup_of_system.thMuLat_of
  have hMuSpan : UpperTheory.Gal.productCup_of_system.MuSpan := UpperTheory.Gal.productCup_of_system.muSpan_of
  have hWdUni : UpperTheory.Gal.productCup_of_system.WdUni := UpperTheory.Gal.productCup_of_system.wdUni_of
  have hKapInd : UpperTheory.Gal.productCup_of_system.KapInd := UpperTheory.Gal.productCup_of_system.kapInd_of hThMu hWdUni
  have hSysOk : UpperTheory.Gal.productCup_of_system.SysOk := UpperTheory.Gal.productCup_of_system.sysOk_of hWdUni
  have hZCol : UpperTheory.Gal.productCup_of_system.ZCol := UpperTheory.Gal.productCup_of_system.zCol_of hIdIJ hColZ hK2Ex hK2Inj hKSub hRS hThMu hThMuLat hMuSpan hKapInd hActsLin hSysOk hGoodZ hWdBasic hWdUni
  have hColQEx : UpperTheory.Gal.productCup_of_system.ColQEx := UpperTheory.Gal.productCup_of_system.colQEx_of hWdUni
  have hL2 : UpperTheory.Gal.productCup_of_system.L2 := UpperTheory.Gal.productCup_of_system.localTwo_of_gl2 hGL2 hColQEx hWdUni
  have hSysL2 : UpperTheory.Gal.productCup_of_system.CechKoszulSystemCocycleGluing := UpperTheory.Gal.productCup_of_system.coordinateSystem_degree_two_of_universalDerivation hL2 hSysOk hWdUni
  have hZEx : UpperTheory.Gal.productCup_of_system.ZEx := UpperTheory.Gal.productCup_of_system.zEx_of hZCol hColZ hSysL2 hK2Inj hKSub hRS hActsLin hSysOk hGoodZ hThMuLat
  have hRCup : UpperTheory.Gal.productCup_of_system.RCup := UpperTheory.Gal.productCup_of_system.rCup_of hWdUni
  have hSysBasic : UpperTheory.Gal.productCup_of_system.SysBasic := UpperTheory.Gal.productCup_of_system.sysBasic_of hWdUni hWdBasic
  have hPCup : UpperTheory.Gal.productCup_of_system.PCup := UpperTheory.Gal.productCup_of_system.pCup_of hRCup hSysBasic hSysOk hActsLin hGoodZ
  have hMJ : UpperTheory.Gal.productCup_of_system.MJ := UpperTheory.Gal.productCup_of_system.mJ_of hWdUni
  have hPTheta : UpperTheory.Gal.productCup_of_system.PTheta := UpperTheory.Gal.productCup_of_system.pTheta_of hMJ hThMu hThMuLat hKapInd hLatA hActsLin hGoodZ hSysBasic hSysOk
  have hPLift : UpperTheory.Gal.productCup_of_system.PLift := UpperTheory.Gal.productCup_of_system.pLift_of hThMu hThMuLat hKapInd hActsLin hLatA hGoodZ hSysOk hWdUni
  have hColP : UpperTheory.Gal.productCup_of_system.ColP := UpperTheory.Gal.productCup_of_system.colP_of hRegLat hLatOm hLatA hK1 hLocD hGoodZ
  have hL1 : UpperTheory.Gal.productCup_of_system.L1 := UpperTheory.Gal.productCup_of_system.localOne_of_gl1 hGL1 hColQEx hWdUni
  have hSysL1 : UpperTheory.Gal.productCup_of_system.CechKoszulSystemBoundaryCriterion := UpperTheory.Gal.productCup_of_system.coordinateSystem_degree_one_of_universalDerivation hL1 hSysOk hWdUni
  have hPCmp : UpperTheory.Gal.productCup_of_system.PCmp := UpperTheory.Gal.productCup_of_system.pCmp_of hPLift hColP hSysL1 hSysBasic hSysOk hK2Inj hKSub hRS hGoodZ hThMuLat hMuSpan hActsLin hWdUni
  have hPInt : UpperTheory.Gal.productCup_of_system.PInt := UpperTheory.Gal.productCup_of_system.pInt_of hWdUni hGoodZ
  have hEdgeRel : UpperTheory.Gal.productCup_of_system.EdgeRel := UpperTheory.Gal.productCup_of_system.edgeRel_of hWdUni
  have hZAct : UpperTheory.Gal.productCup_of_system.ZAct := UpperTheory.Gal.productCup_of_system.zAct_of hPCup hPTheta hPCmp hPInt hEdgeRel hSysBasic hGoodZ
  have hRCupTop : UpperTheory.Gal.productCup_of_system.RCupTop := UpperTheory.Gal.productCup_of_system.rCupTop_of hWdUni hGoodZ
  have hKunDec : UpperTheory.Gal.productCup_of_system.KunDec := UpperTheory.Gal.productCup_of_system.kunDec_of hWdUni
  have hZId : UpperTheory.Gal.productCup_of_system.ZId := UpperTheory.Gal.productCup_of_system.zId_of hZAct hRCupTop hKunDec hSysBasic hGoodZ
  have hPrB : UpperTheory.Gal.productCup_of_system.PrB := UpperTheory.Gal.productCup_of_system.prB_of hGoodZ
  have hValBasic : UpperTheory.Gal.productCup_of_system.ValBasic := UpperTheory.Gal.productCup_of_system.valBasic_of
  have hLocMax : UpperTheory.Gal.productCup_of_system.LocMax := UpperTheory.Gal.productCup_of_system.locMax_of hValBasic
  have hLocOne : UpperTheory.Gal.productCup_of_system.LocOne := UpperTheory.Gal.productCup_of_system.locOne_of hLocMax hValBasic
  have hLocForms : UpperTheory.Gal.productCup_of_system.LocForms := UpperTheory.Gal.productCup_of_system.locForms_of hLocOne
  have hDtBasic : UpperTheory.Gal.productCup_of_system.DtBasic := UpperTheory.Gal.productCup_of_system.dtBasic_of
  have hCRT : UpperTheory.Gal.productCup_of_system.CRT := UpperTheory.Gal.productCup_of_system.cRT_of
  have hRT1 : UpperTheory.Gal.productCup_of_system.ResidueOfTraceIsFiberSum := UpperTheory.Gal.productCup_of_system.deRham_restriction_trace_degree_one
  have hResVal : UpperTheory.Gal.productCup_of_system.ResVal := UpperTheory.Gal.productCup_of_system.resVal_of hValBasic
  have hTrVal : UpperTheory.Gal.productCup_of_system.TrVal := UpperTheory.Gal.productCup_of_system.trVal_of hRT1 hResVal hCRT hValBasic
  have hOmLoc : UpperTheory.Gal.productCup_of_system.OmLoc := UpperTheory.Gal.productCup_of_system.omLoc_of
  have hIdVal : UpperTheory.Gal.productCup_of_system.IdVal := UpperTheory.Gal.productCup_of_system.idVal_of hLocForms hDtBasic hCRT hTrVal hResVal hLatA hValBasic hOmLoc
  have hRedK : UpperTheory.Gal.productCup_of_system.RedK := UpperTheory.Gal.productCup_of_system.redK_of
  have hRYBasic : UpperTheory.Gal.productCup_of_system.RYBasic := UpperTheory.Gal.productCup_of_system.rYBasic_of
  have hFixZ : UpperTheory.Gal.productCup_of_system.FixZ := UpperTheory.Gal.productCup_of_system.fixZ_of hValBasic hRYBasic
  have hDtPull : UpperTheory.Gal.productCup_of_system.DtPull := UpperTheory.Gal.productCup_of_system.dtPull_of hLocOne hValBasic
  have hMinorSum : UpperTheory.Gal.productCup_of_system.MinorSum := UpperTheory.Gal.productCup_of_system.minorSum_of
  have hValG : UpperTheory.Gal.productCup_of_system.ValG := UpperTheory.Gal.productCup_of_system.valG_of hIdVal hRedK hFixZ hDtPull hMinorSum hDtBasic hValBasic
  have hLG : UpperTheory.Gal.productCup_of_system.LG := UpperTheory.Gal.productCup_of_system.lG_of
  have hRYFT : UpperTheory.Gal.productCup_of_system.RYFT := UpperTheory.Gal.productCup_of_system.rYFT_of
  have hLocReg : UpperTheory.Gal.productCup_of_system.LocReg := UpperTheory.Gal.productCup_of_system.locReg_of hLocForms hDtBasic hValBasic
  have hYKE : UpperTheory.Gal.productCup_of_system.YKE := UpperTheory.Gal.productCup_of_system.yKE_of hLG hOmLoc hRYFT hHtpy hK1 hLocReg hValBasic hRYBasic
  have hLocEq : UpperTheory.Gal.productCup_of_system.LocEq := UpperTheory.Gal.productCup_of_system.locEq_of hValBasic hRYBasic
  have hPtT : UpperTheory.Gal.productCup_of_system.PtT := UpperTheory.Gal.productCup_of_system.ptT_of hLocEq hValBasic hRYBasic
  have hPtG : UpperTheory.Gal.productCup_of_system.PtG := UpperTheory.Gal.productCup_of_system.ptG_of hLocEq hValBasic hRYBasic hPtT
  have hFixLoc : UpperTheory.Gal.productCup_of_system.FixLoc := UpperTheory.Gal.productCup_of_system.fixLoc_of hValBasic
  have hGMap : UpperTheory.Gal.productCup_of_system.GMap := UpperTheory.Gal.productCup_of_system.gMap_of hRYBasic hWdUni
  have hYCols : UpperTheory.Gal.productCup_of_system.YCols := UpperTheory.Gal.productCup_of_system.yCols_of hYKE hPtG hPtT hFixLoc hGMap hThMuLat hSysOk hRS hRYBasic
  have hYBig : UpperTheory.Gal.productCup_of_system.YBig := UpperTheory.Gal.productCup_of_system.yBig_of hYCols hYKE hK2Ex hSysL2 hSysOk hRS hPtT hLocMax hFixZ hGMap hDtBasic hValBasic hRYBasic hOmLoc
  have hThT : UpperTheory.Gal.productCup_of_system.ThT := UpperTheory.Gal.productCup_of_system.thT_of hDet
  have hYXi : UpperTheory.Gal.productCup_of_system.YXi := UpperTheory.Gal.productCup_of_system.yXi_of hMJ hThT hDtBasic hSysBasic hRYBasic hOmLoc
  have hYCmpT : UpperTheory.Gal.productCup_of_system.YCmpT := UpperTheory.Gal.productCup_of_system.yCmpT_of hYXi hYCols hYKE hPtT hSysL1 hSysBasic hSysOk hK2Inj hRS hLocMax hFixZ hValBasic hRYBasic hDtBasic hOmLoc
  have hK3 : UpperTheory.Gal.productCup_of_system.K3 := UpperTheory.Gal.productCup_of_system.koszulThree_of_det hDet hK2Inj hKSub hWdBasic
  have hYCmpG : UpperTheory.Gal.productCup_of_system.YCmpG := UpperTheory.Gal.productCup_of_system.yCmpG_of hYCols hYKE hPtG hFixLoc hK1 hK2Inj hK3 hLocReg hLocMax hLocForms hSysL1 hSysBasic hSysOk hRS hValBasic hRYBasic hOmLoc hWdUni
  have hYMain : UpperTheory.Gal.productCup_of_system.YMain := UpperTheory.Gal.productCup_of_system.yMain_of hValG hYBig hYCmpT hYCmpG hGMap hCRT hThMu hKapInd hActsLin hDtBasic hSysBasic hRYBasic hOmLoc hWdUni
  have hLCupRel : UpperTheory.Gal.productCup_of_system.LCupRel := UpperTheory.Gal.productCup_of_system.lCupRel_of hWdUni
  have hEdgeInj : UpperTheory.Gal.productCup_of_system.EdgeInj := UpperTheory.Gal.productCup_of_system.edgeInj_of hWdUni
  have hRowEx : UpperTheory.Gal.productCup_of_system.RowEx := UpperTheory.Gal.productCup_of_system.rowEx_of hLG hOmLoc hRYBasic hRYFT hValBasic hWdBasic
  have hEdgeB : UpperTheory.Gal.productCup_of_system.EdgeB := UpperTheory.Gal.productCup_of_system.edgeB_of hEdgeInj hRowEx hL1 hRYBasic hWdUni hWdBasic
  have hTrTop : UpperTheory.Gal.productCup_of_system.TrTop := UpperTheory.Gal.productCup_of_system.trTop_of
  have hTrLin : UpperTheory.Gal.productCup_of_system.TrLin := UpperTheory.Gal.productCup_of_system.trLin_of
  have hFieldLe : UpperTheory.Gal.productCup_of_system.FieldLe := UpperTheory.Gal.productCup_of_system.fieldLe_of hZFam hZEx hZId hPrB hYMain hGMap hLCupRel hEdgeB hTrTop hRT1 hTrLin hSysBasic hRYBasic hOmLoc
  have hField0 : UpperTheory.Gal.productCup_of_system.Field0 := UpperTheory.Gal.productCup_of_system.field0_of hFieldLe hValBasic
  exact hField0

theorem UpperTheory.Cb.exists_chart_lift_of_finite_cover :
    ∀ (d a : ℕ) (F K K' : Type) [Field F] [Field K] [Field K'] [Algebra ℂ F] [Algebra ℂ K] [Algebra ℂ K'] [Algebra F K] [IsScalarTower ℂ F K] [Algebra K K'] [IsScalarTower ℂ K K'] [Algebra F K'] [IsScalarTower F K K'] [IsScalarTower ℂ F K'] (x : Fin (d + 1) → F) (j2 : K →ₐ[ℂ] K'),
      IsFinCover ℂ K x → IsFinCover ℂ K' x →
      (∀ (i : Fin (d + 1)) (e : rB ℂ K' x {i} →ₐ[ℂ] ℂ), ∃ j : Fin (d + 1), ∀ v ∈ R2 x j2 {j}, ∃ (b : K') (hb : b ∈ rB ℂ K' x {i}), e ⟨b, hb⟩ ≠ 0 ∧ b * v ∈ rB ℂ K' x {i}) →
      IsReduced ((rB ℂ K' x {0}) ⧸ (Ideal.span (Set.range fun j : Fin d => (⟨_, tco_mem ℂ K' x j⟩ : rB ℂ K' x {0})))) →
      (∀ (i : Fin (d + 1)), i ≠ 0 → ∀ e : rB ℂ K' x {i} →ₐ[ℂ] ℂ, ¬ IsFix (rB ℂ K' x {i}) e j2 (rB ℂ K x {i})) →
      (∀ e : rB ℂ K' x {0} →ₐ[ℂ] ℂ, IsFix (rB ℂ K' x {0}) e j2 (rB ℂ K x {0}) → ∀ j : Fin d, e ⟨_, tco_mem ℂ K' x j⟩ = 0) →
      ∀ (Fx : Finset (fib ℂ K' x)), (∀ e : fib ℂ K' x, e ∈ Fx ↔ IsFix (rB ℂ K' x {0}) e.1 j2 (rB ℂ K x {0})) →
      (∀ e ∈ Fx, ∀ (b : K) (hb1 : algebraMap K K' b ∈ rB ℂ K' x {0}), b ∈ rB ℂ K x {0} → e.1 ⟨_, hb1⟩ = 0 →
        ∃ (c : K) (hc1 : algebraMap K K' c ∈ rB ℂ K' x {0}), c ∈ rB ℂ K x {0} ∧ e.1 ⟨_, hc1⟩ ≠ 0 ∧
          ∃ g : Fin d → K, (∀ l, g l ∈ rB ℂ K x {0}) ∧ c * b = ∑ l, g l * algebraMap F K (x l.succ / x 0)) →
      ∀ A : fib ℂ K' x → Matrix (Fin d) (Fin d) ℂ,
      (∀ e ∈ Fx, ∀ m : Fin d, ∃ (c : K') (hc : c ∈ rB ℂ K' x {0}) (g : Fin d → K') (hg : ∀ l, g l ∈ rB ℂ K' x {0}), e.1 ⟨c, hc⟩ ≠ 0 ∧
        c * j2 (algebraMap F K (x m.succ / x 0)) = ∑ l, g l * algebraMap F K' (x l.succ / x 0) ∧ ∀ l, e.1 ⟨g l, hg l⟩ = e.1 ⟨c, hc⟩ * A e m l) →
      (∀ e ∈ Fx, (1 - A e).det ≠ 0) →
      ∀ u : ∀ p : ℕ, (cech fun I => omB ℂ K (rB ℂ K x I) a).H p →ₗ[ℂ] (cech fun I => omB ℂ K (rB ℂ K x I) a).H p,
      (∀ (p : ℕ) (b : Finset (Fin (d + 1)) → DR ℂ K) (hb : b ∈ (cech fun I => omB ℂ K (rB ℂ K x I) a).Z p),
        ∃ bt ∈ (cech fun s : Finset (Fin (d + 1) ⊕ₗ Fin (d + 1)) => omB ℂ K' (RY x j2 (lft s) (rgt s)) a).Z p,
          (∀ J, bt (uni ∅ J) = pr2L j2 (b J)) ∧
          ∃ h : trC (k := ℂ) (K := K) (L := K') (fun I => bt (uni I ∅)) ∈ (cech fun I => omB ℂ K (rB ℂ K x I) a).Z p,
            u p (Submodule.Quotient.mk ⟨b, hb⟩) = Submodule.Quotient.mk ⟨_, h⟩) →
      (∀ p : ℕ, FiniteDimensional ℂ ((cech fun I => omB ℂ K (rB ℂ K x I) a).H p)) →
      ∑ p ∈ Finset.range (d + 1), (-1 : ℂ) ^ p * LinearMap.trace ℂ _ (u p) =
        ∑ e ∈ Fx, (Matrix.det (1 + (Polynomial.X : Polynomial ℂ) • (A e).map Polynomial.C)).coeff a / (1 - A e).det :=
  field0
