module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAntiJFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitarySatakeWeylInvariant

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeylConjugateOfUnitarySatakeDiagDoubleCosets
noncomputable section

namespace GlobalTheory.LFun.Orbit

open GlobalTheory.InertThetaCompare (mono mono_injective)
open GlobalTheory.LGrp (WeylConjU)

variable {m : ℕ}

abbrev Sgn (m : ℕ) : Type := Equiv.Perm (Fin m) × (Fin m → ℤˣ)

def act (w : Sgn m) (γ : Fin m → ℂˣ) : Fin m → ℂˣ := fun i => γ (w.1 i) ^ (w.2 i : ℤ)

def coact (w : Sgn m) (a : Fin m → ℤ) : Fin m → ℤ := fun j => w.2 (w.1.symm j) * a (w.1.symm j)

def Dom (a : Fin m → ℤ) : Prop := Antitone a ∧ ∀ i, 0 ≤ a i

theorem weylConj_act (w : Sgn m) (γ : Fin m → ℂˣ) : WeylConjU γ (act w γ) :=
  ⟨w.1, fun i => by rcases Int.units_eq_one_or (w.2 i) with h | h <;> simp [act, h]⟩

theorem mono_act (w : Sgn m) (a : Fin m → ℤ) (γ : Fin m → ℂˣ) : mono a (act w γ) = mono (coact w a) γ := by
  change ∏ i, ((act w γ i : ℂˣ) : ℂ) ^ a i = ∏ i, (γ i : ℂ) ^ coact w a i
  rw [← Equiv.prod_comp w.1 fun i => (γ i : ℂ) ^ coact w a i]
  simp [act, coact, zpow_mul]

theorem coact_injective (w : Sgn m) : Function.Injective (coact w) := fun a b h => funext fun i => by
  simpa [coact] using congrFun h (w.1 i)

theorem exists_dom (a : Fin m → ℤ) : ∃ w : Sgn m, Dom (coact w a) := by
  let π := Tuple.sort fun i => -|a i|
  have hπ := Tuple.monotone_sort fun i => -|a i|
  have e : coact (π.symm, fun i => if 0 ≤ a i then 1 else -1) a = fun j => |a (π j)| := by
    funext j
    simp only [coact, Equiv.symm_symm]
    split_ifs with h
    · simp [abs_of_nonneg h]
    · simp [abs_of_neg (not_le.1 h)]
  refine ⟨(π.symm, fun i => if 0 ≤ a i then 1 else -1), ?_⟩
  rw [e]
  exact ⟨fun i j hij => neg_le_neg_iff.1 (hπ hij), fun i => abs_nonneg _⟩

def sym (a : Fin m → ℤ) (γ : Fin m → ℂˣ) : ℂ := ∑ w : Sgn m, mono a (act w γ)

theorem sym_coact (w : Sgn m) (a : Fin m → ℤ) (γ : Fin m → ℂˣ) : sym (coact w a) γ = sym a γ := by
  let φ : Sgn m → Sgn m := fun u => (u.1 * w.1, fun i => u.2 (w.1 i) * w.2 i)
  have hφ : Function.Injective φ := fun u u' h => Prod.ext (mul_right_cancel (congrArg Prod.fst h))
    (funext fun i => by simpa [φ] using congrFun (congrArg Prod.snd h) (w.1.symm i))
  refine Fintype.sum_bijective φ (Finite.injective_iff_bijective.1 hφ) _ _ fun u => ?_
  rw [← mono_act]
  congr 1
  funext i
  simp [act, φ, zpow_mul]

def ev (c : (Fin m → ℤ) →₀ ℂ) (γ : Fin m → ℂˣ) : ℂ := ∑ a ∈ c.support, c a * mono a γ

theorem coeff_coact {c : (Fin m → ℤ) →₀ ℂ} {w : Sgn m} (h : ∀ γ, ev c (act w γ) = ev c γ) (a : Fin m → ℤ) :
    c (coact w a) = c a := by
  have hli := (linearIndependent_monoidHom (Fin m → ℂˣ) ℂ).comp _ mono_injective
  have e : c.mapDomain (coact w) = c := by
    refine hli (funext fun γ => ?_)
    rw [Finsupp.linearCombination_mapDomain]
    simpa [Finsupp.linearCombination_apply, Finsupp.sum, ev, mono_act] using h γ
  conv_lhs => rw [← e]
  exact Finsupp.mapDomain_apply_of_injective (coact_injective w) _ _

def chr (γ : Fin m → ℂˣ) : Multiplicative (Fin m → ℤ) →* ℂ where
  toFun a := mono a.toAdd γ
  map_one' := by simp [mono]
  map_mul' a b := by simp [mono, zpow_add₀, Finset.prod_mul_distrib]

theorem chr_injective : Function.Injective (chr (m := m)) := fun γ γ' h => funext fun i => by
  have e : ∀ δ : Fin m → ℂˣ, chr δ (Multiplicative.ofAdd (Pi.single i 1)) = δ i := fun δ => by
    change ∏ j : Fin m, _ = _
    rw [Finset.prod_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
    simp
  exact Units.ext (by rw [← e, ← e, h])

theorem weylConj_of_sym {α β : Fin m → ℂˣ} (h : ∀ a, sym a α = sym a β) : WeylConjU α β := by
  classical
  have hli := (linearIndependent_monoidHom (Multiplicative (Fin m → ℤ)) ℂ).comp _ chr_injective
  have e : ∑ w : Sgn m, Finsupp.single (act w α) (1 : ℂ) = ∑ w : Sgn m, Finsupp.single (act w β) (1 : ℂ) := by
    refine hli (funext fun a => ?_)
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [map_sum, sym] using (show ∑ w : Sgn m, chr (act w α) a = ∑ w : Sgn m, chr (act w β) a from h a.toAdd)
  by_contra hn
  have h1 := DFunLike.congr_fun e β
  rw [Finsupp.finsetSum_apply, Finsupp.finsetSum_apply, Finset.sum_eq_zero fun w _ =>
    Finsupp.single_eq_of_ne (a := act w α) (a' := β) fun h0 => hn (by rw [h0]; exact weylConj_act w α)] at h1
  simp only [Finsupp.single_apply, Finset.sum_boole, eq_comm (a := (0 : ℂ)), Nat.cast_eq_zero,
    Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h1
  exact h1 (Finset.mem_univ (1, 1)) (funext fun i => by simp [act])

theorem weylConj_of_triangular (H : (Fin m → ℤ) → ℕ) (c : (Fin m → ℤ) → (Fin m → ℤ) →₀ ℂ)
    (hinv : ∀ d, Dom d → ∀ w γ, ev (c d) (act w γ) = ev (c d) γ) (hself : ∀ d, Dom d → c d d ≠ 0)
    (htri : ∀ d a, Dom d → Dom a → c d a ≠ 0 → a = d ∨ H a < H d) {α β : Fin m → ℂˣ}
    (h : ∀ d, Dom d → ev (c d) α = ev (c d) β) : WeylConjU α β := by
  classical
  have h1 : ∀ d, Dom d → ∀ γ, ∑ a ∈ (c d).support, c d a * sym a γ = Fintype.card (Sgn m) * ev (c d) γ :=
    fun d hd γ => by
      simp only [sym, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact (Finset.sum_congr rfl fun w _ => hinv d hd w γ).trans (by simp)
  have h2 : ∀ d, Dom d → sym d α - sym d β = 0 := fun d => by
    induction hk : H d using Nat.strong_induction_on generalizing d with
    | _ k ih =>
      intro hd
      have h3 : ∑ a ∈ (c d).support, c d a * (sym a α - sym a β) = 0 := by
        simp only [mul_sub, Finset.sum_sub_distrib, h1 d hd, h d hd, sub_self]
      rw [← Finset.sum_filter_ne_zero, Finset.sum_congr rfl (g := fun _ => c d d * (sym d α - sym d β)),
        Finset.sum_const, smul_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h3
      · refine (mul_eq_zero.1 (h3.elim (fun h4 => ?_) id)).resolve_left (hself d hd)
        exact not_not.1 (h4 (Finsupp.mem_support_iff.2 (hself d hd)))
      · intro a ha
        obtain ⟨w, hw⟩ := exists_dom a
        have h5 := (Finset.mem_filter.1 ha).2
        rw [← coeff_coact (hinv d hd w), ← sym_coact w a, ← sym_coact w a] at h5 ⊢
        rcases htri d _ hd hw (left_ne_zero_of_mul h5) with e | e
        · rw [e]
        · exact absurd (ih _ (hk ▸ e) _ rfl hw) (right_ne_zero_of_mul h5)
  refine weylConj_of_sym fun a => ?_
  obtain ⟨w, hw⟩ := exists_dom a
  rw [← sym_coact w a, ← sym_coact w a]
  exact sub_eq_zero.1 (h2 _ hw)

open Formalism.UG GlobalTheory.InertThetaCompare
open GlobalTheory.LGrp (bcParam bcParam_of_weylConj)
open GlobalTheory.IndefiniteRowSideFullHecke.InertPlaceSetting (labInd)

section Local

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n q : ℕ} {ϖ ϖ' : L}

theorem antitone_tExp {d : Fin (n / 2) → ℤ} (hd : Dom d) : Antitone (tExp n (n / 2) d) := fun i j hij => by
  have h0 : (i : ℕ) ≤ j := hij
  have h1 := j.2
  unfold tExp
  split_ifs with a b c e f g k l
  · exact hd.1 h0
  · omega
  · omega
  · exact (neg_nonpos.2 (hd.2 _)).trans (hd.2 _)
  · exact neg_le_neg (hd.1 (show n - 1 - j ≤ n - 1 - i by omega))
  · exact neg_nonpos.2 (hd.2 _)
  · exact hd.2 _
  · omega
  · exact le_rfl

theorem tExp_rev (d : Fin (n / 2) → ℤ) (i : Fin n) : tExp n (n / 2) d i.rev = -tExp n (n / 2) d i := by
  have h1 := i.2
  have h2 : (i.rev : ℕ) = n - 1 - i := by rw [Fin.val_rev]; omega
  unfold tExp
  split_ifs with a b c e f g k l
  all_goals first | omega | (simp only [neg_neg, neg_inj]; congr 2; omega) | (simp only [h2, neg_neg])

theorem getD_ofFn (f : Fin n → ℤ) (i : Fin n) : (List.ofFn f).getD i 0 = f i := by
  simp [List.getD_eq_getElem?_getD]

def lab (n : ℕ) (d : Fin (n / 2) → ℤ) : List ℤ := List.ofFn (tExp n (n / 2) d)

theorem good_lab {d : Fin (n / 2) → ℤ} (hd : Dom d) : Good n (lab n d) := by
  refine ⟨List.length_ofFn, List.pairwise_ofFn.2 fun i j h => antitone_tExp hd h.le, ?_⟩
  refine eq_of_getD (n := n) (by simp [Formalism.IndefR.Mult.dualLab, lab]) List.length_ofFn fun i => ?_
  rw [lab, GlobalTheory.DualDivU.getD_dualLab _ List.length_ofFn, getD_ofFn, getD_ofFn, tExp_rev, neg_neg]

theorem getD_lab (d : Fin (n / 2) → ℤ) : (fun j : Fin (n / 2) => (lab n d).getD j.1 0) = d := by
  funext j
  refine (getD_ofFn _ (Fin.castLE (Nat.div_le_self n 2) j)).trans ?_
  simp [tExp]

theorem tail_nonpos {d : List ℤ} (h : Good n d) (k : Fin n) : ∑ i ∈ Finset.Ici k, d.getD i.1 0 ≤ 0 := by
  have := sum_Ici_le (anti_getD h.1 h.2.1) k ((Finset.Ici k).map Fin.revPerm.toEmbedding) (Finset.card_map _).symm
  rw [Finset.sum_map] at this
  simp only [Equiv.toEmbedding_apply, Fin.revPerm_apply, h.rev, Finset.sum_neg_distrib] at this
  omega

theorem labInd_eq_dosetInd {d : List ℤ} {t : GU σ n}
    (ht : t.1.1 = Matrix.diagonal fun i : Fin n => ϖ ^ d.getD i.1 0) : labInd σ n ϖ d = dosetInd ℂ (KU σ n) t := by
  unfold labInd dosetInd
  congr 1
  ext g
  rw [DoubleCoset.mem_doubleCoset, ← ht]
  refine exists_congr fun a => and_congr_right fun _ => exists_congr fun b => and_congr_right fun _ => ?_
  rw [Subtype.ext_iff, Units.ext_iff]
  rfl

variable [CompleteSpace L]

theorem unitarySatakeTransform_weylConjugate_invariant (hW : SatWeyl) (hU : IsUnramInv ϖ σ q) {h : GU σ n → ℂ} (hh : h ∈ Hecke ℂ (KU σ n))
    {α β : Fin (n / 2) → ℂˣ} (e : WeylConjU α β) :
    SatU ϖ q h (fun i => (α i : ℂ)) = SatU ϖ q h (fun i => (β i : ℂ)) := by
  have e1 := congrArg (Multiset.map fun z : ℂˣ => (z : ℂ)) (add_right_cancel (bcParam_of_weylConj e))
  refine GlobalTheory.eq_of_perm_inv_invariant_of_multiset_eq _ (SatU ϖ q h)
    (fun γ hγ => hW L ϖ σ q n (n / 2) hU (by omega) (by omega) γ hγ h hh) _ _ (fun i => (α i).ne_zero) ?_
  simpa [Multiset.map_map, Function.comp_def] using e1

theorem weylConjugate_of_unitarySatake_diagDoubleCosets (hW : SatWeyl) (hU : IsUnramInv ϖ σ q) {α β : Fin (n / 2) → ℂˣ}
    (h : ∀ (d : Fin n → ℤ) (t : GU σ n), Antitone d → t.1.1 = Matrix.diagonal (fun i => ϖ ^ d i) →
      SatU ϖ q (dosetInd ℂ (KU σ n) t) (fun i => (α i : ℂ)) = SatU ϖ q (dosetInd ℂ (KU σ n) t) fun i => (β i : ℂ)) :
    WeylConjU α β := by
  classical
  have hq : (q : ℂ) ≠ 0 := by
    have := hU.2.2.2.2.2.1
    exact_mod_cast (by omega : q ≠ 0)
  let x : (Fin (n / 2) → ℤ) → ℂ := fun a => ∏ i, (q : ℂ) ^ (-(a i) * ((n : ℤ) - 1 - 2 * (i.val : ℤ)))
  have hx : ∀ a, x a ≠ 0 := fun a => Finset.prod_ne_zero_iff.2 fun i _ => zpow_ne_zero _ hq
  have hex : ∀ d : Fin (n / 2) → ℤ, ∃ c : (Fin (n / 2) → ℤ) →₀ ℂ, Dom d →
      ∀ a, c a = x a * cnt σ n ϖ (lab n d) a := fun d => by
    by_cases hd : Dom d
    · exact ⟨Finsupp.ofSupportFinite (fun a => x a * cnt σ n ϖ (lab n d) a)
        ((finite_cnt hU (good_lab hd)).subset fun a ha h0 => ha (by simp [h0])), fun _ _ => rfl⟩
    · exact ⟨0, fun h => absurd h hd⟩
  choose c hc using hex
  have hev : ∀ d, Dom d → ∀ γ : Fin (n / 2) → ℂˣ,
      ev (c d) γ = SatU ϖ q (labInd σ n ϖ (lab n d)) fun i => (γ i : ℂ) := fun d hd γ => by
    rw [satU_labInd hU (good_lab hd), finsum_eq_sum_of_support_subset (s := (c d).support), ev]
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [hc d hd, Finset.prod_mul_distrib]
      change _ * ∏ i, (γ i : ℂ) ^ a i = _
      ring
    · intro a ha
      rw [Finset.mem_coe, Finsupp.mem_support_iff, hc d hd]
      exact mul_ne_zero (hx a) (right_ne_zero_of_mul ha)
  let T : (Fin (n / 2) → ℤ) → Fin n → ℤ := fun d k => ∑ i ∈ Finset.Ici k, (lab n d).getD i.1 0
  refine weylConj_of_triangular (fun d => (-∑ k, T d k).toNat) c (fun d hd w γ => ?_) (fun d hd => ?_)
    (fun d a hd ha h0 => ?_) fun d hd => ?_
  · obtain ⟨t, ht⟩ := exists_diag hU (good_lab hd)
    rw [hev d hd, hev d hd, labInd_eq_dosetInd ht]
    exact (unitarySatakeTransform_weylConjugate_invariant hW hU (Final.DosetIndMem _ _ _ _) (weylConj_act w γ)).symm
  · have := cnt_self hU (good_lab hd)
    rw [getD_lab] at this
    rw [hc d hd]
    exact mul_ne_zero (hx d) (by exact_mod_cast this)
  · rw [hc d hd] at h0
    have h1 : ∀ k, T d k ≤ T a k := tail_of_cnt hU (good_lab ha) (good_lab hd) (by
      rw [getD_lab]; exact_mod_cast right_ne_zero_of_mul h0)
    have h2 : ∑ k, T a k ≤ 0 := Finset.sum_nonpos fun k _ => tail_nonpos (good_lab ha) k
    rcases (Finset.sum_le_sum (s := Finset.univ) fun k _ => h1 k).eq_or_lt with e | e
    · have h3 := eq_of_tails fun k => (Finset.sum_eq_sum_iff_of_le fun k _ => h1 k).1 e k (Finset.mem_univ k)
      rw [← getD_lab a, ← getD_lab d, eq_of_getD (good_lab hd).1 (good_lab ha).1 (congrFun h3)]
      exact Or.inl rfl
    · exact Or.inr (by omega)
  · obtain ⟨t, ht⟩ := exists_diag hU (good_lab hd)
    rw [hev d hd, hev d hd, labInd_eq_dosetInd ht]
    exact h _ t (anti_getD (good_lab hd).1 (good_lab hd).2.1) ht

end Local

end GlobalTheory.LFun.Orbit

end
end

noncomputable section

namespace GlobalTheory.LFun

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun.Orbit
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (WeylConjU bcParam bcParam_of_weylConj)

section Local

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n q : ℕ} {ϖ ϖ' : L}

theorem exists_dosetInd_eq (hU : IsUnramInv ϖ σ q) (hU' : IsUnramInv ϖ' σ q) {d : Fin n → ℤ} {t : GU σ n}
    (ht : t.1.1 = Matrix.diagonal fun i => ϖ ^ d i) :
    ∃ t' : GU σ n, t'.1.1 = Matrix.diagonal (fun i => ϖ' ^ d i) ∧ dosetInd ℂ (KU σ n) t' = dosetInd ℂ (KU σ n) t := by
  have h0 := GlobalTheory.InertThetaCompare.unif_ne_zero hU
  have h0' := GlobalTheory.InertThetaCompare.unif_ne_zero hU'
  have hv : ∀ a : ℤ, Valued.v (ϖ ^ a) = WithZero.exp (-a) := fun a => by
    simpa using GlobalTheory.InertThetaCompare.val_prod_zpow (ϖ := ϖ) hU.2.2.2.1 (Finset.univ : Finset Unit) fun _ => a
  have hd : ∀ i, d i + d i.rev = 0 := fun i => by
    have h1 := P.fSatake_unit_diag (P.fSatake_borel_of_diag ht) i
    rw [ht, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, map_zpow₀, hU.2.2.1, ← zpow_add₀ h0] at h1
    have h2 := hv (d i + d i.rev)
    rw [h1, map_one, eq_comm, WithZero.exp_eq_one] at h2
    omega
  obtain ⟨k, hk, hk'⟩ := P.fSatake_diag_exists (σ := σ) (fun i : Fin n => (ϖ' / ϖ) ^ d i) fun i => by
    rw [map_zpow₀, map_div₀, hU.2.2.1, hU'.2.2.1, ← zpow_add₀ (div_ne_zero h0' h0), hd, zpow_zero]
  have hK : k ∈ KU σ n := P.fSatake_diag_mem_K hk hk' fun i => by
    rw [map_zpow₀, map_div₀, hU.2.2.2.1, hU'.2.2.2.1, div_self WithZero.coe_ne_zero, one_zpow]
  refine ⟨t * k, ?_, ?_⟩
  · rw [Subgroup.coe_mul, Units.val_mul, ht, hk, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rw [← mul_zpow, mul_div_cancel₀ _ h0]
  · rw [dosetInd, dosetInd, DoubleCoset.doubleCoset_eq_of_mem
      (DoubleCoset.mem_doubleCoset.2 ⟨1, one_mem _, k, hK, by rw [one_mul]⟩)]

variable [CompleteSpace L] {V : Type} [AddCommGroup V] [Module ℂ V] {α β : Fin (n / 2) → ℂˣ}

theorem satU_of_weylConj (hU : IsUnramInv ϖ σ q) {h : GU σ n → ℂ} (hh : h ∈ Hecke ℂ (KU σ n)) (e : WeylConjU α β) :
    SatU ϖ q h (fun i => (α i : ℂ)) = SatU ϖ q h (fun i => (β i : ℂ)) :=
  unitarySatakeTransform_weylConjugate_invariant GlobalTheory.T.unitarySatake_weylInvariant hU hh e

theorem weylConj_of_dosetInd (hU : IsUnramInv ϖ σ q)
    (h : ∀ (d : Fin n → ℤ) (t : GU σ n), Antitone d → t.1.1 = Matrix.diagonal (fun i => ϖ ^ d i) →
      SatU ϖ q (dosetInd ℂ (KU σ n) t) (fun i => (α i : ℂ)) = SatU ϖ q (dosetInd ℂ (KU σ n) t) fun i => (β i : ℂ)) :
    WeylConjU α β := weylConjugate_of_unitarySatake_diagDoubleCosets GlobalTheory.T.unitarySatake_weylInvariant hU h

theorem satU_eq_iff_weylConj (hU : IsUnramInv ϖ σ q) :
    (∀ h ∈ Hecke ℂ (KU σ n), SatU ϖ q h (fun i => (α i : ℂ)) = SatU ϖ q h fun i => (β i : ℂ)) ↔ WeylConjU α β :=
  ⟨fun h => weylConj_of_dosetInd hU fun _ _ _ _ => h _ (Final.DosetIndMem _ _ _ _),
    fun e _ hh => satU_of_weylConj hU hh e⟩

theorem bcParam_eq_of_satU_eq (hU : IsUnramInv ϖ σ q)
    (h : ∀ h ∈ Hecke ℂ (KU σ n), SatU ϖ q h (fun i => (α i : ℂ)) = SatU ϖ q h fun i => (β i : ℂ)) :
    bcParam n α = bcParam n β := bcParam_of_weylConj ((satU_eq_iff_weylConj hU).1 h)

variable {ρ : Representation ℂ (GU σ n) V} {x : V}

theorem IsSatVecU.unique (hU : IsUnramInv ϖ σ q) (h : IsSatVecU ϖ q ρ x α) (h' : IsSatVecU ϖ q ρ x β) :
    WeylConjU α β :=
  (satU_eq_iff_weylConj hU).1 fun t ht => smul_left_injective ℂ h.1 ((h.2.2 t ht).symm.trans (h'.2.2 t ht))

end Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

section Place

variable {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)}

theorem toCompl_surjective (h : w.under (𝓞 F) = v) : Function.Surjective (toCompl h) := fun y => by
  obtain ⟨a, ha⟩ := (finAdEquiv F E).surjective (Neutral.B1.finiteSingle E w y)
  refine ⟨_, (finAdEquiv_apply h a).symm.trans ?_⟩
  rw [ha]
  classical exact Pi.mulSingle_eq_same (M := fun u : HeightOneSpectrum (𝓞 E) => u.adicCompletion E) w y

variable {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)}
  {V : Type} [AddCommGroup V] [Module ℂ V] {h : w.under (𝓞 F) = v}

theorem IsConjAt.unique {c c' : w.adicCompletion E →+* w.adicCompletion E} (hc : IsConjAt σ h c)
    (hc' : IsConjAt σ h c') : c = c' := RingHom.ext fun y => by
  obtain ⟨z, rfl⟩ := toCompl_surjective h y
  rw [hc, hc']

variable {ρ : Representation ℂ (GLoc σ J v) V} {x : V} {B B' : Multiset ℂˣ}

theorem IsParamVec.unique (hx : IsParamVec σ J L h ρ x B) (hx' : IsParamVec σ J L h ρ x B') : B = B' := by
  by_cases hv : IsSplit (E := E) v
  · exact hx.unique_of_isSplit hv hx'
  obtain ⟨-, c, ϖ, e, α, hU, he, hα, rfl⟩ := hx.resolve_left fun h => hv h.1
  obtain ⟨-, c', ϖ', e', β, hU', he', hβ, rfl⟩ := hx'.resolve_left fun h => hv h.1
  obtain rfl := he.1.unique he'.1
  exact bcParam_of_weylConj (((hα.of_chart he he').of_unif hU hU').unique hU' hβ)

theorem HasParam.unique (hρ : HasParam σ J L h ρ B) (hρ' : HasParam σ J L h ρ B') : B = B' := by
  obtain ⟨x, hx⟩ := hρ.exists_vec
  exact hx.unique (hρ'.isParamVec hx.mem_fixed hx.ne_zero)

theorem IsSysParam.unique {c : List ℤ → ℂ} (hc : IsSysParam σ n h c B) (hc' : IsSysParam σ n h c B') : B = B' := by
  rcases hc with ⟨hv, hB, hc⟩ | ⟨hw, τ, ϖ, α, hU, hτ, rfl, hc⟩ <;>
    rcases hc' with ⟨hv', hB', hc'⟩ | ⟨hw', τ', ϖ', β, hU', hτ', rfl, hc'⟩
  · exact eq_of_satEig_eq (qV_ne_zero w) hB hB' fun j hj => (hc j hj).symm.trans (hc' j hj)
  · exact absurd hv (not_isSplit_of_isInertAt hw')
  · exact absurd hv' (not_isSplit_of_isInertAt hw)
  · obtain rfl := hτ.unique hτ'
    refine bcParam_of_weylConj (weylConj_of_dosetInd hU fun d t hd ht => ?_)
    obtain ⟨t', ht', e⟩ := exists_dosetInd_eq hU hU' ht
    rw [← hc d t hd ht, hc' d t' hd ht', e, satU_indep hU hU' (Final.DosetIndMem _ _ _ _)]

end Place

section Global

variable {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)}
  {S : Set (HeightOneSpectrum (𝓞 F))} {V : Type} [AddCommGroup V] [Module ℂ V]
  {Vl : HeightOneSpectrum (𝓞 F) → Type} [∀ v, AddCommGroup (Vl v)] [∀ v, Module ℂ (Vl v)]
  {π : ∀ v, Representation ℂ (GLoc σ J v) (Vl v)} {c c' : Fam E} {w : HeightOneSpectrum (𝓞 E)}

theorem IsParamVecOff.unique {ρ : Representation ℂ (GAd σ J) V} {x : V} (h : IsParamVecOff σ J L S ρ x c)
    (h' : IsParamVecOff σ J L S ρ x c') (hw : w ∉ above E S) : c w = c' w :=
  (h _ hw w rfl).unique (h' _ hw w rfl)

theorem IsSysParamOff.unique {s : HeightOneSpectrum (𝓞 E) → List ℤ → ℂ} (h : IsSysParamOff σ n S s c)
    (h' : IsSysParamOff σ n S s c') (hw : w ∉ above E S) : c w = c' w :=
  (h _ hw w rfl).unique (h' _ hw w rfl)

theorem LSTw_congr (h : ∀ w ∉ above E S, c w = c' w) (m : HeightOneSpectrum (𝓞 E) → ℂˣ) (s : ℂ) :
    LSTw S c m s = LSTw S c' m s := eulerProd_congr (fun w hw => by rw [twist, twist, h w hw]) s

end Global

end GlobalTheory.LFun

end
