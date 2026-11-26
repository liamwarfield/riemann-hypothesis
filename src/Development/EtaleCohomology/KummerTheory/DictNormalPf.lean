module

public import Development.EtaleCohomology.KummerTheory.LHCutGlue
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsBisTail

@[expose] public section

section -- merged from Development.EtaleCohomology.KummerTheory.DictNormalPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory

def NrmMk : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}
  (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U),
  (∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U),
    Sec.res g (a p s h U x) = a p s h V ((E.obj (op (SimplexCategory.mk p))).map g.op x)) →
  ∃ α : Cochain ((chains R).obj E) I n, ∀ p s h U x, ev α p s h U x = a p s h U x

def NrmDelta : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n m : ℤ} (_hm : n + 1 = m)
  (α : Cochain ((chains R).obj E) I n) (U : Scheme.{0}) (p : ℕ) (s t : ℤ)
  (hs : -((p + 1 : ℕ) : ℤ) + n = s) (ht : -((p + 1 : ℕ) : ℤ) + m = t) (x : Sx E (p + 1) U),
  ev (δ n m α) (p + 1) t ht U x = Sec.map (I.d s t) (ev α (p + 1) s hs U x) +
    m.negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • ev α p t (by omega) U ((E.δ i).app (op U) x)

def up {X U : Scheme.{0}} {p q : ℕ} (x : Sx (sch.obj X) p U) : Sx (sch.obj X) q U := x

theorem face_sch {X U : Scheme.{0}} {p : ℕ} (x : Sx (sch.obj X) (p + 1) U) (i : Fin (p + 2)) :
    ((sch.obj X).δ i).app (op U) x = up x := rfl

theorem altsum (k : ℕ) : ∑ i : Fin k, (-1 : ℤ) ^ (i : ℕ) = if Even k then 0 else 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => (-1 : ℤ) ^ i) k]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    rcases Nat.even_or_odd k with hk | hk
    · have : ¬ Even (k + 1) := by rw [Nat.even_add_one]; exact not_not.mpr hk
      simp [hk, this, hk.neg_one_pow]
    · have : Even (k + 1) := hk.add_one
      have h2 : ¬ Even k := Nat.not_even_iff_odd.mpr hk
      simp [h2, this, hk.neg_one_pow]

theorem ev_zero' (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} p s h U x :
    ev (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 := by simp [ev]

theorem ev_sub' (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (α β : Cochain ((chains R).obj E) I n) p s h U x :
    ev (α - β) p s h U x = ev α p s h U x - ev β p s h U x := by
  rw [sub_eq_add_neg, ev_add, ev_neg, ← sub_eq_add_neg]

end LateralTheory.KummerTheory

namespace LateralTheory.KummerTheory

theorem DictNormal_of (hM : NrmMk) (hD : NrmDelta) : DictNormal := by
  intro R _ I X n α
  have hα : δ n (n + 1) α.1 = 0 := (Cocycle.mem_iff n (n + 1) rfl α.1).1 α.2
  obtain ⟨β, hβ⟩ := hM R (E := sch.obj X) (I := I) (n := n - 1)
    (fun p s h U x => if Odd p then n.negOnePow • ev α.1 (p + 1) s (by push_cast; omega) U (up x) else 0)
    (by
      intro p s h V U g x
      dsimp only
      split_ifs
      · rw [Units.smul_def, Units.smul_def]
        refine (map_zsmul ((I.X s).obj.map g.op).hom _ _).trans ?_
        exact congrArg (fun v => (n.negOnePow : ℤ) • v) (ev_res R α.1 (p + 1) s _ V U g (up x))
      · exact map_zero _)
  let γ : Cocycle ((chains R).obj (sch.obj X)) I n :=
    ⟨δ (n - 1) n β, (Cocycle.mem_iff n (n + 1) rfl _).2 (δ_δ _ _ _ _)⟩
  refine ⟨α - γ, ?_, ?_⟩
  · rw [CohomologyClass.mk_sub, sub_eq_self, CohomologyClass.mk_eq_zero_iff,
      mem_coboundaries_iff γ (n - 1) (by omega)]
    exact ⟨β, rfl⟩
  · intro p s h U y
    show ev (α.1 - δ (n - 1) n β) (p + 1) s h U y = 0
    rw [ev_sub', sub_eq_zero]
    rw [hD R (by omega) β U p (s - 1) s (by push_cast at h ⊢; omega) h y]
    simp only [face_sch, hβ]
    rcases Nat.even_or_odd p with hp | hp
    ·
      have hp1 : Odd (p + 1) := hp.add_one
      have hp0 : ¬ Odd p := Nat.not_odd_iff_even.mpr hp
      simp only [hp1, hp0, if_true, if_false, smul_zero, Finset.sum_const_zero, add_zero]
      have hc := hD R (n := n) (m := n + 1) rfl α.1 U (p + 1) (s - 1) s (by push_cast at h ⊢; omega)
        (by push_cast at h ⊢; omega) (up y)
      rw [hα, ev_zero'] at hc
      simp only [face_sch] at hc
      rw [← Finset.sum_smul, altsum] at hc
      have he : ¬ Even (p + 1 + 2) := by
        rw [Nat.not_even_iff_odd]; exact hp1.add_even even_two
      simp only [he, if_false, one_smul] at hc
      rw [Int.negOnePow_succ, Units.neg_smul] at hc
      have key := add_neg_eq_zero.1 hc.symm
      rw [Units.smul_def]
      refine Eq.trans ?_ (map_zsmul ((I.d (s - 1) s).hom.app (op U)).hom _ _).symm
      rw [show (ModuleCat.Hom.hom ((I.d (s - 1) s).hom.app (op U))) (ev α.1 (p + 1 + 1) (s - 1) (by push_cast at h ⊢; omega) U (up y))
          = n.negOnePow • ev α.1 (p + 1) s (by push_cast at h ⊢; omega) U (up (up y)) from key]
      rw [← Units.smul_def, smul_smul, Int.units_mul_self, one_smul]
      rfl
    · have hp1 : ¬ Odd (p + 1) := Nat.not_odd_iff_even.mpr hp.add_one
      simp only [hp1, hp, if_true, if_false, map_zero, zero_add]
      rw [← Finset.sum_smul, altsum]
      have he : ¬ Even (p + 2) := by
        rw [Nat.not_even_iff_odd]; exact hp.add_even even_two
      simp only [he, if_false, one_smul, smul_smul, Int.units_mul_self]
      rfl

end LateralTheory.KummerTheory

namespace LateralTheory.KummerTheory

theorem chains_d (R : Type) [CommRing R] (E : Spc) (p : ℕ) :
    (chainsXIso R E (p + 1)).inv ≫ ((chains R).obj E).d (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) =
      (∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (E.δ i)) ≫ (chainsXIso R E p).inv := by
  simp only [chainsXIso, chains, Functor.comp_obj]
  erw [HomologicalComplex.extend_d_eq _ _ (i := p + 1) (j := p) rfl rfl]
  erw [Iso.inv_hom_id_assoc]
  congr 1
  simp only [chainsN, Functor.comp_obj]
  erw [AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq]
  rfl

def evAt {R : Type} [CommRing R] {F G : Shv R} (U : Scheme.{0}) (y : Sec F U) : (F ⟶ G) →+ Sec G U where
  toFun φ := (φ.hom.app (op U)).hom y
  map_zero' := by simp
  map_add' := by simp

theorem evAt_apply {R : Type} [CommRing R] {F G : Shv R} (U : Scheme.{0}) (y : Sec F U) (φ : F ⟶ G) :
    evAt U y φ = (φ.hom.app (op U)).hom y := rfl

theorem nrmDelta : NrmDelta := by
  intro R _ E I n m hm α U p s t hs ht x
  unfold ev
  rw [δ_v n m hm α (-((p + 1 : ℕ) : ℤ)) t ht s (-(p : ℤ)) (by omega) (by push_cast; omega)]
  rw [Preadditive.comp_add, Units.smul_def, Preadditive.comp_zsmul, ← Category.assoc _ (((chains R).obj E).d _ _),
    chains_d]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, Category.assoc]
  simp [Units.smul_def, Finset.smul_sum]
  refine (map_sum (evAt (G := I.X t) U (freeGen R (E.obj (op (SimplexCategory.mk (p + 1)))) U x)) _ _).trans ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, map_zsmul]
  congr 2
  have := free_gen_map R (E.δ i) U x
  rw [evAt_apply]
  simp
  exact congrArg (fun z => (ModuleCat.Hom.hom ((α.v (-(p : ℤ)) t (by push_cast at ht ⊢; omega)).hom.app (op U)))
    ((ModuleCat.Hom.hom ((chainsXIso R E p).inv.hom.app (op U))) z)) this

end LateralTheory.KummerTheory

namespace LateralTheory.KummerTheory

theorem DictNormal_of' (hM : NrmMk) : DictNormal := DictNormal_of hM nrmDelta
end LateralTheory.KummerTheory
end
end

section -- merged from Development.EtaleCohomology.KummerTheory.PlaceStepPf
noncomputable section

open IsLocalRing Algebra

namespace LateralTheory.KummerTheory

def PlaceResGood : Prop := ∀ (k K : Type) [Field k] [IsAlgClosed k] [Field K] [Algebra k K] (A : LocalSubring K),
  PlaceGood k K A → ∀ (y : K) (S : Subring K) (hAS : A.toSubring ≤ S),
    S = (Algebra.adjoin A.toSubring {y}).toSubring → ∀ (Q : Ideal S) [Q.IsMaximal],
      (maximalIdeal A.toSubring).map (Subring.inclusion hAS) ≤ Q →
        PlaceGood k K (LocalSubring.ofPrime S Q)

theorem PlaceStep_of (hR : PlaceResGood) : PlaceStep := by
  intro k K _ _ _ _ A hA hmax x

  have collapse : ∀ (y : K) (S : Subring K) (hAS : A.toSubring ≤ S),
      S = (Algebra.adjoin A.toSubring {y}).toSubring → ∀ (Q : Ideal S) [Q.IsMaximal],
      (maximalIdeal A.toSubring).map (Subring.inclusion hAS) ≤ Q → S ≤ A.toSubring := by
    intro y S hAS hS Q _ hQ
    have hle : A ≤ LocalSubring.ofPrime S Q := by
      refine ⟨hAS.trans (LocalSubring.le_ofPrime ..), ((local_hom_tfae _).out 3 1).mp ?_⟩
      conv_rhs => rw [← IsLocalization.AtPrime.map_eq_maximalIdeal Q]
      refine .trans ?_ (Ideal.map_mono hQ)
      rw [Ideal.map_map]; rfl
    exact (LocalSubring.le_ofPrime S Q).trans (hmax _ hle (hR k K A hA y S hAS hS Q hQ)).1
  have top : ∀ y ∉ A.toSubring,
      (maximalIdeal A.toSubring).map
        (Subring.inclusion (T := (Algebra.adjoin A.toSubring {y}).toSubring)
          (fun r hr => algebraMap_mem (Algebra.adjoin A.toSubring {y}) ⟨r, hr⟩)) = ⊤ := by
    intro y hy
    by_contra hne
    obtain ⟨Q, hQm, hQ⟩ := Ideal.exists_le_maximal _ hne
    exact hy (collapse y _ _ rfl Q hQ (self_mem_adjoin_singleton _ _))
  have intmem : ∀ z : K, IsIntegral A.toSubring z → z ∈ A.toSubring := by
    intro z hz
    let S := A.toSubring[z]
    have : Algebra.IsIntegral A.toSubring S := Algebra.IsIntegral.adjoin (by simpa)
    obtain ⟨Q : Ideal S.toSubring, hQ, e⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral
      (S := S) (maximalIdeal A.toSubring) (le_maximalIdeal (by set_option synthInstance.maxHeartbeats 400000 in simp))
    exact collapse z S.toSubring (fun r hr => algebraMap_mem S ⟨r, hr⟩) rfl Q
      (Ideal.map_le_iff_le_comap.mpr e.ge) (self_mem_adjoin_singleton _ _)
  by_cases hx : x ∈ A.toSubring
  · exact Or.inl hx
  right
  refine intmem _ ?_
  have hx0 : x ≠ 0 := fun e => hx (e ▸ zero_mem _)
  let := invertibleOfNonzero hx0
  have ⟨p, hp, hpx⟩ := exists_aeval_invOf_eq_zero_of_idealMap_adjoin_sup_span_eq_top x _
    (maximalIdeal.isMaximal A.toSubring).ne_top (top_unique ((top x hx).ge.trans le_self_add))
  have H : IsUnit p.leadingCoeff := of_not_not fun h => by simpa using sub_mem h hp
  exact ⟨.C H.unit⁻¹.1 * p, by simp [Polynomial.Monic], by simpa using .inr hpx⟩

end LateralTheory.KummerTheory
end
end

section -- merged from Development.EtaleCohomology.KummerTheory.PlaceExPfZorn
noncomputable section

namespace LateralTheory.KummerTheory.PlaceZornPf

variable {k K : Type} [Field k] [Field K] [Algebra k K]

theorem good_range : PlaceGood k K (LocalSubring.range (algebraMap k K)) := by
  refine ⟨fun c => ⟨c, rfl⟩, ?_⟩
  rintro a ⟨c, rfl⟩
  exact ⟨c, Or.inl rfl⟩

theorem ub (s : Set (LocalSubring K)) (hs : s ⊆ {A | PlaceGood k K A}) (H : IsChain (· ≤ ·) s)
    (y : LocalSubring K) (hys : y ∈ s) :
    ∃ U ∈ {A | PlaceGood k K A}, ∀ z ∈ s, z ≤ U := by
  have inst : Nonempty s := ⟨⟨y, hys⟩⟩
  have hdir := H.directed.mono_comp _ LocalSubring.toSubring_mono
  refine ⟨@LocalSubring.mk _ _ (⨆ i : s, i.1.toSubring) ⟨?_⟩, ?_, ?_⟩
  · intro ⟨a, ha⟩ ⟨b, hb⟩ e
    obtain ⟨A, haA : a ∈ A.1.toSubring⟩ := (Subring.mem_iSup_of_directed hdir).mp ha
    obtain ⟨B, hbB : b ∈ B.1.toSubring⟩ := (Subring.mem_iSup_of_directed hdir).mp hb
    obtain ⟨C, hCA, hCB⟩ := hdir A B
    refine (C.1.2.2 (a := ⟨a, hCA haA⟩) (b := ⟨b, hCB hbB⟩) (Subtype.ext congr(($e).1))).imp ?_ ?_
    · exact fun h ↦ h.map (Subring.inclusion (le_iSup (fun i : s ↦ i.1.toSubring) C))
    · exact fun h ↦ h.map (Subring.inclusion (le_iSup (fun i : s ↦ i.1.toSubring) C))
  · refine ⟨fun c => ?_, ?_⟩
    · exact le_iSup (fun i : s ↦ i.1.toSubring) ⟨y, hys⟩ ((hs hys).1 c)
    · intro a ha
      obtain ⟨A, haA : a ∈ A.1.toSubring⟩ := (Subring.mem_iSup_of_directed hdir).mp ha
      obtain ⟨c, hc⟩ := (hs A.2).2 a haA
      refine ⟨c, hc.imp_right fun hn hinv => hn ?_⟩
      obtain ⟨B, hbB : (a - algebraMap k K c)⁻¹ ∈ B.1.toSubring⟩ := (Subring.mem_iSup_of_directed hdir).mp hinv
      obtain ⟨C, hCA, hCB⟩ := H.directed A B
      have hd : a - algebraMap k K c ∈ A.1.toSubring := sub_mem haA ((hs A.2).1 c)
      have hne : a - algebraMap k K c ≠ 0 := by
        intro h0; rw [h0, inv_zero] at hn; exact hn (zero_mem _)
      have hu : IsUnit (⟨a - algebraMap k K c, hCA.1 hd⟩ : C.1.toSubring) :=
        isUnit_iff_exists_inv.mpr ⟨⟨_, hCB.1 hbB⟩, Subtype.ext (by simp [mul_inv_cancel₀ hne])⟩
      have hu' : IsUnit (⟨a - algebraMap k K c, hd⟩ : A.1.toSubring) := by
        have := hCA.2
        apply IsUnit.of_map (Subring.inclusion hCA.1)
        exact hu
      obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp hu'
      have : (a - algebraMap k K c)⁻¹ = (w : K) :=
        inv_eq_of_mul_eq_one_right (by simpa using congrArg Subtype.val hw)
      rw [this]; exact w.2
  · intro A hA
    refine ⟨le_iSup (fun i : s ↦ i.1.toSubring) ⟨A, hA⟩, ⟨?_⟩⟩
    rintro ⟨a, haA⟩ h
    obtain ⟨⟨b, hb⟩, e⟩ := isUnit_iff_exists_inv.mp h
    obtain ⟨B, hbB : b ∈ B.1.toSubring⟩ := (Subring.mem_iSup_of_directed hdir).mp hb
    obtain ⟨C, hCA, hCB⟩ := H.directed ⟨A, hA⟩ B
    apply hCA.2.1
    exact isUnit_iff_exists_inv.mpr ⟨⟨b, hCB.1 hbB⟩, Subtype.ext congr(($e).1)⟩

end LateralTheory.KummerTheory.PlaceZornPf

theorem LateralTheory.KummerTheory.PlaceZorn_of : LateralTheory.KummerTheory.PlaceZorn := by
  intro k K _ _ _ _
  obtain ⟨m, -, hm⟩ := zorn_le_nonempty₀ {A : LocalSubring K | LateralTheory.KummerTheory.PlaceGood k K A}
    (fun s hs H y hy => LateralTheory.KummerTheory.PlaceZornPf.ub s hs H y hy) _ LateralTheory.KummerTheory.PlaceZornPf.good_range
  exact ⟨m, hm.1, fun B hB hgB => hm.2 hgB hB⟩

theorem LateralTheory.KummerTheory.PlaceEx_of_step (h : LateralTheory.KummerTheory.PlaceStep) : LateralTheory.KummerTheory.PlaceEx :=
  LateralTheory.KummerTheory.PlaceEx_of LateralTheory.KummerTheory.PlaceZorn_of h
end
end

section -- merged from Development.EtaleCohomology.KummerTheory.AdicLimPfKer
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

universe u

namespace LateralTheory.KummerTheory.KerPf

theorem seqSec (S : ℕ → Type u) [∀ a, Finite (S a)] [∀ a, Nonempty (S a)] (t : ∀ a, S (a + 1) → S a) :
    ∃ s : ∀ a, S a, ∀ a, t a (s (a + 1)) = s a :=
  _root_.UpperTheory.Reformulated.B.DYra4.main S t

variable (l : ℕ) [Fact l.Prime]

theorem redk (hA : A11) (E : Spc) (n i : ℤ) (x : Hl l E n i) (m : ℕ) :
    ∀ a : ℕ, red (l ^ (m + a)) (l ^ m) E n i (x.1 (m + a)) = x.1 m := by
  have hl : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  intro a
  induction a with
  | zero => exact (@hA (l ^ m) (l ^ m) _ dvd_rfl E).2.2.1 n i _
  | succ a ih =>
    have h := (@hA (l ^ (m + (a + 1))) (l ^ (m + a)) _ (pow_dvd_pow l (by omega)) E).2.2.2 (l ^ m)
      (pow_dvd_pow l (by omega)) n i (x.1 (m + (a + 1)))
    rw [← h, ← ih]
    exact congrArg _ (x.2 (m + a))

omit [Fact l.Prime] in
theorem smul_zero_of (E : Spc) (n i : ℤ) (k b : ℕ) (hkb : k ≤ b) (z : Ht (l ^ k) E n i) : (l ^ b) • z = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod (l ^ k)), (CharP.cast_eq_zero_iff (ZMod (l ^ k)) (l ^ k) _).2 (pow_dvd_pow l hkb), zero_smul]

theorem ker (hA : A11) (E : Spc) (i : ℤ) (hB : ∀ b, BockData l b E i)
    (hFin : ∀ (k : ℕ) (n : ℤ), Finite (Ht (l ^ k) E n i)) (n : ℤ) (b : ℕ) (x : Hl l E n i) (hx : lev l x b = 0) :
    ∃ y : Hl l E n i, x = ((l : ℤ_[l]) ^ b) • y := by
  obtain ⟨u, d, h⟩ := hB b
  let S : ℕ → Type 1 := fun a => {w : Ht (l ^ a) E n i // u a n w = x.1 (b + a)}
  have hS : ∀ a, Finite (S a) := fun a => by have := hFin a n; exact Subtype.finite
  have hN : ∀ a, Nonempty (S a) := fun a => by
    obtain ⟨w, hw⟩ := ((h a n).1 (x.1 (b + a))).1 (by rw [redk l hA E n i x b a]; exact hx)
    exact ⟨⟨w, hw⟩⟩
  let t : ∀ a, S (a + 1) → S a := fun a w => ⟨red (l ^ (a + 1)) (l ^ a) E n i w.1, by
    rw [← (h a n).2.2.2.2.2 w.1, w.2]; exact x.2 (b + a)⟩
  obtain ⟨s, hs⟩ := seqSec S t
  let y : Hl l E n i := ⟨fun a => (s a).1, fun a => congrArg Subtype.val (hs a)⟩
  refine ⟨y, ?_⟩
  have e : ((l : ℤ_[l]) ^ b) • y = (l ^ b : ℕ) • y := by
    rw [← Nat.cast_smul_eq_nsmul ℤ_[l]]; push_cast; rfl
  rw [e]
  apply Subtype.ext
  funext k
  change x.1 k = (l ^ b) • (s k).1
  rcases le_or_gt b k with hk | hk
  · obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hk
    have hr := redk l hA E n i y a b
    rw [Nat.add_comm a b] at hr
    rw [← (h a n).2.2.2.1 ((s (b + a)).1)]
    change x.1 (b + a) = u a n (red _ _ E n i (y.1 (b + a)))
    rw [hr]
    exact (s a).2.symm
  · rw [smul_zero_of l E n i k b hk.le]
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hk.le
    rw [← redk l hA E n i x k c]
    change red _ _ E n i (lev l x (k + c)) = 0
    rw [hx, map_zero]

end LateralTheory.KummerTheory.KerPf

namespace LateralTheory.KummerTheory

theorem AdicKer_holds : AdicKer := fun hA l _ E i hB hFin n k x hx => KerPf.ker l hA E i hB hFin n k x hx

end LateralTheory.KummerTheory
end
end

section -- merged from Development.EtaleCohomology.KummerTheory.ShSectPf
open Polynomial IsLocalRing CategoryTheory AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.KummerTheory.ShSectPf

theorem isUnit_of_map {A K : Type} [CommRing A] [IsLocalRing A] [Field K] (φ : A →+* K)
    (hφ : ∀ a ∈ maximalIdeal A, φ a = 0) {a : A} (h : IsUnit (φ a)) : IsUnit a := by
  by_contra ha
  have := hφ a ((mem_maximalIdeal a).2 ha)
  rw [this] at h; exact not_isUnit_zero h

theorem alg_sect (A B : Type) [CommRing A] [HenselianLocalRing A] [IsSepClosed (ResidueField A)]
    [CommRing B] [Algebra A B] [Algebra.Etale A B] (Q : Ideal B) [Q.IsPrime]
    (hQ : Q.comap (algebraMap A B) = maximalIdeal A) : Nonempty (B →ₐ[A] A) := by
  obtain ⟨s, hsQ, hst⟩ := Algebra.IsEtaleAt.exists_isStandardEtale (R := A) Q
  let S := Localization.Away s
  let P : StandardEtalePresentation A S := hst.nonempty_standardEtalePresentation.some
  let K := Q.ResidueField
  have hsu : IsUnit ((IsScalarTower.toAlgHom A B K) s) := by
    rw [isUnit_iff_ne_zero]
    show algebraMap B Q.ResidueField s ≠ 0
    rw [Ne, Ideal.algebraMap_residueField_eq_zero]; exact hsQ
  let ψ : S →ₐ[A] K := IsLocalization.Away.liftAlgHom s hsu
  let xb : K := ψ P.x
  have hmap := P.hasMap.map ψ
  have hder := hmap.isUnit_derivative_f

  have hkill : ∀ a ∈ maximalIdeal A, algebraMap A K a = 0 := by
    intro a ha
    rw [IsScalarTower.algebraMap_apply A B K, Ideal.algebraMap_residueField_eq_zero]
    rw [← hQ] at ha; exact ha
  have hloc : IsLocalHom (algebraMap A K) := ⟨fun a h => isUnit_of_map _ hkill h⟩
  let i : ResidueField A →+* K := ResidueField.lift (algebraMap A K)
  have hi : ∀ a, i (residue A a) = algebraMap A K a := fun a => ResidueField.lift_residue_apply _ a
  let _ : Algebra (ResidueField A) K := i.toAlgebra
  have hev : ∀ q : A[X], aeval xb (q.map (residue A)) = aeval xb q := by
    intro q
    rw [aeval_def, aeval_def, eval₂_map]
    congr 1
  let fb := P.f.map (residue A)
  have hint : IsIntegral (ResidueField A) xb :=
    ⟨fb, P.monic_f.map _, by rw [← aeval_def, hev]; exact hmap.1⟩
  have hirr := minpoly.irreducible hint
  have hsep : (minpoly (ResidueField A) xb).Separable := by
    rw [Polynomial.separable_iff_derivative_ne_zero hirr]
    intro h0
    obtain ⟨h, hh⟩ := minpoly.dvd (ResidueField A) xb (p := fb) (by rw [hev]; exact hmap.1)
    have : aeval xb (derivative fb) = 0 := by
      rw [hh, derivative_mul, h0]; simp
    rw [show derivative fb = (derivative P.f).map (residue A) from derivative_map _ _,
      hev] at this
    rw [this] at hder; exact not_isUnit_zero hder
  obtain ⟨a0, ha0⟩ := IsSepClosed.exists_root _ (minpoly.degree_pos hint).ne' hsep
  have hd0 : X - C a0 ∣ minpoly (ResidueField A) xb := dvd_iff_isRoot.2 ha0
  have hdvd : minpoly (ResidueField A) xb ∣ X - C a0 :=
    Irreducible.dvd_symm (irreducible_X_sub_C a0) hirr hd0
  obtain ⟨a00, ha00⟩ := residue_surjective a0
  have hxb : xb = algebraMap A K a00 := by
    have h1 : aeval xb (X - C a0) = 0 := by
      obtain ⟨c, hc⟩ := hdvd; rw [hc, map_mul, minpoly.aeval, zero_mul]
    rw [map_sub, aeval_X, aeval_C, sub_eq_zero] at h1
    rw [h1, ← ha00]; exact hi a00
  have hzero : ∀ a : A, algebraMap A K a = 0 → a ∈ maximalIdeal A := by
    intro a ha; by_contra hn
    have := ((mem_maximalIdeal a).not.1 hn |> not_not.1).map (algebraMap A K)
    rw [ha] at this; exact not_isUnit_zero this
  have hev' : ∀ q : A[X], algebraMap A K (q.eval a00) = aeval xb q := by
    intro q; rw [hxb, aeval_algebraMap_apply, coe_aeval_eq_eval]
  obtain ⟨r, hr, hra⟩ := HenselianLocalRing.is_henselian P.f P.monic_f a00
    (hzero _ (by rw [hev']; exact hmap.1)) (isUnit_of_map _ hkill (by rw [hev']; exact hder))
  have hrK : algebraMap A K r = xb := by
    rw [hxb, ← sub_eq_zero, ← map_sub]; exact hkill _ hra
  have hr' : P.HasMap r := by
    refine ⟨by rw [coe_aeval_eq_eval]; exact hr, isUnit_of_map _ hkill ?_⟩
    rw [← aeval_algebraMap_apply, hrK]; exact hmap.2
  exact ⟨((P.lift r hr').comp P.equivRing.toAlgHom).comp (IsScalarTower.toAlgHom A B S)⟩

theorem ShSect_of : LateralTheory.KummerTheory.SecSHPf.ShSect := by
  intro A _ hA Y f hf hsurj
  obtain ⟨hH, hsc⟩ := hA
  obtain ⟨y, hy⟩ := hsurj.surj (IsLocalRing.closedPoint A : Spec (CommRingCat.of A))
  let 𝒰 := Y.affineOpenCover
  let j := 𝒰.idx y
  obtain ⟨y', hy'⟩ := 𝒰.covers y
  let g := 𝒰.f j
  let φ : CommRingCat.of A ⟶ 𝒰.X j := Spec.preimage (g ≫ f)
  have hφ : Spec.map φ = g ≫ f := Spec.map_preimage _
  have het : φ.hom.Etale := by
    rw [← HasRingHomProperty.Spec_iff (P := @Etale), hφ]; infer_instance
  algebraize [φ.hom]
  have hpt : (Spec.map φ) y' = IsLocalRing.closedPoint A := by
    rw [hφ, Scheme.Hom.comp_apply]
    simp only [g, j] at hy' ⊢
    rw [hy', hy]
  have hQ : y'.asIdeal.comap (algebraMap A (𝒰.X j)) = IsLocalRing.maximalIdeal A := by
    have := congrArg PrimeSpectrum.asIdeal hpt
    exact this
  have : y'.asIdeal.IsPrime := PrimeSpectrum.isPrime y'
  obtain ⟨ψ⟩ := alg_sect A (𝒰.X j) y'.asIdeal hQ
  refine ⟨Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ g, ?_⟩
  rw [Category.assoc, ← hφ, ← Spec.map_comp]
  convert Spec.map_id (CommRingCat.of A)
  ext a
  exact ψ.commutes a

end LateralTheory.KummerTheory.ShSectPf
end

section -- merged from Development.EtaleCohomology.KummerTheory.ExIsoPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open LateralTheory.KummerTheory LateralTheory.KummerTheory.LHCut

namespace LateralTheory.KummerTheory.ExIsoPf

variable {Λ : Type} [CommRing Λ]

theorem d_zero_of {F : Cx Λ} {Y : Scheme.{0}} {n m : ℤ} (h : m = n + 1) (a : Sec (F.X n) Y)
    (ha : Sec.map (F.d n (n + 1)) a = 0) : Sec.map (F.d n m) a = 0 := by
  subst h; exact ha

theorem d_zero_of' {F : Cx Λ} {Y : Scheme.{0}} {n m : ℤ} (h : m = n + 1) (a : Sec (F.X n) Y)
    (ha : Sec.map (F.d n m) a = 0) : Sec.map (F.d n (n + 1)) a = 0 := by
  subst h; exact ha

theorem coneEx' {I J K : Cx Λ} {X S : Scheme.{0}} {r : ℕ → ℕ} {M : ℕ} {μ : Pair I J K} {p : X ⟶ S}
    {γ : ∀ a : ℕ, Fin (r a) → Sec (I.X (a : ℤ)) X} {N : ℕ} {j : ℤ} {U : Over S}
    (h : ConeEx M μ p γ N j U) (j₀ : ℤ) (hj : j₀ + 1 = j) (x : Cone J K p r M j U)
    (hx : cD μ p γ j (j + 1) rfl U x = 0) : ∃ y : Cone J K p r M j₀ U, cD μ p γ j₀ j hj U y = N • x := by
  obtain rfl : j₀ = j - 1 := by omega
  exact h x hx

theorem ker_part (hD : Dict) (hL : LhSec) (q : ℕ) {X S : Scheme.{0}} (p : X ⟶ S) (i : ℤ) (r : ℕ → ℕ)
    (c : ∀ a : ℕ, Fin (r a) → Ht q (sch.obj X) a i)
    (γ : ∀ a : ℕ, Fin (r a) → Sec ((res _ (tw q i)).X (a : ℤ)) X) (hγ : ∀ a s, IsCls (c a s) (γ a s)) (M N : ℕ) (j : ℤ)
    (U : Over S) (h0 : ConeEx M (mu q i) p γ N j U) (y : ∀ a : Fin (M + 1), Fin (r a) → Ht q (sch.obj U.left) ((j + 1) - ((a : ℕ) : ℤ)) 0)
    (hy : lh q p U.hom i r c M (j + 1) y = 0) : N • y = 0 := by
  have hC := clsMore_of hD
  choose b hb using fun (a : Fin (M + 1)) (s : Fin (r a)) =>
    (hD (ZMod q) (res _ (tw q 0)) U.left ((j + 1) - ((a : ℕ) : ℤ))).2.1 (y a s)
  have hlh := hL q p i r c γ hγ M (j + 1) U y b hb
  obtain ⟨k, hk⟩ := ((hC (ZMod q) (res _ (tw q i)) (pullback p U.hom) (j + 1)).2.2.2 j rfl _ _ _ _ hlh
    (hC (ZMod q) (res _ (tw q i)) (pullback p U.hom) (j + 1)).1).1 hy
  have hcl : cD (mu q i) p γ j (j + 1) rfl U (b, k) = 0 := by
    refine Prod.ext ?_ ?_
    · funext a s
      show ((a : ℕ) : ℤ).negOnePow • Sec.map _ (b a s) = 0
      rw [d_zero_of (by omega) _ ((hD (ZMod q) (res _ (tw q 0)) U.left _).2.2.1 _ _ (hb a s)).1, smul_zero]
    · show Phi (mu q i) p γ (j + 1) (j + 1) rfl U b - Sec.map _ k = 0
      rw [hk, sub_zero, sub_self]
  obtain ⟨y', hy'⟩ := h0 (b, k) hcl
  funext a s
  have e := congrArg (fun z => z.1 a s) hy'
  change ((a : ℕ) : ℤ).negOnePow • Sec.map _ (y'.1 a s) = N • b a s at e
  show N • y a s = 0
  refine ((hC (ZMod q) (res _ (tw q 0)) U.left ((j + 1) - ((a : ℕ) : ℤ))).2.2.2 ((j - 1) + 1 - ((a : ℕ) : ℤ))
    (by omega) _ _ _ _ ((hC _ _ _ _).2.1 N _ _ (hb a s)) (hC _ _ _ _).1).2 ⟨(((a : ℕ) : ℤ).negOnePow : ℤ) • y'.1 a s, ?_⟩
  rw [sub_zero, ← e, Units.smul_def]
  exact map_zsmul _ _ _

section Gen
variable {I J K : Cx Λ} {X S : Scheme.{0}} {r : ℕ → ℕ} {M : ℕ} (μ : Pair I J K) (p : X ⟶ S)
  (γ : ∀ a : ℕ, Fin (r a) → Sec (I.X (a : ℤ)) X)

theorem cD_fst (j j' : ℤ) (h : j + 1 = j') (U : Over S) (x : Cone J K p r M j U) :
    (cD μ p γ j j' h U x).1 = dS (j + 1) (j' + 1) x.1 := rfl

theorem cD_snd (j j' : ℤ) (h : j + 1 = j') (U : Over S) (x : Cone J K p r M j U) :
    (cD μ p γ j j' h U x).2 = Phi μ p γ (j + 1) j' h U x.1 - Sec.map (K.d j j') x.2 := rfl

theorem dS_zero (n m : ℤ) (U : Scheme.{0}) : dS n m (0 : FinalTheorems J r M n U) = 0 := by
  funext a s
  simp [dS]

theorem Phi_zero (n w : ℤ) (h : n = w) (U : Over S) : Phi μ p γ n w h U (0 : FinalTheorems J r M n U.left) = 0 := by
  simp [Phi]

theorem closed_of_dS (n m : ℤ) (hm : m = n + 1) (U : Scheme.{0}) (b : FinalTheorems J r M n U) (hb : dS n m b = 0)
    (a : Fin (M + 1)) (s : Fin (r a)) : Sec.map (J.d (n - ((a : ℕ) : ℤ)) (n - ((a : ℕ) : ℤ) + 1)) (b a s) = 0 := by
  have e := congrFun (congrFun hb a) s
  simp only [dS, Pi.zero_apply] at e
  rw [smul_eq_zero_iff_eq] at e
  exact d_zero_of' (by omega) _ e

end Gen

theorem cok_part (hD : Dict) (hL : LhSec) (q : ℕ) {X S : Scheme.{0}} (p : X ⟶ S) (i : ℤ) (r : ℕ → ℕ)
    (c : ∀ a : ℕ, Fin (r a) → Ht q (sch.obj X) a i)
    (γ : ∀ a : ℕ, Fin (r a) → Sec ((res _ (tw q i)).X (a : ℤ)) X) (hγ : ∀ a s, IsCls (c a s) (γ a s)) (M N : ℕ) (j : ℤ)
    (U : Over S) (h1 : ConeEx M (mu q i) p γ N (j + 1) U) (b0 : Ht q (sch.obj (pullback p U.hom)) (j + 1) i) :
    ∃ y, lh q p U.hom i r c M (j + 1) y = N • b0 := by
  have hC := clsMore_of hD
  obtain ⟨k0, hk0⟩ := (hD (ZMod q) (res _ (tw q i)) (pullback p U.hom) (j + 1)).2.1 b0
  have hk0c := ((hD (ZMod q) (res _ (tw q i)) (pullback p U.hom) (j + 1)).2.2.1 _ _ hk0).1
  have hcl : cD (mu q i) p γ (j + 1) (j + 1 + 1) rfl U ((0, k0) : Cone _ _ p r M (j + 1) U) = 0 := by
    refine Prod.ext ?_ ?_
    · rw [cD_fst, dS_zero, Prod.fst_zero]
    · rw [cD_snd, Phi_zero, hk0c, sub_zero, Prod.snd_zero]
  obtain ⟨y', hy'⟩ := coneEx' h1 j rfl _ hcl
  have e1 := congrArg Prod.fst hy'
  rw [cD_fst, Prod.smul_fst, smul_zero] at e1
  have hcls := closed_of_dS (j + 1) (j + 1 + 1) rfl U.left y'.1 e1
  choose yc hyc using fun (a : Fin (M + 1)) (s : Fin (r a)) =>
    (hD (ZMod q) (res _ (tw q 0)) U.left ((j + 1) - ((a : ℕ) : ℤ))).1 (y'.1 a s) (hcls a s)
  refine ⟨yc, ?_⟩
  have hlh := hL q p i r c γ hγ M (j + 1) U yc y'.1 hyc
  refine ((hC (ZMod q) (res _ (tw q i)) (pullback p U.hom) (j + 1)).2.2.2 j rfl _ _ _ _ hlh
    ((hC _ _ _ _).2.1 N _ _ hk0)).2 ⟨y'.2, ?_⟩
  have e2 := congrArg Prod.snd hy'
  rw [cD_snd, Prod.smul_snd] at e2
  rw [← e2, sub_sub_cancel]

theorem exIso_of (hD : Dict) (hL : LhSec) : ExIso := by
  intro q X S p i r c γ hγ M N j U h0 h1
  exact ⟨fun y hy => ker_part hD hL q p i r c γ hγ M N j U h0 y hy, cok_part hD hL q p i r c γ hγ M N j U h1⟩

end LateralTheory.KummerTheory.ExIsoPf

end
end

section -- merged from Development.EtaleCohomology.KummerTheory.EtaleLerayHirschConeSourceComponentVanishesAfter
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory.LHCut

theorem lcv_cls_of_d {R : Type} [CommRing R] (hD : Dict) {I : Cx R} {X : Scheme.{0}} (n n' : ℤ) (h : n + 1 = n')
    (a : Sec (I.X n) X) (ha : Sec.map (I.d n n') a = 0) : ∃ x, IsCls x a := by
  subst h; exact (hD R I X n).1 a ha

theorem lcv_d_of_cls {R : Type} [CommRing R] (hD : Dict) {I : Cx R} {X : Scheme.{0}} {n : ℤ} (n' : ℤ) (h : n + 1 = n')
    x (a : Sec (I.X n) X) (ha : IsCls x a) : Sec.map (I.d n n') a = 0 := by
  subst h; exact ((hD R I X n).2.2.1 x a ha).1

section
variable {Λ : Type} [CommRing Λ] {I J K : Cx Λ} {X S : Scheme.{0}} {r : ℕ → ℕ} {M : ℕ}
  (μ : Pair I J K) (p : X ⟶ S) (γ : ∀ a : ℕ, Fin (r a) → Sec (I.X (a : ℤ)) X)

theorem lcv_cD_fst (j j' : ℤ) (h : j + 1 = j') (U : Over S) (x : Cone J K p r M j U) :
    (cD μ p γ j j' h U x).1 = dS (j + 1) (j' + 1) x.1 := rfl

theorem lcv_cD_snd (j j' : ℤ) (h : j + 1 = j') (U : Over S) (x : Cone J K p r M j U) :
    (cD μ p γ j j' h U x).2 = Phi μ p γ (j + 1) j' h U x.1 - Sec.map (K.d j j') x.2 := rfl

theorem lcv_cres_fst {j : ℤ} {V U : Over S} (g : V ⟶ U) (x : Cone J K p r M j U) :
    (cres g x).1 = fun a s => Sec.res g.left (x.1 a s) := rfl

theorem lcv_cres_snd {j : ℤ} {V U : Over S} (g : V ⟶ U) (x : Cone J K p r M j U) :
    (cres g x).2 = Sec.res (rst p g) x.2 := rfl
end

theorem lcv_step1 (hD : Dict) (hL : LhSec) (q : ℕ) {X S : Scheme.{0}} (p : X ⟶ S) (i : ℤ)
    (r : ℕ → ℕ) (c : ∀ a : ℕ, Fin (r a) → Ht q (sch.obj X) a i)
    (γ : ∀ a : ℕ, Fin (r a) → Sec ((res _ (tw q i)).X (a : ℤ)) X) (hc : ∀ a s, IsCls (c a s) (γ a s)) (M N : ℕ)
    (j₀ : ℤ) (hK : KerLoc q p i r c M N (j₀ + 1 + 1)) (U : Over S)
    (x1 : FinalTheorems (res _ (tw q 0)) r M (j₀ + 1 + 1) U.left) (k : Sec ((res _ (tw q i)).X (j₀ + 1)) (pullback p U.hom))
    (hx1 : dS (j₀ + 1 + 1) (j₀ + 1 + 1 + 1) x1 = 0)
    (hx2 : Phi (mu q i) p γ (j₀ + 1 + 1) (j₀ + 1 + 1) rfl U x1 = Sec.map ((res _ (tw q i)).d (j₀ + 1) (j₀ + 1 + 1)) k)
    (u : U.left) : ∃ (V1 : Over S) (g1 : V1 ⟶ U), Nbhd g1 u ∧ ∃ b : FinalTheorems (res _ (tw q 0)) r M (j₀ + 1) V1.left,
      dS (j₀ + 1) (j₀ + 1 + 1) b = fun a s => N • Sec.res g1.left (x1 a s) := by
  have hCM := clsMore_of hD
  have hb : ∀ (a : Fin (M + 1)) (s : Fin (r a)),
      Sec.map ((res _ (tw q 0)).d (j₀ + 1 + 1 - ((a : ℕ) : ℤ)) (j₀ + 1 + 1 + 1 - ((a : ℕ) : ℤ))) (x1 a s) = 0 := by
    intro a s
    have h0 := congrFun (congrFun hx1 a) s
    have := congrArg (fun v => ((a : ℕ) : ℤ).negOnePow • v) h0
    simpa only [dS, Pi.zero_apply, smul_smul, Int.units_mul_self, one_smul, smul_zero] using this
  choose y hy using fun a s => lcv_cls_of_d hD _ _ (by omega) _ (hb a s)
  have hl := hL q p i r c γ hc M (j₀ + 1 + 1) U y x1 hy
  have hly : lh q p U.hom i r c M (j₀ + 1 + 1) y = 0 :=
    ((hCM _ _ _ _).2.2.2 (j₀ + 1) rfl _ 0 _ 0 hl (hCM _ _ _ _).1).2 ⟨k, by rw [sub_zero]; exact hx2.symm⟩
  obtain ⟨V1, g1, hg1, hk1⟩ := hK U u y hly
  have hcl1 : ∀ (a : Fin (M + 1)) (s : Fin (r a)),
      IsCls (N • pull _ (sch.map g1.left) _ _ (y a s)) (N • Sec.res g1.left (x1 a s)) :=
    fun a s => (hCM _ _ _ _).2.1 N _ _ ((hD _ _ _ _).2.2.2.2 g1.left _ _ (hy a s))
  choose b1 hb1 using fun (a : Fin (M + 1)) (s : Fin (r a)) =>
    ((hCM _ _ _ _).2.2.2 (j₀ + 1 - ((a : ℕ) : ℤ)) (by omega) _ 0 _ 0 (hcl1 a s) (hCM _ _ _ _).1).1 (hk1 a s)
  refine ⟨V1, g1, hg1, fun a s => ((a : ℕ) : ℤ).negOnePow • b1 a s, ?_⟩
  funext a s
  simp only [dS, Units.smul_def, map_zsmul, smul_smul, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_smul]
  exact (hb1 a s).trans (sub_zero _)

theorem lcv_step2 (hD : Dict) (hL : LhSec) (q : ℕ) {X S : Scheme.{0}} (p : X ⟶ S) (i : ℤ)
    (r : ℕ → ℕ) (c : ∀ a : ℕ, Fin (r a) → Ht q (sch.obj X) a i)
    (γ : ∀ a : ℕ, Fin (r a) → Sec ((res _ (tw q i)).X (a : ℤ)) X) (hc : ∀ a s, IsCls (c a s) (γ a s)) (M N : ℕ)
    (j₀ : ℤ) (hC : CokLoc q p i r c M N (j₀ + 1)) (V1 : Over S) (v1 : V1.left)
    (k : Sec ((res _ (tw q i)).X (j₀ + 1)) (pullback p V1.hom))
    (hk : Sec.map ((res _ (tw q i)).d (j₀ + 1) (j₀ + 1 + 1)) k = 0) :
    ∃ (V2 : Over S) (g2 : V2 ⟶ V1), Nbhd g2 v1 ∧ ∃ (b2 : FinalTheorems (res _ (tw q 0)) r M (j₀ + 1) V2.left)
      (k' : Sec ((res _ (tw q i)).X j₀) (pullback p V2.hom)), dS (j₀ + 1) (j₀ + 1 + 1) b2 = 0 ∧
      Phi (mu q i) p γ (j₀ + 1) (j₀ + 1) rfl V2 b2 - Sec.map ((res _ (tw q i)).d j₀ (j₀ + 1)) k' =
        N • Sec.res (rst p g2) k := by
  have hCM := clsMore_of hD
  obtain ⟨κ, hκ⟩ := (hD _ _ _ _).1 k hk
  obtain ⟨V2, g2, hg2, y2, hy2⟩ := hC V1 v1 κ
  choose b2 hb2 using fun (a : Fin (M + 1)) (s : Fin (r a)) => (hD _ _ _ _).2.1 (y2 a s)
  have hl2 := hL q p i r c γ hc M (j₀ + 1) V2 y2 b2 hb2
  have hcl2 : IsCls (N • pull _ (sch.map (rst p g2)) _ _ κ) (N • Sec.res (rst p g2) k) :=
    (hCM _ _ _ _).2.1 N _ _ ((hD _ _ _ _).2.2.2.2 (rst p g2) _ _ hκ)
  obtain ⟨k', hk'⟩ := ((hCM _ _ _ _).2.2.2 j₀ rfl _ _ _ _ hl2 hcl2).1 hy2
  refine ⟨V2, g2, hg2, b2, k', ?_, ?_⟩
  · funext a s
    simp only [dS, Pi.zero_apply]
    rw [lcv_d_of_cls hD _ (by omega) _ _ (hb2 a s), smul_zero]
  · rw [hk', sub_sub_cancel]

section
variable {Λ : Type} [CommRing Λ] {I J K : Cx Λ} {X S : Scheme.{0}} {r : ℕ → ℕ} {M : ℕ}
  (μ : Pair I J K) (p : X ⟶ S) (γ : ∀ a : ℕ, Fin (r a) → Sec (I.X (a : ℤ)) X)

theorem etale_leray_hirsch_cone_comparison_map_degree_cast (n w : ℤ) (h : n = w) (U : Over S) : Phi (J := J) (M := M) μ p γ n w h U 0 = 0 := by
  simp [Phi]

theorem etale_leray_hirsch_cone_source_component_vanishes_after_correction (j₀ : ℤ) {U V1 : Over S} (g1 : V1 ⟶ U) (x : Cone J K p r M (j₀ + 1) U) (N : ℕ)
    (b1 : FinalTheorems J r M (j₀ + 1) V1.left) (hb1 : dS (j₀ + 1) (j₀ + 1 + 1) b1 = fun a s => N • Sec.res g1.left (x.1 a s)) :
    (N • cres g1 x - cD μ p γ j₀ (j₀ + 1) rfl V1 (b1, 0)).1 = 0 := by
  rw [Prod.fst_sub, Prod.smul_fst, lcv_cres_fst, lcv_cD_fst, hb1]
  funext a s
  simp only [Pi.sub_apply, Pi.smul_apply, sub_self, Pi.zero_apply]

theorem etale_leray_hirsch_cone_cycle_with_zero_source_has_closed_complex_part (j₀ : ℤ) {V1 : Over S} (z : Cone J K p r M (j₀ + 1) V1) (hz1 : z.1 = 0)
    (hzc : cD μ p γ (j₀ + 1) (j₀ + 1 + 1) rfl V1 z = 0) : Sec.map (K.d (j₀ + 1) (j₀ + 1 + 1)) z.2 = 0 := by
  have := congrArg Prod.snd hzc
  rw [lcv_cD_snd, hz1, etale_leray_hirsch_cone_comparison_map_degree_cast, zero_sub, Prod.snd_zero, neg_eq_zero] at this
  exact this

theorem lcv_bk (j₀ : ℤ) {V1 V2 : Over S} (g2 : V2 ⟶ V1) (z : Cone J K p r M (j₀ + 1) V1) (hz1 : z.1 = 0) (N : ℕ)
    (b2 : FinalTheorems J r M (j₀ + 1) V2.left) (k' : Sec (K.X j₀) (pullback p V2.hom)) (hdb2 : dS (j₀ + 1) (j₀ + 1 + 1) b2 = 0)
    (hk' : Phi μ p γ (j₀ + 1) (j₀ + 1) rfl V2 b2 - Sec.map (K.d j₀ (j₀ + 1)) k' = N • Sec.res (rst p g2) z.2) :
    cD μ p γ j₀ (j₀ + 1) rfl V2 (b2, k') = N • cres g2 z := by
  refine Prod.ext ?_ ?_
  · rw [lcv_cD_fst, Prod.smul_fst, lcv_cres_fst, hz1]
    exact hdb2.trans (by funext a s; simp)
  · rw [lcv_cD_snd, Prod.smul_snd, lcv_cres_snd]
    exact hk'

theorem lcv_nbhd {U V1 V2 : Over S} (g1 : V1 ⟶ U) (g2 : V2 ⟶ V1) (u : U.left) (hg1 : Nbhd g1 u) (v1 : V1.left)
    (hv1 : g1.left v1 = u) (hg2 : Nbhd g2 v1) : Nbhd (g2 ≫ g1) u := by
  refine ⟨?_, ?_⟩
  · have := hg1.1; have := hg2.1
    rw [Over.comp_left]; infer_instance
  · obtain ⟨v2, hv2⟩ := hg2.2
    exact ⟨v2, by simp [hv2, hv1]⟩

theorem lcv_alg (hA : ConeAlg) (hγ : Closed γ) (j₀ : ℤ) {U V1 V2 : Over S} (g1 : V1 ⟶ U) (g2 : V2 ⟶ V1)
    (x : Cone J K p r M (j₀ + 1) U) (N : ℕ)
    (w0 : Cone J K p r M j₀ V1) (y2 : Cone J K p r M j₀ V2)
    (hy2 : cD μ p γ j₀ (j₀ + 1) rfl V2 y2 = N • cres g2 (N • cres g1 x - cD μ p γ j₀ (j₀ + 1) rfl V1 w0)) :
    cD μ p γ j₀ (j₀ + 1) rfl V2 (N • cres g2 w0 + y2) = N ^ 2 • cres (g2 ≫ g1) x := by
  obtain ⟨-, -, nat1⟩ := hA _ μ p r M γ hγ j₀ (j₀ + 1) rfl V1
  obtain ⟨-, -, nat2⟩ := hA _ μ p r M γ hγ (j₀ + 1) (j₀ + 1 + 1) rfl V1
  obtain ⟨-, -, natU⟩ := hA _ μ p r M γ hγ (j₀ + 1) (j₀ + 1 + 1) rfl U
  obtain ⟨linV2, -, -⟩ := hA _ μ p r M γ hγ j₀ (j₀ + 1) rfl V2
  have e1 := (map_add (IsLinearMap.mk' _ linV2) (N • cres g2 w0) y2).trans
    (congrArg (· + _) (map_nsmul (IsLinearMap.mk' _ linV2) N (cres g2 w0)))
  simp only [IsLinearMap.mk'_apply] at e1
  have e2 := map_sub (IsLinearMap.mk' _ (nat2 V2 g2).1) (N • cres g1 x) (cD μ p γ j₀ (j₀ + 1) rfl V1 w0)
  have e3 := map_nsmul (IsLinearMap.mk' _ (nat2 V2 g2).1) N (cres g1 x)
  simp only [IsLinearMap.mk'_apply] at e2 e3
  rw [e1, hy2, e2, e3, (nat1 V2 g2).2.1 w0, smul_sub, add_sub_cancel, smul_smul, ← pow_two,
    (natU V1 g1).2.2 V2 g2 x]

theorem lcv_zc (hA : ConeAlg) (hγ : Closed γ) (j₀ : ℤ) {U V1 : Over S} (g1 : V1 ⟶ U)
    (x : Cone J K p r M (j₀ + 1) U) (hx : cD μ p γ (j₀ + 1) (j₀ + 1 + 1) rfl U x = 0) (N : ℕ)
    (w0 : Cone J K p r M j₀ V1) :
    cD μ p γ (j₀ + 1) (j₀ + 1 + 1) rfl V1 (N • cres g1 x - cD μ p γ j₀ (j₀ + 1) rfl V1 w0) = 0 := by
  obtain ⟨-, sq1, -⟩ := hA _ μ p r M γ hγ j₀ (j₀ + 1) rfl V1
  obtain ⟨lin2, -, -⟩ := hA _ μ p r M γ hγ (j₀ + 1) (j₀ + 1 + 1) rfl V1
  obtain ⟨-, -, natU⟩ := hA _ μ p r M γ hγ (j₀ + 1) (j₀ + 1 + 1) rfl U
  have c0 : cres g1 (0 : Cone J K p r M (j₀ + 1 + 1) U) = 0 :=
    map_zero (IsLinearMap.mk' _ ((hA _ μ p r M γ hγ (j₀ + 1 + 1) (j₀ + 1 + 1 + 1) rfl U).2.2 V1 g1).1)
  have e := (map_sub (IsLinearMap.mk' _ lin2) (N • cres g1 x) (cD μ p γ j₀ (j₀ + 1) rfl V1 w0)).trans
    (congrArg (· - _) (map_nsmul (IsLinearMap.mk' _ lin2) N (cres g1 x)))
  simp only [IsLinearMap.mk'_apply] at e
  rw [e, sq1 _ rfl w0, ← (natU V1 g1).2.1 x, hx, c0, smul_zero, sub_zero]
end

theorem etale_leray_hirsch_cone_cycle_locally_bounded_boundary (hD : Dict) (hL : LhSec) (hA : ConeAlg) (q : ℕ) {X S : Scheme.{0}} (p : X ⟶ S) (i : ℤ)
    (r : ℕ → ℕ) (c : ∀ a : ℕ, Fin (r a) → Ht q (sch.obj X) a i)
    (γ : ∀ a : ℕ, Fin (r a) → Sec ((res _ (tw q i)).X (a : ℤ)) X) (hc : ∀ a s, IsCls (c a s) (γ a s)) (M N : ℕ)
    (j₀ j : ℤ) (h : j₀ + 1 = j) (hK : KerLoc q p i r c M N (j + 1)) (hC : CokLoc q p i r c M N j)
    (U : Over S) (x : Cone (res _ (tw q 0)) (res _ (tw q i)) p r M j U)
    (hx : cD (mu q i) p γ j (j + 1) rfl U x = 0) (u : U.left) :
    ∃ (V : Over S) (g : V ⟶ U), Nbhd g u ∧
      ∃ y : Cone (res _ (tw q 0)) (res _ (tw q i)) p r M j₀ V, cD (mu q i) p γ j₀ j h V y = N ^ 2 • cres g x := by
  subst h
  have hγ : Closed γ := fun a s => ((hD _ _ X _).2.2.1 _ _ (hc a s)).1
  have hx1 : dS (J := res _ (tw q 0)) (r := r) (M := M) (j₀ + 1 + 1) (j₀ + 1 + 1 + 1) x.1 = 0 :=
    ((lcv_cD_fst (mu q i) p γ (j₀ + 1) (j₀ + 1 + 1) rfl U x).symm.trans (congrArg Prod.fst hx)).trans Prod.fst_zero
  have hx2 : Phi (mu q i) p γ (j₀ + 1 + 1) (j₀ + 1 + 1) rfl U x.1 =
      Sec.map ((res _ (tw q i)).d (j₀ + 1) (j₀ + 1 + 1)) x.2 :=
    sub_eq_zero.1 (((lcv_cD_snd (mu q i) p γ (j₀ + 1) (j₀ + 1 + 1) rfl U x).symm.trans (congrArg Prod.snd hx)).trans
      Prod.snd_zero)
  obtain ⟨V1, g1, hg1, b1, hb1⟩ := lcv_step1 hD hL q p i r c γ hc M N j₀ hK U x.1 x.2 hx1 hx2 u
  have hz1 := etale_leray_hirsch_cone_source_component_vanishes_after_correction (mu q i) p γ j₀ g1 x N b1 hb1
  have hzc := lcv_zc (mu q i) p γ hA hγ j₀ g1 x hx N (b1, 0)
  have hz2 := etale_leray_hirsch_cone_cycle_with_zero_source_has_closed_complex_part (mu q i) p γ j₀ _ hz1 hzc
  obtain ⟨v1, hv1⟩ := hg1.2
  obtain ⟨V2, g2, hg2, b2, k', hdb2, hk'⟩ := lcv_step2 hD hL q p i r c γ hc M N j₀ hC V1 v1 _ hz2
  exact ⟨V2, g2 ≫ g1, lcv_nbhd g1 g2 u hg1 v1 hv1 hg2, N • cres g2 (b1, 0) + (b2, k'),
    lcv_alg (mu q i) p γ hA hγ j₀ g1 g2 x N (b1, 0) (b2, k') (lcv_bk (mu q i) p γ j₀ g2 _ hz1 N b2 k' hdb2 hk')⟩

theorem locCone_of (hD : Dict) (hL : LhSec) (hA : ConeAlg) : LocCone := by
  intro q X S p i r c γ hc M N j hK hC U x hx u
  exact etale_leray_hirsch_cone_cycle_locally_bounded_boundary hD hL hA q p i r c γ hc M N (j - 1) j (by omega) hK hC U x hx u
end LateralTheory.KummerTheory.LHCut
end
end
