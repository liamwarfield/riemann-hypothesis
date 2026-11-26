module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.IntegralPartFibres.ContinuousOnZpart
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.IntegralPartFibres.ContinuousLinearMat

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.IntegralPartFibres.ValLeOneOfNabsLt
noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil ValuativeRel
open scoped Pointwise

namespace PositivityTheory.RgUd.TP.Nil.Fib1

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Nil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem val_le_one_of_nabs_lt {t : kˣ} (ht : nabs k t < 1) : valuation k (t : k) ≤ 1 := by
  have h := (nabs_le_iff t 1).1 (by rw [nabs_one]; exact ht.le)
  simpa using h

theorem lat_le_inv {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {L : AddSubgroup (Matrix (Fin n) (Fin n) k)}
    (hL : IsLat Z L) {t : kˣ} (ht : nabs k t < 1) : L ≤ ((t⁻¹ : kˣ) : k) • L := by
  intro x hx
  refine (AddSubgroup.mem_smul_pointwise_iff_exists x _ L).2 ⟨(t : k) • x, hL.int _ (val_le_one_of_nabs_lt ht) x hx, ?_⟩
  simp [smul_smul]

theorem lat_smul_le {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {L : AddSubgroup (Matrix (Fin n) (Fin n) k)}
    (hL : IsLat Z L) {t : kˣ} (ht : nabs k t < 1) (j : ℕ) : ((t ^ j : kˣ) : k) • L ≤ L := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (AddSubgroup.mem_smul_pointwise_iff_exists x _ L).1 hx
  refine hL.int _ ?_ y hy
  rw [Units.val_pow_eq_pow_val, map_pow]
  exact pow_le_one' (val_le_one_of_nabs_lt ht) j

end PositivityTheory.RgUd.TP.Nil.Fib1
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.LocallyConstantCosets.PsiBiUnion
noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil
open scoped Pointwise

namespace PositivityTheory.RgUd.TP.Nil.Fib2

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Nil PositivityTheory.RgUd.TP.Nil.Fib1

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

variable {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)}

def psi (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (A : Set (Matrix (Fin n) (Fin n) k)) (h : Sp k n → ℂ)
    (p : Sp k n) : ℂ :=
  {q : Sp k n | q.1 ∈ CC Z}.indicator (fun q => A.indicator 1 (zpart Z q.1) * h (q.1 - zpart Z q.1, q.2)) p

theorem psi_of_mem {A : Set (Matrix (Fin n) (Fin n) k)} {h : Sp k n → ℂ} {p : Sp k n} (hp : p.1 ∈ CC Z) :
    psi Z A h p = A.indicator 1 (zpart Z p.1) * h (p.1 - zpart Z p.1, p.2) := by
  unfold psi
  exact Set.indicator_of_mem (s := {q : Sp k n | q.1 ∈ CC Z}) hp _

theorem psi_of_not {A : Set (Matrix (Fin n) (Fin n) k)} {h : Sp k n → ℂ} {p : Sp k n} (hp : p.1 ∉ CC Z) :
    psi Z A h p = 0 := by
  unfold psi
  exact Set.indicator_of_notMem (s := {q : Sp k n | q.1 ∈ CC Z}) hp _

def OO (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : Set (Sp k n) := {p | p.1 ∈ CC Z ∧ p.2 ≠ 0}

def tr (c : Matrix (Fin n) (Fin n) k) (p : Sp k n) : Sp k n := (p.1 + c, p.2)

theorem psi_add (A : Set (Matrix (Fin n) (Fin n) k)) (h h' : Sp k n → ℂ) :
    psi Z A (h + h') = psi Z A h + psi Z A h' := by
  funext p
  by_cases hp : p.1 ∈ CC Z
  · rw [Pi.add_apply, psi_of_mem hp, psi_of_mem hp, psi_of_mem hp, Pi.add_apply, mul_add]
  · rw [Pi.add_apply, psi_of_not hp, psi_of_not hp, psi_of_not hp, add_zero]

theorem psi_smul (A : Set (Matrix (Fin n) (Fin n) k)) (c : ℂ) (h : Sp k n → ℂ) :
    psi Z A (c • h) = c • psi Z A h := by
  funext p
  by_cases hp : p.1 ∈ CC Z
  · rw [Pi.smul_apply, psi_of_mem hp, psi_of_mem hp, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
      mul_left_comm]
  · rw [Pi.smul_apply, psi_of_not hp, psi_of_not hp, smul_zero]

theorem psi_tr (hZ : CR Z) (A : Set (Matrix (Fin n) (Fin n) k)) (h : Sp k n → ℂ) {c : Matrix (Fin n) (Fin n) k}
    (hc : c ∈ Z) : (fun p => psi Z A h (tr c p)) = psi Z ((fun a => a - c) '' A) h := by
  funext p
  have himg : ∀ z, z ∈ (fun a => a - c) '' A ↔ z + c ∈ A := fun z =>
    ⟨fun ⟨a, ha, e⟩ => by rw [← e, sub_add_cancel]; exact ha,
      fun hz => ⟨z + c, hz, add_sub_cancel_right z c⟩⟩
  by_cases hp : p.1 ∈ CC Z
  · have h1 := cc_add hZ (x := p.1) hc
    have hm : (tr c p).1 ∈ CC Z := h1.1.2 hp
    rw [psi_of_mem hm, psi_of_mem hp]
    simp only [tr, h1.2 hp, add_sub_add_right_eq_sub]
    congr 1
    by_cases hz : zpart Z p.1 + c ∈ A
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem ((himg _).2 hz), Pi.one_apply, Pi.one_apply]
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem (fun h' => hz ((himg _).1 h'))]
  · have hm : (tr c p).1 ∉ CC Z := fun h' => hp ((cc_add hZ (x := p.1) hc).1.1 h')
    rw [psi_of_not hm, psi_of_not hp]

theorem psi_hom (hZ : CR Z) (A : Set (Matrix (Fin n) (Fin n) k)) (h : Sp k n → ℂ) (t : kˣ) :
    (fun p => psi Z A h (hom t p)) = psi Z (((t⁻¹ : kˣ) : k) • A) (fun q => h (hom t q)) := by
  funext p
  have hmem : ∀ z, z ∈ ((((t⁻¹ : kˣ) : k)) • A) ↔ (t : k) • z ∈ A := fun z => by
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ (Units.ne_zero _), Units.val_inv_eq_inv_val, inv_inv]
  by_cases hp : p.1 ∈ CC Z
  · have h1 := cc_smul hZ (t : k) hp
    have hm : (hom t p).1 ∈ CC Z := h1.1
    rw [psi_of_mem hm, psi_of_mem hp]
    simp only [hom, h1.2, smul_sub]
    congr 1
    by_cases hz : (t : k) • zpart Z p.1 ∈ A
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem ((hmem _).2 hz), Pi.one_apply, Pi.one_apply]
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem (fun h' => hz ((hmem _).1 h'))]
  · have hm : (hom t p).1 ∉ CC Z := fun h' => by
      have h2 := (cc_smul hZ ((t : k)⁻¹) h').1
      change (t : k)⁻¹ • ((t : k) • p.1) ∈ CC Z at h2
      rw [inv_smul_smul₀ (Units.ne_zero t)] at h2
      exact hp h2
    rw [psi_of_not hm, psi_of_not hp]

theorem psi_act (hZ : CR Z) (A : Set (Matrix (Fin n) (Fin n) k)) (h : Sp k n → ℂ) {g : GL (Fin n) k} (hg : g ∈ Gz Z) :
    (fun p => psi Z A h (act g p)) = psi Z A (fun q => h (act g q)) := by
  funext p
  have hg' : g⁻¹ ∈ Gz Z := fun a ha => by
    have e := hg a ha
    calc a * ↑g⁻¹ = (↑g⁻¹ * ↑g) * a * ↑g⁻¹ := by rw [Units.inv_mul, one_mul]
      _ = ↑g⁻¹ * (↑g * a) * ↑g⁻¹ := by simp only [mul_assoc]
      _ = ↑g⁻¹ * (a * ↑g) * ↑g⁻¹ := by rw [e]
      _ = ↑g⁻¹ * a * (↑g * ↑g⁻¹) := by simp only [mul_assoc]
      _ = ↑g⁻¹ * a := by rw [Units.mul_inv, mul_one]
  by_cases hp : p.1 ∈ CC Z
  · have h1 := cc_conj hZ hg hp
    have hm : (act g p).1 ∈ CC Z := h1.1
    have hz := (zpart_spec hp).1
    have key : (g : Matrix (Fin n) (Fin n) k) * (p.1 - zpart Z p.1) *
        ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
        (g : Matrix (Fin n) (Fin n) k) * p.1 * ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) -
          zpart Z p.1 := by
      rw [mul_sub, sub_mul, ← hg _ hz, mul_assoc (zpart Z p.1), Units.mul_inv, mul_one]
    rw [psi_of_mem hm, psi_of_mem hp]
    simp only [act, h1.2, key]
  · have hm : (act g p).1 ∉ CC Z := fun h' => by
      have h2 := (cc_conj hZ hg' h').1
      simp only [act, inv_inv, mul_assoc, Units.inv_mul, Units.inv_mul_cancel_left,
        Units.mul_inv, mul_one] at h2
      exact hp h2
    rw [psi_of_not hm, psi_of_not hp]

theorem psi_zero (hZ : CR Z) (A : Set (Matrix (Fin n) (Fin n) k)) {h : Sp k n → ℂ}
    (h0 : ∀ p ∈ NB Z ×ˢ (Set.univ : Set (Fin n → k)), h p = 0) : psi Z A h = 0 := by
  funext p
  by_cases hp : p.1 ∈ CC Z
  · rw [psi_of_mem hp, h0 _ ⟨sub_mem_NB hZ hp, Set.mem_univ _⟩, mul_zero, Pi.zero_apply]
  · rw [psi_of_not hp, Pi.zero_apply]

end PositivityTheory.RgUd.TP.Nil.Fib2

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.LocallyConstantCosets.Imports
section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.LocallyConstantCosets.UnifLC
noncomputable section

open Matrix GroundTheory.Automorphic GroundTheory.Automorphic.Whittaker Set

namespace PositivityTheory.RgUd.TP.Nil.Fib2

open PositivityTheory.RgUd.T

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem unifLC {F : Sp k n → ℂ} (hF : F ∈ locallyConstantCompactSupport (Sp k n) ℂ ℂ) :
    ∃ W ∈ nhds (0 : Matrix (Fin n) (Fin n) k), ∀ w ∈ W, ∀ p : Sp k n, F (p.1 + w, p.2) = F p := by
  obtain ⟨hlc, hcs⟩ := hF
  have hK : IsCompact (tsupport F) := hcs
  have hc1 : Continuous fun z : Matrix (Fin n) (Fin n) k × Sp k n => ((z.2.1 + z.1, z.2.2) : Sp k n) := by
    fun_prop
  have hc2 : Continuous fun z : Matrix (Fin n) (Fin n) k × Sp k n => ((z.2.1 - z.1, z.2.2) : Sp k n) := by
    fun_prop
  have hev : ∀ᶠ w in nhds (0 : Matrix (Fin n) (Fin n) k), ∀ q ∈ tsupport F,
      F (q.1 + w, q.2) = F q ∧ F (q.1 - w, q.2) = F q := by
    refine hK.eventually_forall_of_forall_eventually ?_
    intro q _
    have e1 := (hlc.comp_continuous hc1).eventually_eq ((0 : Matrix (Fin n) (Fin n) k), q)
    have e2 := (hlc.comp_continuous hc2).eventually_eq ((0 : Matrix (Fin n) (Fin n) k), q)
    have e3 := (hlc.comp_continuous continuous_snd).eventually_eq ((0 : Matrix (Fin n) (Fin n) k), q)
    filter_upwards [e1, e2, e3] with z h1 h2 h3
    simp only [Function.comp_apply, add_zero, sub_zero] at h1 h2 h3
    exact ⟨by rw [h1, h3], by rw [h2, h3]⟩
  refine ⟨_, hev, ?_⟩
  intro w hw p
  by_cases hp : p ∈ tsupport F
  · exact (hw p hp).1
  · have h0 : F p = 0 := image_eq_zero_of_notMem_tsupport hp
    by_cases hp' : ((p.1 + w, p.2) : Sp k n) ∈ tsupport F
    · have := (hw _ hp').2
      simp only [add_sub_cancel_right] at this
      rw [h0] at this ⊢
      exact this.symm
    · rw [h0]
      exact image_eq_zero_of_notMem_tsupport hp'

end PositivityTheory.RgUd.TP.Nil.Fib2

end
end

noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil
open scoped Pointwise

namespace PositivityTheory.RgUd.TP.Nil.Fib2

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Nil PositivityTheory.RgUd.TP.Nil.Fib1

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
  {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)}

theorem dec (hZ : CR Z) {L : AddSubgroup (Matrix (Fin n) (Fin n) k)} (hL : IsLat Z L) {t : kˣ}
    (ht : nabs k t < 1) {F : Sp k n → ℂ} (hF : F ∈ supportedIn (UU : Set (Sp k n))) :
    ∃ (j : ℕ) (S : Finset (Matrix (Fin n) (Fin n) k)), (∀ c ∈ S, c ∈ Z) ∧
      ∀ p ∈ OO Z, F p = ∑ c ∈ S, psi Z ((fun a => a + c) '' ((((t ^ j : kˣ) : k) • L : AddSubgroup _) : Set _))
        (fun q => F (tr c q)) p := by
  classical
  obtain ⟨W, hW, hWF⟩ := unifLC hF.1
  obtain ⟨j, hj⟩ := lat_small hL ht hW
  have hLat' : IsLat Z ((((t ^ j : kˣ) : k) • L : AddSubgroup (Matrix (Fin n) (Fin n) k))) := isLat_smul hL (t ^ j)
  set L' : AddSubgroup (Matrix (Fin n) (Fin n) k) := (((t ^ j : kˣ) : k) • L) with hLe
  have hL'W : ∀ w ∈ L', w ∈ W := fun w hw => hj (by rw [← AddSubgroup.coe_pointwise_smul]; exact hw)
  obtain ⟨U, hUo, hU0, hUZ⟩ := hLat'.nhd
  have hK : IsCompact (Prod.fst '' tsupport F) := hF.1.2.image continuous_fst
  obtain ⟨S0, hS0, hS0Z, hS0K⟩ := exists_cpt hZ hK
  obtain ⟨S1, hS1⟩ := hS0.elim_finite_subcover (fun c : S0 => (fun a => a + (c : Matrix (Fin n) (Fin n) k)) '' U)
    (fun c => isOpenMap_add_right _ U hUo) (fun s hs => Set.mem_iUnion.2 ⟨⟨s, hs⟩, 0, hU0, zero_add s⟩)
  let g : Matrix (Fin n) (Fin n) k → Matrix (Fin n) (Fin n) k :=
    fun c => Quotient.out (QuotientAddGroup.mk c : Matrix (Fin n) (Fin n) k ⧸ L')
  have hg : ∀ c, g c - c ∈ L' := by
    intro c
    have h1 := QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' (QuotientAddGroup.mk c : Matrix (Fin n) (Fin n) k ⧸ L'))
    have h2 : g c - c = -(-(g c) + c) := by abel
    rw [h2]
    exact L'.neg_mem h1
  have hgeq : ∀ c c', c - c' ∈ L' → g c = g c' := by
    intro c c' h
    show Quotient.out _ = Quotient.out _
    congr 1
    refine QuotientAddGroup.eq.2 ?_
    rw [show -c + c' = -(c - c') by abel]
    exact L'.neg_mem h
  have hgg : ∀ a a', g a - g a' ∈ L' → g a = g a' := by
    intro a a' h
    apply hgeq
    have e : a - a' = (g a - g a') - (g a - a) + (g a' - a') := by abel
    rw [e]
    exact L'.add_mem (L'.sub_mem h (hg a)) (hg a')
  have hmemI : ∀ z c, z ∈ (fun a => a + c) '' (L' : Set (Matrix (Fin n) (Fin n) k)) ↔ z - c ∈ L' := by
    intro z c
    constructor
    · rintro ⟨m, hm, rfl⟩
      simpa using hm
    · intro hz
      exact ⟨z - c, hz, by simp⟩
  refine ⟨j, S1.image (fun c : S0 => g (c : Matrix (Fin n) (Fin n) k)), ?_, ?_⟩
  · intro c hc
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hc
    have e : g (i : Matrix (Fin n) (Fin n) k) = (i : Matrix (Fin n) (Fin n) k) + (g i - i) := by abel
    rw [e]
    exact Z.add_mem (hS0Z i.2) (hLat'.sub (hg _))
  · rintro ⟨x, v⟩ hp
    have hx : x ∈ CC Z := hp.1
    simp only [psi_of_mem (p := (x, v)) hx, tr]
    by_cases hA : ∃ c ∈ S1.image (fun c : S0 => g (c : Matrix (Fin n) (Fin n) k)), zpart Z x - c ∈ L'
    · obtain ⟨c, hcS, hcz⟩ := hA
      rw [Finset.sum_eq_single c]
      · rw [Set.indicator_of_mem ((hmemI _ _).2 hcz), Pi.one_apply, one_mul]
        have e : x - zpart Z x + c = x + (c - zpart Z x) := by abel
        rw [e]
        have hw : c - zpart Z x ∈ L' := by
          rw [show c - zpart Z x = -(zpart Z x - c) by abel]
          exact L'.neg_mem hcz
        exact (hWF _ (hL'W _ hw) (x, v)).symm
      · intro c' hc' hne
        rw [Set.indicator_of_notMem, zero_mul]
        intro h'
        apply hne
        obtain ⟨a', _, rfl⟩ := Finset.mem_image.1 hc'
        obtain ⟨a, _, rfl⟩ := Finset.mem_image.1 hcS
        apply hgg
        have e : g (a' : Matrix (Fin n) (Fin n) k) - g a = (zpart Z x - g a) - (zpart Z x - g a') := by abel
        rw [e]
        exact L'.sub_mem hcz ((hmemI _ _).1 h')
      · intro h
        exact absurd hcS h
    · push_neg at hA
      rw [Finset.sum_eq_zero]
      · by_contra hne
        have hsupp : (x, v) ∈ tsupport F := subset_tsupport F hne
        have hz := hS0K x ⟨⟨(x, v), hsupp, rfl⟩, hx⟩
        obtain ⟨i, hi, hzi⟩ := Set.mem_iUnion₂.1 (hS1 hz)
        obtain ⟨u, hu, hue⟩ := hzi
        simp only at hue
        have huZ : u ∈ Z := by
          have e : u = zpart Z x - i := by rw [← hue]; abel
          rw [e]
          exact Z.sub_mem (hS0Z hz) (hS0Z i.2)
        have huL : u ∈ L' := hUZ ⟨hu, huZ⟩
        apply hA (g i) (Finset.mem_image.2 ⟨i, hi, rfl⟩)
        have e : zpart Z x - g i = u - (g i - i) := by rw [← hue]; abel
        rw [e]
        exact L'.sub_mem huL (hg _)
      · intro c hc
        rw [Set.indicator_of_notMem, zero_mul]
        intro h'
        exact hA c hc ((hmemI _ _).1 h')

end PositivityTheory.RgUd.TP.Nil.Fib2

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.LocallyConstantCosets.ExistsLiftOfLatticeAverage
section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.LocallyConstantCosets.PsiCosets
noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil
open scoped Pointwise

namespace PositivityTheory.RgUd.TP.Nil.Fib2

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Nil PositivityTheory.RgUd.TP.Nil.Fib1

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
  {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)}

theorem psi_cosets {L M : AddSubgroup (Matrix (Fin n) (Fin n) k)} (hL : IsLat Z L) (hM : IsLat Z M) (hML : M ≤ L) :
    ∃ D : Finset (Matrix (Fin n) (Fin n) k), D.card = M.relIndex L ∧ (∀ d ∈ D, d ∈ L) ∧
      ∀ h : Sp k n → ℂ, psi Z (L : Set (Matrix (Fin n) (Fin n) k)) h =
        ∑ d ∈ D, psi Z ((fun a => a + d) '' (M : Set (Matrix (Fin n) (Fin n) k))) h := by
  classical
  have hfi : (M.addSubgroupOf L).FiniteIndex := ⟨lat_index_pos hL hM hML⟩
  haveI : Fintype (L ⧸ M.addSubgroupOf L) := Fintype.ofFinite _
  let f : (L ⧸ M.addSubgroupOf L) → Matrix (Fin n) (Fin n) k := fun q => ((Quotient.out q : L) : Matrix (Fin n) (Fin n) k)
  have hf : Function.Injective f := fun a b hab => Quotient.out_inj.1 (Subtype.ext hab)
  have hmem : ∀ z q, z ∈ (fun a => a + f q) '' (M : Set (Matrix (Fin n) (Fin n) k)) ↔ z - f q ∈ M := by
    intro z q
    constructor
    · rintro ⟨m, hm, rfl⟩
      simpa using hm
    · intro hz
      exact ⟨z - f q, hz, by simp⟩
  have key : ∀ z, (L : Set (Matrix (Fin n) (Fin n) k)).indicator (1 : Matrix (Fin n) (Fin n) k → ℂ) z =
      ∑ d ∈ Finset.univ.image f, ((fun a => a + d) '' (M : Set (Matrix (Fin n) (Fin n) k))).indicator 1 z := by
    intro z
    rw [Finset.sum_image (fun a _ b _ hab => hf hab)]
    by_cases hz : z ∈ L
    · rw [Set.indicator_of_mem (show z ∈ (L : Set (Matrix (Fin n) (Fin n) k)) from hz)]
      have hq : ∀ q, ((fun a => a + f q) '' (M : Set (Matrix (Fin n) (Fin n) k))).indicator
          (1 : Matrix (Fin n) (Fin n) k → ℂ) z =
          if (QuotientAddGroup.mk ⟨z, hz⟩ : L ⧸ M.addSubgroupOf L) = q then 1 else 0 := by
        intro q
        have e : z - f q ∈ M ↔ (QuotientAddGroup.mk ⟨z, hz⟩ : L ⧸ M.addSubgroupOf L) =
            QuotientAddGroup.mk (Quotient.out q) := by
          rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
          show z - f q ∈ M ↔ -z + f q ∈ M
          rw [show -z + f q = -(z - f q) by abel, neg_mem_iff]
        rw [QuotientAddGroup.out_eq'] at e
        by_cases h : (QuotientAddGroup.mk ⟨z, hz⟩ : L ⧸ M.addSubgroupOf L) = q
        · rw [if_pos h, Set.indicator_of_mem ((hmem z q).2 (e.2 h))]
          rfl
        · rw [if_neg h, Set.indicator_of_notMem (fun h' => h (e.1 ((hmem z q).1 h')))]
      simp only [hq, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rfl
    · rw [Set.indicator_of_notMem (show z ∉ (L : Set (Matrix (Fin n) (Fin n) k)) from hz)]
      symm
      apply Finset.sum_eq_zero
      intro q _
      apply Set.indicator_of_notMem
      intro h'
      apply hz
      have h2 : z = (z - f q) + f q := by abel
      rw [h2]
      exact L.add_mem (hML ((hmem z q).1 h')) (Quotient.out q).2
  refine ⟨Finset.univ.image f, ?_, ?_, fun h => funext fun p => ?_⟩
  · rw [Finset.card_image_of_injective _ hf, Finset.card_univ, ← Nat.card_eq_fintype_card]
    rfl
  · intro d hd
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.1 hd
    exact (Quotient.out q).2
  · rw [Finset.sum_apply]
    by_cases hp : p.1 ∈ CC Z
    · simp only [psi, Set.indicator_of_mem (show p ∈ {q : Sp k n | q.1 ∈ CC Z} from hp)]
      rw [key, Finset.sum_mul]
    · simp only [psi, Set.indicator_of_notMem (show p ∉ {q : Sp k n | q.1 ∈ CC Z} from hp), Finset.sum_const_zero]

end PositivityTheory.RgUd.TP.Nil.Fib2

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.LocallyConstantCosets.LcIndicator
noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil
open scoped Pointwise

namespace PositivityTheory.RgUd.TP.Nil.Fib2

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Nil PositivityTheory.RgUd.TP.Nil.Fib1

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
  {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)}

theorem lc_indicator {X : Type*} [TopologicalSpace X] {S : Set X} (hS : IsClopen S) (c : ℂ) :
    IsLocallyConstant (S.indicator fun _ => c) := by
  intro s
  by_cases h1 : c ∈ s <;> by_cases h0 : (0 : ℂ) ∈ s
  · convert isOpen_univ using 1
    ext x; by_cases hx : x ∈ S <;> simp [Set.indicator, hx, h1, h0]
  · convert hS.isOpen using 1
    ext x; by_cases hx : x ∈ S <;> simp [Set.indicator, hx, h1, h0]
  · convert hS.isClosed.isOpen_compl using 1
    ext x; by_cases hx : x ∈ S <;> simp [Set.indicator, hx, h1, h0]
  · convert isOpen_empty using 1
    ext x; by_cases hx : x ∈ S <;> simp [Set.indicator, hx, h1, h0]

theorem psi_lift (hZ : CR Z) {A : Set (Matrix (Fin n) (Fin n) k)} (hAZ : A ⊆ Z) (hAc : IsCompact A)
    (hAo : ∀ a ∈ A, ∃ U : Set (Matrix (Fin n) (Fin n) k), IsOpen U ∧ a ∈ U ∧ U ∩ Z ⊆ A)
    {h : Sp k n → ℂ} (hh : h ∈ supportedIn (UU : Set (Sp k n))) :
    ∃ f ∈ supportedIn (UU : Set (Sp k n)), ∀ p ∈ OO Z, f p = psi Z A h p := by
  classical
  haveI : TotallyDisconnectedSpace k := totallyDisconnectedSpace_localField
  haveI : T2Space k := GlobalTheory.SplitWeil.t2Space k
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) k) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → k))
  haveI : TotallyDisconnectedSpace (Matrix (Fin n) (Fin n) k) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin n → Fin n → k))
  haveI : T2Space (Matrix (Fin n) (Fin n) k) := inferInstanceAs (T2Space (Fin n → Fin n → k))
  have hUU : IsOpen (UU : Set (Sp k n)) := isOpen_ne_fun continuous_snd continuous_const
  have hOU : OO Z ⊆ UU := fun p hp => hp.2
  have hhl : IsLocallyConstant h := (GroundTheory.Automorphic.mem_locallyConstantCompactSupport.1 hh.1).1
  have hhc : HasCompactSupport h := (GroundTheory.Automorphic.mem_locallyConstantCompactSupport.1 hh.1).2

  have hg1 : Continuous (fun p : OO Z => zpart Z (p : Sp k n).1) :=
    (continuousOn_zpart hZ).comp_continuous (continuous_fst.comp continuous_subtype_val) fun p => p.2.1
  have hg2 : Continuous (fun p : OO Z => (((p : Sp k n).1 - zpart Z (p : Sp k n).1, (p : Sp k n).2) : Sp k n)) :=
    ((continuous_fst.comp continuous_subtype_val).sub hg1).prodMk (continuous_snd.comp continuous_subtype_val)

  set S : Set (OO Z) := {p | zpart Z (p : Sp k n).1 ∈ A} with hSdef
  have hSc : IsClosed S := hAc.isClosed.preimage hg1
  have hSo : IsOpen S := by
    rw [isOpen_iff_forall_mem_open]
    intro p hp
    obtain ⟨U, hU, hpU, hUA⟩ := hAo _ hp
    refine ⟨(fun q : OO Z => zpart Z (q : Sp k n).1) ⁻¹' U, fun q hq => hUA ⟨hq, (zpart_spec q.2.1).1⟩,
      hU.preimage hg1, hpU⟩
  have hphi : (fun p : OO Z => psi Z A h p) =
      fun p => S.indicator (fun _ => (1 : ℂ)) p * h (((p : Sp k n).1 - zpart Z (p : Sp k n).1, (p : Sp k n).2)) := by
    funext p
    rw [psi_of_mem p.2.1]
    by_cases hp : p ∈ S
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem (show zpart Z (p : Sp k n).1 ∈ A from hp)]; rfl
    · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem (show zpart Z (p : Sp k n).1 ∉ A from hp)]

  have hsupp_cl : IsClosed (Function.support h) := by
    have : Function.support h = (h ⁻¹' {0})ᶜ := by ext x; simp [Function.mem_support]
    rw [this]
    exact (hhl.isOpen_fiber 0).isClosed_compl
  have hts : tsupport h ⊆ UU := by
    rw [tsupport, hsupp_cl.closure_eq]; exact hh.2

  set K : Set (Matrix (Fin n) (Fin n) k × Sp k n) := A ×ˢ (tsupport h ∩ (NB Z ×ˢ Set.univ)) with hK
  have hKc : IsCompact K := hAc.prod (hhc.inter_right ((isClosed_NB Z).prod isClosed_univ))
  set Φ : Matrix (Fin n) (Fin n) k × Sp k n → Sp k n := fun aq => (aq.1 + aq.2.1, aq.2.2) with hΦ
  have hΦc : Continuous Φ := (continuous_fst.add (continuous_fst.comp continuous_snd)).prodMk
    (continuous_snd.comp continuous_snd)
  have hΦO : Φ '' K ⊆ OO Z := by
    rintro _ ⟨⟨a, q⟩, ⟨ha, hq, hqN⟩, rfl⟩
    have h2 : q.2 ≠ 0 := hts hq
    exact ⟨(cc_of_NB hZ (hAZ ha) hqN.1).1, h2⟩
  set Kc : Set (OO Z) := (Subtype.val : OO Z → Sp k n) ⁻¹' (Φ '' K) with hKcdef
  have hKcc : IsCompact Kc := by
    rw [Subtype.isCompact_iff, Set.image_preimage_eq_inter_range, Subtype.range_coe,
      Set.inter_eq_left.2 hΦO]
    exact hKc.image hΦc
  have hsub : Function.support (fun p : OO Z => psi Z A h p) ⊆ Kc := by
    intro p hp
    rw [hphi, Function.mem_support] at hp
    have hpS : p ∈ S := by
      by_contra hn; rw [Set.indicator_of_notMem hn, zero_mul] at hp; exact hp rfl
    have hq : h (((p : Sp k n).1 - zpart Z (p : Sp k n).1, (p : Sp k n).2)) ≠ 0 := by
      rw [Set.indicator_of_mem hpS, one_mul] at hp; exact hp
    refine ⟨(zpart Z (p : Sp k n).1, (((p : Sp k n).1 - zpart Z (p : Sp k n).1, (p : Sp k n).2))),
      ⟨hpS, subset_tsupport _ hq, sub_mem_NB hZ p.2.1, Set.mem_univ _⟩, ?_⟩
    simp only [hΦ, add_sub_cancel]
  obtain ⟨f, hf, hfe⟩ := GroundTheory.Automorphic.Whittaker.exists_lift hUU hOU (φ := fun p : OO Z => psi Z A h p) (by
    rw [GroundTheory.Automorphic.mem_locallyConstantCompactSupport]
    refine ⟨?_, ?_⟩
    · rw [hphi]
      exact IsLocallyConstant.comp₂ (lc_indicator ⟨hSc, hSo⟩ 1) (hhl.comp_continuous hg2) (· * ·)
    · exact IsCompact.of_isClosed_subset hKcc isClosed_closure (closure_minimal hsub hKcc.isClosed))
  exact ⟨f, hf, fun p hp => hfe ⟨p, hp⟩⟩

end PositivityTheory.RgUd.TP.Nil.Fib2

end
end

noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil
open scoped Pointwise

namespace PositivityTheory.RgUd.TP.Nil.Fib2

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Nil PositivityTheory.RgUd.TP.Nil.Fib1

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
  {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)}

theorem comp_mem {e : Sp k n ≃ₜ Sp k n} (he : ∀ p, (e p).2 ≠ 0 → p.2 ≠ 0) {f : Sp k n → ℂ}
    (hf : f ∈ supportedIn (UU : Set (Sp k n))) : (fun p => f (e p)) ∈ supportedIn (UU : Set (Sp k n)) := by
  obtain ⟨⟨hlc, hcs⟩, hsu⟩ := hf
  refine ⟨⟨hlc.comp_continuous e.continuous, hcs.comp_homeomorph e⟩, ?_⟩
  intro p hp
  exact he p (hsu hp)

theorem comp_mem_univ {e : Sp k n ≃ₜ Sp k n} {f : Sp k n → ℂ}
    (hf : f ∈ supportedIn (Set.univ : Set (Sp k n))) : (fun p => f (e p)) ∈ supportedIn (Set.univ : Set (Sp k n)) := by
  obtain ⟨⟨hlc, hcs⟩, -⟩ := hf
  exact ⟨⟨hlc.comp_continuous e.continuous, hcs.comp_homeomorph e⟩, Set.subset_univ _⟩

def trH (c : Matrix (Fin n) (Fin n) k) : Sp k n ≃ₜ Sp k n := Homeomorph.addRight ((c, 0) : Sp k n)

theorem trH_apply (c : Matrix (Fin n) (Fin n) k) (p : Sp k n) : trH c p = tr c p :=
  Prod.ext rfl (add_zero p.2)

def homH (t : kˣ) : Sp k n ≃ₜ Sp k n :=
  Homeomorph.prodCongr (Homeomorph.smulOfNeZero (t : k) t.ne_zero) (Homeomorph.refl _)

def actH (g : GL (Fin n) k) : Sp k n ≃ₜ Sp k n where
  toFun := act g
  invFun := act g⁻¹
  left_inv p := Prod.ext (by simp [act, mul_assoc]) (by simp [act, Matrix.mulVec_mulVec])
  right_inv p := Prod.ext (by simp [act, mul_assoc]) (by simp [act, Matrix.mulVec_mulVec])
  continuous_toFun := by
    unfold act
    exact ((continuous_const.matrix_mul continuous_fst).matrix_mul continuous_const).prodMk
      (continuous_const.matrix_mulVec continuous_snd)
  continuous_invFun := by
    unfold act
    exact ((continuous_const.matrix_mul continuous_fst).matrix_mul continuous_const).prodMk
      (continuous_const.matrix_mulVec continuous_snd)

theorem tr_mem {f : Sp k n → ℂ} (hf : f ∈ supportedIn (UU : Set (Sp k n))) (c : Matrix (Fin n) (Fin n) k) :
    (fun p => f (tr c p)) ∈ supportedIn (UU : Set (Sp k n)) := by
  have key := comp_mem (e := trH c) (fun p hp => by simpa [trH_apply, tr] using hp) hf
  simpa [trH_apply] using key

theorem hom_mem {f : Sp k n → ℂ} (hf : f ∈ supportedIn (UU : Set (Sp k n))) (t : kˣ) :
    (fun p => f (hom t p)) ∈ supportedIn (UU : Set (Sp k n)) :=
  comp_mem (e := homH t) (fun p hp => hp) hf

theorem act_mem {f : Sp k n → ℂ} (hf : f ∈ supportedIn (UU : Set (Sp k n))) (g : GL (Fin n) k) :
    (fun p => f (act g p)) ∈ supportedIn (UU : Set (Sp k n)) := by
  refine comp_mem (e := actH g) (fun p hp h0 => hp ?_) hf
  show g.val *ᵥ p.2 = 0
  rw [h0, Matrix.mulVec_zero]

def Good (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (ζ : (Sp k n → ℂ) →ₗ[ℂ] ℂ) : Prop :=
  TranslInv Z ζ ∧ SuppU ζ (CC Z ×ˢ Set.univ)

theorem agree {ζ : (Sp k n → ℂ) →ₗ[ℂ] ℂ} (hs : SuppU ζ (CC Z ×ˢ Set.univ)) {f f' : Sp k n → ℂ}
    (hf : f ∈ supportedIn (UU : Set (Sp k n))) (hf' : f' ∈ supportedIn (UU : Set (Sp k n)))
    (h : ∀ p ∈ OO Z, f p = f' p) : ζ f = ζ f' := by
  have hsub : f - f' ∈ supportedIn (UU : Set (Sp k n)) := Submodule.sub_mem _ hf hf'
  have hz := hs (f - f') hsub (by
    rintro p ⟨hp1, -⟩
    by_cases hp2 : p.2 = 0
    · have h1 : f p = 0 := by
        by_contra hne
        exact hf.2 hne hp2
      have h2 : f' p = 0 := by
        by_contra hne
        exact hf'.2 hne hp2
      simp [h1, h2]
    · simp [h ⟨p.1, p.2⟩ ⟨hp1, hp2⟩])
  rw [map_sub, sub_eq_zero] at hz
  exact hz

theorem good_tr {ζ : (Sp k n → ℂ) →ₗ[ℂ] ℂ} (hg : Good Z ζ) {c : Matrix (Fin n) (Fin n) k} (hc : c ∈ Z)
    {f : Sp k n → ℂ} (hf : f ∈ supportedIn (UU : Set (Sp k n))) : ζ (fun p => f (tr c p)) = ζ f := by
  exact hg.1 c hc f ⟨hf.1, Set.subset_univ _⟩

theorem coset_ok {M : AddSubgroup (Matrix (Fin n) (Fin n) k)} (hM : IsLat Z M) {c : Matrix (Fin n) (Fin n) k}
    (hc : c ∈ Z) :
    (fun a => a + c) '' (M : Set (Matrix (Fin n) (Fin n) k)) ⊆ Z ∧
      IsCompact ((fun a => a + c) '' (M : Set (Matrix (Fin n) (Fin n) k))) ∧
      ∀ a ∈ (fun a => a + c) '' (M : Set (Matrix (Fin n) (Fin n) k)), ∃ U : Set (Matrix (Fin n) (Fin n) k),
        IsOpen U ∧ a ∈ U ∧ U ∩ Z ⊆ (fun a => a + c) '' (M : Set (Matrix (Fin n) (Fin n) k)) := by
  refine ⟨?_, hM.cpt.image (continuous_id.add continuous_const), ?_⟩
  · rintro _ ⟨m, hm, rfl⟩
    exact Z.add_mem (hM.sub hm) hc
  · rintro _ ⟨m, hm, rfl⟩
    obtain ⟨U0, hU0, h0, hU0Z⟩ := hM.nhd
    have hmZ : m + c ∈ Z := Z.add_mem (hM.sub hm) hc
    refine ⟨(fun x => x - (m + c)) ⁻¹' U0, hU0.preimage (continuous_sub_right _), by simpa using h0, ?_⟩
    rintro x ⟨hxU, hxZ⟩
    have hxM : x - (m + c) ∈ M := hU0Z ⟨hxU, Z.sub_mem hxZ hmZ⟩
    refine ⟨x - (m + c) + m, M.add_mem hxM hm, ?_⟩
    show x - (m + c) + m + c = x
    abel

theorem lift_ex (hZ : CR Z) {M : AddSubgroup (Matrix (Fin n) (Fin n) k)} (hM : IsLat Z M) {c : Matrix (Fin n) (Fin n) k}
    (hc : c ∈ Z) {h : Sp k n → ℂ} (hh : h ∈ supportedIn (UU : Set (Sp k n))) :
    ∃ f ∈ supportedIn (UU : Set (Sp k n)), ∀ p ∈ OO Z,
      f p = psi Z ((fun a => a + c) '' (M : Set (Matrix (Fin n) (Fin n) k))) h p := by
  obtain ⟨h1, h2, h3⟩ := coset_ok hM hc
  exact psi_lift hZ h1 h2 h3 hh

theorem image_add_zero (M : Set (Matrix (Fin n) (Fin n) k)) : (fun a => a + (0 : Matrix (Fin n) (Fin n) k)) '' M = M := by
  simp

theorem exists_lift_of_lattice_average (hZ : CR Z) {M : AddSubgroup (Matrix (Fin n) (Fin n) k)} (hM : IsLat Z M) {h : Sp k n → ℂ}
    (hh : h ∈ supportedIn (UU : Set (Sp k n))) :
    ∃ f ∈ supportedIn (UU : Set (Sp k n)), ∀ p ∈ OO Z, f p = psi Z (M : Set (Matrix (Fin n) (Fin n) k)) h p := by
  have key := lift_ex hZ hM (c := 0) Z.zero_mem hh
  rwa [image_add_zero] at key

theorem tr_OO (hZ : CR Z) {c : Matrix (Fin n) (Fin n) k} (hc : c ∈ Z) {p : Sp k n} (hp : p ∈ OO Z) : tr c p ∈ OO Z :=
  ⟨(cc_add hZ hc).1.2 hp.1, hp.2⟩

theorem ind (hZ : CR Z) {ζ : (Sp k n → ℂ) →ₗ[ℂ] ℂ} (hg : Good Z ζ) {L M : AddSubgroup (Matrix (Fin n) (Fin n) k)}
    (hL : IsLat Z L) (hM : IsLat Z M) (hML : M ≤ L) {h : Sp k n → ℂ} (hh : h ∈ supportedIn (UU : Set (Sp k n)))
    {fL fM : Sp k n → ℂ} (hfL : fL ∈ supportedIn (UU : Set (Sp k n))) (hfM : fM ∈ supportedIn (UU : Set (Sp k n)))
    (eL : ∀ p ∈ OO Z, fL p = psi Z (L : Set (Matrix (Fin n) (Fin n) k)) h p)
    (eM : ∀ p ∈ OO Z, fM p = psi Z (M : Set (Matrix (Fin n) (Fin n) k)) h p) :
    ζ fL = (M.relIndex L : ℂ) * ζ fM := by
  obtain ⟨D, hcard, hDL, hpsi⟩ := psi_cosets hL hM hML
  have hlift : ∀ d ∈ D, ∃ f ∈ supportedIn (UU : Set (Sp k n)), ∀ p ∈ OO Z,
      f p = psi Z ((fun a => a + d) '' (M : Set (Matrix (Fin n) (Fin n) k))) h p :=
    fun d hd => lift_ex hZ hM (hL.sub (hDL d hd)) hh
  choose! F hFmem hFeq using hlift
  have hsum : ζ fL = ζ (∑ d ∈ D, F d) := by
    refine agree hg.2 hfL (Submodule.sum_mem _ fun d hd => hFmem d hd) ?_
    intro p hp
    rw [eL p hp, hpsi h, Finset.sum_apply, Finset.sum_apply]
    exact Finset.sum_congr rfl fun d hd => (hFeq d hd p hp).symm
  have hterm : ∀ d ∈ D, ζ (F d) = ζ fM := by
    intro d hd
    have hcZ : d ∈ Z := hL.sub (hDL d hd)
    have e1 : ∀ p, psi Z (M : Set (Matrix (Fin n) (Fin n) k)) h p =
        psi Z ((fun a => a + d) '' (M : Set (Matrix (Fin n) (Fin n) k))) h (tr d p) := by
      intro p
      have key := congrFun (psi_tr hZ ((fun a => a + d) '' (M : Set (Matrix (Fin n) (Fin n) k))) h hcZ) p
      rw [key, Set.image_image]
      simp only [add_sub_cancel_right, Set.image_id']
    have e2 : ζ fM = ζ (fun p => F d (tr d p)) := by
      refine agree hg.2 hfM (tr_mem (hFmem d hd) d) ?_
      intro p hp
      rw [eM p hp, hFeq d hd _ (tr_OO hZ hcZ hp), e1]
    rw [e2, good_tr hg hcZ (hFmem d hd)]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hsum, map_sum, Finset.sum_congr rfl hterm, Finset.sum_const, hcard, nsmul_eq_mul]

theorem scale (hZ : CR Z) {ζ : (Sp k n → ℂ) →ₗ[ℂ] ℂ} (hg : Good Z ζ) {L : AddSubgroup (Matrix (Fin n) (Fin n) k)}
    (hL : IsLat Z L) {t : kˣ} (ht : nabs k t < 1) {h : Sp k n → ℂ} (hh : h ∈ supportedIn (UU : Set (Sp k n)))
    {f f' : Sp k n → ℂ} (hf : f ∈ supportedIn (UU : Set (Sp k n))) (hf' : f' ∈ supportedIn (UU : Set (Sp k n)))
    (e : ∀ p ∈ OO Z, f p = psi Z (L : Set (Matrix (Fin n) (Fin n) k)) h p)
    (e' : ∀ p ∈ OO Z, f' p = psi Z (L : Set (Matrix (Fin n) (Fin n) k)) (fun q => h (hom t q)) p) :
    ζ (fun p => f (hom t p)) = (((nabs k t)⁻¹ ^ Module.finrank k Z : ℝ) : ℂ) * ζ f' := by
  have hL' : IsLat Z (t⁻¹.val • L) := isLat_smul hL t⁻¹
  have hle : L ≤ t⁻¹.val • L := lat_le_inv hL ht
  have hh' : (fun q => h (hom t q)) ∈ supportedIn (UU : Set (Sp k n)) := hom_mem hh t
  have hg' : (fun p => f (hom t p)) ∈ supportedIn (UU : Set (Sp k n)) := hom_mem hf t
  have eg : ∀ p ∈ OO Z, (fun p => f (hom t p)) p =
      psi Z ((t⁻¹.val • L : AddSubgroup (Matrix (Fin n) (Fin n) k)) : Set (Matrix (Fin n) (Fin n) k))
        (fun q => h (hom t q)) p := by
    intro p hp
    have hp' : hom t p ∈ OO Z := ⟨(cc_smul hZ (t : k) hp.1).1, hp.2⟩
    have key := congrFun (psi_hom hZ (L : Set (Matrix (Fin n) (Fin n) k)) h t) p
    simp only at key ⊢
    rw [e _ hp', key, AddSubgroup.coe_pointwise_smul]
  have main := ind hZ hg hL' hL hle hh' hg' hf' eg e'
  rw [main]
  congr 1
  rw [← lat_index_smul hL t ht]
  push_cast
  rfl

end PositivityTheory.RgUd.TP.Nil.Fib2

end
end

noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil
open scoped Pointwise

namespace PositivityTheory.RgUd.TP.Nil.Fib2

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Nil PositivityTheory.RgUd.TP.Nil.Fib1

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
  {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)}

theorem lemB (hZ : CR Z) {ζ : (Sp k n → ℂ) →ₗ[ℂ] ℂ} (hg : Good Z ζ) {L : AddSubgroup (Matrix (Fin n) (Fin n) k)}
    (hL : IsLat Z L) {t : kˣ} (ht : nabs k t < 1)
    (h0 : ∀ h ∈ supportedIn (UU : Set (Sp k n)), ∀ f ∈ supportedIn (UU : Set (Sp k n)),
      (∀ p ∈ OO Z, f p = psi Z (L : Set (Matrix (Fin n) (Fin n) k)) h p) → ζ f = 0) :
    ∀ F ∈ supportedIn (UU : Set (Sp k n)), ζ F = 0 := by
  classical
  intro F hFm
  obtain ⟨j, S, hSZ, hF⟩ := dec hZ hL ht hFm
  have hM : IsLat Z (((t ^ j : kˣ) : k) • L) := isLat_smul hL (t ^ j)
  have hML : ((t ^ j : kˣ) : k) • L ≤ L := lat_smul_le hL ht j
  have hex : ∀ c, c ∈ S → ∃ g ∈ supportedIn (UU : Set (Sp k n)), ∀ p ∈ OO Z,
      g p = psi Z ((((t ^ j : kˣ) : k) • L : AddSubgroup _) : Set (Matrix (Fin n) (Fin n) k))
        (fun q => F (tr c q)) p := fun c _ => exists_lift_of_lattice_average hZ hM (tr_mem hFm c)
  choose! g hgm hge using hex
  have hz : ∀ c ∈ S, ζ (g c) = 0 := by
    intro c hc
    obtain ⟨fL, hfL, efL⟩ := exists_lift_of_lattice_average hZ hL (tr_mem hFm c)
    have e := ind hZ hg hL hM hML (tr_mem hFm c) hfL (hgm c hc) efL (hge c hc)
    rw [h0 _ (tr_mem hFm c) fL hfL efL] at e
    have hne : ((((t ^ j : kˣ) : k) • L).relIndex L : ℂ) ≠ 0 := by
      exact_mod_cast lat_index_pos hL hM hML
    exact ((mul_eq_zero.1 e.symm).resolve_left hne)
  let G : Sp k n → ℂ := ∑ c ∈ S, fun p => g c (tr (-c) p)
  have hGm : G ∈ supportedIn (UU : Set (Sp k n)) := Submodule.sum_mem _ fun c hc => tr_mem (hgm c hc) _
  have e1 : ζ F = ζ G := by
    refine agree hg.2 hFm hGm fun p hp => ?_
    rw [hF p hp]
    simp only [G, Finset.sum_apply]
    refine Finset.sum_congr rfl fun c hc => ?_
    have hcZ : -c ∈ Z := Z.neg_mem (hSZ c hc)
    rw [hge c hc _ (tr_OO hZ hcZ hp)]
    have := congrFun (psi_tr hZ ((((t ^ j : kˣ) : k) • L : AddSubgroup _) : Set (Matrix (Fin n) (Fin n) k))
      (fun q => F (tr c q)) hcZ) p
    rw [this]
    congr 2
    funext a
    rw [sub_neg_eq_add]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e1, map_sum]
  refine Finset.sum_eq_zero fun c hc => ?_
  rw [good_tr hg (Z.neg_mem (hSZ c hc)) (hgm c hc)]
  exact hz c hc

theorem good_sub {ζ ζ' : (Sp k n → ℂ) →ₗ[ℂ] ℂ} (h : Good Z ζ) (h' : Good Z ζ') : Good Z (ζ - ζ') :=
  ⟨fun z hz f hf => by simp [h.1 z hz f hf, h'.1 z hz f hf],
    fun f hf h0 => by simp [h.2 f hf h0, h'.2 f hf h0]⟩

theorem good_smul {ζ : (Sp k n → ℂ) →ₗ[ℂ] ℂ} (h : Good Z ζ) (c : ℂ) : Good Z (c • ζ) :=
  ⟨fun z hz f hf => by simp [h.1 z hz f hf], fun f hf h0 => by simp [h.2 f hf h0]⟩

theorem good_pull (hZ : CR Z) {ζ : (Sp k n → ℂ) →ₗ[ℂ] ℂ} (h : Good Z ζ) (t : kˣ) : Good Z (pullH t ζ) := by
  refine ⟨fun z hz f hf => ?_, fun f hf h0 => ?_⟩
  · show ζ (fun p => f ((t : k) • p.1 + z, p.2)) = ζ (fun p => f ((t : k) • p.1, p.2))
    have hz' : ((t⁻¹ : kˣ) : k) • z ∈ Z := Z.smul_mem hz _
    have hf' : (fun p : Sp k n => f ((t : k) • p.1, p.2)) ∈ supportedIn (Set.univ : Set (Sp k n)) :=
      comp_mem_univ (e := homH t) hf
    have := h.1 _ hz' _ hf'
    rw [← this]
    congr 1
    funext p
    congr 2
    rw [smul_add, smul_smul, Units.mul_inv, one_smul]
  · show ζ (fun p => f (hom t p)) = 0
    refine h.2 _ (hom_mem hf t) fun p hp => h0 _ ⟨(cc_smul hZ (t : k) hp.1).1, Set.mem_univ _⟩

theorem polyH_nil (t : kˣ) (ζ : (Sp k n → ℂ) →ₗ[ℂ] ℂ) : polyH t [] ζ = ζ := by
  simp [polyH]

theorem polyH_cons (t : kˣ) (x : ℝ) (a : List ℝ) (ζ : (Sp k n → ℂ) →ₗ[ℂ] ℂ) :
    polyH t (x :: a) ζ = pullH t (polyH t a ζ) - ((((nabs k t)⁻¹ : ℝ) ^ x : ℝ) : ℂ) • polyH t a ζ := by
  simp [polyH, List.map_cons, List.prod_cons, Module.End.mul_apply]

theorem fibre_quotient_holds : FibQ k := by
  classical
  intro n Z hZ η _ hInv hTr hSU
  have hg0 : Good Z η := ⟨hTr, hSU⟩
  obtain ⟨L, hL⟩ := exists_lat Z
  have hlift : ∀ h : supportedIn (UU : Set (Sp k n)), ∃ f ∈ supportedIn (UU : Set (Sp k n)),
      ∀ p ∈ OO Z, f p = psi Z (L : Set (Matrix (Fin n) (Fin n) k)) h p := fun h => exists_lift_of_lattice_average hZ hL h.2
  choose F0 hF0 hF0e using hlift
  have K0 : ∀ (h : supportedIn (UU : Set (Sp k n))) (f : Sp k n → ℂ), f ∈ supportedIn (UU : Set (Sp k n)) →
      (∀ p ∈ OO Z, f p = psi Z (L : Set (Matrix (Fin n) (Fin n) k)) h p) → η (F0 h) = η f :=
    fun h f hf ef => agree hg0.2 (hF0 h) hf fun p hp => by rw [hF0e h p hp, ef p hp]
  let η0 : supportedIn (UU : Set (Sp k n)) →ₗ[ℂ] ℂ :=
    { toFun := fun h => η (F0 h)
      map_add' := fun h h' => by
        rw [K0 (h + h') (F0 h + F0 h') (Submodule.add_mem _ (hF0 h) (hF0 h')) fun p hp => by
          rw [Pi.add_apply, hF0e h p hp, hF0e h' p hp, Submodule.coe_add, psi_add, Pi.add_apply], map_add (f := _)]
      map_smul' := fun c h => by
        rw [K0 (c • h) (c • F0 h) (Submodule.smul_mem _ c (hF0 h)) fun p hp => by
          rw [Pi.smul_apply, hF0e h p hp, Submodule.coe_smul, psi_smul, Pi.smul_apply], map_smul]
        rfl }
  obtain ⟨η', hη'⟩ := LinearMap.exists_extend η0
  have E0 : ∀ h (hh : h ∈ supportedIn (UU : Set (Sp k n))) (f : Sp k n → ℂ), f ∈ supportedIn (UU : Set (Sp k n)) →
      (∀ p ∈ OO Z, f p = psi Z (L : Set (Matrix (Fin n) (Fin n) k)) h p) → η' h = η f := by
    intro h hh f hf ef
    have := congrArg (fun φ => φ ⟨h, hh⟩) hη'
    simp only [LinearMap.coe_comp, Submodule.coe_subtype, Function.comp_apply] at this
    rw [this]
    exact K0 ⟨h, hh⟩ f hf ef
  refine ⟨η', fun h hh h0 => ?_, fun g hg h hh => ?_, fun t ht a hK => ?_⟩
  ·
    rw [E0 h hh 0 (Submodule.zero_mem _) fun p _ => by rw [psi_zero hZ _ h0], map_zero]
  ·
    have hOO : ∀ p ∈ OO Z, act g p ∈ OO Z := fun p hp => ⟨(cc_conj hZ hg hp.1).1, fun h0 => hp.2 (by
      have := congrArg (fun v => (g⁻¹ : GL (Fin n) k).val *ᵥ v) h0
      simpa [act, Matrix.mulVec_mulVec] using this)⟩
    rw [E0 _ (act_mem hh g) (fun p => F0 ⟨h, hh⟩ (act g p)) (act_mem (hF0 _) g) fun p hp => by
      rw [hF0e _ _ (hOO p hp), ← psi_act hZ _ h hg]]
    rw [hInv g hg _ (supportedIn_mono (Set.subset_univ _) (hF0 _)), E0 h hh (F0 ⟨h, hh⟩) (hF0 _) (hF0e ⟨h, hh⟩)]
  ·
    set N : ℂ := (((nabs k t)⁻¹ ^ Module.finrank k Z : ℝ) : ℂ) with hN
    have hpos : 0 < (nabs k t)⁻¹ := inv_pos.2 (NNReal.coe_pos.mpr MeasureTheory.distribHaarChar_pos)
    have claim : ∀ b : List ℝ, Good Z (polyH t (b.map (· + (Module.finrank k Z : ℝ))) η) ∧
        ∀ h ∈ supportedIn (UU : Set (Sp k n)), ∀ f ∈ supportedIn (UU : Set (Sp k n)),
          (∀ p ∈ OO Z, f p = psi Z (L : Set (Matrix (Fin n) (Fin n) k)) h p) →
          polyH t (b.map (· + (Module.finrank k Z : ℝ))) η f = N ^ b.length * polyH t b η' h := by
      intro b
      induction b with
      | nil =>
        refine ⟨by simpa [polyH_nil] using hg0, fun h hh f hf ef => ?_⟩
        simp only [List.map_nil, polyH_nil, List.length_nil, pow_zero, one_mul]
        exact (E0 h hh f hf ef).symm
      | cons x b ih =>
        obtain ⟨hgb, hb⟩ := ih
        simp only [List.map_cons]
        refine ⟨?_, fun h hh f hf ef => ?_⟩
        · rw [show polyH t ((x + (Module.finrank k Z : ℝ)) :: b.map (· + (Module.finrank k Z : ℝ))) η =
            pullH t _ - _ from polyH_cons t _ _ η]
          exact good_sub (good_pull hZ hgb t) (good_smul hgb _)
        · rw [polyH_cons, polyH_cons, LinearMap.sub_apply, LinearMap.sub_apply, LinearMap.smul_apply,
            LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
          obtain ⟨f', hf', ef'⟩ := exists_lift_of_lattice_average hZ hL (hom_mem hh t)
          have e1 : pullH t (polyH t (b.map (· + (Module.finrank k Z : ℝ))) η) f =
              N * (N ^ b.length * polyH t b η' (fun q => h (hom t q))) := by
            show polyH t (b.map (· + (Module.finrank k Z : ℝ))) η (fun p => f (hom t p)) = _
            rw [scale hZ hgb hL ht hh hf hf' ef ef', hb _ (hom_mem hh t) f' hf' ef']
          rw [e1, hb h hh f hf ef]
          show _ = N ^ (b.length + 1) * (polyH t b η' (fun q => h (hom t q)) - _ * polyH t b η' h)
          have hc : ((((nabs k t)⁻¹ : ℝ) ^ (x + (Module.finrank k Z : ℝ)) : ℝ) : ℂ) =
              ((((nabs k t)⁻¹ : ℝ) ^ x : ℝ) : ℂ) * N := by
            rw [Real.rpow_add hpos, Real.rpow_natCast, hN]; push_cast; ring
          rw [hc]
          ring
    obtain ⟨hgA, hA⟩ := claim a
    refine lemB hZ hgA hL ht fun h hh f hf ef => ?_
    rw [hA h hh f hf ef, hK h hh, mul_zero]

theorem fibQ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] : FibQ k :=
  fibre_quotient_holds

end PositivityTheory.RgUd.TP.Nil.Fib2

end
