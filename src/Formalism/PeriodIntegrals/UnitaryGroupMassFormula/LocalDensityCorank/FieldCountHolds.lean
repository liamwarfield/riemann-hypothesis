module

public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DensInert
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.ResidueFieldCount
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDensityCorank.SplitCount

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.CardCount
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.GramCondIff
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.IndepOf
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DensGFC
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open Formalism.MainNotions.S ValuativeRel
open Classical

namespace FC

variable {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E}
  {V : Type} [AddCommGroup V] [Module E V]

theorem h_add_right (H : Loc.HermSp M V) (x y y' : V) : H.h x (y + y') = H.h x y + H.h x y' := by
  rw [H.h_herm (y + y') x, H.h_add_left, map_add (f := _), ← H.h_herm y x, ← H.h_herm y' x]

theorem h_smul_right (H : Loc.HermSp M V) (a : E) (x y : V) : H.h x (a • y) = M.L.cj a * H.h x y := by
  rw [H.h_herm (a • y) x, H.h_smul_left, map_mul, ← H.h_herm y x]

theorem h_sum_left (H : Loc.HermSp M V) {ι : Type} (s : Finset ι) (f : ι → V) (y : V) :
    H.h (∑ i ∈ s, f i) y = ∑ i ∈ s, H.h (f i) y :=
  map_sum (AddMonoidHom.mk' (fun x => H.h x y) (fun x x' => H.h_add_left x x' y)) f s

theorem h_sum_right (H : Loc.HermSp M V) {ι : Type} (s : Finset ι) (f : ι → V) (x : V) :
    H.h x (∑ i ∈ s, f i) = ∑ i ∈ s, H.h x (f i) :=
  map_sum (AddMonoidHom.mk' (fun y => H.h x y) (fun y y' => h_add_right H x y y')) f s

theorem h_expand (H : Loc.HermSp M V) {n : ℕ} (b : Fin n → V) (c d : Fin n → E) :
    H.h (∑ k, c k • b k) (∑ l, d l • b l) = ∑ k, ∑ l, c k * M.L.cj (d l) * H.h (b k) (b l) := by
  rw [h_sum_left]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [H.h_smul_left, h_sum_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [h_smul_right]
  ring

theorem smul_O (o : M.L.O) (v : V) : o • v = (o : E) • v := rfl

theorem smulLat_mem (H : Loc.HermSp M V) (c : E) (Λ : Submodule M.L.O V) (y : V) :
    y ∈ H.smulLat c Λ ↔ ∃ w ∈ Λ, y = c • w := by
  constructor
  · intro hy
    unfold Loc.HermSp.smulLat at hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, hw, rfl⟩ := hx
      exact ⟨w, hw, rfl⟩
    | zero => exact ⟨0, Λ.zero_mem, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨w, hw, rfl⟩ := hx
      obtain ⟨w', hw', rfl⟩ := hy
      exact ⟨w + w', Λ.add_mem hw hw', by simp [smul_add]⟩
    | smul o x _ hx =>
      obtain ⟨w, hw, rfl⟩ := hx
      refine ⟨o • w, Λ.smul_mem o hw, ?_⟩
      rw [smul_O, smul_O, smul_smul, smul_smul, mul_comm]
  · rintro ⟨w, hw, rfl⟩
    exact Submodule.subset_span ⟨w, hw, rfl⟩

theorem coord_unique {n : ℕ} {b : Fin n → V} (hb : LinearIndependent E b) {c c' : Fin n → E}
    (h : ∑ k, c k • b k = ∑ k, c' k • b k) : c = c' := by
  have := Fintype.linearIndependent_iff.1 hb (c - c') (by
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, h, sub_self])
  funext k
  exact sub_eq_zero.1 (this k)

theorem comb_mem {n : ℕ} {b : Fin n → V} {Λ : Submodule M.L.O V} (hbΛ : ∀ k, b k ∈ Λ)
    (c : Fin n → E) (hc : ∀ k, c k ∈ M.L.O) : ∑ k, c k • b k ∈ Λ := by
  refine Λ.sum_mem fun k _ => ?_
  have := Λ.smul_mem (⟨c k, hc k⟩ : M.L.O) (hbΛ k)
  exact this

end FC

namespace FC

variable {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E}
  {V : Type} [AddCommGroup V] [Module E V]

structure RedData (ϖ : 𝒪[F]) (k : Type) [Field k] (r : M.L.O →+* k) (n : ℕ) (b : Fin n → V)
    (Λ : Submodule M.L.O V) : Prop where
  ker : ∀ x : M.L.O, r x = 0 ↔ ∃ z ∈ M.L.O, (x : E) = algebraMap F E ϖ * z
  surj : Function.Surjective r
  bΛ : ∀ j, b j ∈ Λ
  bind : LinearIndependent E b
  crd : ∀ x ∈ Λ, ∃ c : Fin n → E, (∀ j, c j ∈ M.L.O) ∧ x = ∑ j, c j • b j

variable {ϖ : 𝒪[F]} {k : Type} [Field k] {r : M.L.O →+* k} {n : ℕ} {b : Fin n → V}
  {Λ : Submodule M.L.O V}

def cO (hR : RedData ϖ k r n b Λ) (x : V) : Fin n → E :=
  if hx : x ∈ Λ then Classical.choose (hR.crd x hx) else 0

theorem cO_mem (hR : RedData ϖ k r n b Λ) (x : V) (j : Fin n) : cO hR x j ∈ M.L.O := by
  unfold cO
  split_ifs with hx
  · exact (Classical.choose_spec (hR.crd x hx)).1 j
  · exact M.L.O.zero_mem

theorem cO_sum (hR : RedData ϖ k r n b Λ) {x : V} (hx : x ∈ Λ) : x = ∑ j, cO hR x j • b j := by
  unfold cO
  rw [dite_eq_left hx]
  exact (Classical.choose_spec (hR.crd x hx)).2

theorem cO_eq (hR : RedData ϖ k r n b Λ) {x : V} (hx : x ∈ Λ) (c : Fin n → E)
    (hc : x = ∑ j, c j • b j) : cO hR x = c :=
  coord_unique hR.bind ((cO_sum hR hx).symm.trans hc)

def red (hR : RedData ϖ k r n b Λ) (x : V) : Fin n → k := fun j => r ⟨cO hR x j, cO_mem hR x j⟩

theorem cO_lincomb (hR : RedData ϖ k r n b Λ) {ι : Type} [Fintype ι] (h : ι → E) (v : ι → V)
    (hv : ∀ a, v a ∈ Λ) (hh : ∀ a, h a ∈ M.L.O) :
    cO hR (∑ a, h a • v a) = fun j => ∑ a, h a * cO hR (v a) j := by
  have hmem : ∑ a, h a • v a ∈ Λ := by
    refine Λ.sum_mem fun a _ => ?_
    exact Λ.smul_mem (⟨h a, hh a⟩ : M.L.O) (hv a)
  refine cO_eq hR hmem _ ?_
  conv_lhs => rw [Finset.sum_congr rfl fun a _ => by rw [cO_sum hR (hv a)]]
  simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
  exact Finset.sum_comm

theorem red_lincomb (hR : RedData ϖ k r n b Λ) {ι : Type} [Fintype ι] (h : ι → M.L.O) (v : ι → V)
    (hv : ∀ a, v a ∈ Λ) :
    red hR (∑ a, (h a : E) • v a) = ∑ a, r (h a) • red hR (v a) := by
  funext j
  have h1 := congrFun (cO_lincomb hR (fun a => (h a : E)) v hv (fun a => (h a).2)) j
  have h2 : (⟨cO hR (∑ a, (h a : E) • v a) j, cO_mem hR _ j⟩ : M.L.O) =
      ∑ a, h a * ⟨cO hR (v a) j, cO_mem hR _ j⟩ := by
    apply Subtype.ext
    show cO hR (∑ a, (h a : E) • v a) j = _
    rw [h1]
    push_cast
    rfl
  simp only [red, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h2, map_sum]
  simp only [map_mul]

end FC

namespace FC

variable {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E}
  {V : Type} [AddCommGroup V] [Module E V]
variable {ϖ : 𝒪[F]} {k : Type} [Field k] {r : M.L.O →+* k} {n : ℕ} {b : Fin n → V}
  {Λ : Submodule M.L.O V}

theorem red_sub (hR : RedData ϖ k r n b Λ) {x y : V} (hx : x ∈ Λ) (hy : y ∈ Λ) :
    red hR (x - y) = red hR x - red hR y := by
  have hc : cO hR (x - y) = cO hR x - cO hR y := by
    refine cO_eq hR (Λ.sub_mem hx hy) _ ?_
    conv_lhs => rw [cO_sum hR hx, cO_sum hR hy]
    simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib]
  funext j
  simp only [red, Pi.sub_apply]
  rw [← map_sub]
  congr 1
  apply Subtype.ext
  show cO hR (x - y) j = _
  rw [hc]
  rfl

theorem red_zero_iff (hR : RedData ϖ k r n b Λ) {x : V} (hx : x ∈ Λ) :
    red hR x = 0 ↔ ∃ w ∈ Λ, x = algebraMap F E (ϖ : F) • w := by
  constructor
  · intro h0
    have hz : ∀ j, ∃ z ∈ M.L.O, cO hR x j = algebraMap F E (ϖ : F) * z := fun j =>
      (hR.ker ⟨cO hR x j, cO_mem hR x j⟩).1 (congrFun h0 j)
    choose z hzO hz using hz
    refine ⟨∑ j, z j • b j, comb_mem hR.bΛ z hzO, ?_⟩
    conv_lhs => rw [cO_sum hR hx]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hz j, smul_smul]
  · rintro ⟨w, hw, rfl⟩
    have hc : cO hR (algebraMap F E (ϖ : F) • w) = fun j => algebraMap F E (ϖ : F) * cO hR w j := by
      refine cO_eq hR hx _ ?_
      conv_lhs => rw [cO_sum hR hw]
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_smul]
    funext j
    refine (hR.ker _).2 ⟨cO hR w j, cO_mem hR w j, ?_⟩
    show cO hR (algebraMap F E (ϖ : F) • w) j = _
    rw [hc]

theorem class_iff (hR : RedData ϖ k r n b Λ) (H : Loc.HermSp M V) {x y : V} (hx : x ∈ Λ) (hy : y ∈ Λ) :
    x - y ∈ H.smulLat (algebraMap F E (ϖ : F)) Λ ↔ red hR x = red hR y := by
  rw [smulLat_mem, ← red_zero_iff hR (Λ.sub_mem hx hy), red_sub hR hx hy, sub_eq_zero]

theorem red_lift (hR : RedData ϖ k r n b Λ) (X : Fin n → k) : ∃ x ∈ Λ, red hR x = X := by
  choose o ho using fun j => hR.surj (X j)
  refine ⟨∑ j, (o j : E) • b j, comb_mem hR.bΛ _ fun j => (o j).2, ?_⟩
  have hc := cO_eq hR (comb_mem hR.bΛ _ fun j => (o j).2) (fun j => (o j : E)) rfl
  funext j
  simp only [red]
  rw [← ho j]
  congr 1
  apply Subtype.ext
  show cO hR _ j = _
  rw [hc]

end FC

namespace FC

variable {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E}
  {V : Type} [AddCommGroup V] [Module E V]
variable {ϖ : 𝒪[F]} {k : Type} [Field k] {r : M.L.O →+* k} {n : ℕ} {b : Fin n → V}
  {Λ : Submodule M.L.O V}

theorem algO (c : 𝒪[F]) : algebraMap F E (c : F) ∈ M.L.O :=
  (M.L.O_def _).2 (by
    rw [show algebraMap F E (c : F) = algebraMap 𝒪[F] E c from
      (IsScalarTower.algebraMap_apply 𝒪[F] F E c).symm]
    exact isIntegral_algebraMap)

theorem pi_unit (hϖ : Irreducible ϖ) : IsUnit (algebraMap F E (ϖ : F)) := by
  have h0 : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  exact (IsUnit.mk0 _ h0).map _

theorem red_zero (hR : RedData ϖ k r n b Λ) : red hR 0 = 0 := by
  have hc : cO hR (0 : V) = 0 := cO_eq hR Λ.zero_mem 0 (by simp)
  funext j
  simp only [red, Pi.zero_apply]
  rw [← map_zero r]
  congr 1
  apply Subtype.ext
  show cO hR 0 j = 0
  rw [hc]
  rfl

theorem minpow (hR : RedData ϖ k r n b Λ) (hϖ : Irreducible ϖ)
    (o3 : ∀ x ∈ M.L.O, x ≠ 0 → ∃ j : ℕ, ∃ u ∈ M.L.O, (∃ w ∈ M.L.O, u * w = 1) ∧
      x = algebraMap F E ϖ ^ j * u) {ι : Type} (h : ι → E) (hh : ∀ a, h a ∈ M.L.O)
    (a0 : ι) (ha0 : h a0 ≠ 0) :
    ∃ j : ℕ, ∃ z : ι → E, ∃ hz : ∀ a, z a ∈ M.L.O, (∀ a, h a = algebraMap F E (ϖ : F) ^ j * z a) ∧
      ∃ a1, r ⟨z a1, hz a1⟩ ≠ 0 := by
  have hex : ∃ j : ℕ, ∃ a, ¬ ∃ z ∈ M.L.O, h a = algebraMap F E (ϖ : F) ^ (j + 1) * z := by
    obtain ⟨j, u, huO, ⟨w, hw, huw⟩, hju⟩ := o3 _ (hh a0) ha0
    refine ⟨j, a0, ?_⟩
    rintro ⟨z, hzO, hz⟩
    have hcan : u = algebraMap F E (ϖ : F) * z := by
      have h2 : algebraMap F E (ϖ : F) ^ j * u = algebraMap F E (ϖ : F) ^ j * (algebraMap F E (ϖ : F) * z) := by
        rw [← hju, hz]; ring
      exact ((pi_unit hϖ).pow j).mul_left_cancel h2
    have hr0 : r ⟨u, huO⟩ = 0 := (hR.ker _).2 ⟨z, hzO, hcan⟩
    have hr1 : r ⟨u, huO⟩ * r ⟨w, hw⟩ = 1 := by
      rw [← map_mul, ← map_one r]
      congr 1
      exact Subtype.ext huw
    rw [hr0, zero_mul] at hr1
    exact zero_ne_one hr1
  obtain ⟨j0, hj0, hmin⟩ : ∃ j0 : ℕ, (∃ a, ¬ ∃ z ∈ M.L.O, h a = algebraMap F E (ϖ : F) ^ (j0 + 1) * z) ∧
      ∀ m < j0, ¬ ∃ a, ¬ ∃ z ∈ M.L.O, h a = algebraMap F E (ϖ : F) ^ (m + 1) * z :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
  have hall : ∀ a, ∃ z ∈ M.L.O, h a = algebraMap F E (ϖ : F) ^ j0 * z := by
    intro a
    rcases Nat.eq_zero_or_pos j0 with h0 | hpos
    · exact ⟨h a, hh a, by rw [h0, pow_zero, one_mul]⟩
    · have hm := hmin (j0 - 1) (Nat.sub_lt hpos one_pos)
      push Not at hm
      obtain ⟨z, hz, hza⟩ := hm a
      refine ⟨z, hz, ?_⟩
      rwa [show j0 - 1 + 1 = j0 from by omega] at hza
  choose z hzO hz using hall
  obtain ⟨a1, ha1⟩ := hj0
  refine ⟨j0, z, hzO, hz, a1, ?_⟩
  intro hr
  obtain ⟨z', hz'O, hz'⟩ := (hR.ker _).1 hr
  have hz'' : z a1 = algebraMap F E (ϖ : F) * z' := hz'
  apply ha1
  exact ⟨z', hz'O, by rw [hz a1, hz'', pow_succ]; ring⟩

end FC

end PI.UnitaryGroupMassFormula.CntFormula
end
end

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open Formalism.MainNotions.S ValuativeRel
open Classical

namespace FC

variable {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E}
  {V : Type} [AddCommGroup V] [Module E V]
variable {ϖ : 𝒪[F]} {k : Type} [Field k] {r : M.L.O →+* k} {n : ℕ} {b : Fin n → V}
  {Λ : Submodule M.L.O V}

theorem prim_of (hR : RedData ϖ k r n b Λ) (H : Loc.HermSp M V) (hϖ : Irreducible ϖ)
    {ι : Type} [Fintype ι] (v : ι → V) (hv : ∀ a, v a ∈ Λ) (hP : H.Prim Λ v) :
    LinearIndependent k (fun a => red hR (v a)) := by
  obtain ⟨-, hind, hsat⟩ := hP
  have hϖ0 : ((ϖ : 𝒪[F]) : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  rw [Fintype.linearIndependent_iff]
  intro g hg a0
  choose h hh using fun a => hR.surj (g a)
  have hsum_mem : ∑ a, ((h a : M.L.O) : E) • v a ∈ Λ :=
    Submodule.sum_mem _ fun a _ => Λ.smul_mem (h a) (hv a)
  have hred : red hR (∑ a, ((h a : M.L.O) : E) • v a) = 0 := by
    rw [red_lincomb hR h v hv]
    simp only [hh]
    exact hg
  obtain ⟨w, hw, hweq⟩ := (red_zero_iff hR hsum_mem).mp hred

  have hwspan : w ∈ Submodule.span E (Set.range v) := by
    have e : w = algebraMap F E ((ϖ : F))⁻¹ • ∑ a, ((h a : M.L.O) : E) • v a := by
      rw [hweq, smul_smul, ← map_mul, inv_mul_cancel₀ hϖ0, map_one, one_smul]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun a _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩))
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun M.L.O).mp (hsat w hw hwspan)

  have hzero : ∑ a, (((h a : M.L.O) : E) - algebraMap F E (ϖ : F) * (c a : E)) • v a = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, mul_smul]
    rw [← Finset.smul_sum, sub_eq_zero, hweq, ← hc]
    simp only [Subring.smul_def]
  have ha0 := Fintype.linearIndependent_iff.mp hind _ hzero a0
  rw [← hh a0]
  exact (hR.ker (h a0)).mpr ⟨c a0, (c a0).2, sub_eq_zero.mp ha0⟩

theorem indep_of (hR : RedData ϖ k r n b Λ) (hϖ : Irreducible ϖ)
    (o2 : ∀ x : E, ∃ c : 𝒪[F], c ≠ 0 ∧ algebraMap F E c * x ∈ M.L.O)
    (o3 : ∀ x ∈ M.L.O, x ≠ 0 → ∃ j : ℕ, ∃ u ∈ M.L.O, (∃ w ∈ M.L.O, u * w = 1) ∧
      x = algebraMap F E ϖ ^ j * u)
    {ι : Type} [Fintype ι] (v : ι → V) (hv : ∀ a, v a ∈ Λ)
    (hX : LinearIndependent k (fun a => red hR (v a))) : LinearIndependent E v := by
  have hϖ0 : ((ϖ : 𝒪[F]) : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hOalg : ∀ c : 𝒪[F], algebraMap F E (c : F) ∈ M.L.O := by
    intro c
    rw [M.L.O_def]
    exact (isIntegral_algebraMap (R := 𝒪[F]) (A := F) (x := c)).map (IsScalarTower.toAlgHom 𝒪[F] F E)
  rw [Fintype.linearIndependent_iff]
  intro g hg a0
  by_contra hne

  choose c hc0 hcO using fun a => o2 (g a)
  have hDne : (∏ a, c a) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun a _ => hc0 a
  have hD0 : (((∏ a, c a : 𝒪[F])) : F) ≠ 0 := fun h => hDne (Subtype.ext h)
  have hDg : ∀ a, algebraMap F E ((∏ b, c b : 𝒪[F]) : F) * g a ∈ M.L.O := by
    intro a
    have e : ((∏ b, c b : 𝒪[F]) : F) = (c a : F) * ((∏ b ∈ Finset.univ.erase a, c b : 𝒪[F]) : F) := by
      rw [← Finset.mul_prod_erase Finset.univ c (Finset.mem_univ a)]
      rfl
    rw [e, map_mul, mul_comm (algebraMap F E (c a : F)), mul_assoc]
    exact M.L.O.mul_mem (hOalg _) (hcO a)
  let h : ι → M.L.O := fun a => ⟨algebraMap F E ((∏ b, c b : 𝒪[F]) : F) * g a, hDg a⟩
  have hsum : ∑ a, ((h a : M.L.O) : E) • v a = 0 := by
    simp only [h, mul_smul, ← Finset.smul_sum, hg, smul_zero]
  have hh0 : ((h a0 : M.L.O) : E) ≠ 0 := by
    intro h0
    apply hne
    have h1 := congrArg (algebraMap F E (((∏ b, c b : 𝒪[F]) : F))⁻¹ * ·) h0
    simp only [h, mul_zero, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hD0, map_one, one_mul] at h1
    exact h1
  obtain ⟨j, z, hz, hzeq, a1, ha1⟩ :=
    minpow hR hϖ o3 (fun a => ((h a : M.L.O) : E)) (fun a => (h a).2) a0 hh0
  have hsumz : ∑ a, z a • v a = 0 := by
    have e1 : ∑ a, ((h a : M.L.O) : E) • v a = (algebraMap F E (ϖ : F)) ^ j • ∑ a, z a • v a := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hzeq a, mul_smul]
    rw [e1] at hsum
    have h2 := congrArg (fun x => (algebraMap F E ((ϖ : F))⁻¹) ^ j • x) hsum
    simp only [smul_smul, ← mul_pow, ← map_mul, inv_mul_cancel₀ hϖ0, map_one, one_pow, one_smul,
      smul_zero] at h2
    exact h2
  have hred : ∑ a, r ⟨z a, hz a⟩ • red hR (v a) = 0 := by
    rw [← red_lincomb hR (fun a => (⟨z a, hz a⟩ : M.L.O)) v hv]
    simp only [hsumz, red_zero]
  exact ha1 (Fintype.linearIndependent_iff.mp hX _ hred a1)

theorem sat_of (hR : RedData ϖ k r n b Λ) (hϖ : Irreducible ϖ)
    (o2 : ∀ x : E, ∃ c : 𝒪[F], c ≠ 0 ∧ algebraMap F E c * x ∈ M.L.O)
    (o3 : ∀ x ∈ M.L.O, x ≠ 0 → ∃ j : ℕ, ∃ u ∈ M.L.O, (∃ w ∈ M.L.O, u * w = 1) ∧
      x = algebraMap F E ϖ ^ j * u)
    {ι : Type} [Fintype ι] (v : ι → V) (hv : ∀ a, v a ∈ Λ)
    (hX : LinearIndependent k (fun a => red hR (v a))) :
    ∀ x ∈ Λ, x ∈ Submodule.span E (Set.range v) → x ∈ Submodule.span M.L.O (Set.range v) := by
  have hϖ0 : ((ϖ : 𝒪[F]) : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hOalg : ∀ c : 𝒪[F], algebraMap F E (c : F) ∈ M.L.O := by
    intro c
    rw [M.L.O_def]
    exact (isIntegral_algebraMap (R := 𝒪[F]) (A := F) (x := c)).map (IsScalarTower.toAlgHom 𝒪[F] F E)
  have hϖO : algebraMap F E (ϖ : F) ∈ M.L.O := hOalg ϖ
  have hϖu : IsUnit (algebraMap F E (ϖ : F)) := (isUnit_iff_ne_zero.mpr hϖ0).map (algebraMap F E)
  intro x hx hxs
  obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun E).mp hxs

  choose c hc0 hcO using fun a => o2 (g a)
  have hDne : (∏ a, c a) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun a _ => hc0 a
  have hD0 : (((∏ a, c a : 𝒪[F])) : F) ≠ 0 := fun h => hDne (Subtype.ext h)
  have hDg : ∀ a, algebraMap F E ((∏ b, c b : 𝒪[F]) : F) * g a ∈ M.L.O := by
    intro a
    have e : ((∏ b, c b : 𝒪[F]) : F) = (c a : F) * ((∏ b ∈ Finset.univ.erase a, c b : 𝒪[F]) : F) := by
      rw [← Finset.mul_prod_erase Finset.univ c (Finset.mem_univ a)]
      rfl
    rw [e, map_mul, mul_comm (algebraMap F E (c a : F)), mul_assoc]
    exact M.L.O.mul_mem (hOalg _) (hcO a)
  have hdO : algebraMap F E ((∏ b, c b : 𝒪[F]) : F) ∈ M.L.O := hOalg _
  have hdu : IsUnit (algebraMap F E ((∏ b, c b : 𝒪[F]) : F)) :=
    (isUnit_iff_ne_zero.mpr hD0).map (algebraMap F E)
  let h : ι → M.L.O := fun a => ⟨algebraMap F E ((∏ b, c b : 𝒪[F]) : F) * g a, hDg a⟩
  have hdx : algebraMap F E ((∏ b, c b : 𝒪[F]) : F) • x = ∑ a, ((h a : M.L.O) : E) • v a := by
    rw [← hg, Finset.smul_sum]
    simp only [h, mul_smul]
  by_cases hall : ∀ a, ((h a : M.L.O) : E) = 0
  · have h0 : algebraMap F E ((∏ b, c b : 𝒪[F]) : F) • x = 0 := by
      rw [hdx]
      simp [hall]
    have hx0 : x = 0 := by
      rw [← smul_zero (algebraMap F E ((∏ b, c b : 𝒪[F]) : F))] at h0
      exact hdu.smul_left_cancel.mp h0
    rw [hx0]
    exact zero_mem _
  push_neg at hall
  obtain ⟨a0, ha0⟩ := hall
  obtain ⟨j, z, hz, hzeq, a1, ha1⟩ :=
    minpow hR hϖ o3 (fun a => ((h a : M.L.O) : E)) (fun a => (h a).2) a0 ha0
  haveI : Nontrivial E := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    have h10 : (1 : M.L.O) = 0 := Subtype.ext (Subsingleton.elim _ _)
    have h11 := congrArg r h10
    simp at h11
  obtain ⟨m, u, huO, ⟨w, hwO, huw⟩, hdeq⟩ := o3 _ hdO hdu.ne_zero
  have key : (algebraMap F E (ϖ : F)) ^ m • (u • x) =
      (algebraMap F E (ϖ : F)) ^ j • ∑ a, z a • v a := by
    rw [smul_smul, ← hdeq, hdx, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hzeq a, mul_smul]
  by_cases hjm : m ≤ j
  · rw [show j = m + (j - m) by omega, pow_add, mul_smul] at key
    have e1 := (hϖu.pow m).smul_left_cancel.mp key
    have hx' : x = ∑ a, (w * (algebraMap F E (ϖ : F)) ^ (j - m) * z a) • v a := by
      have e2 : x = w • (u • x) := by rw [smul_smul, mul_comm w u, huw, one_smul]
      rw [e2, e1, Finset.smul_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [smul_smul, smul_smul, mul_assoc]
    rw [hx']
    refine Submodule.sum_mem _ fun a _ => ?_
    have hmem : w * (algebraMap F E (ϖ : F)) ^ (j - m) * z a ∈ M.L.O :=
      M.L.O.mul_mem (M.L.O.mul_mem hwO (M.L.O.pow_mem hϖO _)) (hz a)
    have h3 := Submodule.smul_mem (Submodule.span M.L.O (Set.range v)) (⟨_, hmem⟩ : M.L.O)
      (Submodule.subset_span ⟨a, rfl⟩)
    rwa [Subring.smul_def] at h3
  · push_neg at hjm
    rw [show m = j + ((m - j - 1) + 1) by omega, pow_add, mul_smul] at key
    have e1 := (hϖu.pow j).smul_left_cancel.mp key
    have hzs : ∑ a, z a • v a = algebraMap F E (ϖ : F) •
        ((algebraMap F E (ϖ : F)) ^ (m - j - 1) • (u • x)) := by
      rw [← e1, pow_succ, mul_smul, smul_comm]
    have hmemΛ : ∑ a, z a • v a ∈ Λ :=
      Submodule.sum_mem _ fun a _ => Λ.smul_mem (⟨z a, hz a⟩ : M.L.O) (hv a)
    have hred0 : red hR (∑ a, z a • v a) = 0 := by
      rw [red_zero_iff hR hmemΛ]
      refine ⟨(algebraMap F E (ϖ : F)) ^ (m - j - 1) • (u • x), ?_, hzs⟩
      have hc : (algebraMap F E (ϖ : F)) ^ (m - j - 1) * u ∈ M.L.O :=
        M.L.O.mul_mem (M.L.O.pow_mem hϖO _) huO
      have h4 := Λ.smul_mem (⟨_, hc⟩ : M.L.O) hx
      rwa [Subring.smul_def, mul_smul] at h4
    have hred : ∑ a, r ⟨z a, hz a⟩ • red hR (v a) = 0 := by
      rw [← red_lincomb hR (fun a => (⟨z a, hz a⟩ : M.L.O)) v hv]
      exact hred0
    exact absurd (Fintype.linearIndependent_iff.mp hX _ hred a1) ha1

theorem prim_iff (hR : RedData ϖ k r n b Λ) (H : Loc.HermSp M V) (hϖ : Irreducible ϖ)
    (o2 : ∀ x : E, ∃ c : 𝒪[F], c ≠ 0 ∧ algebraMap F E c * x ∈ M.L.O)
    (o3 : ∀ x ∈ M.L.O, x ≠ 0 → ∃ j : ℕ, ∃ u ∈ M.L.O, (∃ w ∈ M.L.O, u * w = 1) ∧
      x = algebraMap F E ϖ ^ j * u)
    {ι : Type} [Fintype ι] (v : ι → V) (hv : ∀ a, v a ∈ Λ) :
    H.Prim Λ v ↔ LinearIndependent k (fun a => red hR (v a)) :=
  ⟨prim_of hR H hϖ v hv, fun hX => ⟨hv, indep_of hR hϖ o2 o3 v hv hX, sat_of hR hϖ o2 o3 v hv hX⟩⟩

end FC

end PI.UnitaryGroupMassFormula.CntFormula
end
end

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open Formalism.MainNotions.S ValuativeRel
open Classical

namespace FC

variable {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E}
  {V : Type} [AddCommGroup V] [Module E V]
variable {ϖ : 𝒪[F]} {k : Type} [Field k] {r : M.L.O →+* k} {n : ℕ} {b : Fin n → V}
  {Λ : Submodule M.L.O V}

theorem span_pi_iff (hR : RedData ϖ k r n b Λ) (x : M.L.O) :
    (x : E) ∈ Submodule.span M.L.O {algebraMap F E (ϖ : F)} ↔ r x = 0 := by
  rw [Submodule.mem_span_singleton, hR.ker]
  constructor
  · rintro ⟨o, ho⟩
    exact ⟨o, o.2, by rw [← ho]; show (o : E) * _ = _; ring⟩
  · rintro ⟨z, hz, hzx⟩
    exact ⟨⟨z, hz⟩, by rw [hzx]; show z * _ = _; ring⟩

theorem cj_mem {x : E} (hx : x ∈ M.L.O) : M.L.cj x ∈ M.L.O := by
  rw [M.L.O_def] at hx ⊢
  exact hx.map (M.L.cj.toAlgHom.restrictScalars 𝒪[F])

def Ph (r : M.L.O →+* k) (H : Loc.HermSp M V) (b : Fin n → V) (hint : ∀ i j, H.h (b i) (b j) ∈ M.L.O) :
    Matrix (Fin n) (Fin n) k := fun i j => r ⟨H.h (b i) (b j), hint i j⟩

theorem gram_mem (hR : RedData ϖ k r n b Λ) (H : Loc.HermSp M V) (hint : ∀ i j, H.h (b i) (b j) ∈ M.L.O)
    {x y : V} (hx : x ∈ Λ) (hy : y ∈ Λ) :
    H.h x y = ∑ i, ∑ j, cO hR x i * M.L.cj (cO hR y j) * H.h (b i) (b j) ∧ H.h x y ∈ M.L.O := by
  have he : H.h x y = ∑ i, ∑ j, cO hR x i * M.L.cj (cO hR y j) * H.h (b i) (b j) := by
    conv_lhs => rw [cO_sum hR hx, cO_sum hR hy]
    exact h_expand H b _ _
  refine ⟨he, ?_⟩
  rw [he]
  exact M.L.O.sum_mem fun i _ => M.L.O.sum_mem fun j _ =>
    M.L.O.mul_mem (M.L.O.mul_mem (cO_mem hR x i) (cj_mem (cO_mem hR y j))) (hint i j)

theorem gram_red (hR : RedData ϖ k r n b Λ) (H : Loc.HermSp M V) (hint : ∀ i j, H.h (b i) (b j) ∈ M.L.O)
    (q : ℕ) (rfrob : ∀ x y : M.L.O, (y : E) = M.L.cj x → r y = r x ^ q)
    {x y : V} (hx : x ∈ Λ) (hy : y ∈ Λ) :
    r ⟨H.h x y, (gram_mem hR H hint hx hy).2⟩ =
      ∑ i, ∑ j, red hR x i * Ph r H b hint i j * red hR y j ^ q := by
  have h1 : (⟨H.h x y, (gram_mem hR H hint hx hy).2⟩ : M.L.O) =
      ∑ i, ∑ j, (⟨cO hR x i, cO_mem hR x i⟩ : M.L.O) * ⟨M.L.cj (cO hR y j), cj_mem (cO_mem hR y j)⟩ *
        ⟨H.h (b i) (b j), hint i j⟩ := by
    apply Subtype.ext
    show H.h x y = _
    rw [(gram_mem hR H hint hx hy).1]
    push_cast
    rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h1, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_mul, rfrob ⟨cO hR y j, cO_mem hR y j⟩ ⟨M.L.cj (cO hR y j), cj_mem (cO_mem hR y j)⟩ rfl]
  simp only [red, Ph]
  ring

theorem gram_cond_iff (hR : RedData ϖ k r n b Λ) (H : Loc.HermSp M V)
    (hint : ∀ i j, H.h (b i) (b j) ∈ M.L.O)
    (q : ℕ) (rfrob : ∀ x y : M.L.O, (y : E) = M.L.cj x → r y = r x ^ q)
    {x y : V} (hx : x ∈ Λ) (hy : y ∈ Λ) (g : E) (hg : g ∈ M.L.O) :
    H.h x y - g ∈ Submodule.span M.L.O {algebraMap F E (ϖ : F)} ↔
      ∑ i, ∑ j, red hR x i * Ph r H b hint i j * red hR y j ^ q = r ⟨g, hg⟩ := by
  have hm := (gram_mem hR H hint hx hy).2
  have := span_pi_iff hR ⟨H.h x y - g, M.L.O.sub_mem hm hg⟩
  simp only at this
  rw [this, show (⟨H.h x y - g, M.L.O.sub_mem hm hg⟩ : M.L.O) = ⟨H.h x y, hm⟩ - ⟨g, hg⟩ from
    Subtype.ext rfl, map_sub, sub_eq_zero, gram_red hR H hint q rfrob hx hy]

end FC

end PI.UnitaryGroupMassFormula.CntFormula
end
end

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open Formalism.MainNotions.S ValuativeRel
open Classical

namespace FC

variable {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E}
  {V : Type} [AddCommGroup V] [Module E V]
variable {ϖ : 𝒪[F]} {k : Type} [Field k] {r : M.L.O →+* k} {n : ℕ} {b : Fin n → V}
  {Λ : Submodule M.L.O V}

theorem card_count (hR : RedData ϖ k r n b Λ) (H : Loc.HermSp M V) (hϖ : Irreducible ϖ)
    (o2 : ∀ x : E, ∃ c : 𝒪[F], c ≠ 0 ∧ algebraMap F E c * x ∈ M.L.O)
    (o3 : ∀ x ∈ M.L.O, x ≠ 0 → ∃ j : ℕ, ∃ u ∈ M.L.O, (∃ w ∈ M.L.O, u * w = 1) ∧
      x = algebraMap F E ϖ ^ j * u)
    (hint : ∀ i j, H.h (b i) (b j) ∈ M.L.O)
    (q : ℕ) (rfrob : ∀ x y : M.L.O, (y : E) = M.L.cj x → r y = r x ^ q)
    {ι : Type} [Fintype ι] (G₀ : Matrix ι ι E) (hG1 : ∀ a a', G₀ a a' ∈ M.L.O) :
    Nat.card (Set.range fun v : {v : ι → V // H.Prim Λ v ∧ ∀ a a', H.h (v a') (v a) - G₀ a a' ∈
        Submodule.span M.L.O {algebraMap F E (ϖ : F)}} =>
      fun a => Submodule.Quotient.mk (p := H.smulLat (algebraMap F E (ϖ : F)) Λ) (v.1 a)) =
    Nat.card {X : ι → Fin n → k // LinearIndependent k X ∧
      ∀ a a', ∑ i, ∑ j, X a' i * Ph r H b hint i j * X a j ^ q = r ⟨G₀ a a', hG1 a a'⟩} := by
  let Φ : {v : ι → V // H.Prim Λ v ∧ ∀ a a', H.h (v a') (v a) - G₀ a a' ∈
      Submodule.span M.L.O {algebraMap F E (ϖ : F)}} →
      {X : ι → Fin n → k // LinearIndependent k X ∧
        ∀ a a', ∑ i, ∑ j, X a' i * Ph r H b hint i j * X a j ^ q = r ⟨G₀ a a', hG1 a a'⟩} :=
    fun v => ⟨fun a => red hR (v.1 a), (prim_iff hR H hϖ o2 o3 v.1 v.2.1.1).1 v.2.1,
      fun a a' => (gram_cond_iff hR H hint q rfrob (v.2.1.1 a') (v.2.1.1 a) (G₀ a a') (hG1 a a')).1 (v.2.2 a a')⟩
  have hsurj : Function.Surjective Φ := by
    intro X
    choose x hxΛ hxr using fun a => red_lift hR (X.1 a)
    have hfx : (fun a => red hR (x a)) = X.1 := funext hxr
    have hli : LinearIndependent k (fun a => red hR (x a)) := by rw [hfx]; exact X.2.1
    refine ⟨⟨x, (prim_iff hR H hϖ o2 o3 x hxΛ).2 hli, fun a a' =>
      (gram_cond_iff hR H hint q rfrob (hxΛ a') (hxΛ a) (G₀ a a') (hG1 a a')).2 ?_⟩, ?_⟩
    · rw [hxr, hxr]; exact X.2.2 a a'
    · exact Subtype.ext hfx
  refine Nat.card_congr ((Setoid.quotientKerEquivRange _).symm.trans
    ((Quotient.congrRight ?_).trans (Setoid.quotientKerEquivOfSurjective Φ hsurj)))
  intro v v'
  rw [Setoid.ker_def, Setoid.ker_def]
  constructor
  · intro h
    apply Subtype.ext
    funext a
    have h1 := congrFun h a
    rw [Submodule.Quotient.eq] at h1
    exact (class_iff hR H (v.2.1.1 a) (v'.2.1.1 a)).1 h1
  · intro h
    funext a
    have h1 := congrFun (congrArg Subtype.val h) a
    rw [Submodule.Quotient.eq]
    exact (class_iff hR H (v.2.1.1 a) (v'.2.1.1 a)).2 h1

end FC

end PI.UnitaryGroupMassFormula.CntFormula
end
end

noncomputable section

namespace PI.UnitaryGroupMassFormula.LocDensCorank

open Formalism.MainNotions.S ValuativeRel PI.UnitaryGroupMassFormula.CntFormula
open Classical

theorem fld_dvd_iff {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] (L : Loc.LocE F E) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (a : 𝒪[F]) :
    (∃ z ∈ L.O, algebraMap F E (a : F) = algebraMap F E (ϖ : F) * z) ↔ ϖ ∣ a := by
  have hϖ0 : (ϖ : F) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  constructor
  · rintro ⟨z, hz, he⟩
    have hz' : z = algebraMap F E ((a : F) / ϖ) := by
      rw [div_eq_mul_inv, map_mul, he, mul_comm (algebraMap F E (ϖ : F)) z, mul_assoc, ← map_mul,
        mul_inv_cancel₀ hϖ0, map_one, mul_one]
    have hm : (a : F) / ϖ ∈ 𝒪[F] :=
      PI.UnitaryGroupMassFormula.CntFormula.fl_mem_int L (PI.UnitaryGroupMassFormula.CntFormula.fl_inj L) (hz' ▸ hz)
    refine ⟨⟨_, hm⟩, Subtype.ext ?_⟩
    show (a : F) = (ϖ : F) * ((a : F) / ϖ)
    field_simp
  · rintro ⟨c, rfl⟩
    exact ⟨algebraMap F E (c : F), PI.UnitaryGroupMassFormula.CntFormula.fl_int_mem L c, by simp [map_mul]⟩

theorem fld_count_core {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] [MeasurableSpace E] (M : Loc.Model F E) (hl : IsNonarchimedeanLocalField F)
    (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ)
    (o2 : ∀ x : E, ∃ c : 𝒪[F], c ≠ 0 ∧ algebraMap F E c * x ∈ M.L.O)
    (o3 : ∀ x ∈ M.L.O, x ≠ 0 → ∃ k : ℕ, ∃ u ∈ M.L.O, (∃ w ∈ M.L.O, u * w = 1) ∧ x = algebraMap F E ϖ ^ k * u)
    (k : Type) [Field k] [Fintype k] (r : M.L.O →+* k) (hsurj : Function.Surjective r)
    (hker : ∀ x : M.L.O, r x = 0 ↔ ∃ z ∈ M.L.O, (x : E) = algebraMap F E ϖ * z)
    (hcard : Fintype.card k = Nat.card 𝓀[F] ^ 2)
    (hfrob : ∀ x y : M.L.O, (y : E) = M.L.cj x → r y = r x ^ Nat.card 𝓀[F])
    (V : Type) [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (Λ : Submodule M.L.O V)
    (hΛ : H.IsSelfDual Λ)
    (b : Fin (Module.finrank E V) → V) (hbΛ : ∀ k, b k ∈ Λ) (hbind : LinearIndependent E b)
    (hbcrd : ∀ x ∈ Λ, ∃ c : Fin (Module.finrank E V) → E, (∀ k, c k ∈ M.L.O) ∧ x = ∑ k, c k • b k)
    (Q : Matrix (Fin (Module.finrank E V)) (Fin (Module.finrank E V)) E) (hQO : ∀ k l, Q k l ∈ M.L.O)
    (hQ : Q * Matrix.of (fun k l => H.h (b k) (b l)) = 1)
    (ι : Type) [Fintype ι] [DecidableEq ι] (a : ι → 𝒪[F]) :
    H.dens ϖ Λ (Matrix.diagonal (fun i => algebraMap F E (a i : F))) =
      Formalism.L2.SG.DensExact.densProd (Nat.card 𝓀[F]) (-1)
        (Module.finrank E V) (Fintype.card ι) (Finset.univ.filter fun i => ϖ ∣ a i).card := by
  have := hl
  set G₀ : Matrix ι ι E := Matrix.diagonal (fun i => algebraMap F E (a i : F)) with hG₀
  have hG1 : ∀ x y, G₀ x y ∈ M.L.O := by
    intro x y
    by_cases h : x = y
    · subst h; rw [hG₀, Matrix.diagonal_apply_eq]; exact fl_int_mem M.L (a x)
    · rw [hG₀, Matrix.diagonal_apply_ne _ h]; exact M.L.O.zero_mem
  have hG2 : ∀ x y, G₀ y x = M.L.cj (G₀ x y) := by
    intro x y
    by_cases h : x = y
    · subst h; rw [hG₀, Matrix.diagonal_apply_eq, M.L.cj.commutes]
    · rw [hG₀, Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h), map_zero]
  have hR : FC.RedData ϖ k r (Module.finrank E V) b Λ := ⟨hker, hsurj, hbΛ, hbind, hbcrd⟩
  have hint : ∀ i j, H.h (b i) (b j) ∈ M.L.O := fun i j => (hΛ.2.2 (b i)).1 (hbΛ i) (b j) (hbΛ j)
  have hS := FC.card_count hR H hϖ o2 o3 hint (Nat.card 𝓀[F]) hfrob G₀ hG1
  let _ : Fintype 𝓀[F] := Fintype.ofFinite _
  have hqF : Fintype.card 𝓀[F] = Nat.card 𝓀[F] := Nat.card_eq_fintype_card.symm
  let ψ : 𝒪[F] →+* M.L.O := RingHom.codRestrict ((algebraMap F E).comp (𝒪[F]).subtype) M.L.O
    (fun c => FC.algO c)
  let φ0 : 𝒪[F] →+* k := r.comp ψ
  have hker0 : ∀ a ∈ IsLocalRing.maximalIdeal 𝒪[F], φ0 a = 0 := by
    intro a ha
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.mem_span_singleton'] at ha
    obtain ⟨c, rfl⟩ := ha
    have h0 : r (ψ ϖ) = 0 := (hker _).2 ⟨1, M.L.O.one_mem, by
      show algebraMap F E (ϖ : F) = _
      rw [mul_one]⟩
    simp only [φ0, RingHom.comp_apply, map_mul, h0, mul_zero]
  let ι0 : 𝓀[F] →+* k := Ideal.Quotient.lift (IsLocalRing.maximalIdeal 𝒪[F]) φ0 hker0
  let _ : Algebra 𝓀[F] k := ι0.toAlgebra
  have hfin : Module.finrank 𝓀[F] k = 2 := by
    have h1 := Module.card_eq_pow_finrank (K := 𝓀[F]) (V := k)
    rw [hcard, ← hqF] at h1
    exact (Nat.pow_right_injective (Fintype.one_lt_card (α := 𝓀[F]))).eq_iff.1 h1.symm
  let QO : Matrix (Fin (Module.finrank E V)) (Fin (Module.finrank E V)) M.L.O := fun i j => ⟨Q i j, hQO i j⟩
  let GO : Matrix (Fin (Module.finrank E V)) (Fin (Module.finrank E V)) M.L.O :=
    fun i j => ⟨H.h (b i) (b j), hint i j⟩
  have hQG : QO * GO = 1 := by
    have e1 : QO.map M.L.O.subtype = Q := by ext i j; rfl
    have e2 : GO.map M.L.O.subtype = Matrix.of fun k l => H.h (b k) (b l) := by ext i j; rfl
    apply Matrix.map_injective (f := M.L.O.subtype) Subtype.val_injective
    simp only
    rw [Matrix.map_mul, e1, e2, hQ, Matrix.map_one _ (map_zero _) (map_one _)]
  have hPh : IsUnit (FC.Ph r H b hint).det := by
    have h2 : (QO.map r) * (GO.map r) = 1 := by
      rw [← Matrix.map_mul, hQG, Matrix.map_one _ (map_zero r) (map_one r)]
    exact Matrix.isUnit_det_of_left_inverse h2
  have hPhH : ∀ i j, FC.Ph r H b hint j i = FC.Ph r H b hint i j ^ Fintype.card 𝓀[F] := by
    intro i j
    rw [hqF]
    exact hfrob ⟨H.h (b i) (b j), hint i j⟩ ⟨H.h (b j) (b i), hint j i⟩ (H.h_herm (b i) (b j))
  set m := Fintype.card ι
  let e := Fintype.equivFin ι
  let Gm : Matrix (Fin m) (Fin m) k := fun i j => r ⟨G₀ (e.symm j) (e.symm i), hG1 _ _⟩
  have hGmH : ∀ i j, Gm j i = Gm i j ^ Fintype.card 𝓀[F] := by
    intro i j
    rw [hqF]
    exact hfrob ⟨G₀ (e.symm j) (e.symm i), hG1 _ _⟩ ⟨G₀ (e.symm i) (e.symm j), hG1 _ _⟩
      (hG2 (e.symm j) (e.symm i))

  let d : Fin m → k := fun i => r ⟨algebraMap F E (a (e.symm i) : F), fl_int_mem M.L _⟩
  have hGmd : Gm = Matrix.diagonal d := by
    ext i j
    by_cases h : i = j
    · subst h
      rw [Matrix.diagonal_apply_eq]
      exact congrArg r (Subtype.ext (show G₀ (e.symm i) (e.symm i) = _ from Matrix.diagonal_apply_eq _ _))
    · rw [Matrix.diagonal_apply_ne _ h]
      have hne : e.symm j ≠ e.symm i := fun h' => h (e.symm.injective h').symm
      exact (congrArg r (Subtype.ext (show G₀ (e.symm j) (e.symm i) = 0 from Matrix.diagonal_apply_ne _ hne) :
        (⟨G₀ (e.symm j) (e.symm i), hG1 _ _⟩ : M.L.O) = 0)).trans (map_zero r)
  have hd0 : ∀ i, d i = 0 ↔ ϖ ∣ a (e.symm i) := by
    intro i
    rw [hker]
    exact fld_dvd_iff M.L hϖ _
  have hrank : m - Gm.rank = (Finset.univ.filter fun i => ϖ ∣ a i).card := by
    have hc := Fintype.card_subtype_compl (fun i : Fin m => d i ≠ 0)
    rw [Fintype.card_fin] at hc
    rw [hGmd, Matrix.rank_diagonal, ← hc]
    rw [← Fintype.card_subtype]
    refine Fintype.card_congr ((Equiv.subtypeEquiv e.symm fun i => ?_))
    rw [← hd0]
    exact not_not
  have hT : Nat.card {X : ι → Fin (Module.finrank E V) → k // LinearIndependent k X ∧
      ∀ a a', ∑ i, ∑ j, X a' i * FC.Ph r H b hint i j * X a j ^ Nat.card 𝓀[F] = r ⟨G₀ a a', hG1 a a'⟩} =
      Formalism.L2.SG.DensExact.countInert 𝓀[F] k (Module.finrank E V) m (FC.Ph r H b hint) Gm := by
    unfold Formalism.L2.SG.DensExact.countInert
    rw [← Nat.card_coe_set_eq]
    refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.arrowCongr e (Equiv.refl _)) fun X => ?_)
    simp only [Equiv.arrowCongr_apply, Equiv.coe_refl, Set.mem_ofPred_eq, hqF]
    refine and_congr (linearIndependent_equiv e.symm).symm ⟨fun h i j => h (e.symm j) (e.symm i), fun h a a' => ?_⟩
    have := h (e a') (e a)
    simpa [Gm] using this
  have hD := density_exact_inert 𝓀[F] k hfin (Module.finrank E V) m (FC.Ph r H b hint) Gm hPh hPhH hGmH
  rw [hrank, hqF] at hD
  unfold Loc.HermSp.dens
  rw [hS, hT, ← hD]
  congr 1
  have hq0 : (Nat.card 𝓀[F] : ℝ) ≠ 0 := by
    rw [← hqF]; exact_mod_cast Fintype.card_ne_zero
  rw [show ((2 * Module.finrank E V * m : ℤ) - (m : ℤ) ^ 2) =
      ((2 * Module.finrank E V * m : ℕ) : ℤ) - ((m ^ 2 : ℕ) : ℤ) by push_cast; ring,
    zpow_sub₀ hq0, zpow_natCast, zpow_natCast]

theorem fieldCount_holds : FieldCount := by
  intro F E _ _ _ _ _ _ _ M hl hc hE V _ _ H Λ hΛ ϖ hϖ ι _ _ a _
  obtain ⟨_, o2, o3⟩ := local_density_integral F E M.L hl hc hE ϖ hϖ
  obtain ⟨rmax, rcard, rfrob⟩ := residue_field_count F E M.L hl hc hE ϖ hϖ
  obtain ⟨b, hb1, hb2, hb3, Q, hQ1, hQ2⟩ := flatBasis_of local_density_integral F E M hl hc hE V H Λ hΛ
  let _ : Field (M.L.O ⧸ Ideal.span {piO M.L ϖ}) := Ideal.Quotient.field _
  have hq : 0 < Nat.card 𝓀[F] := Nat.card_pos
  have : Finite (M.L.O ⧸ Ideal.span {piO M.L ϖ}) :=
    Nat.finite_of_card_ne_zero (by rw [rcard]; positivity)
  let _ : Fintype (M.L.O ⧸ Ideal.span {piO M.L ϖ}) := Fintype.ofFinite _
  refine fld_count_core M hl ϖ hϖ o2 o3 (M.L.O ⧸ Ideal.span {piO M.L ϖ})
    (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective ?_ ?_ rfrob V H Λ hΛ b hb1 hb2 hb3 Q hQ1 hQ2 ι a
  · intro x
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨c, c.2, by rw [← hc]; simp [piO, mul_comm]⟩
    · rintro ⟨z, hz, he⟩
      exact ⟨⟨z, hz⟩, Subtype.ext (by simp [piO, he, mul_comm])⟩
  · rw [Fintype.card_eq_nat_card, rcard]

end PI.UnitaryGroupMassFormula.LocDensCorank
