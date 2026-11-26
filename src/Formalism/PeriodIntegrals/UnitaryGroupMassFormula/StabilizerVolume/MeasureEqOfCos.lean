module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensFF

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.MeasureEqOfCos
noncomputable section

namespace PI.VolStabS

open MeasureTheory Topology Set Filter

section CosMeas

variable {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
  [MeasurableSpace X] [OpensMeasurableSpace X]


omit [MeasurableSpace X] [OpensMeasurableSpace X] in
def thick (S : Set X) (Λ : AddSubgroup X) : Set X := {x | ∃ s ∈ S, x - s ∈ Λ}

omit [MeasurableSpace X] [OpensMeasurableSpace X] in
theorem isOpen_thick (S : Set X) (Λ : AddSubgroup X) (hΛ : IsOpen (Λ : Set X)) :
    IsOpen (thick S Λ) := by
  have e : thick S Λ = ⋃ s ∈ S, (fun x => x - s) ⁻¹' (Λ : Set X) := by
    ext x
    simp [thick]
  rw [e]
  exact isOpen_biUnion fun s _ => hΛ.preimage (continuous_id.sub continuous_const)

theorem measure_thick_eq (m1 m2 : Measure X) (Λ : AddSubgroup X) (hΛ : IsOpen (Λ : Set X))
    (h : ∀ y, m1 {z | z - y ∈ Λ} = m2 {z | z - y ∈ Λ}) (S : Set X) (hS : IsCompact S) :
    m1 (thick S Λ) = m2 (thick S Λ) := by
  classical

  have hfib : ∀ c : X ⧸ Λ, m1 (((↑) : X → X ⧸ Λ) ⁻¹' {c}) = m2 (((↑) : X → X ⧸ Λ) ⁻¹' {c}) ∧
      MeasurableSet (((↑) : X → X ⧸ Λ) ⁻¹' {c}) := by
    intro c
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective c
    have e : ((↑) : X → X ⧸ Λ) ⁻¹' {(y : X ⧸ Λ)} = {z | z - y ∈ Λ} := by
      ext z
      simp [QuotientAddGroup.eq_iff_sub_mem]
    rw [e]
    exact ⟨h y, (hΛ.preimage (continuous_id.sub continuous_const)).measurableSet⟩
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover (fun s : S => {z : X | z - (s : X) ∈ Λ})
    (fun s => hΛ.preimage (continuous_id.sub continuous_const))
    (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, by simp⟩)
  have hT : thick S Λ = ⋃ c ∈ t.image (fun s : S => ((s : X) : X ⧸ Λ)),
      ((↑) : X → X ⧸ Λ) ⁻¹' {c} := by
    ext x
    simp only [thick, mem_ofPred_eq, mem_iUnion, mem_preimage, mem_singleton_iff,
      Finset.mem_image, exists_prop]
    constructor
    · rintro ⟨s, hs, hxs⟩
      obtain ⟨s', hs't, hss'⟩ := mem_iUnion₂.mp (ht hs)
      refine ⟨((s' : X) : X ⧸ Λ), ⟨s', hs't, rfl⟩, ?_⟩
      rw [QuotientAddGroup.eq_iff_sub_mem]
      have e : x - (s' : X) = (x - s) + (s - s') := by abel
      rw [e]
      exact Λ.add_mem hxs hss'
    · rintro ⟨c, ⟨s', _, rfl⟩, hx⟩
      exact ⟨s', s'.2, (QuotientAddGroup.eq_iff_sub_mem).mp hx⟩
  rw [hT, measure_biUnion_finset, measure_biUnion_finset]
  · exact Finset.sum_congr rfl fun c _ => (hfib c).1
  all_goals first
    | exact fun c _ c' _ hne => (Set.disjoint_singleton.mpr hne).preimage _
    | exact fun c _ => (hfib c).2


omit [MeasurableSpace X] [OpensMeasurableSpace X] in
theorem iInter_thick (S : Set X) (hSc : IsClosed S) (Λ : ℕ → AddSubgroup X)
    (hb : ∀ N ∈ 𝓝 (0 : X), ∃ n, (Λ n : Set X) ⊆ N) : ⋂ n, thick S (Λ n) = S := by
  ext x
  simp only [mem_iInter]
  constructor
  · intro hx
    by_contra hxS
    have hN : (fun u => x - u) ⁻¹' Sᶜ ∈ 𝓝 (0 : X) := by
      apply (continuous_const.sub continuous_id).continuousAt.preimage_mem_nhds
      simpa using hSc.isOpen_compl.mem_nhds hxS
    obtain ⟨n, hn⟩ := hb _ hN
    obtain ⟨s, hs, hxs⟩ := hx n
    have hmem := hn hxs
    simp only [mem_preimage, mem_compl_iff, sub_sub_cancel] at hmem
    exact hmem hs
  · intro hx n
    exact ⟨x, hx, by simp⟩

theorem measure_eq_of_cos (m1 m2 : Measure X) [IsFiniteMeasure m1]
    (Λ : ℕ → AddSubgroup X) (hΛo : ∀ n, IsOpen (Λ n : Set X)) (hanti : Antitone Λ)
    (hb : ∀ N ∈ 𝓝 (0 : X), ∃ n, (Λ n : Set X) ⊆ N)
    (h : ∀ n y, m1 {z | z - y ∈ Λ n} = m2 {z | z - y ∈ Λ n})
    (S : Set X) (hS : IsCompact S) (hSc : IsClosed S) : m1 S = m2 S := by
  have hmono : Antitone fun n => thick S (Λ n) := by
    intro a c hac x hx
    obtain ⟨s, hs, hxs⟩ := hx
    exact ⟨s, hs, hanti hac hxs⟩
  have hnull : ∀ (μ : Measure X) n, NullMeasurableSet (thick S (Λ n)) μ := fun μ n =>
    (isOpen_thick S (Λ n) (hΛo n)).measurableSet.nullMeasurableSet
  have heq : ∀ n, m1 (thick S (Λ n)) = m2 (thick S (Λ n)) := fun n =>
    measure_thick_eq m1 m2 (Λ n) (hΛo n) (h n) S hS
  rw [← iInter_thick S hSc Λ hb, hmono.measure_iInter (hnull m1) ⟨0, measure_ne_top _ _⟩,
    hmono.measure_iInter (hnull m2) ⟨0, by rw [← heq 0]; exact measure_ne_top _ _⟩]
  simp only [heq]

end CosMeas

theorem cosDens_holds : CosDens := by
  unfold CosDens
  intro X _ _ _ _ _ _ ν m _ _ H hHo _ hanti hb c0 κ hm0 hcos S hS
  have hle : ∀ n, H n ≤ H 0 := fun n => hanti (Nat.zero_le n)
  have hcos' : ∀ n y, m {z | z - y ∈ H n} = ((κ • ν).restrict {z | z - c0 ∈ H 0}) {z | z - y ∈ H n} := by
    intro n y
    have hmeas : MeasurableSet {z : X | z - y ∈ H n} :=
      ((hHo n).preimage (continuous_id.sub continuous_const)).measurableSet
    rw [Measure.restrict_apply hmeas, Measure.smul_apply, smul_eq_mul]
    by_cases hy : y - c0 ∈ H 0
    · have hsub : {z : X | z - y ∈ H n} ∩ {z | z - c0 ∈ H 0} = {z | z - y ∈ H n} := by
        apply inter_eq_left.mpr
        intro z hz
        have e : z - c0 = (z - y) + (y - c0) := by abel
        show z - c0 ∈ H 0
        rw [e]
        exact (H 0).add_mem (hle n hz) hy
      rw [hsub]
      exact hcos n y hy
    ·
      have hout : ∀ z, z - y ∈ H n → z - c0 ∉ H 0 := by
        intro z hz hz0
        apply hy
        have e : y - c0 = (z - c0) - (z - y) := by abel
        rw [e]
        exact (H 0).sub_mem hz0 (hle n hz)
      have hempty : {z : X | z - y ∈ H n} ∩ {z | z - c0 ∈ H 0} = ∅ := by
        ext z
        simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
        exact hout z
      rw [hempty, measure_empty, mul_zero]
      exact measure_mono_null (fun z hz => hout z hz) hm0
  rw [measure_eq_of_cos m _ H hHo hanti hb hcos' S hS hS.isClosed,
    Measure.restrict_apply hS.isClosed.measurableSet, Measure.smul_apply, smul_eq_mul]

end PI.VolStabS
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.HenselCountHolds
noncomputable section

namespace PI.VolStabS

open MeasureTheory Topology

section Hensel

variable {V X : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [BorelSpace V] [AddCommGroup X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [MeasurableSpace X] [BorelSpace X]

def hlev (Λ0 : AddSubgroup V) (H : AddSubgroup X) (G : V → X) (y : V) (h : X) : Set V :=
  {Z | Z ∈ Λ0 ∧ G (y + Z) - h ∈ H}

theorem hensel_main (μ : Measure V) (ν : Measure X) [μ.IsAddHaarMeasure] [ν.IsAddHaarMeasure]
    (Λ : ℕ → AddSubgroup V) (H : ℕ → AddSubgroup X) (hΛo : ∀ n, IsOpen (Λ n : Set V))
    (hΛa : Antitone Λ) (hHo : ∀ n, IsOpen (H n : Set X)) (hHc : ∀ n, IsCompact (H n : Set X))
    (D : V →+ X) (hD : ∀ n, (Λ n).map D = H n) (G : V → X) (y : V)
    (hG : ∀ n, ∀ Z ∈ Λ 0, ∀ W ∈ Λ n, G (y + Z + W) - G (y + Z) - D W ∈ H (n + 1))
    (h : X) (hh : h - G y ∈ H 0) (n : ℕ) :
    μ (hlev (Λ 0) (H n) G y h) * ν (H 0) = μ (Λ 0) * ν (H n) := by
  classical
  obtain ⟨f, hf⟩ : ∃ f : V → X, ∀ Z, f Z = G (y + Z) - h := ⟨_, fun _ => rfl⟩
  have memS : ∀ m Z, Z ∈ hlev (Λ 0) (H m) G y h ↔ Z ∈ Λ 0 ∧ f Z ∈ H m := by
    intro m Z; rw [hf]; rfl
  have hHa : ∀ m, H (m + 1) ≤ H m := fun m => by
    rw [← hD, ← hD]; exact AddSubgroup.map_mono (hΛa (Nat.le_succ m))
  have hΛ0 : ∀ m, Λ m ≤ Λ 0 := fun m => hΛa (Nat.zero_le m)
  have hDm : ∀ m, ∀ W ∈ Λ m, D W ∈ H m := fun m W hW => by
    rw [← hD]; exact AddSubgroup.mem_map_of_mem D hW

  have hstep : ∀ m, ∀ Z ∈ Λ 0, ∀ W ∈ Λ m, f (Z + W) - f Z - D W ∈ H (m + 1) := by
    intro m Z hZ W hW
    have e := hG m Z hZ W hW
    have : f (Z + W) - f Z - D W = G (y + Z + W) - G (y + Z) - D W := by
      rw [hf, hf, ← add_assoc]; abel
    rw [this]; exact e

  have hinv : ∀ m, ∀ Z ∈ hlev (Λ 0) (H m) G y h, ∀ W ∈ Λ m, Z + W ∈ hlev (Λ 0) (H m) G y h := by
    intro m Z hZ W hW
    rw [memS] at hZ ⊢
    refine ⟨(Λ 0).add_mem hZ.1 (hΛ0 m hW), ?_⟩
    have e := hstep m Z hZ.1 W hW
    have : f (Z + W) = (f (Z + W) - f Z - D W) + f Z + D W := by abel
    rw [this]
    exact (H m).add_mem ((H m).add_mem (hHa m e) hZ.2) (hDm m W hW)
  have hopen : ∀ m, IsOpen (hlev (Λ 0) (H m) G y h) := by
    intro m
    rw [isOpen_iff_forall_mem_open]
    intro Z hZ
    refine ⟨(fun u => -Z + u) ⁻¹' (Λ m : Set V), ?_,
      (hΛo m).preimage (continuous_const.add continuous_id), ?_⟩
    · intro u hu
      have := hinv m Z hZ _ hu
      have e : Z + (-Z + u) = u := by abel
      rw [e] at this; exact this
    · show -Z + Z ∈ Λ m
      rw [neg_add_cancel]; exact (Λ m).zero_mem
  have hsub : ∀ m, hlev (Λ 0) (H (m + 1)) G y h ⊆ hlev (Λ 0) (H m) G y h := by
    intro m Z hZ
    rw [memS] at hZ ⊢
    exact ⟨hZ.1, hHa m hZ.2⟩
  induction n with
  | zero =>
    have hS0 : hlev (Λ 0) (H 0) G y h = (Λ 0 : Set V) := by
      ext Z
      rw [memS]
      refine ⟨And.left, fun hZ => ⟨hZ, ?_⟩⟩
      have e := hstep 0 0 (Λ 0).zero_mem Z hZ
      have h0 : f 0 ∈ H 0 := by
        have : f 0 = -(h - G y) := by rw [hf, add_zero]; abel
        rw [this]; exact (H 0).neg_mem hh
      have : f Z = (f (0 + Z) - f 0 - D Z) + f 0 + D Z := by rw [zero_add]; abel
      rw [this]
      exact (H 0).add_mem ((H 0).add_mem (hHa 0 e) h0) (hDm 0 Z hZ)
    rw [hS0]
  | succ m ih =>

    haveI : DiscreteTopology (X ⧸ H (m + 1)) := QuotientAddGroup.discreteTopology (hHo (m + 1))
    set C : Set (X ⧸ H (m + 1)) := (QuotientAddGroup.mk : X → X ⧸ H (m + 1)) '' (H m : Set X)
      with hC
    have hCf : C.Finite := ((hHc m).image QuotientAddGroup.continuous_mk).finite_of_discrete
    haveI : Fintype C := hCf.fintype
    have hxc : ∀ c : C, ∃ u ∈ H m, (u : X ⧸ H (m + 1)) = c := fun c => c.2
    choose x hxm hxq using hxc
    have htc : ∀ c : C, ∃ W ∈ Λ m, D W = x c := by
      intro c
      have := hxm c
      rw [← hD] at this
      exact AddSubgroup.mem_map.1 this
    choose t htm htD using htc
    have hcov : ∀ u ∈ H m, ∃ c : C, -x c + u ∈ H (m + 1) := by
      intro u hu
      refine ⟨⟨(u : X ⧸ H (m + 1)), u, hu, rfl⟩, ?_⟩
      rw [← QuotientAddGroup.eq, hxq]
    have hinj : ∀ c d : C, -x c + x d ∈ H (m + 1) → c = d := by
      intro c d hcd
      apply Subtype.ext
      rw [← hxq c, ← hxq d]
      exact QuotientAddGroup.eq.2 hcd
    have hne : Nonempty C := ⟨(hcov 0 (H m).zero_mem).choose⟩

    have hAi : ∀ c Z, Z ∈ (fun Z => -t c + Z) ⁻¹' hlev (Λ 0) (H (m + 1)) G y h →
        -x c + f Z ∈ H (m + 1) := by
      intro c Z hZ
      have hZ' := (memS _ _).1 hZ
      have e := hstep m (-t c + Z) hZ'.1 (t c) (htm c)
      have e2 : -t c + Z + t c = Z := by abel
      rw [e2, htD] at e
      have : -x c + f Z = (f Z - f (-t c + Z) - x c) + f (-t c + Z) := by abel
      rw [this]
      exact (H (m + 1)).add_mem e hZ'.2
    have hμ : μ (hlev (Λ 0) (H m) G y h) =
        (Fintype.card C : ENNReal) * μ (hlev (Λ 0) (H (m + 1)) G y h) := by
      have hU : hlev (Λ 0) (H m) G y h =
          ⋃ c : C, (fun Z => -t c + Z) ⁻¹' hlev (Λ 0) (H (m + 1)) G y h := by
        ext Z
        simp only [Set.mem_iUnion, Set.mem_preimage]
        constructor
        · intro hZ
          have hZ' := (memS _ _).1 hZ
          obtain ⟨c, hc⟩ := hcov (f Z) hZ'.2
          refine ⟨c, (memS _ _).2 ⟨(Λ 0).add_mem ((Λ 0).neg_mem (hΛ0 m (htm c))) hZ'.1, ?_⟩⟩
          have e := hstep m (-t c + Z) ((Λ 0).add_mem ((Λ 0).neg_mem (hΛ0 m (htm c))) hZ'.1)
            (t c) (htm c)
          have e2 : -t c + Z + t c = Z := by abel
          rw [e2, htD] at e
          have : f (-t c + Z) = -(f Z - f (-t c + Z) - x c) + (-x c + f Z) := by abel
          rw [this]
          exact (H (m + 1)).add_mem ((H (m + 1)).neg_mem e) hc
        · rintro ⟨c, hc⟩
          have := hinv m _ (hsub m hc) (t c) (htm c)
          have e2 : -t c + Z + t c = Z := by abel
          rwa [e2] at this
      rw [hU, measure_iUnion, tsum_fintype]
      · simp only [measure_preimage_add, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      · intro c d hcd
        rw [Function.onFun, Set.disjoint_left]
        intro Z hc hd
        apply hcd
        apply hinj
        have a1 := hAi c Z hc
        have a2 := hAi d Z hd
        have : -x c + x d = (-x c + f Z) - (-x d + f Z) := by abel
        rw [this]; exact (H (m + 1)).sub_mem a1 a2
      · intro c
        exact ((hopen (m + 1)).preimage (continuous_const.add continuous_id)).measurableSet
    have hν : ν (H m) = (Fintype.card C : ENNReal) * ν (H (m + 1)) := by
      have hU : (H m : Set X) = ⋃ c : C, (fun u => -x c + u) ⁻¹' (H (m + 1) : Set X) := by
        ext u
        simp only [Set.mem_iUnion, Set.mem_preimage, SetLike.mem_coe]
        constructor
        · intro hu; exact hcov u hu
        · rintro ⟨c, hc⟩
          have : u = x c + (-x c + u) := by abel
          rw [this]; exact (H m).add_mem (hxm c) (hHa m hc)
      rw [hU, measure_iUnion, tsum_fintype]
      · simp only [measure_preimage_add, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      · intro c d hcd
        rw [Function.onFun, Set.disjoint_left]
        intro u hc hd
        apply hcd
        apply hinj
        simp only [Set.mem_preimage, SetLike.mem_coe] at hc hd
        have : -x c + x d = (-x c + u) - (-x d + u) := by abel
        rw [this]; exact (H (m + 1)).sub_mem hc hd
      · intro c
        exact ((hHo (m + 1)).preimage (continuous_const.add continuous_id)).measurableSet
    have hc0 : (Fintype.card C : ENNReal) ≠ 0 := by
      exact_mod_cast (Fintype.card_ne_zero : Fintype.card C ≠ 0)
    have hct : (Fintype.card C : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
    apply (ENNReal.mul_right_inj hc0 hct).1
    calc (Fintype.card C : ENNReal) * (μ (hlev (Λ 0) (H (m + 1)) G y h) * ν (H 0))
        = μ (hlev (Λ 0) (H m) G y h) * ν (H 0) := by rw [hμ, mul_assoc]
      _ = μ (Λ 0) * ν (H m) := ih
      _ = (Fintype.card C : ENNReal) * (μ (Λ 0) * ν (H (m + 1))) := by rw [hν]; ring

end Hensel

theorem henselCount_holds : HenselCount := by
  intro V X _ _ _ _ _ _ _ _ _ _ μ ν _ _ Λ H hΛo _ hΛa hHo hHc D hD G y hG n h hh
  exact hensel_main μ ν Λ H hΛo hΛa hHo hHc D hD G y hG h hh n

end PI.VolStabS
end
end
