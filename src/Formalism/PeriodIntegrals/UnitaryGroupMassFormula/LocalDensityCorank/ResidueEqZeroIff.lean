module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DoubleSumEqDotProduct
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalDensityCorank.SplitCount

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.GramIff
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.MemSmulLatCoord
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DensGSDvr
noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open Classical ValuativeRel

section Dvr

variable (F : Type) [Field F] [ValuativeRel F]

def resF (x : F) : 𝓀[F] := if h : x ∈ 𝒪[F] then IsLocalRing.residue 𝒪[F] ⟨x, h⟩ else 0

def liftF (c : 𝓀[F]) : F := ((IsLocalRing.residue_surjective c).choose : 𝒪[F])

theorem resF_coe (o : 𝒪[F]) : resF F (o : F) = IsLocalRing.residue 𝒪[F] o := by
  rw [resF, dite_eq_left o.2]

theorem liftF_mem (c : 𝓀[F]) : liftF F c ∈ 𝒪[F] :=
  (IsLocalRing.residue_surjective c).choose.2

theorem resF_liftF (c : 𝓀[F]) : resF F (liftF F c) = c := by
  rw [liftF, resF_coe]
  exact (IsLocalRing.residue_surjective c).choose_spec

theorem resF_one : resF F 1 = 1 := by
  simpa using resF_coe F 1

theorem resF_mul {x y : F} (hx : x ∈ 𝒪[F]) (hy : y ∈ 𝒪[F]) : resF F (x * y) = resF F x * resF F y := by
  have h := resF_coe F (⟨x, hx⟩ * ⟨y, hy⟩)
  rw [map_mul, ← resF_coe F ⟨x, hx⟩, ← resF_coe F ⟨y, hy⟩] at h
  exact h

theorem resF_sum_mul {ι : Type} [Fintype ι] (c x : ι → F) (hc : ∀ i, c i ∈ 𝒪[F]) (hx : ∀ i, x i ∈ 𝒪[F]) :
    resF F (∑ i, c i * x i) = ∑ i, resF F (c i) * resF F (x i) := by
  have hs : ((∑ i, (⟨c i, hc i⟩ : 𝒪[F]) * ⟨x i, hx i⟩ : 𝒪[F]) : F) = ∑ i, c i * x i := by
    simp
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← hs, resF_coe, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, ← resF_coe F ⟨c i, hc i⟩, ← resF_coe F ⟨x i, hx i⟩]

theorem resF_eq_zero_of_lt {x : F} (hx : valuation F x < 1) : resF F x = 0 := by
  have hx1 : x ∈ 𝒪[F] := (Valuation.mem_integer_iff _ _).2 hx.le
  rw [show x = ((⟨x, hx1⟩ : 𝒪[F]) : F) from rfl, resF_coe, IsLocalRing.residue_eq_zero_iff,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    (Valuation.integer.integers _).isUnit_iff_valuation_eq_one]
  exact hx.ne

theorem dvd_of_resF_eq_zero [IsDiscreteValuationRing 𝒪[F]] {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {x : F}
    (hx : x ∈ 𝒪[F]) (h0 : resF F x = 0) : ∃ o : 𝒪[F], x = (ϖ : F) * o := by
  rw [show x = ((⟨x, hx⟩ : 𝒪[F]) : F) from rfl, resF_coe, IsLocalRing.residue_eq_zero_iff,
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.mem_span_singleton'] at h0
  obtain ⟨a, ha⟩ := h0
  refine ⟨a, ?_⟩
  rw [show x = ((⟨x, hx⟩ : 𝒪[F]) : F) from rfl, ← ha]
  push_cast
  ring

theorem resF_irr {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) : resF F (ϖ : F) = 0 := by
  rw [resF_coe, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact hϖ.not_isUnit

def SatF {ι : Type} [Fintype ι] {n : ℕ} (X : ι → Fin n → F) : Prop :=
  ∀ u : Fin n → F, (∀ k, u k ∈ 𝒪[F]) → (∃ c : ι → F, ∑ i, c i • X i = u) →
    ∃ c : ι → F, (∀ i, c i ∈ 𝒪[F]) ∧ ∑ i, c i • X i = u

def redM {ι : Type} {n : ℕ} (X : ι → Fin n → F) : ι → Fin n → 𝓀[F] := fun i k => resF F (X i k)

variable {F}

theorem key_norm {ι : Type} [Fintype ι] {n : ℕ} (X : ι → Fin n → F) (hX : ∀ i k, X i k ∈ 𝒪[F])
    (hred : LinearIndependent 𝓀[F] (redM F X)) (c : ι → F) (u : Fin n → F) (hu : ∑ i, c i • X i = u)
    (j : ι) (hj : ∀ i, valuation F (c i) ≤ valuation F (c j)) (hcj : c j ≠ 0)
    (hlt : ∀ k, valuation F (u k) < valuation F (c j)) : False := by
  have hvj : 0 < valuation F (c j) := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hcj)
  have hd : ∀ i, c i / c j ∈ 𝒪[F] := fun i =>
    (Valuation.mem_integer_iff _ _).2 (by rw [map_div₀]; exact (div_le_one₀ hvj).2 (hj i))
  have hz : ∑ i, resF F (c i / c j) • redM F X i = 0 := by
    funext k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, redM, Pi.zero_apply]
    have h := resF_sum_mul F (fun i => c i / c j) (fun i => X i k) hd (fun i => hX i k)
    rw [← h]
    apply resF_eq_zero_of_lt F
    have hs : ∑ i, c i / c j * X i k = u k / c j := by
      rw [← hu, Finset.sum_apply, Finset.sum_div]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [hs, map_div₀]
    exact (div_lt_one₀ hvj).2 (hlt k)
  have h1 := (Fintype.linearIndependent_iff.1 hred) _ hz j
  rw [div_self hcj, resF_one] at h1
  exact one_ne_zero h1

theorem indep_of_red {ι : Type} [Fintype ι] {n : ℕ} (X : ι → Fin n → F) (hX : ∀ i k, X i k ∈ 𝒪[F])
    (hred : LinearIndependent 𝓀[F] (redM F X)) : LinearIndependent F X := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  by_contra hne
  push_neg at hne
  obtain ⟨i0, hi0⟩ := hne
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun i => valuation F (g i))
    ⟨i0, Finset.mem_univ _⟩
  have hcj : g j ≠ 0 := by
    intro h
    have h2 := hj i0 (Finset.mem_univ _)
    rw [h, map_zero] at h2
    exact hi0 ((Valuation.zero_iff _).1 (le_antisymm h2 zero_le'))
  refine key_norm X hX hred g 0 hg j (fun i => hj i (Finset.mem_univ _)) hcj (fun k => ?_)
  rw [Pi.zero_apply, map_zero]
  exact zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hcj)

theorem sat_of_red {ι : Type} [Fintype ι] {n : ℕ} (X : ι → Fin n → F) (hX : ∀ i k, X i k ∈ 𝒪[F])
    (hred : LinearIndependent 𝓀[F] (redM F X)) : SatF F X := by
  intro u hu hex
  obtain ⟨c, hc⟩ := hex
  refine ⟨c, fun i => ?_, hc⟩
  by_contra hci
  rw [Valuation.mem_integer_iff, not_le] at hci
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun i => valuation F (c i))
    ⟨i, Finset.mem_univ _⟩
  have hj1 : 1 < valuation F (c j) := lt_of_lt_of_le hci (hj i (Finset.mem_univ _))
  have hcj : c j ≠ 0 := by
    intro h
    rw [h, map_zero] at hj1
    exact not_lt.2 zero_le' hj1
  exact key_norm X hX hred c u hc j (fun i => hj i (Finset.mem_univ _)) hcj
    (fun k => lt_of_le_of_lt ((Valuation.mem_integer_iff _ _).1 (hu k)) hj1)

theorem red_of_indep_sat [IsDiscreteValuationRing 𝒪[F]] {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ)
    {ι : Type} [Fintype ι] {n : ℕ} (X : ι → Fin n → F) (hX : ∀ i k, X i k ∈ 𝒪[F])
    (hind : LinearIndependent F X) (hsat : SatF F X) : LinearIndependent 𝓀[F] (redM F X) := by
  rw [Fintype.linearIndependent_iff]
  intro a ha i
  obtain ⟨d, hdm, hres⟩ : ∃ d : ι → F, (∀ i, d i ∈ 𝒪[F]) ∧ ∀ i, resF F (d i) = a i :=
    ⟨fun i => liftF F (a i), fun i => liftF_mem F _, fun i => resF_liftF F _⟩
  have hcomp : ∀ k, (∑ i, d i • X i) k = ∑ i, d i * X i k := fun k => by
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hmem : ∀ k, (∑ i, d i • X i) k ∈ 𝒪[F] := fun k => by
    rw [hcomp]
    exact Subring.sum_mem _ fun i _ => Subring.mul_mem _ (hdm i) (hX i k)
  have hr0 : ∀ k, resF F ((∑ i, d i • X i) k) = 0 := fun k => by
    have h := resF_sum_mul F d (fun i => X i k) hdm (fun i => hX i k)
    rw [hcomp, h]
    simp only [hres]
    have h2 := congrFun ha k
    simpa [Finset.sum_apply, redM] using h2
  choose w hw using fun k => dvd_of_resF_eq_zero F hϖ (hmem k) (hr0 k)
  have hϖ0 : (ϖ : F) ≠ 0 := by exact_mod_cast hϖ.ne_zero
  obtain ⟨c', hc'm, hc'⟩ := hsat (fun k => (w k : F)) (fun k => (w k).2)
    ⟨fun i => d i / ϖ, by
      funext k
      have e := hw k
      rw [hcomp] at e
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      simp_rw [div_mul_eq_mul_div]
      rw [← Finset.sum_div, e]
      field_simp⟩
  have hzero : ∑ i, (d i - ϖ * c' i) • X i = 0 := by
    funext k
    have e1 := congrFun hc' k
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at e1
    have e2 := hw k
    rw [hcomp] at e2
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sub_mul, Finset.sum_sub_distrib,
      Pi.zero_apply]
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, e1, e2, sub_self]
  have hdi := (Fintype.linearIndependent_iff.1 hind) _ hzero i
  rw [← hres i, sub_eq_zero.1 hdi, resF_mul F ϖ.2 (hc'm i), resF_irr F hϖ, zero_mul]

theorem dvr_prim_iff [IsDiscreteValuationRing 𝒪[F]] {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ)
    {ι : Type} [Fintype ι] {n : ℕ} (X : ι → Fin n → F) (hX : ∀ i k, X i k ∈ 𝒪[F]) :
    (LinearIndependent F X ∧ SatF F X) ↔ LinearIndependent 𝓀[F] (redM F X) :=
  ⟨fun h => red_of_indep_sat hϖ X hX h.1 h.2, fun h => ⟨indep_of_red X hX h, sat_of_red X hX h⟩⟩

end Dvr

end PI.UnitaryGroupMassFormula.CntFormula
end
end

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S
open Classical ValuativeRel

section Coord

variable {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E}
  {V : Type} [AddCommGroup V] [Module E V]

def InP (ϖ : 𝒪[F]) (u : F) : Prop := ∃ o : 𝒪[F], u = (ϖ : F) * o

theorem e_alg (e : E ≃ₐ[F] F × F) (c : F) : e (algebraMap F E c) = (c, c) := by
  first
  | (rw [e.commutes]; rfl)
  | simp [e.commutes]

theorem pi_smulF (e : E ≃ₐ[F] F × F) {n : ℕ} (π : V ≃+ (Fin n → F) × (Fin n → F))
    (hπ : ∀ (a : E) (x : V), π (a • x) = ((e a).1 • (π x).1, (e a).2 • (π x).2)) (c : F) (x : V) :
    π (algebraMap F E c • x) = (c • (π x).1, c • (π x).2) := by
  rw [hπ, e_alg]

theorem mem_smulLat_iff' (H : Loc.HermSp M V) (Λ : Submodule M.L.O V) (c : E) (x : V) :
    x ∈ H.smulLat c Λ ↔ ∃ y ∈ Λ, x = c • y := by
  unfold Loc.HermSp.smulLat
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨y, hy, rfl⟩ := hz
      exact ⟨y, hy, rfl⟩
    | zero => exact ⟨0, Λ.zero_mem, (smul_zero c).symm⟩
    | add z w _ _ hz hw =>
      obtain ⟨y, hy, rfl⟩ := hz
      obtain ⟨y', hy', rfl⟩ := hw
      exact ⟨y + y', Λ.add_mem hy hy', (smul_add c y y').symm⟩
    | smul a z _ hz =>
      obtain ⟨y, hy, rfl⟩ := hz
      refine ⟨a • y, Λ.smul_mem a hy, ?_⟩
      first
      | exact smul_comm a c y
      | exact (smul_comm c a y).symm
      | (show ((a : E)) • c • y = c • ((a : E) • y); exact smul_comm _ _ _)
  · rintro ⟨y, hy, rfl⟩
    exact Submodule.subset_span ⟨y, hy, rfl⟩

theorem mem_smulLat_coord (e : E ≃ₐ[F] F × F) (H : Loc.HermSp M V) (Λ : Submodule M.L.O V) {n : ℕ}
    (π : V ≃+ (Fin n → F) × (Fin n → F))
    (hπa : ∀ (a : E) (x : V), π (a • x) = ((e a).1 • (π x).1, (e a).2 • (π x).2))
    (hπL : ∀ x : V, x ∈ Λ ↔ (∀ k, (π x).1 k ∈ 𝒪[F]) ∧ ∀ k, (π x).2 k ∈ 𝒪[F]) (ϖ : 𝒪[F]) (x : V) :
    x ∈ H.smulLat (algebraMap F E ϖ) Λ ↔ (∀ k, InP ϖ ((π x).1 k)) ∧ ∀ k, InP ϖ ((π x).2 k) := by
  rw [mem_smulLat_iff']
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [pi_smulF e π hπa]
    obtain ⟨h1, h2⟩ := (hπL y).1 hy
    exact ⟨fun k => ⟨⟨_, h1 k⟩, by simp [Pi.smul_apply, smul_eq_mul]⟩,
      fun k => ⟨⟨_, h2 k⟩, by simp [Pi.smul_apply, smul_eq_mul]⟩⟩
  · rintro ⟨h1, h2⟩
    choose o1 ho1 using h1
    choose o2 ho2 using h2
    refine ⟨π.symm ((fun k => (o1 k : F)), (fun k => (o2 k : F))), ?_, ?_⟩
    · rw [hπL, AddEquiv.apply_symm_apply]
      exact ⟨fun k => (o1 k).2, fun k => (o2 k).2⟩
    · apply π.injective
      rw [pi_smulF e π hπa, AddEquiv.apply_symm_apply]
      ext k <;> simp [ho1, ho2, Pi.smul_apply, smul_eq_mul]

theorem inP_sub_iff [IsDiscreteValuationRing 𝒪[F]] {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {u w : F}
    (hu : u ∈ 𝒪[F]) (hw : w ∈ 𝒪[F]) : InP ϖ (u - w) ↔ resF F u = resF F w := by
  have key : ∀ d : 𝒪[F], InP ϖ (d : F) ↔ ϖ ∣ d := by
    intro d
    constructor
    · rintro ⟨o, ho⟩
      exact ⟨o, Subtype.ext (by simp [ho])⟩
    · rintro ⟨o, rfl⟩
      exact ⟨o, by simp⟩
  have e1 : resF F u = IsLocalRing.residue 𝒪[F] ⟨u, hu⟩ := by
    first
    | simp [resF, hu]
    | (unfold resF; rw [dite_eq_left hu])
  have e2 : resF F w = IsLocalRing.residue 𝒪[F] ⟨w, hw⟩ := by
    first
    | simp [resF, hw]
    | (unfold resF; rw [dite_eq_left hw])
  have hs : (u - w : F) = ((⟨u, hu⟩ - ⟨w, hw⟩ : 𝒪[F]) : F) := rfl
  have hm : IsLocalRing.maximalIdeal 𝒪[F] = Ideal.span {ϖ} := by
    first
    | exact hϖ.maximalIdeal_eq
    | exact (IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 hϖ
  rw [e1, e2, hs, key, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, hm, Ideal.mem_span_singleton]

theorem mk_eq_iff [IsDiscreteValuationRing 𝒪[F]] (e : E ≃ₐ[F] F × F) (H : Loc.HermSp M V)
    (Λ : Submodule M.L.O V) {n : ℕ} (π : V ≃+ (Fin n → F) × (Fin n → F))
    (hπa : ∀ (a : E) (x : V), π (a • x) = ((e a).1 • (π x).1, (e a).2 • (π x).2))
    (hπL : ∀ x : V, x ∈ Λ ↔ (∀ k, (π x).1 k ∈ 𝒪[F]) ∧ ∀ k, (π x).2 k ∈ 𝒪[F]) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ)
    {x y : V} (hx : x ∈ Λ) (hy : y ∈ Λ) :
    Submodule.Quotient.mk (p := H.smulLat (algebraMap F E ϖ) Λ) x =
        Submodule.Quotient.mk (p := H.smulLat (algebraMap F E ϖ) Λ) y ↔
      (∀ k, resF F ((π x).1 k) = resF F ((π y).1 k)) ∧ ∀ k, resF F ((π x).2 k) = resF F ((π y).2 k) := by
  rw [Submodule.Quotient.eq, mem_smulLat_coord e H Λ π hπa hπL ϖ]
  obtain ⟨hx1, hx2⟩ := (hπL x).1 hx
  obtain ⟨hy1, hy2⟩ := (hπL y).1 hy
  simp only [map_sub, Prod.fst_sub, Prod.snd_sub, Pi.sub_apply]
  exact and_congr (forall_congr' fun k => inP_sub_iff hϖ (hx1 k) (hy1 k))
    (forall_congr' fun k => inP_sub_iff hϖ (hx2 k) (hy2 k))

theorem mem_span_irr_iff (e : E ≃ₐ[F] F × F)
    (hO : ∀ x : E, x ∈ M.L.O ↔ (e x).1 ∈ 𝒪[F] ∧ (e x).2 ∈ 𝒪[F]) (ϖ : 𝒪[F]) (z : E) :
    z ∈ Submodule.span M.L.O {algebraMap F E (ϖ : F)} ↔ InP ϖ (e z).1 ∧ InP ϖ (e z).2 := by
  rw [Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, rfl⟩
    have ha := (hO a).1 a.2
    refine ⟨⟨⟨(e a).1, ha.1⟩, ?_⟩, ⟨⟨(e a).2, ha.2⟩, ?_⟩⟩ <;>
      simp [Subring.smul_def, Submonoid.smul_def, Subalgebra.smul_def, map_mul, e_alg, mul_comm]
  · rintro ⟨⟨o1, h1⟩, ⟨o2, h2⟩⟩
    have hmem : e.symm ((o1 : F), (o2 : F)) ∈ M.L.O := by
      rw [hO, AlgEquiv.apply_symm_apply]
      exact ⟨o1.2, o2.2⟩
    refine ⟨⟨_, hmem⟩, ?_⟩
    apply e.injective
    ext <;> simp [Subring.smul_def, Submonoid.smul_def, Subalgebra.smul_def, map_mul, e_alg, h1, h2, mul_comm]

theorem resF_bil {n : ℕ} (x y : Fin n → F) (hx : ∀ k, x k ∈ 𝒪[F]) (hy : ∀ k, y k ∈ 𝒪[F])
    (Ph : Matrix (Fin n) (Fin n) 𝒪[F]) :
    resF F (∑ k, ∑ l, x k * (Ph k l : F) * y l) =
      ∑ k, ∑ l, resF F (x k) * IsLocalRing.residue 𝒪[F] (Ph k l) * resF F (y l) := by
  have hc : ∀ (a : F) (ha : a ∈ 𝒪[F]), resF F a = IsLocalRing.residue 𝒪[F] ⟨a, ha⟩ := by
    intro a ha
    first
    | simp [resF, ha]
    | (unfold resF; rw [dite_eq_left ha])
  have hsum : (∑ k, ∑ l, x k * (Ph k l : F) * y l) =
      ((∑ k, ∑ l, (⟨x k, hx k⟩ : 𝒪[F]) * Ph k l * (⟨y l, hy l⟩ : 𝒪[F]) : 𝒪[F]) : F) := by
    first
    | (push_cast; rfl)
    | (simp only [AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul]; rfl)
    | (simp only [AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul])
    | (push_cast; simp)
    | simp
  have hxk : ∀ k, resF F (x k) = IsLocalRing.residue 𝒪[F] ⟨x k, hx k⟩ := fun k => hc _ (hx k)
  have hyl : ∀ l, resF F (y l) = IsLocalRing.residue 𝒪[F] ⟨y l, hy l⟩ := fun l => hc _ (hy l)
  have hc' : ∀ z : 𝒪[F], resF F (z : F) = IsLocalRing.residue 𝒪[F] z := fun z => hc z z.2
  rw [hsum, hc']
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, hxk, hyl]

theorem bil_mem {n : ℕ} (x y : Fin n → F) (hx : ∀ k, x k ∈ 𝒪[F]) (hy : ∀ k, y k ∈ 𝒪[F])
    (Ph : Matrix (Fin n) (Fin n) 𝒪[F]) : (∑ k, ∑ l, x k * (Ph k l : F) * y l) ∈ 𝒪[F] := by
  exact sum_mem fun k _ => sum_mem fun l _ => mul_mem (mul_mem (hx k) (Ph k l).2) (hy l)

end Coord

end PI.UnitaryGroupMassFormula.CntFormula
end
end

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S
open Classical ValuativeRel

section Coord2

variable {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E] {M : Loc.Model F E}
  {V : Type} [AddCommGroup V] [Module E V]

theorem gram_iff [IsDiscreteValuationRing 𝒪[F]] (e : E ≃ₐ[F] F × F)
    (hes : ∀ x, e (M.L.cj x) = (e x).swap)
    (hO : ∀ x : E, x ∈ M.L.O ↔ (e x).1 ∈ 𝒪[F] ∧ (e x).2 ∈ 𝒪[F]) (H : Loc.HermSp M V)
    (Λ : Submodule M.L.O V) {n : ℕ} (π : V ≃+ (Fin n → F) × (Fin n → F)) (Ph : Matrix (Fin n) (Fin n) 𝒪[F])
    (hπ : IsSplitCoord e H Λ π Ph) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {ι : Type} [Fintype ι] (G₀ : Matrix ι ι E)
    (h1 : ∀ a b, G₀ a b ∈ M.L.O) (h2 : ∀ a b, G₀ b a = M.L.cj (G₀ a b)) (v : ι → V) (hv : ∀ a, v a ∈ Λ) :
    (∀ a b, H.h (v b) (v a) - G₀ a b ∈ Submodule.span M.L.O {algebraMap F E (ϖ : F)}) ↔
      ∀ a b, resF F (∑ k, ∑ l, (π (v b)).1 k * (Ph k l : F) * (π (v a)).2 l) = resF F ((e (G₀ a b)).1) := by
  have hform := hπ.2.2.2
  have hL := fun a => (hπ.2.1 (v a)).1 (hv a)
  have hc : ∀ a b, InP ϖ (e (H.h (v b) (v a) - G₀ a b)).1 ↔
      resF F (∑ k, ∑ l, (π (v b)).1 k * (Ph k l : F) * (π (v a)).2 l) = resF F ((e (G₀ a b)).1) := by
    intro a b
    rw [map_sub, Prod.fst_sub, hform]
    exact inP_sub_iff hϖ (bil_mem _ _ (hL b).1 (hL a).2 Ph) ((hO _).1 (h1 a b)).1
  have hc2 : ∀ a b, (e (H.h (v b) (v a) - G₀ a b)).2 = (e (H.h (v a) (v b) - G₀ b a)).1 := by
    intro a b
    have hg : e (G₀ a b) = (e (G₀ b a)).swap := by rw [h2 b a, hes]
    rw [map_sub, map_sub, Prod.snd_sub, Prod.fst_sub, hform, hform, hg]
    rfl
  constructor
  · intro h a b
    exact (hc a b).1 ((mem_span_irr_iff e hO ϖ _).1 (h a b)).1
  · intro h a b
    rw [mem_span_irr_iff e hO ϖ]
    exact ⟨(hc a b).2 (h a b), by rw [hc2]; exact (hc b a).2 (h b a)⟩

theorem pi_sum (e : E ≃ₐ[F] F × F) {n : ℕ} (π : V ≃+ (Fin n → F) × (Fin n → F))
    (hπa : ∀ (a : E) (x : V), π (a • x) = ((e a).1 • (π x).1, (e a).2 • (π x).2))
    {ι : Type} [Fintype ι] (v : ι → V) (c : ι → E) :
    π (∑ i, c i • v i) = (∑ i, (e (c i)).1 • (π (v i)).1, ∑ i, (e (c i)).2 • (π (v i)).2) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [hπa]
  exact Prod.ext (by simp [Prod.fst_sum]) (by simp [Prod.snd_sum])

theorem prim_iff [IsDiscreteValuationRing 𝒪[F]] (e : E ≃ₐ[F] F × F)
    (hO : ∀ x : E, x ∈ M.L.O ↔ (e x).1 ∈ 𝒪[F] ∧ (e x).2 ∈ 𝒪[F]) (H : Loc.HermSp M V)
    (Λ : Submodule M.L.O V) {n : ℕ} (π : V ≃+ (Fin n → F) × (Fin n → F))
    (hπa : ∀ (a : E) (x : V), π (a • x) = ((e a).1 • (π x).1, (e a).2 • (π x).2))
    (hπL : ∀ x : V, x ∈ Λ ↔ (∀ k, (π x).1 k ∈ 𝒪[F]) ∧ ∀ k, (π x).2 k ∈ 𝒪[F]) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ)
    {ι : Type} [Fintype ι] (v : ι → V) (hv : ∀ a, v a ∈ Λ) :
    H.Prim Λ v ↔ LinearIndependent 𝓀[F] (redM F fun a => (π (v a)).1) ∧
      LinearIndependent 𝓀[F] (redM F fun a => (π (v a)).2) := by
  set X : ι → Fin n → F := fun a => (π (v a)).1 with hXd
  set Y : ι → Fin n → F := fun a => (π (v a)).2 with hYd
  have hX : ∀ a k, X a k ∈ 𝒪[F] := fun a k => ((hπL (v a)).1 (hv a)).1 k
  have hY : ∀ a k, Y a k ∈ 𝒪[F] := fun a k => ((hπL (v a)).1 (hv a)).2 k
  have hsum := pi_sum e π hπa v
  have hpiS : ∀ u w : Fin n → F, π (π.symm (u, w)) = (u, w) := fun u w => AddEquiv.apply_symm_apply _ _

  have hLI : LinearIndependent E v ↔ LinearIndependent F X ∧ LinearIndependent F Y := by
    constructor
    · intro hind
      constructor
      · rw [Fintype.linearIndependent_iff]
        intro c hc i
        have h0 := Fintype.linearIndependent_iff.1 hind (fun i => e.symm (c i, 0)) (by
          apply π.injective
          rw [hsum, map_zero]
          simp only [AlgEquiv.apply_symm_apply, zero_smul, Finset.sum_const_zero]
          ext k
          · simpa [hXd] using congrFun hc k
          · simp) i
        have := congrArg (fun z => (e z).1) h0
        simpa using this
      · rw [Fintype.linearIndependent_iff]
        intro c hc i
        have h0 := Fintype.linearIndependent_iff.1 hind (fun i => e.symm (0, c i)) (by
          apply π.injective
          rw [hsum, map_zero]
          simp only [AlgEquiv.apply_symm_apply, zero_smul, Finset.sum_const_zero]
          ext k
          · simp
          · simpa [hYd] using congrFun hc k) i
        have := congrArg (fun z => (e z).2) h0
        simpa using this
    · rintro ⟨hXi, hYi⟩
      rw [Fintype.linearIndependent_iff]
      intro c hc i
      have h0 := congrArg π hc
      rw [hsum, map_zero] at h0
      have a1 := Fintype.linearIndependent_iff.1 hXi (fun i => (e (c i)).1) (congrArg Prod.fst h0) i
      have a2 := Fintype.linearIndependent_iff.1 hYi (fun i => (e (c i)).2) (congrArg Prod.snd h0) i
      apply e.injective
      rw [map_zero]
      exact Prod.ext a1 a2

  have hSat : (∀ x ∈ Λ, x ∈ Submodule.span E (Set.range v) → x ∈ Submodule.span M.L.O (Set.range v)) ↔
      SatF F X ∧ SatF F Y := by
    have hOsum : ∀ d : ι → M.L.O, ∑ i, d i • v i = ∑ i, (d i : E) • v i := fun d => rfl
    constructor
    · intro hs
      constructor
      · rintro u hu ⟨c, hc⟩
        have hxL : π.symm (u, 0) ∈ Λ := (hπL _).2 (by rw [hpiS]; exact ⟨hu, fun k => Subring.zero_mem _⟩)
        have hxs : π.symm (u, 0) ∈ Submodule.span E (Set.range v) := by
          rw [Submodule.mem_span_range_iff_exists_fun]
          refine ⟨fun i => e.symm (c i, 0), ?_⟩
          apply π.injective
          rw [hsum, hpiS]
          simp only [AlgEquiv.apply_symm_apply, zero_smul, Finset.sum_const_zero]
          rw [← hc]
        obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun M.L.O).1 (hs _ hxL hxs)
        refine ⟨fun i => (e (d i)).1, fun i => ((hO _).1 (d i).2).1, ?_⟩
        have h0 := congrArg (fun z => (π z).1) hd
        simp only [hOsum, hsum, hpiS] at h0
        exact h0
      · rintro u hu ⟨c, hc⟩
        have hxL : π.symm (0, u) ∈ Λ := (hπL _).2 (by rw [hpiS]; exact ⟨fun k => Subring.zero_mem _, hu⟩)
        have hxs : π.symm (0, u) ∈ Submodule.span E (Set.range v) := by
          rw [Submodule.mem_span_range_iff_exists_fun]
          refine ⟨fun i => e.symm (0, c i), ?_⟩
          apply π.injective
          rw [hsum, hpiS]
          simp only [AlgEquiv.apply_symm_apply, zero_smul, Finset.sum_const_zero]
          rw [← hc]
        obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun M.L.O).1 (hs _ hxL hxs)
        refine ⟨fun i => (e (d i)).2, fun i => ((hO _).1 (d i).2).2, ?_⟩
        have h0 := congrArg (fun z => (π z).2) hd
        simp only [hOsum, hsum, hpiS] at h0
        exact h0
    · rintro ⟨sX, sY⟩ x hx hxs
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hxs
      have hπx := hsum c
      rw [hc] at hπx
      have hxc := (hπL x).1 hx
      obtain ⟨c1, hc1, hs1⟩ := sX (π x).1 hxc.1 ⟨_, (congrArg Prod.fst hπx).symm⟩
      obtain ⟨c2, hc2, hs2⟩ := sY (π x).2 hxc.2 ⟨_, (congrArg Prod.snd hπx).symm⟩
      have hmem : ∀ i, e.symm (c1 i, c2 i) ∈ M.L.O := fun i => by
        rw [hO, AlgEquiv.apply_symm_apply]; exact ⟨hc1 i, hc2 i⟩
      rw [Submodule.mem_span_range_iff_exists_fun]
      refine ⟨fun i => ⟨_, hmem i⟩, ?_⟩
      rw [hOsum]
      apply π.injective
      rw [hsum]
      simp only [AlgEquiv.apply_symm_apply]
      exact Prod.ext hs1 hs2
  have hP : H.Prim Λ v ↔ (LinearIndependent F X ∧ LinearIndependent F Y) ∧ (SatF F X ∧ SatF F Y) := by
    unfold Loc.HermSp.Prim
    rw [← hLI, ← hSat]
    exact ⟨fun h => ⟨h.2.1, h.2.2⟩, fun h => ⟨hv, h.1, h.2⟩⟩
  rw [hP, ← dvr_prim_iff hϖ X hX, ← dvr_prim_iff hϖ Y hY]
  tauto

end Coord2

end PI.UnitaryGroupMassFormula.CntFormula
end
end

noncomputable section

namespace PI.UnitaryGroupMassFormula.LocDensCorank

open NumberField Formalism.MainNotions.S PI.UnitaryGroupMassFormula.CntFormula
open Classical ValuativeRel

theorem count_split_gen (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Loc.Model F E)
    (hl : IsNonarchimedeanLocalField F)
    (e : E ≃ₐ[F] F × F) (hes : ∀ x, e (M.L.cj x) = (e x).swap)
    (hO : ∀ x : E, x ∈ M.L.O ↔ (e x).1 ∈ 𝒪[F] ∧ (e x).2 ∈ 𝒪[F])
    (V : Type) [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (Λ : Submodule M.L.O V)
    (π : V ≃+ (Fin (Module.finrank E V) → F) × (Fin (Module.finrank E V) → F))
    (Ph : Matrix (Fin (Module.finrank E V)) (Fin (Module.finrank E V)) 𝒪[F]) (hπ : IsSplitCoord e H Λ π Ph)
    (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ)
    (ι : Type) [Fintype ι] [DecidableEq ι] (G₀ : Matrix ι ι E) (h1 : ∀ a b, G₀ a b ∈ M.L.O)
    (h2 : ∀ a b, G₀ b a = M.L.cj (G₀ a b)) :
    H.dens ϖ Λ G₀ * (Nat.card 𝓀[F] : ℝ) ^
        ((2 * Module.finrank E V * Fintype.card ι : ℤ) - (Fintype.card ι : ℤ) ^ 2) =
      (Formalism.L2.SG.DensExact.countSplit 𝓀[F] (Module.finrank E V) (Fintype.card ι)
        (Ph.map (IsLocalRing.residue 𝒪[F]))
        (Matrix.of fun i j => resF F ((e (G₀ ((Fintype.equivFin ι).symm j)
          ((Fintype.equivFin ι).symm i))).1)) : ℝ) := by
  haveI := hl
  obtain ⟨hπa, hπL, hdet, hform⟩ := hπ
  have hlift : ∀ c : 𝓀[F], liftF F c ∈ 𝒪[F] := fun c =>
    ((IsLocalRing.residue_surjective c).choose).2
  obtain ⟨lamV, hlamV⟩ : ∃ f : (Fin (Module.finrank E V) → 𝓀[F]) × (Fin (Module.finrank E V) → 𝓀[F]) → V,
      ∀ p, f p = π.symm (fun k => liftF F (p.1 k), fun l => liftF F (p.2 l)) := ⟨_, fun _ => rfl⟩
  have hlamπ : ∀ p, π (lamV p) = (fun k => liftF F (p.1 k), fun l => liftF F (p.2 l)) := fun p => by
    rw [hlamV, AddEquiv.apply_symm_apply]
  have hlamΛ : ∀ p, lamV p ∈ Λ := fun p =>
    (hπL _).2 ⟨fun k => by rw [hlamπ]; exact hlift _, fun k => by rw [hlamπ]; exact hlift _⟩
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : (Fin (Fintype.card ι) → Fin (Module.finrank E V) → 𝓀[F]) ×
      (Fin (Fintype.card ι) → Fin (Module.finrank E V) → 𝓀[F]) →
      ι → V ⧸ H.smulLat (algebraMap F E (ϖ : F)) Λ,
      ∀ XY a, Ψ XY a = Submodule.Quotient.mk (p := H.smulLat (algebraMap F E (ϖ : F)) Λ)
        (lamV (XY.1 ((Fintype.equivFin ι) a), XY.2 ((Fintype.equivFin ι) a))) := ⟨_, fun _ _ => rfl⟩
  have hΨinj : Function.Injective Ψ := by
    intro XY XY' h
    have key : ∀ a, (∀ k, XY.1 ((Fintype.equivFin ι) a) k = XY'.1 ((Fintype.equivFin ι) a) k) ∧
        ∀ k, XY.2 ((Fintype.equivFin ι) a) k = XY'.2 ((Fintype.equivFin ι) a) k := by
      intro a
      have h3 := congrFun h a
      rw [hΨ, hΨ, mk_eq_iff e H Λ π hπa hπL hϖ (hlamΛ _) (hlamΛ _)] at h3
      simpa only [hlamπ, resF_liftF] using h3
    refine Prod.ext (funext fun i => funext fun k => ?_) (funext fun i => funext fun k => ?_)
    · simpa using (key ((Fintype.equivFin ι).symm i)).1 k
    · simpa using (key ((Fintype.equivFin ι).symm i)).2 k
  obtain ⟨g, hg⟩ : ∃ g : {v : ι → V // H.Prim Λ v ∧ ∀ a b,
      H.h (v b) (v a) - G₀ a b ∈ Submodule.span M.L.O {algebraMap F E (ϖ : F)}} →
      (Fin (Fintype.card ι) → Fin (Module.finrank E V) → 𝓀[F]) ×
      (Fin (Fintype.card ι) → Fin (Module.finrank E V) → 𝓀[F]),
      ∀ v, g v = (fun i k => resF F ((π (v.1 ((Fintype.equivFin ι).symm i))).1 k),
        fun j l => resF F ((π (v.1 ((Fintype.equivFin ι).symm j))).2 l)) := ⟨_, fun _ => rfl⟩
  have hfg : (fun v : {v : ι → V // H.Prim Λ v ∧ ∀ a b,
      H.h (v b) (v a) - G₀ a b ∈ Submodule.span M.L.O {algebraMap F E (ϖ : F)}} =>
      fun a => Submodule.Quotient.mk (p := H.smulLat (algebraMap F E (ϖ : F)) Λ) (v.1 a)) = Ψ ∘ g := by
    funext v a
    have hv : v.1 a ∈ Λ := v.2.1.1 a
    rw [Function.comp_apply, hΨ, mk_eq_iff e H Λ π hπa hπL hϖ hv (hlamΛ _), hlamπ, hg]
    simp [Equiv.symm_apply_apply, resF_liftF]
  have hrange : Set.range g = {XY : (Fin (Fintype.card ι) → Fin (Module.finrank E V) → 𝓀[F]) ×
      (Fin (Fintype.card ι) → Fin (Module.finrank E V) → 𝓀[F]) |
      LinearIndependent 𝓀[F] XY.1 ∧ LinearIndependent 𝓀[F] XY.2 ∧
        ∀ i j, ∑ k, ∑ l, XY.1 i k * (Ph.map (IsLocalRing.residue 𝒪[F])) k l * XY.2 j l =
          (Matrix.of fun i j => resF F ((e (G₀ ((Fintype.equivFin ι).symm j)
            ((Fintype.equivFin ι).symm i))).1)) i j} := by
    ext ⟨X, Y⟩
    simp only [Set.mem_range, Set.mem_setOf_eq]
    constructor
    · rintro ⟨v, hv⟩
      rw [hg] at hv
      obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hv
      have hvΛ : ∀ a, v.1 a ∈ Λ := v.2.1.1
      have hP := (prim_iff e hO H Λ π hπa hπL hϖ v.1 hvΛ).1 v.2.1
      have hG := (gram_iff e hes hO H Λ π Ph ⟨hπa, hπL, hdet, hform⟩ hϖ G₀ h1 h2 v.1 hvΛ).1 v.2.2
      refine ⟨hP.1.comp _ (Fintype.equivFin ι).symm.injective,
        hP.2.comp _ (Fintype.equivFin ι).symm.injective, fun i j => ?_⟩
      have h3 := hG ((Fintype.equivFin ι).symm j) ((Fintype.equivFin ι).symm i)
      rw [resF_bil _ _ (fun k => ((hπL _).1 (hvΛ _)).1 k) (fun l => ((hπL _).1 (hvΛ _)).2 l)] at h3
      simpa [Matrix.map_apply] using h3
    · rintro ⟨hX, hY, hXY⟩
      have hvΛ : ∀ a, lamV (X ((Fintype.equivFin ι) a), Y ((Fintype.equivFin ι) a)) ∈ Λ :=
        fun a => hlamΛ _
      have e1 : (PI.UnitaryGroupMassFormula.CntFormula.redM F fun a =>
          (π (lamV (X ((Fintype.equivFin ι) a), Y ((Fintype.equivFin ι) a)))).1) =
          X ∘ (Fintype.equivFin ι) := by
        funext a k
        simp [PI.UnitaryGroupMassFormula.CntFormula.redM, hlamπ, resF_liftF]
      have e2 : (PI.UnitaryGroupMassFormula.CntFormula.redM F fun a =>
          (π (lamV (X ((Fintype.equivFin ι) a), Y ((Fintype.equivFin ι) a)))).2) =
          Y ∘ (Fintype.equivFin ι) := by
        funext a k
        simp [PI.UnitaryGroupMassFormula.CntFormula.redM, hlamπ, resF_liftF]
      refine ⟨⟨fun a => lamV (X ((Fintype.equivFin ι) a), Y ((Fintype.equivFin ι) a)), ?_, ?_⟩, ?_⟩
      · rw [prim_iff e hO H Λ π hπa hπL hϖ _ hvΛ, e1, e2]
        exact ⟨hX.comp _ (Fintype.equivFin ι).injective, hY.comp _ (Fintype.equivFin ι).injective⟩
      · rw [gram_iff e hes hO H Λ π Ph ⟨hπa, hπL, hdet, hform⟩ hϖ G₀ h1 h2 _ hvΛ]
        intro a b
        rw [resF_bil _ _ (fun k => ((hπL _).1 (hvΛ _)).1 k) (fun l => ((hπL _).1 (hvΛ _)).2 l)]
        have h4 := hXY ((Fintype.equivFin ι) b) ((Fintype.equivFin ι) a)
        simpa [Matrix.map_apply, hlamπ, resF_liftF] using h4
      · rw [hg]
        refine Prod.ext (funext fun i => funext fun k => ?_) (funext fun i => funext fun k => ?_)
        · simp [hlamπ, resF_liftF]
        · simp [hlamπ, resF_liftF]
  have hQ : (Nat.card 𝓀[F] : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  unfold Formalism.MainNotions.S.Loc.HermSp.dens
  rw [div_mul_cancel₀ _ (zpow_ne_zero _ hQ), hfg, Set.range_comp, Nat.card_image_of_injective hΨinj,
    hrange, Formalism.L2.SG.DensExact.countSplit, Nat.card_coe_set_eq]

theorem diag_red (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    (e : E ≃ₐ[F] F × F) (ι : Type) [Fintype ι] [DecidableEq ι] (a : ι → 𝒪[F]) :
    (Matrix.of fun i j => resF F ((e ((Matrix.diagonal fun i => algebraMap F E (a i : F))
        ((Fintype.equivFin ι).symm j) ((Fintype.equivFin ι).symm i))).1) :
      Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) 𝓀[F]) =
      Matrix.diagonal fun i => IsLocalRing.residue 𝒪[F] (a ((Fintype.equivFin ι).symm i)) := by
  have hc : ∀ x : 𝒪[F], resF F (x : F) = IsLocalRing.residue 𝒪[F] x := fun x => by
    unfold resF
    rw [dite_eq_left x.2]
  have h0 : resF F 0 = 0 := by simpa using hc 0
  ext i j
  rw [Matrix.of_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
  by_cases h : i = j
  · subst h
    rw [if_pos rfl, if_pos rfl, AlgEquiv.commutes]
    exact hc _
  · rw [if_neg (fun h' => h ((Fintype.equivFin ι).symm.injective h').symm), if_neg h, map_zero]
    exact h0

theorem residue_eq_zero_iff' (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsDiscreteValuationRing 𝒪[F]] {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (x : 𝒪[F]) :
    IsLocalRing.residue 𝒪[F] x = 0 ↔ ϖ ∣ x := by
  rw [IsLocalRing.residue_eq_zero_iff, hϖ.maximalIdeal_eq, Ideal.mem_span_singleton]

theorem corank_diag (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsDiscreteValuationRing 𝒪[F]] {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (a : ι → 𝒪[F]) :
    Fintype.card ι -
        (Matrix.diagonal fun i => IsLocalRing.residue 𝒪[F] (a ((Fintype.equivFin ι).symm i))).rank =
      (Finset.univ.filter fun i => ϖ ∣ a i).card := by
  rw [Matrix.rank_diagonal, Fintype.card_subtype]
  have h1 := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin (Fintype.card ι))))
    (fun i => IsLocalRing.residue 𝒪[F] (a ((Fintype.equivFin ι).symm i)) ≠ 0)
  have h2 : (Finset.univ.filter fun i : Fin (Fintype.card ι) =>
      ¬ IsLocalRing.residue 𝒪[F] (a ((Fintype.equivFin ι).symm i)) ≠ 0).card =
      (Finset.univ.filter fun i : ι => ϖ ∣ a i).card := by
    refine Finset.card_equiv (Fintype.equivFin ι).symm fun i => ?_
    simp [residue_eq_zero_iff' F hϖ]
  rw [Finset.card_univ, Fintype.card_fin] at h1
  omega

theorem dens_diag_split (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E]
    [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Loc.Model F E)
    (hl : IsNonarchimedeanLocalField F)
    (e : E ≃ₐ[F] F × F) (hes : ∀ x, e (M.L.cj x) = (e x).swap)
    (hO : ∀ x : E, x ∈ M.L.O ↔ (e x).1 ∈ 𝒪[F] ∧ (e x).2 ∈ 𝒪[F])
    (V : Type) [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (Λ : Submodule M.L.O V)
    (π : V ≃+ (Fin (Module.finrank E V) → F) × (Fin (Module.finrank E V) → F))
    (Ph : Matrix (Fin (Module.finrank E V)) (Fin (Module.finrank E V)) 𝒪[F]) (hπ : IsSplitCoord e H Λ π Ph)
    (ϖ : 𝒪[F]) (hϖ : Irreducible ϖ) (ι : Type) [Fintype ι] [DecidableEq ι] (a : ι → 𝒪[F]) :
    H.dens ϖ Λ (Matrix.diagonal (fun i => algebraMap F E (a i : F))) =
      Formalism.L2.SG.DensExact.densProd (Nat.card 𝓀[F]) 1 (Module.finrank E V) (Fintype.card ι)
        (Finset.univ.filter fun i => ϖ ∣ a i).card := by
  haveI := hl
  haveI : Fintype 𝓀[F] := Fintype.ofFinite _
  have hdiagO : ∀ i j, (Matrix.diagonal fun i => algebraMap F E (a i : F)) i j ∈ M.L.O := by
    intro i j
    rw [hO, Matrix.diagonal_apply]
    split_ifs
    · rw [AlgEquiv.commutes]
      exact ⟨(a i).2, (a i).2⟩
    · rw [map_zero]
      exact ⟨zero_mem _, zero_mem _⟩
  have hcjfix : ∀ x : E, (e x).1 = (e x).2 → M.L.cj x = x := fun x hx =>
    e.injective (by rw [hes]; exact Prod.ext hx.symm hx)
  have hdiagH : ∀ i j, (Matrix.diagonal fun i => algebraMap F E (a i : F)) j i =
      M.L.cj ((Matrix.diagonal fun i => algebraMap F E (a i : F)) i j) := by
    intro i j
    rw [Matrix.diagonal_apply, Matrix.diagonal_apply]
    by_cases h : i = j
    · subst h
      rw [if_pos rfl]
      exact (hcjfix _ (by rw [AlgEquiv.commutes]; rfl)).symm
    · rw [if_neg (Ne.symm h), if_neg h]
      exact (hcjfix 0 (by rw [map_zero]; rfl)).symm
  have hcnt := count_split_gen F E M hl e hes hO V H Λ π Ph hπ ϖ hϖ ι _ hdiagO hdiagH
  rw [diag_red F E e ι a] at hcnt
  have hunit : IsUnit (Ph.map (IsLocalRing.residue 𝒪[F])).det := by
    have h3 := hπ.2.2.1.map (IsLocalRing.residue 𝒪[F])
    rwa [RingHom.map_det, RingHom.mapMatrix_apply] at h3
  have hDE := PI.DensSplitW.densExactSplit_of PI.DensSplitW.fiberCard_holds 𝓀[F]
    (Module.finrank E V) (Fintype.card ι) (Ph.map (IsLocalRing.residue 𝒪[F]))
    (Matrix.diagonal fun i => IsLocalRing.residue 𝒪[F] (a ((Fintype.equivFin ι).symm i))) hunit
  rw [corank_diag F hϖ ι a] at hDE
  rw [Nat.card_eq_fintype_card] at hcnt ⊢
  rw [← hDE, ← hcnt]
  have hQ : (Fintype.card 𝓀[F] : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hk : (Fintype.card 𝓀[F] : ℝ) ^
      ((2 * Module.finrank E V * Fintype.card ι : ℤ) - (Fintype.card ι : ℤ) ^ 2) =
      (Fintype.card 𝓀[F] : ℝ) ^ (2 * Module.finrank E V * Fintype.card ι) /
        (Fintype.card 𝓀[F] : ℝ) ^ (Fintype.card ι ^ 2) := by
    rw [zpow_sub₀ hQ]
    norm_cast
  rw [hk, mul_div_assoc, div_self (div_ne_zero (pow_ne_zero _ hQ) (pow_ne_zero _ hQ)), mul_one]

theorem splitCount_holds : SplitCount := by
  intro F E _ _ _ _ _ _ _ M hl hc ⟨e, hes⟩ V _ _ H Λ hΛ ϖ hϖ ι _ _ a hle
  have hO := PI.UnitaryGroupMassFormula.CntFormula.integral_split_count F E M.L hl e
  obtain ⟨π, Ph, hπ⟩ := PI.UnitaryGroupMassFormula.CntFormula.adapted_coords_self_dual F E M hl hc e hes V H Λ hΛ
  exact dens_diag_split F E M hl e hes hO V H Λ π Ph hπ ϖ hϖ ι a

end PI.UnitaryGroupMassFormula.LocDensCorank
