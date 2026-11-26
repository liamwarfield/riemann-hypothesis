module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthCommensurableSpanSpanOfDetNeZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameUnipotentUnitriangular
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.FrameTri

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem hf_add_left (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (a b y : Fin n → E) :
    hf L Hm (a + b) y = hf L Hm a y + hf L Hm b y := by
  simp [hf, add_mul, Finset.sum_add_distrib]

theorem hf_smul_left (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (c : E) (a y : Fin n → E) :
    hf L Hm (c • a) y = c * hf L Hm a y := by
  simp [hf, Finset.mul_sum, mul_assoc]

theorem hf_add_right (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (x a b : Fin n → E) :
    hf L Hm x (a + b) = hf L Hm x a + hf L Hm x b := by
  simp [hf, mul_add, Finset.sum_add_distrib]

theorem hf_smul_right (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (c : E) (x a : Fin n → E) :
    hf L Hm x (c • a) = L.cj c * hf L Hm x a := by
  simp only [hf, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hf_sum_left (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) {ι : Type} (s : Finset ι)
    (c : ι → E) (g : ι → Fin n → E) (y : Fin n → E) :
    hf L Hm (∑ i ∈ s, c i • g i) y = ∑ i ∈ s, c i * hf L Hm (g i) y := by
  induction s using Finset.induction_on with
  | empty => simp [hf]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hf_add_left, hf_smul_left, ih]

variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem spanTo_mono (g : Fin (r + 1) → S.V) {i j : ℕ} (h : i ≤ j) : S.spanTo g i ≤ S.spanTo g j :=
  Submodule.span_mono (Set.image_mono fun _ ha => lt_of_lt_of_le ha h)

theorem mem_spanTo (g : Fin (r + 1) → S.V) {i : Fin (r + 1)} {j : ℕ} (h : (i : ℕ) < j) :
    g i ∈ S.spanTo g j :=
  Submodule.subset_span ⟨i, h, rfl⟩

theorem coeff_of_mem (g : Fin (r + 1) → S.V) {j : ℕ} {v : S.V} (hv : v ∈ S.spanTo g j) :
    ∃ c : Fin (r + 1) → E, (∀ i : Fin (r + 1), j ≤ (i : ℕ) → c i = 0) ∧ v = ∑ i, c i • g i := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    refine ⟨Pi.single i 1, fun a ha => ?_, ?_⟩
    · have hi' : (i : ℕ) < j := hi
      have : a ≠ i := by rintro rfl; omega
      simp [this]
    · simp [Pi.single_apply]
  | zero => exact ⟨0, fun _ _ => rfl, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc, rfl⟩ := hx
    obtain ⟨d, hd, rfl⟩ := hy
    exact ⟨c + d, fun i hi => by simp [hc i hi, hd i hi], by simp [add_smul, Finset.sum_add_distrib]⟩
  | smul a x _ hx =>
    obtain ⟨c, hc, rfl⟩ := hx
    exact ⟨a • c, fun i hi => by simp [hc i hi], by simp [Finset.smul_sum, smul_smul]⟩

section
variable (g : Fin (r + 1) → S.V) (gs : Fin r → S.V) (t : Fˣ)
  (hg : ∀ a b, hf L S.Hm (g a) (g b) =
    if a = Fin.last r ∧ b = Fin.last r then -algebraMap F E t else 0)
  (hd : ∀ a j, hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0)

include hg hd in
theorem linInd : LinearIndependent E g := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have key : ∀ y, ∑ a, c a * hf L S.Hm (g a) y = 0 := by
    intro y
    rw [← hf_sum_left, hc]; simp [hf]
  refine Fin.lastCases ?_ (fun j => ?_) i
  · have h := key (g (Fin.last r))
    simp only [hg, and_true, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
    have hu : IsUnit (-algebraMap F E t) := (t.isUnit.map (algebraMap F E)).neg
    exact (hu.mul_left_eq_zero).1 h
  · have h := key (gs j)
    simpa [hd] using h

include hg in
theorem last_mem_perp : g (Fin.last r) ∈ perp L S.Hm (S.spanTo g r) := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    have hi' : (i : ℕ) < r := hi
    have : i ≠ Fin.last r := by rintro rfl; simp at hi'
    simp [hg, this]
  | zero => simp [hf]
  | add x y _ _ hx hy => rw [hf_add_right, hx, hy, add_zero]
  | smul a x _ hx => rw [hf_smul_right, hx, mul_zero]

include hg in
theorem sub_mem {n : S.GLV} (hn : n ∈ S.Nof g) (i : Fin (r + 1)) :
    n (g i) - g i ∈ S.spanTo g i := by
  obtain ⟨⟨_, h2⟩, h3⟩ := hn
  refine Fin.lastCases ?_ (fun j => ?_) i
  · exact h3.2 _ (last_mem_perp S g t hg)
  · have h := (Subgroup.mem_iInf.1 h2 j).2 (g j.castSucc) (mem_spanTo S g (by simp))
    exact h

include hg in
theorem map_mem {n : S.GLV} (hn : n ∈ S.Nof g) (j : ℕ) {v : S.V} (hv : v ∈ S.spanTo g j) :
    n v ∈ S.spanTo g j := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, hi, rfl⟩ := hx
    have hi' : (i : ℕ) < j := hi
    have h := Submodule.add_mem _ (spanTo_mono S g hi'.le (sub_mem S g t hg hn i)) (mem_spanTo S g hi')
    simpa using h
  | zero => simp
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

include hg in
theorem map_mem_iff {n : S.GLV} (hn : n ∈ S.Nof g) (j : ℕ) (v : S.V) :
    n v ∈ S.spanTo g j ↔ v ∈ S.spanTo g j := by
  refine ⟨fun h => ?_, map_mem S g t hg hn j⟩
  have h' := map_mem S g t hg ((S.Nof g).inv_mem hn) j h
  have e : n⁻¹ (n v) = v := n.symm_apply_apply v
  rwa [e] at h'

include hg in
theorem spanTo_comp {n : S.GLV} (hn : n ∈ S.Nof g) (j : ℕ) :
    S.spanTo (fun b => n (g b)) j = S.spanTo g j := by
  have h : S.spanTo (fun b => n (g b)) j = (S.spanTo g j).map (n : S.V →ₗ[E] S.V) := by
    unfold Frames.spanTo
    rw [Submodule.map_span, Set.image_image]
    rfl
  rw [h]
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact map_mem S g t hg hn j hx
  · intro hv
    refine ⟨n.symm v, ?_, by simp⟩
    apply (map_mem_iff S g t hg hn j _).1
    simpa using hv

include hg in
theorem exists_tri {n : S.GLV} (hn : n ∈ S.Nof g) :
    ∃ s : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ((∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1)) ∧
      ∀ j, n (g j) = ∑ i, s i j • g i := by
  choose c hc hc' using fun j => coeff_of_mem S g (sub_mem S g t hg hn j)
  refine ⟨Matrix.of fun i j => c j i + if i = j then 1 else 0, ⟨fun i j hij => ?_, fun i => ?_⟩, fun j => ?_⟩
  · simp [hc j i (le_of_lt hij), hij.ne']
  · simp [hc i i le_rfl]
  · simp only [Matrix.of_apply, add_smul, Finset.sum_add_distrib, ← hc' j, ite_smul, one_smul, zero_smul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp

end

end GlobalTheory.HL.FrameTri

namespace GlobalTheory.HL

theorem frame_unipotent_unitriangular : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (g : Fin (r + 1) → S.V) (gs : Fin r → S.V), (g = S.f ∧ gs = S.es) ∨ (g = S.f' ∧ gs = S.es') → LinearIndependent E g ∧ ∀ n ∈ S.Nof g, (∃ s : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ((∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1)) ∧ ∀ j, n (g j) = ∑ i, s i j • g i) ∧ (∀ j, S.spanTo (fun b => n (g b)) j = S.spanTo g j) ∧ (∀ j, ∀ v, n v ∈ S.spanTo g j ↔ v ∈ S.spanTo g j) ∧ ∀ v, n v ∈ perp L S.Hm (S.spanTo g r) ↔ v ∈ perp L S.Hm (S.spanTo g r) := by
  intro F _ _ _ _ _ E _ _ _ L r k S g gs h
  obtain ⟨t, hg, hd⟩ : ∃ t : Fˣ, (∀ a b, hf L S.Hm (g a) (g b) =
      if a = Fin.last r ∧ b = Fin.last r then -algebraMap F E t else 0) ∧
      ∀ a j, hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0 := by
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨S.T, S.gram, S.dual⟩
    · exact ⟨S.T', S.gram', S.dual'⟩
  exact ⟨FrameTri.linInd S g gs t hg hd, fun n hn => ⟨FrameTri.exists_tri S g t hg hn,
    FrameTri.spanTo_comp S g t hg hn, FrameTri.map_mem_iff S g t hg hn, hn.2.1⟩⟩

end GlobalTheory.HL
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsBasisFgMaximalOrderSpanningFree
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.OrderBasis

theorem exists_basis_pi {E : Type} [CommRing E] (R : Subring E) [IsPrincipalIdealRing R]
    (s t : E) (hs : IsUnit s) (ht : IsUnit t) :
    ∀ (m : ℕ) (Q : Submodule R (Fin m → E)), (∀ q ∈ Q, ∀ i, s * q i ∈ R) →
      (∀ i, (Pi.single i t : Fin m → E) ∈ Q) →
      ∃ b : Fin m → Fin m → E, LinearIndependent E b ∧ Q = Submodule.span R (Set.range b) := by
  intro m
  induction m with
  | zero =>
    intro Q _ _
    exact ⟨fun i => i.elim0, linearIndependent_empty_type, Subsingleton.elim _ _⟩
  | succ m ih =>
    intro Q h1 h2
    let I : Ideal R :=
      { carrier := {r | ∃ q ∈ Q, s * q 0 = r}
        add_mem' := by
          rintro a b ⟨p, hp, hpa⟩ ⟨q, hq, hqb⟩
          exact ⟨p + q, Q.add_mem hp hq, by simp [mul_add, hpa, hqb]⟩
        zero_mem' := ⟨0, Q.zero_mem, by simp⟩
        smul_mem' := by
          rintro c a ⟨p, hp, hpa⟩
          refine ⟨c • p, Q.smul_mem c hp, ?_⟩
          simp only [Pi.smul_apply, Subring.smul_def, smul_eq_mul, Subring.coe_mul, ← hpa]
          ring }
    obtain ⟨a, ha⟩ := (IsPrincipalIdealRing.principal I).principal
    have haI : a ∈ I := by rw [ha]; exact Submodule.mem_span_singleton_self a
    obtain ⟨q0, hq0, hq0a⟩ := haI
    have hmul : ∀ q ∈ Q, ∃ c : R, q 0 = c * q0 0 := by
      intro q hq
      have : (⟨s * q 0, h1 q hq 0⟩ : R) ∈ I := ⟨q, hq, rfl⟩
      rw [ha, Submodule.mem_span_singleton] at this
      obtain ⟨c, hc⟩ := this
      refine ⟨c, hs.mul_left_cancel ?_⟩
      have := congrArg Subtype.val hc
      simp only [smul_eq_mul, Subring.coe_mul] at this
      rw [← this, ← hq0a]; ring
    have hu : IsUnit (q0 0) := by
      obtain ⟨c, hc⟩ := hmul _ (h2 0)
      simp only [Pi.single_eq_same] at hc
      rw [hc] at ht
      exact isUnit_of_mul_isUnit_right ht
    let j : (Fin m → E) →ₗ[E] (Fin (m + 1) → E) :=
      LinearMap.pi (fun i => Fin.cases 0 (fun k => LinearMap.proj k) i)
    have j0 : ∀ v, j v 0 = 0 := fun v => by simp [j]
    have js : ∀ v k, j v (Fin.succ k) = v k := fun v k => by simp [j]
    obtain ⟨b, hb, hQ⟩ := ih (Q.comap (j.restrictScalars R))
      (fun q hq i => by have := h1 _ hq i.succ; simpa [js] using this)
      (fun i => by
        have : j (Pi.single i t) = Pi.single i.succ t := by
          funext k
          refine Fin.cases ?_ (fun k => ?_) k
          · rw [j0, Pi.single_eq_of_ne (Fin.succ_ne_zero i).symm]
          · rw [js]; simp [Pi.single_apply]
        show j (Pi.single i t) ∈ Q
        rw [this]; exact h2 _)
    refine ⟨Fin.cons q0 (fun i => j (b i)), ?_, ?_⟩
    · rw [Fintype.linearIndependent_iff]
      intro g hg
      rw [Fin.sum_univ_succ] at hg
      simp only [Fin.cons_zero, Fin.cons_succ] at hg
      have hg0 : g 0 = 0 := by
        have := congrFun hg 0
        simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_apply, j0, smul_eq_mul, mul_zero,
          Finset.sum_const_zero, add_zero, Pi.zero_apply] at this
        exact hu.mul_left_eq_zero.mp this
      have hgs : ∑ i, g (Fin.succ i) • b i = 0 := by
        funext k
        have := congrFun hg k.succ
        simpa [hg0, js, Finset.sum_apply] using this
      intro i
      refine Fin.cases hg0 (fun i => ?_) i
      exact Fintype.linearIndependent_iff.mp hb _ hgs i
    · apply le_antisymm
      · intro q hq
        obtain ⟨c, hc⟩ := hmul q hq
        have hq' : q - c • q0 ∈ Q := Q.sub_mem hq (Q.smul_mem c hq0)
        have he : j (fun k => (q - c • q0) k.succ) = q - c • q0 := by
          funext k
          refine Fin.cases ?_ (fun k => ?_) k
          · rw [j0]; simp [Subring.smul_def, hc]
          · rw [js]
        have hm : (fun k : Fin m => (q - c • q0) k.succ) ∈ Q.comap (j.restrictScalars R) := by
          show j _ ∈ Q
          rw [he]; exact hq'
        rw [hQ] at hm
        have hm2 := Submodule.mem_map_of_mem (f := j.restrictScalars R) hm
        rw [Submodule.map_span] at hm2
        have hm3 : q - c • q0 ∈ Submodule.span R
            (Set.range (Fin.cons q0 (fun i => j (b i)) : Fin (m + 1) → Fin (m + 1) → E)) := by
          rw [← he]
          refine Submodule.span_mono ?_ hm2
          rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
          exact ⟨i.succ, by simp⟩
        have : q = (q - c • q0) + c • q0 := by abel
        rw [this]
        exact Submodule.add_mem _ hm3 (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      · rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        refine Fin.cases hq0 (fun i => ?_) i
        have : b i ∈ Q.comap (j.restrictScalars R) := by
          rw [hQ]; exact Submodule.subset_span ⟨i, rfl⟩
        simpa using this

theorem exists_common {E : Type} [CommRing E] (R : Subring E) {ι : Type} [Fintype ι]
    (P : ι → E → Prop) (hP : ∀ i d c, c ∈ R → P i d → P i (c * d))
    (h : ∀ i, ∃ d ∈ R, IsUnit d ∧ P i d) : ∃ d ∈ R, IsUnit d ∧ ∀ i, P i d := by
  choose d hdR hdu hd using h
  refine ⟨∏ i, d i, R.prod_mem fun i _ => hdR i, IsUnit.prod_iff.mpr fun i _ => hdu i, fun i => ?_⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  exact hP _ _ _ (R.prod_mem fun i _ => hdR i) (hd i)

theorem exists_basis {E : Type} [CommRing E] (R : Subring E) [IsPrincipalIdealRing R]
    (hD : ∀ x : E, ∃ d ∈ R, IsUnit d ∧ d * x ∈ R) {V : Type} [AddCommGroup V] [Module E V]
    {m : ℕ} (y : Fin m → V) (hy : LinearIndependent E y) (Q : Submodule R V) (hQ : Q.FG)
    (hs : Submodule.span E (Q : Set V) = Submodule.span E (Set.range y)) :
    ∃ b : Fin m → V, LinearIndependent E b ∧ Q = Submodule.span R (Set.range b) := by
  let φ : (Fin m → E) →ₗ[E] V := Fintype.linearCombination E y
  have hφ : Function.Injective φ := hy.fintypeLinearCombination_injective
  have hr : ∀ q ∈ Q, ∃ v, φ v = q := by
    intro q hq
    have : q ∈ Submodule.span E (Set.range y) := hs ▸ Submodule.subset_span hq
    rw [← Fintype.range_linearCombination] at this
    exact this
  have hmap : (Q.comap (φ.restrictScalars R)).map (φ.restrictScalars R) = Q :=
    Submodule.map_comap_eq_self fun q hq => hr q hq
  have hfg : (Q.comap (φ.restrictScalars R)).FG :=
    Submodule.fg_of_fg_map_injective (φ.restrictScalars R) hφ (by rw [hmap]; exact hQ)
  obtain ⟨k, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hfg
  obtain ⟨s, -, hsu, hs1⟩ := exists_common R (fun (p : Fin k × Fin m) d => d * g p.1 p.2 ∈ R)
    (fun p d c hc h => by rw [mul_assoc]; exact R.mul_mem hc h) (fun p => hD _)
  have hsp : ∀ x ∈ Submodule.span E (Q : Set V), ∃ d ∈ R, IsUnit d ∧ d • x ∈ Q := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact ⟨1, R.one_mem, isUnit_one, by simpa using hx⟩
    | zero => exact ⟨1, R.one_mem, isUnit_one, by simp⟩
    | add x z _ _ hx hz =>
      obtain ⟨d, hd, hdu, hx⟩ := hx
      obtain ⟨e, he, heu, hz⟩ := hz
      refine ⟨d * e, R.mul_mem hd he, hdu.mul heu, ?_⟩
      have : (d * e) • (x + z) = (⟨e, he⟩ : R) • d • x + (⟨d, hd⟩ : R) • e • z := by
        simp only [Subring.smul_def, smul_add, smul_smul, mul_comm]
      rw [this]
      exact Q.add_mem (Q.smul_mem _ hx) (Q.smul_mem _ hz)
    | smul c x _ hx =>
      obtain ⟨d, hd, hdu, hx⟩ := hx
      obtain ⟨e, he, heu, hc⟩ := hD c
      refine ⟨d * e, R.mul_mem hd he, hdu.mul heu, ?_⟩
      have : (d * e) • (c • x) = (⟨e * c, hc⟩ : R) • d • x := by
        simp only [Subring.smul_def, smul_smul]
        congr 1; ring
      rw [this]
      exact Q.smul_mem _ hx
  obtain ⟨t, -, htu, ht1⟩ := exists_common R (fun (i : Fin m) d => d • y i ∈ Q)
    (fun i d c hc h => by rw [mul_smul]; exact Q.smul_mem (⟨c, hc⟩ : R) h)
    (fun i => hsp _ (hs ▸ Submodule.subset_span ⟨i, rfl⟩))
  obtain ⟨b, hb, hQb⟩ := exists_basis_pi R s t hsu htu m (Q.comap (φ.restrictScalars R))
    (by
      intro q hq i
      rw [← hg] at hq
      induction hq using Submodule.span_induction with
      | mem x hx => obtain ⟨l, rfl⟩ := hx; exact hs1 (l, i)
      | zero => simp
      | add x z _ _ hx hz => rw [Pi.add_apply, mul_add]; exact R.add_mem hx hz
      | smul c x _ hx =>
        have : s * (c • x) i = c * (s * x i) := by
          simp only [Pi.smul_apply, Subring.smul_def, smul_eq_mul]; ring
        rw [this]; exact R.mul_mem c.2 hx)
    (fun i => by
      show φ (Pi.single i t) ∈ Q
      simpa [φ, Fintype.linearCombination_apply_single] using ht1 i)
  refine ⟨φ ∘ b, hb.map' φ (LinearMap.ker_eq_bot.mpr hφ), ?_⟩
  rw [← hmap, hQb, Submodule.map_span, Set.range_comp]
  rfl

theorem order_basis : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n m : ℕ} (y : Fin m → Fin n → E), LinearIndependent E y → ∀ Q : Submodule L.O (Fin n → E), Q.FG → Submodule.span E (Q : Set (Fin n → E)) = Submodule.span E (Set.range y) → ∃ b : Fin m → Fin n → E, LinearIndependent E b ∧ Q = Submodule.span L.O (Set.range b) := by
  intro F _ _ _ _ _ E _ _ _ L n m y hy Q hQ hs
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  haveI : IsPrincipalIdealRing L.O := (GlobalTheory.UnramOrder.order_facts L ϖ hϖ).2.2.2.1
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; norm_num)
  refine exists_basis L.O (fun x => ?_) y hy Q hQ hs
  obtain ⟨d, hd⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
    (nonZeroDivisors 𝒪[F]) (Rₘ := F) x (Algebra.IsIntegral.isIntegral x)
  refine ⟨algebraMap 𝒪[F] E d, (L.O_def _).mpr isIntegral_algebraMap, ?_, (L.O_def _).mpr ?_⟩
  · rw [IsScalarTower.algebraMap_apply 𝒪[F] F E]
    exact (IsLocalization.map_units F d).map _
  · rwa [Submonoid.smul_def, Algebra.smul_def] at hd

end GlobalTheory.OrderBasis
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardCokernelUnramifiedOrderMatrixOfDetBase
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardCokernelUnramifiedOrderMatrixOfDetBase
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.UnramOrder

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
open Ideal in
private lemma card_quotient_span_eq_card_residueField_pow_addVal {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {a : R} (ha : a ≠ 0) :
    Nat.card (R ⧸ Ideal.span {a}) = Nat.card (IsLocalRing.ResidueField R) ^
      (IsDiscreteValuationRing.addVal R a).toNat := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  have hm : IsLocalRing.maximalIdeal R = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  have hspan : Ideal.span {(u : R) * ϖ ^ n} = IsLocalRing.maximalIdeal R ^ n := by
    rw [Ideal.span_singleton_mul_left_unit u.isUnit, hm, Ideal.span_singleton_pow]
  have hv : IsDiscreteValuationRing.addVal R ((u : R) * ϖ ^ n) = n := by
    rw [IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow,
      IsDiscreteValuationRing.addVal_uniformizer hϖ, IsDiscreteValuationRing.addVal_eq_zero_of_unit u]
    simp
  have hne : IsLocalRing.maximalIdeal R ≠ ⊥ := by
    rw [hm, Ne, Ideal.span_singleton_eq_bot]
    exact hϖ.ne_zero
  rw [hv, hspan, ← Submodule.cardQuot_apply, cardQuot_pow_of_prime hne, Submodule.cardQuot_apply]
  simp
  rfl


open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
theorem _root_.GlobalTheory.UnramOrder.card_coker_eq_pow_addVal_det {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {M : Type*} [AddCommGroup M] [Module R M] [Module.Free R M]
    [Module.Finite R M] (f : M →ₗ[R] M) (hf : LinearMap.det f ≠ 0) :
    Nat.card (M ⧸ LinearMap.range f) = Nat.card (IsLocalRing.ResidueField R) ^
      (IsDiscreteValuationRing.addVal R (LinearMap.det f)).toNat := by
  classical
  let b := Module.Free.chooseBasis R M
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    by_contra hx0
    apply hf
    rw [← LinearMap.det_toMatrix b]
    refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨b.repr x, fun h => hx0 ?_, ?_⟩
    · have h' : b.repr x = 0 := by
        ext i
        exact congrFun h i
      simpa using h'
    · rw [LinearMap.toMatrix_mulVec_repr, hx, map_zero]
      rfl
  have hrank : Module.finrank R (LinearMap.range f) = Module.finrank R M :=
    LinearMap.finrank_range_of_inj hinj
  let T := Submodule.smithNormalFormTopBasis b hrank
  let B := Submodule.smithNormalFormBotBasis b hrank
  let a := Submodule.smithNormalFormCoeffs b hrank
  let e : M ≃ₗ[R] LinearMap.range f := T.equiv B (Equiv.refl _)
  let g : M →ₗ[R] M := (LinearMap.range f).subtype ∘ₗ e.toLinearMap
  have hgT : ∀ i, g (T i) = a i • T i := by
    intro i
    simp [g, e, Module.Basis.equiv_apply, B, T, a, Submodule.smithNormalFormBotBasis_def]
  have hdetg : LinearMap.det g = ∏ i, a i := by
    rw [← LinearMap.det_toMatrix T]
    have hmat : LinearMap.toMatrix T T g = Matrix.diagonal a := by
      ext i j
      rw [LinearMap.toMatrix_apply, hgT, map_smul, T.repr_self, Matrix.diagonal_apply]
      by_cases hij : i = j
      · subst hij
        simp
      · simp [hij, Finsupp.single_apply, Ne.symm hij]
    rw [hmat, Matrix.det_diagonal]
  let h : M →ₗ[R] M := e.symm.toLinearMap ∘ₗ f.rangeRestrict
  have hfgh : f = g ∘ₗ h := by
    ext x
    simp [g, h]
  have hsurj : Function.Surjective h := e.symm.surjective.comp f.surjective_rangeRestrict
  have hbij : Function.Bijective h :=
    ⟨OrzechProperty.injective_of_surjective_endomorphism h hsurj, hsurj⟩
  have hdeth : IsUnit (LinearMap.det h) := by
    have h1 := LinearEquiv.isUnit_det' (LinearEquiv.ofBijective h hbij)
    have h2 : ((LinearEquiv.ofBijective h hbij : M ≃ₗ[R] M) : M →ₗ[R] M) = h :=
      LinearMap.ext fun _ => rfl
    rwa [h2] at h1
  have hdet : LinearMap.det f = (∏ i, a i) * LinearMap.det h := by
    rw [hfgh, LinearMap.det_comp, hdetg]
  have ha : ∀ i, a i ≠ 0 := Submodule.smithNormalFormCoeffs_ne_zero b hrank
  have key : ∀ s : Finset (Module.Free.ChooseBasisIndex R M),
      (IsDiscreteValuationRing.addVal R (∏ i ∈ s, a i)).toNat =
        ∑ i ∈ s, (IsDiscreteValuationRing.addVal R (a i)).toNat := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, IsDiscreteValuationRing.addVal_mul,
        ENat.toNat_add, ih]
      · exact IsDiscreteValuationRing.addVal_eq_top_iff.not.mpr (ha i)
      · exact IsDiscreteValuationRing.addVal_eq_top_iff.not.mpr
          (Finset.prod_ne_zero_iff.mpr fun j _ => ha j)
  rw [Nat.card_congr (Submodule.quotientEquivPiSpan (LinearMap.range f) b hrank).toEquiv,
    Nat.card_pi]
  rw [Finset.prod_congr rfl fun i _ =>
    card_quotient_span_eq_card_residueField_pow_addVal (Submodule.smithNormalFormCoeffs_ne_zero b hrank i)]
  have hu : IsDiscreteValuationRing.addVal R (LinearMap.det h) = 0 := by
    have h3 := IsDiscreteValuationRing.addVal_eq_zero_of_unit hdeth.unit
    rwa [IsUnit.unit_spec] at h3
  rw [Finset.prod_pow_eq_pow_sum, hdet, IsDiscreteValuationRing.addVal_mul, hu, add_zero]
  exact congrArg _ (key Finset.univ).symm


open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
theorem _root_.GlobalTheory.UnramOrder.card_coker_of_det_eq : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E), ∀ ϖ : 𝒪[F], Irreducible ϖ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι L.O) (j : ℕ) (u : (𝒪[F])ˣ), ((A.det : L.O) : E) = algebraMap F E ((ϖ : F) ^ j * ((u : 𝒪[F]) : F)) → Nat.card ((ι → L.O) ⧸ LinearMap.range A.mulVecLin) = _root_.GlobalTheory.HL.resQ ϖ ^ (2 * j) := by
  intro F _ _ _ _ _ E _ _ _ L ϖ hϖ ι _ _ A j u hA
  obtain ⟨-, hO, -, -, hmem, -⟩ := _root_.GlobalTheory.UnramOrder.order_facts L ϖ hϖ
  let φ : 𝒪[F] →+* L.O :=
    { toFun := fun r => ⟨algebraMap F E r, (hmem r).mpr r.2⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp
      map_zero' := by ext; simp
      map_add' := by intro x y; ext; simp }
  letI : Algebra 𝒪[F] L.O := φ.toAlgebra
  have hφ : ∀ r : 𝒪[F], ((algebraMap 𝒪[F] L.O r : L.O) : E) = algebraMap F E r := fun r => rfl
  let c : L.O →+* L.O :=
    { toFun := fun x => ⟨L.cj x, (hO x.1 x.2).1⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp
      map_zero' := by ext; simp
      map_add' := by intro x y; ext; simp }
  have hc : ∀ x : L.O, ((c x : L.O) : E) = L.cj x := fun x => rfl
  obtain ⟨ω, hω, e, he, hωe⟩ := _root_.GlobalTheory.UnramOrder.exists_sub_cj_mul_eq_one L
  let ω' : L.O := ⟨ω, hω⟩
  have hunit : IsUnit (ω' - c ω') :=
    isUnit_iff_exists_inv.mpr ⟨⟨e, he⟩, Subtype.ext (by simpa [ω', hc] using hωe)⟩
  have hdecomp := _root_.GlobalTheory.UnramOrder.exists_eq_add_mul (R₀ := 𝒪[F]) c
    (fun x => Subtype.ext (by simp [hc, L.cj_cj]))
    (fun r => Subtype.ext (by simp [hc, hφ]))
    (fun x hx => by
      obtain ⟨r, hr⟩ := _root_.GlobalTheory.UnramOrder.exists_int_of_fixed L x.2 (congrArg Subtype.val hx)
      exact ⟨r, Subtype.ext (by rw [hφ, ← hr])⟩) hunit
  have hinjO : Function.Injective (algebraMap 𝒪[F] L.O) := by
    intro r s h
    have h' := congrArg Subtype.val h
    rw [hφ, hφ] at h'
    exact Subtype.ext (_root_.GlobalTheory.UnramOrder.algebraMap_inj L h')
  have hli : LinearIndependent 𝒪[F] ![(1 : L.O), ω'] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    rw [Algebra.smul_def, Algebra.smul_def, mul_one] at hst
    have hst' := congrArg c hst
    rw [map_add (f := _), map_mul, map_zero] at hst'
    have hfix : ∀ r : 𝒪[F], c (algebraMap 𝒪[F] L.O r) = algebraMap 𝒪[F] L.O r :=
      fun r => Subtype.ext (by simp [hc, hφ])
    rw [hfix, hfix] at hst'
    have ht0 : algebraMap 𝒪[F] L.O t * (ω' - c ω') = 0 := by
      rw [mul_sub]
      linear_combination hst - hst'
    have ht : t = 0 := hinjO (by rw [map_zero]; exact (hunit.mul_left_eq_zero).mp ht0)
    refine ⟨hinjO ?_, ht⟩
    rw [ht, map_zero, zero_mul, add_zero] at hst
    rw [hst, map_zero]
  have hspan : ⊤ ≤ Submodule.span 𝒪[F] (Set.range ![(1 : L.O), ω']) := by
    intro x _
    obtain ⟨a, b, hx⟩ := hdecomp x
    have hx' : x = a • ![(1 : L.O), ω'] 0 + b • ![(1 : L.O), ω'] 1 := by
      simp [hx, Algebra.smul_def]
    rw [hx']
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  let bO := Module.Basis.mk hli hspan
  haveI : Module.Free 𝒪[F] L.O := Module.Free.of_basis bO
  haveI : Module.Finite 𝒪[F] L.O := Module.Finite.of_basis bO
  have hrank : Module.finrank 𝒪[F] L.O = 2 := by
    rw [Module.finrank_eq_card_basis bO, Fintype.card_fin]
  have hdetA : A.det = algebraMap 𝒪[F] L.O (ϖ ^ j * (u : 𝒪[F])) := by
    apply Subtype.ext
    rw [hA, hφ]
    push_cast
    rfl
  have hdetf : LinearMap.det (A.mulVecLin.restrictScalars 𝒪[F]) =
      (ϖ ^ j * (u : 𝒪[F])) ^ 2 := by
    rw [LinearMap.det_restrictScalars]
    change Algebra.norm 𝒪[F] (LinearMap.det (Matrix.toLin' A)) = _
    rw [LinearMap.det_toLin', hdetA, Algebra.norm_algebraMap, hrank]
  have hne : (ϖ ^ j * (u : 𝒪[F])) ^ 2 ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ hϖ.ne_zero) u.ne_zero)
  have h1 := _root_.GlobalTheory.UnramOrder.card_coker_eq_pow_addVal_det (A.mulVecLin.restrictScalars 𝒪[F])
    (by rw [hdetf]; exact hne)
  rw [LinearMap.range_restrictScalars,
    Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv 𝒪[F] _).toEquiv] at h1
  rw [h1, hdetf, IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_mul,
    IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_uniformizer hϖ,
    IsDiscreteValuationRing.addVal_eq_zero_of_unit u, add_zero]
  have hres : Nat.card (IsLocalRing.ResidueField 𝒪[F]) = _root_.GlobalTheory.HL.resQ ϖ := by
    unfold _root_.GlobalTheory.HL.resQ
    rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ]
    rfl
  rw [hres]
  congr 1
  simp [mul_comm]

end GlobalTheory.UnramOrder
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardCokernelUnramifiedOrderMatrixOfDetBaseStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_cokernel_unramifiedOrder_matrix_of_det_base : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ ϖ : 𝒪[F], Irreducible ϖ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι L.O) (j : ℕ) (u : (𝒪[F])ˣ), ((A.det : L.O) : E) = algebraMap F E ((ϖ : F) ^ j * ((u : 𝒪[F]) : F)) → Nat.card ((ι → L.O) ⧸ LinearMap.range A.mulVecLin) = resQ ϖ ^ (2 * j) := by
  first | exact @GlobalTheory.UnramOrder.card_coker_of_det_eq | exact GlobalTheory.UnramOrder.card_coker_of_det_eq | (intros; apply GlobalTheory.UnramOrder.card_coker_of_det_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmpSqLeCardMulSum
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.AmpCS

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
private lemma norm_tsum_sq_le_card_mul_sum_sq {α ι : Type*} (s : Finset ι) (f : ι → α → ℂ)
    (g : α → ℂ) (hg : ∀ a, g a = ∑ i ∈ s, f i a) (hdom : ∀ i ∈ s, ∀ a, ‖f i a‖ ≤ ‖g a‖) :
    ‖∑' a, g a‖ ^ 2 ≤ s.card * ∑ i ∈ s, ‖∑' a, f i a‖ ^ 2 := by
  by_cases hs : Summable g
  · have hfi : ∀ i ∈ s, Summable (f i) := fun i hi =>
      Summable.of_norm_bounded (summable_norm_iff.mpr hs) (hdom i hi)
    have hsum : ∑' a, g a = ∑ i ∈ s, ∑' a, f i a := by
      simp_rw [hg]
      exact Summable.tsum_finsetSum hfi
    rw [hsum]
    calc ‖∑ i ∈ s, ∑' a, f i a‖ ^ 2 ≤ (∑ i ∈ s, ‖∑' a, f i a‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ s.card * ∑ i ∈ s, ‖∑' a, f i a‖ ^ 2 := sq_sum_le_card_mul_sum_sq
  · rw [tsum_eq_zero_of_not_summable hs, norm_zero]
    have : (0 : ℝ) ≤ s.card * ∑ i ∈ s, ‖∑' a, f i a‖ ^ 2 := by positivity
    simpa using this


open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
theorem _root_.GlobalTheory.AmpCS.ampSq_le_card_mul_sum : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E), ∀ (r k : ℕ) (S : _root_.GlobalTheory.HL.Frames L r k), 1 ≤ k → ∀ {ι : Type} (s : Finset ι) (P : ι → S.Datum → Submodule L.O S.V → Prop) (Q : S.Datum → Submodule L.O S.V → Prop), (∀ d Λ, S.IsTerm d Λ → (Q d Λ ↔ ∃ i ∈ s, P i d Λ)) → (∀ d Λ, S.IsTerm d Λ → ∀ i ∈ s, ∀ i' ∈ s, P i d Λ → P i' d Λ → i = i') → S.ampSq Q ≤ (s.card : ℝ≥0∞) * ∑ i ∈ s, S.ampSq (P i) := by
  intro F _ _ _ _ _ E _ _ _ L r k S _ ι s P Q hQ hdisj
  unfold _root_.GlobalTheory.HL.Frames.ampSq _root_.GlobalTheory.HL.Frames.sumData
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable), ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun o => ?_
  rw [← Finset.mul_sum, ← mul_assoc, mul_comm (s.card : ℝ≥0∞), mul_assoc]
  gcongr
  rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity), ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  unfold _root_.GlobalTheory.HL.Frames.amp
  apply norm_tsum_sq_le_card_mul_sum_sq
  · intro a
    by_cases ht : S.IsTerm (Quotient.out o) (Quotient.out a)
    · by_cases hq : Q (Quotient.out o) (Quotient.out a)
      · obtain ⟨i, hi, hPi⟩ := (hQ _ _ ht).mp hq
        rw [if_pos ⟨ht, hq⟩, Finset.sum_eq_single_of_mem i hi, if_pos ⟨ht, hPi⟩]
        intro j hj hji
        rw [if_neg]
        rintro ⟨-, hPj⟩
        exact hji (hdisj _ _ ht j hj i hi hPj hPi)
      · rw [if_neg (fun h => hq h.2)]
        refine (Finset.sum_eq_zero fun i hi => ?_).symm
        rw [if_neg]
        rintro ⟨-, hPi⟩
        exact hq ((hQ _ _ ht).mpr ⟨i, hi, hPi⟩)
    · rw [if_neg (fun h => ht h.1)]
      refine (Finset.sum_eq_zero fun i _ => ?_).symm
      rw [if_neg (fun h => ht h.1)]
  · intro i hi a
    split_ifs with h1 h2
    · exact le_rfl
    · exact absurd ⟨h1.1, (hQ _ _ h1.1).mpr ⟨i, hi, h1.2⟩⟩ h2
    · rw [norm_zero]; exact norm_nonneg _
    · simp

end GlobalTheory.AmpCS
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsTraceChar
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.TraceChar

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
private theorem psi0_eq_one_of_conj_eq_neg {F : Type} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
    (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {z : E} (hz : L.cj z = -z) : L.psi0 z = 1 := by
  set w := algebraMap F E (1 / 2) * z with hw
  have hcw : L.cj w = -w := by
    rw [hw, map_mul, AlgEquiv.commutes, hz, mul_neg]
  have hzw : z = w + w := by
    rw [hw, ← add_mul, ← map_add (f := _)]
    norm_num
  have h1 : L.psi0 w = L.psi0 (-w) := by rw [← hcw, _root_.Formalism.MainNotions.S.Loc.LocE.local_additive_char_conj]
  rw [hzw, AddChar.map_add_eq_mul]
  nth_rewrite 2 [h1]
  rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem ker_mkQ_comp_mulLeft_pow_eq_span' {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (n k : ℕ) :
    ((Submodule.mkQ (Ideal.span {ϖ ^ (n + k)})).comp (LinearMap.mulLeft 𝒪[F] (ϖ ^ k))).ker =
      Ideal.span {ϖ ^ n} := by
  ext y
  simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply,
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton]
  rw [pow_add, mul_comm (ϖ ^ n), mul_dvd_mul_iff_left (pow_ne_zero _ hϖ.ne_zero)]

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem card_quotient_span_pow_succ_eq_resQ_mul {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (n : ℕ) :
    Nat.card (𝒪[F] ⧸ Ideal.span {ϖ ^ (n + 1)}) =
      _root_.GlobalTheory.HL.resQ ϖ * Nat.card (𝒪[F] ⧸ Ideal.span {ϖ ^ n}) := by
  rw [add_comm n 1]
  set f := (Submodule.mkQ (Ideal.span {ϖ ^ (1 + n)})).comp (LinearMap.mulLeft 𝒪[F] (ϖ ^ n))
  have hS : Nat.card (LinearMap.range f) = _root_.GlobalTheory.HL.resQ ϖ := by
    unfold _root_.GlobalTheory.HL.resQ
    have hk := ker_mkQ_comp_mulLeft_pow_eq_span' hϖ 1 n
    rw [pow_one] at hk
    rw [← hk]
    exact (Nat.card_congr (f.quotKerEquivRange).toEquiv).symm
  set g := (Submodule.mkQ (LinearMap.range f)).comp (Submodule.mkQ (Ideal.span {ϖ ^ (1 + n)}))
  have hg : Function.Surjective g :=
    (Submodule.mkQ_surjective _).comp (Submodule.mkQ_surjective _)
  have hker : g.ker = Ideal.span {ϖ ^ n} := by
    ext y
    simp only [g, f, LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, LinearMap.mem_range,
      LinearMap.mulLeft_apply, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨z, hz⟩
      rw [Submodule.Quotient.eq, Ideal.mem_span_singleton] at hz
      have h2 : ϖ ^ n ∣ ϖ ^ (1 + n) := pow_dvd_pow _ (by omega)
      have h4 : ϖ ^ n ∣ ϖ ^ n * z := dvd_mul_right _ _
      simpa using (dvd_sub h4 (h2.trans hz))
    · rintro ⟨z, rfl⟩
      exact ⟨z, rfl⟩
  have e := (g.quotKerEquivOfSurjective hg).toEquiv
  rw [hker] at e
  rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.range f), hS, Nat.card_congr e]

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem card_quotient_span_pow_eq_resQ_pow {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (n : ℕ) :
    Nat.card (𝒪[F] ⧸ Ideal.span {ϖ ^ n}) = _root_.GlobalTheory.HL.resQ ϖ ^ n := by
  induction n with
  | zero =>
    simp only [pow_zero, Ideal.span_singleton_one]
    exact Nat.card_unique
  | succ n ih => rw [card_quotient_span_pow_succ_eq_resQ_mul hϖ, ih, pow_succ, mul_comm]

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem resQ_pos' {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) :
    0 < _root_.GlobalTheory.HL.resQ ϖ := by
  unfold _root_.GlobalTheory.HL.resQ
  have h := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ
  rw [← h]
  exact Nat.card_pos (α := 𝓀[F])

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem finite_quotient_span_pow_flag_measures {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (n : ℕ) :
    Finite (𝒪[F] ⧸ Ideal.span {ϖ ^ n}) :=
  Nat.finite_of_card_ne_zero (by rw [card_quotient_span_pow_eq_resQ_pow hϖ]; exact pow_ne_zero _ (resQ_pos' hϖ).ne')

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem exists_nat_mul_mem_integer (x : F) : ∃ N : ℕ, 0 < N ∧ (N : F) * x ∈ 𝒪[F] := by
  by_cases hx : x ∈ 𝒪[F]
  · exact ⟨1, one_pos, by simpa using hx⟩
  have hx0 : x ≠ 0 := by rintro rfl; exact hx (zero_mem _)
  have hinv : x⁻¹ ∈ 𝒪[F] := by
    rw [Valuation.mem_integer_iff] at hx ⊢
    rw [map_inv₀]
    exact inv_le_one_of_one_le₀ (le_of_lt (not_le.1 hx))
  set b : 𝒪[F] := ⟨x⁻¹, hinv⟩ with hbdef
  have hb0 : b ≠ 0 := by
    intro h
    have : (b : F) = 0 := by rw [h]; rfl
    exact inv_ne_zero hx0 this
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  obtain ⟨n, u, hb⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
  refine ⟨Nat.card (𝒪[F] ⧸ Ideal.span {ϖ ^ n}), ?_, ?_⟩
  · haveI := finite_quotient_span_pow_flag_measures hϖ n
    exact Nat.card_pos
  have hmem : ((Nat.card (𝒪[F] ⧸ Ideal.span {ϖ ^ n}) : ℕ) : 𝒪[F]) ∈ Ideal.span {ϖ ^ n} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← nsmul_one]
    exact card_nsmul_eq_zero'
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 hmem
  have hxb : x * (b : F) = 1 := mul_inv_cancel₀ hx0
  rw [hb] at hxb
  have hu : ((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) * (u : 𝒪[F]) = 1 := Units.inv_mul u
  have hu' : (((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) : F) * ((u : 𝒪[F]) : F) = 1 := by
    rw [← Subring.coe_mul, hu]; rfl
  have hN : ((Nat.card (𝒪[F] ⧸ Ideal.span {ϖ ^ n}) : ℕ) : F) = ((w : 𝒪[F]) : F) * ((ϖ : 𝒪[F]) : F) ^ n := by
    rw [← map_natCast (𝒪[F]).subtype, ← hw]; push_cast; rfl
  have : (Nat.card (𝒪[F] ⧸ Ideal.span {ϖ ^ n}) : F) * x = ((w * ((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) : 𝒪[F]) : F) := by
    rw [hN]
    push_cast at hxb ⊢
    linear_combination ((w : F) * (((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) : F)) * hxb - ((w : F) * ((ϖ : 𝒪[F]) : F) ^ n * x) * hu'
  rw [this]
  exact (w * ((u⁻¹ : (𝒪[F])ˣ) : 𝒪[F])).2


open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
theorem _root_.GlobalTheory.TraceChar.exists_trace_char : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E), ∃ ψ : AddChar F ℂ, (∀ x : F, ‖ψ x‖ = 1) ∧ (∀ x : F, (∀ y : 𝒪[F], ψ (x * y) = 1) ↔ x ∈ 𝒪[F]) ∧ ∀ (y : E) (c : F), y + L.cj y = algebraMap F E c → L.psi0 y = ψ c := by
  intro F _ _ _ _ _ E _ _ _ L
  let ψ : AddChar F ℂ := L.psi0.compAddMonoidHom
    ((algebraMap F E).toAddMonoidHom.comp (AddMonoidHom.mulLeft (1 / 2 : F)))
  have hψ : ∀ c, ψ c = L.psi0 (algebraMap F E (1 / 2 * c)) := fun c => rfl
  have hcomp : ∀ (y : E) (c : F), y + L.cj y = algebraMap F E c → L.psi0 y = ψ c := by
    intro y c h
    have hz : L.cj (y - algebraMap F E (1 / 2 * c)) = -(y - algebraMap F E (1 / 2 * c)) := by
      rw [map_sub, AlgEquiv.commutes]
      have : L.cj y = algebraMap F E c - y := by rw [← h]; ring
      rw [this]
      have : algebraMap F E c = algebraMap F E (1 / 2 * c) + algebraMap F E (1 / 2 * c) := by
        rw [← map_add (f := _)]; congr 1; ring
      rw [this]; ring
    have := psi0_eq_one_of_conj_eq_neg L hz
    rw [hψ, ← one_mul (L.psi0 (algebraMap F E _)), ← this, ← AddChar.map_add_eq_mul, sub_add_cancel]
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  have hint : ∀ c : 𝒪[F], ψ c = 1 := by
    intro c
    obtain ⟨e, he, htr⟩ := (_root_.GlobalTheory.UnramOrder.order_facts L ϖ hϖ).1 c
    rw [← hcomp e c htr, ← one_mul e]
    exact (_root_.Formalism.MainNotions.S.Loc.LocE.additive_character_dual_ring L 1).2 (one_mem _) e he
  refine ⟨ψ, ?_, ?_, hcomp⟩
  · intro x
    obtain ⟨N, hN, hNx⟩ := exists_nat_mul_mem_integer x
    have h1 : ψ x ^ N = 1 := by
      rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]
      exact hint ⟨_, hNx⟩
    have h2 : ‖ψ x‖ ^ N = 1 := by rw [← norm_pow, h1, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hN.ne').1 h2
  · intro x
    constructor
    · intro hx
      rw [← _root_.GlobalTheory.UnramOrder.algebraMap_mem_iff L]
      refine (_root_.Formalism.MainNotions.S.Loc.LocE.additive_character_dual_ring L _).1 fun e he => ?_
      obtain ⟨c, hc⟩ := _root_.GlobalTheory.UnramOrder.exists_trace L he
      have htr : algebraMap F E x * e + L.cj (algebraMap F E x * e) = algebraMap F E (x * c) := by
        rw [map_mul, AlgEquiv.commutes, ← mul_add, hc, map_mul]
      rw [hcomp _ _ htr]
      exact hx c
    · intro hx y
      exact hint ⟨x * y, mul_mem hx y.2⟩

end GlobalTheory.TraceChar
end
