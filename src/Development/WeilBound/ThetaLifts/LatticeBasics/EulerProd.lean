module

public import Development.WeilBound.ThetaLifts.LatticeBasics.HypothesesE

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.OrthogonalGroupLemmas
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ClosureSpanCoefficients
theorem UpperTheory.closure_span_coefficients :
    ∀ {R M L : Type} [Ring R] [AddCommGroup M] [Module R M] [AddCommGroup L] (O : AddSubgroup R) (f : L →+ M) {m : ℕ} (x : Fin m → L),
        Submodule.span ℤ (Set.range x) = ⊤ → ∀ z : M,
          z ∈ AddSubgroup.closure {z : M | ∃ a ∈ O, ∃ l : L, z = a • f l} ↔
            ∃ a : Fin m → R, (∀ i, a i ∈ O) ∧ ∑ i, a i • f (x i) = z := by
  intro R M L _ _ _ _ O f m x hx z
  constructor
  · intro hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, l, rfl⟩ := hz
      have hl : l ∈ Submodule.span ℤ (Set.range x) := hx ▸ Submodule.mem_top
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hl
      refine ⟨fun i => c i • a, fun i => O.zsmul_mem ha _, ?_⟩
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_zsmul, smul_assoc, smul_comm]
    | zero => exact ⟨0, fun _ => O.zero_mem, by simp⟩
    | add u v _ _ hu hv =>
      obtain ⟨a, ha, rfl⟩ := hu
      obtain ⟨b, hb, rfl⟩ := hv
      exact ⟨a + b, fun i => O.add_mem (ha i) (hb i), by
        simp [add_smul, Finset.sum_add_distrib]⟩
    | neg u _ hu =>
      obtain ⟨a, ha, rfl⟩ := hu
      exact ⟨-a, fun i => O.neg_mem (ha i), by simp⟩
  · rintro ⟨a, ha, rfl⟩
    exact sum_mem fun i _ => AddSubgroup.subset_closure ⟨a i, ha i, x i, rfl⟩
end

theorem UpperTheory.Reformulated.B.OrthogonalGroupLemmas.aux1 :
    ∀ (F : Type) [inst : Field F] [inst_1 : NumberField F] {a b : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F},
      a ∈
          {a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F |
            GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F a = (0 : NumberField.mixedEmbedding.mixedSpace F) ∧
              ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)),
                (GlobalTheory.AdelicU.evFin F v : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) a ∈
                  IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers F v} →
        b ∈
            {a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F |
              GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F a = (0 : NumberField.mixedEmbedding.mixedSpace F) ∧
                ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)),
                  (GlobalTheory.AdelicU.evFin F v : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) a ∈
                    IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers F v} →
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (a + b) = (0 : NumberField.mixedEmbedding.mixedSpace F) ∧
            ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)),
              (GlobalTheory.AdelicU.evFin F v : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (a + b) ∈
                IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers F v := by
  intro F _ _ a b ha hb
  refine ⟨?_, fun v => ?_⟩
  · have h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (a + b) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F a + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F b :=
      map_add (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1
    rw [h, ha.1, hb.1, add_zero]
  · rw [map_add (f := _)]
    exact add_mem (ha.2 v) (hb.2 v)

theorem UpperTheory.Reformulated.B.OrthogonalGroupLemmas.aux2 :
    ∀ (F : Type) [inst : Field F] [inst_1 : NumberField F],
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) = (0 : NumberField.mixedEmbedding.mixedSpace F) ∧
        ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)),
          (GlobalTheory.AdelicU.evFin F v : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (0 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) ∈
            IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers F v := by
  intro F _ _
  refine ⟨map_zero (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F), fun v => ?_⟩
  rw [map_zero]
  exact zero_mem _

theorem UpperTheory.Reformulated.B.OrthogonalGroupLemmas.aux3 :
    ∀ (F : Type) [inst : Field F] [inst_1 : NumberField F] {a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F},
      a ∈
          {a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F |
            GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F a = (0 : NumberField.mixedEmbedding.mixedSpace F) ∧
              ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)),
                (GlobalTheory.AdelicU.evFin F v : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) a ∈
                  IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers F v} →
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (-a) = (0 : NumberField.mixedEmbedding.mixedSpace F) ∧
          ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)),
            (GlobalTheory.AdelicU.evFin F v : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (-a) ∈
              IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers F v := by
  intro F _ _ a ha
  refine ⟨?_, fun v => ?_⟩
  · have h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (-a) = -GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F a :=
      map_neg (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1
    rw [h, ha.1, neg_zero]
  · rw [map_neg]
    exact neg_mem (ha.2 v)

noncomputable def UpperTheory.Reformulated.B.OrthogonalGroupLemmas.Oh :
    (F : Type) → [inst : Field F] → [inst_1 : NumberField F] → AddSubgroup (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) :=
    fun (F : Type) [inst : Field F] [inst_1 : NumberField F] ↦
      {
        carrier :=
          {a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F |
            GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F a = (0 : NumberField.mixedEmbedding.mixedSpace F) ∧
              ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)),
                (GlobalTheory.AdelicU.evFin F v : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) a ∈
                  IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers F v},
        add_mem' := @UpperTheory.Reformulated.B.OrthogonalGroupLemmas.aux1 F inst inst_1, zero_mem' := UpperTheory.Reformulated.B.OrthogonalGroupLemmas.aux2 F,
        neg_mem' := @UpperTheory.Reformulated.B.OrthogonalGroupLemmas.aux3 F inst inst_1 : AddSubgroup (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) }

theorem UpperTheory.Reformulated.B.OrthogonalGroupLemmas.lat_gen :
    ∀ {F E : Type} [inst : Field F] [inst_1 : NumberField F] [inst_2 : Field E] [NumberField E] [inst_4 : Algebra F E]
      {n : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n},
      Submodule.IsLattice E Y.L →
        ∃ (m : ℕ) (x : Fin m → ↥Y.L),
          Submodule.span ℤ (Set.range x) = ⊤ ∧
            ∀ (z : Fin n → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
              z ∈ GlobalTheory.ThK.latHat Y ↔
                ∃ (a : Fin m → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F),
                  (∀ (i : Fin m), a i ∈ UpperTheory.Reformulated.B.OrthogonalGroupLemmas.Oh F) ∧ ∑ i : Fin m, a i • GlobalTheory.ThK.incV F (↑(x i) : Fin n → E) = z := by
  intro F E _ _ _ _ _ n Y hL
  have h1 : Module.Finite (NumberField.RingOfIntegers E) Y.L := Module.Finite.iff_fg.2 hL.fg
  have h2 : Module.Finite ℤ Y.L := Module.Finite.trans (NumberField.RingOfIntegers E) Y.L
  obtain ⟨m, x, hx⟩ := Module.Finite.exists_fin (R := ℤ) (M := Y.L)
  refine ⟨m, x, hx, fun z => ?_⟩
  let f : Y.L →+ (Fin n → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :=
    { toFun := fun l => GlobalTheory.ThK.incV F (l : Fin n → E)
      map_zero' := funext fun _ => map_zero (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (E := E) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F))
      map_add' := fun a b => funext fun i =>
        map_add (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (E := E) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F)) (a.1 i) (b.1 i) }
  have hs : GlobalTheory.ThK.latHat Y = AddSubgroup.closure
      {z | ∃ a ∈ UpperTheory.Reformulated.B.OrthogonalGroupLemmas.Oh F, ∃ l : Y.L, z = a • f l} := by
    unfold GlobalTheory.ThK.latHat
    congr 1
    ext w
    constructor
    · rintro ⟨a, h0, hv, y, hy, rfl⟩
      exact ⟨a, ⟨h0, hv⟩, ⟨y, hy⟩, rfl⟩
    · rintro ⟨a, ⟨h0, hv⟩, y, rfl⟩
      exact ⟨a, h0, hv, y.1, y.2, rfl⟩
  rw [hs]
  exact UpperTheory.closure_span_coefficients (UpperTheory.Reformulated.B.OrthogonalGroupLemmas.Oh F) f x hx z
end

section -- merged from Development.WeilBound.ThetaLifts.LatticeBasics.EulerB
noncomputable section

namespace GlobalTheory.ThK.Dbl.Euler

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

def idem (v : Pl F) : AF F := ((0, singleFin v 1) : Ainf F × Af F)

theorem ev_self (v : Pl F) : evFin F v (idem v) = 1 := evalV_singleFin_self v 1

theorem ev_ne {v u : Pl F} (h : u ≠ v) : evFin F u (idem v) = 0 := evalV_singleFin_ne h 1

theorem mul_idem {v : Pl F} {a : AF F} (h : evFin F v a = 0) : a * idem v = 0 := by
  refine Prod.ext (mul_zero a.1) (af_ext fun u => ?_)
  show evFin F u (a * idem v) = evFin F u 0
  rw [map_mul, map_zero]
  by_cases e : u = v
  · rw [e, h, zero_mul]
  · rw [ev_ne e, mul_zero]

theorem at_iff {M : Type} [AddCommGroup M] [Module (AF F) M] {v : Pl F} {z : M} : At (evFin F v) z ↔ idem v • z = z := by
  refine ⟨fun h => ?_, fun h u hu => by rw [← h, smul_smul, mul_idem hu, zero_smul]⟩
  have := h (1 - idem v) (by rw [map_sub, map_one, ev_self, sub_self])
  rw [sub_smul, one_smul, sub_eq_zero] at this
  exact this.symm

theorem idem_sq (v : Pl F) : idem v * idem v = idem v := by
  have := mul_idem (v := v) (a := 1 - idem v) (by rw [map_sub, map_one, ev_self, sub_self])
  linear_combination -this


variable (F) in
def Oh : AddSubgroup (AF F) where
  carrier := {a | evI F a = 0 ∧ ∀ v, evFin F v a ∈ v.adicCompletionIntegers F}
  zero_mem' := ⟨map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F), fun v => by rw [map_zero]; exact zero_mem _⟩
  add_mem' := fun {a b} ha hb => ⟨(map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1).trans
    ((congrArg₂ (· + ·) ha.1 hb.1).trans (add_zero _)),
    fun v => by rw [map_add]; exact add_mem (ha.2 v) (hb.2 v)⟩
  neg_mem' := fun {a} ha => ⟨(map_neg (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1).trans
    ((congrArg Neg.neg ha.1).trans neg_zero), fun v => by rw [map_neg]; exact neg_mem (ha.2 v)⟩

theorem isCompact_Oh : IsCompact (Oh F : Set (AF F)) := by
  have h : IsCompact ((fun a : Af F => (show AF F from ((0, a) : Ainf F × Af F))) '' _) :=
    (GlobalTheory.IntegralFinAdele.integral_finiteAdele_properties F).1.image (continuous_const.prodMk continuous_id)
  refine (Set.ext fun a => ?_ : _ = (Oh F : Set (AF F))) ▸ h
  refine ⟨?_, fun ha => ⟨a.2, ha.2, Prod.ext
    ((map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective).1 ha.1).symm rfl⟩⟩
  rintro ⟨b, hb, rfl⟩
  exact ⟨map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F), hb⟩

theorem idem_mem {v : Pl F} {a : AF F} (h : evFin F v a ∈ v.adicCompletionIntegers F) : idem v * a ∈ Oh F := by
  refine ⟨?_, fun u => ?_⟩
  · show InfiniteAdeleRing.ringEquiv_mixedSpace F (0 * a.1) = 0
    rw [zero_mul, map_zero]
  · rw [map_mul]
    by_cases e : u = v
    · subst e; rwa [ev_self, one_mul]
    · rw [ev_ne e, zero_mul]; exact zero_mem _


variable (F) in
def incA : (Fin n → E) →+ (Fin n → AE F E) := AddMonoidHom.mk' (incV F) fun _ _ => funext fun _ => map_add _ _ _

variable {Y : Spc F E n}

omit [NumberField E] in
theorem gen_mem {a : AF F} (ha : a ∈ Oh F) {x : Fin n → E} (hx : x ∈ Y.L) : a • incV F x ∈ latHat Y :=
  AddSubgroup.subset_closure ⟨a, ha.1, ha.2, x, hx, rfl⟩

theorem lat_gen (hL : Y.L.IsLattice E) : ∃ (m : ℕ) (x : Fin m → Y.L), Submodule.span ℤ (Set.range x) = ⊤ ∧ ∀ z, z ∈ latHat Y ↔
    ∃ a : Fin m → AF F, (∀ i, a i ∈ Oh F) ∧ ∑ i, a i • incV F (x i).1 = z :=
  _root_.UpperTheory.Reformulated.B.OrthogonalGroupLemmas.lat_gen hL

theorem t2Space_cm_host_adeles : T2Space (AE F E) := by
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  exact e.isEmbedding.t2Space

theorem isCompact_latHat (hL : Y.L.IsLattice E) : IsCompact (latHat Y : Set (Fin n → AE F E)) := by
  obtain ⟨m, x, -, hx⟩ := lat_gen hL
  have : ContinuousSMul (AF F) (AE F E) := IsModuleTopology.toContinuousSMul _ _
  have : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) _
  have h := (isCompact_univ_pi fun _ : Fin m => isCompact_Oh (F := F)).image
    (f := fun a : Fin m → AF F => ∑ i, a i • incV F (x i).1)
    (by fun_prop)
  convert h using 1
  ext z
  exact (hx z).trans (exists_congr fun a => and_congr_left' (by simp))

theorem isClosed_latHat (hL : Y.L.IsLattice E) : IsClosed (latHat Y : Set (Fin n → AE F E)) :=
  have := t2Space_cm_host_adeles (F := F) (E := E)
  (isCompact_latHat hL).isClosed

def aeInt (Y : Spc F E n) : Submodule (AF F) (Fin n → AE F E) where
  carrier := {w | ∀ᶠ v : Pl F in cofinite, ∀ a ∈ Oh F, (idem v * a) • w ∈ latHat Y}
  zero_mem' := by
    rw [Set.mem_ofPred_eq]
    exact Eventually.of_forall fun _ _ _ => by rw [smul_zero]; exact zero_mem _
  add_mem' := fun h h' => by
    rw [Set.mem_ofPred_eq] at *
    exact (h.and h').mono fun _ e a ha => by rw [smul_add]; exact add_mem (e.1 a ha) (e.2 a ha)
  smul_mem' := fun c w h => by
    rw [Set.mem_ofPred_eq] at *
    refine (h.and c.2.2).mono fun v e a ha => ?_
    have := e.1 _ (idem_mem (v := v) (a := a * c) (by rw [map_mul]; exact mul_mem (ha.2 v) e.2))
    rwa [← mul_assoc, idem_sq, ← mul_assoc, mul_smul] at this

omit [NumberField E] in
theorem aeInt_iff {w} : w ∈ aeInt Y ↔ ∀ᶠ v : Pl F in cofinite, ∀ a ∈ Oh F, (idem v * a) • w ∈ latHat Y := Iff.rfl

theorem mem_of_lat (hL : Y.L.IsFullLattice E) (P : Submodule (AF F) (Fin n → AE F E)) (hP : ∀ x ∈ Y.L, incV F x ∈ P)
    (w : Fin n → AE F E) : w ∈ P := by
  have h1 : ∀ x : Fin n → E, ∀ t : E, incV F (t • x) ∈ P := fun x => by
    induction (hL.span_eq_top ▸ Submodule.mem_top : x ∈ Submodule.span E (Y.L : Set (Fin n → E))) using Submodule.span_induction with
    | mem x hx =>
      intro t
      obtain ⟨N, hN, hi⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic t)).exists_integral_multiple
      have h2 : incV F ((N • t) • x) ∈ P := hP _ (Y.L.smul_mem (⟨N • t, hi⟩ : 𝓞 E) hx)
      have h3 := P.smul_mem (algebraMap F (AF F) (N : F)⁻¹) h2
      rwa [smul_assoc, show incV F (N • t • x) = N • incV F (t • x) from map_zsmul (incA F) _ _, ← Int.cast_smul_eq_zsmul (AF F),
        smul_smul, ← map_intCast (algebraMap F (AF F)), ← map_mul, inv_mul_cancel₀ (Int.cast_ne_zero.2 hN), map_one, one_smul] at h3
    | zero => exact fun t => by rw [smul_zero, show incV F (0 : Fin n → E) = 0 from map_zero (incA F)]; exact zero_mem _
    | add x y _ _ hx hy =>
      intro t
      rw [smul_add, show incV F (t • x + t • y) = _ from map_add (incA F) _ _]
      exact add_mem (hx t) (hy t)
    | smul s x _ hx => exact fun t => by rw [smul_smul]; exact hx _
  rw [← Finset.univ_sum_single w]
  refine sum_mem fun i _ => ?_
  induction w i using TensorProduct.inductionOn with
  | add x y hx hy => rw [Pi.single_add]; exact add_mem hx hy
  | tmul a y =>
    convert P.smul_mem a (h1 (Pi.single i y) 1) using 1
    ext j
    by_cases e : j = i
    · subst e; simp [incV, inclR, TensorProduct.smul_tmul']
    · simp [incV, e]

theorem mem_aeInt (hL : Y.L.IsFullLattice E) (w : Fin n → AE F E) : w ∈ aeInt Y :=
  mem_of_lat hL _ (fun _ hx => aeInt_iff.2 <| Eventually.of_forall fun v _ ha => gen_mem (idem_mem (ha.2 v)) hx) w

theorem gen_surj (hL : Y.L.IsFullLattice E) {m : ℕ} {x : Fin m → Y.L} (hx : Submodule.span ℤ (Set.range x) = ⊤) :
    Function.Surjective (Fintype.linearCombination (AF F) fun i => incV F (x i).1) := fun w => by
  refine mem_of_lat hL (LinearMap.range _) (fun y hy => ?_) w
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 (hx ▸ Submodule.mem_top : (⟨y, hy⟩ : Y.L) ∈ _)
  have e := congrArg (fun t : Y.L => incA F t.1) hc
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [AddSubmonoidClass.coe_finsetSum, map_sum, SetLike.val_smul_of_tower, map_zsmul] at e
  refine ⟨fun i => c i, Eq.trans ?_ e⟩
  rw [Fintype.linearCombination_apply]
  exact Finset.sum_congr rfl fun i _ => Int.cast_smul_eq_zsmul _ _ _

theorem ae_mulVec (hL : Y.L.IsFullLattice E) (A : Matrix (Fin n) (Fin n) (AE F E)) :
    ∀ᶠ v in cofinite, ∀ z ∈ latHat Y, At (evFin F v) z → A *ᵥ z ∈ latHat Y := by
  obtain ⟨m, x, -, hx⟩ := lat_gen hL.toIsLattice
  filter_upwards [eventually_all.2 fun i => aeInt_iff.1 (mem_aeInt hL (A *ᵥ incV F (x i).1))] with v hv z hz h
  obtain ⟨a, ha, rfl⟩ := (hx z).1 hz
  rw [← at_iff.1 h, Finset.smul_sum, Matrix.mulVec_sum]
  exact sum_mem fun i _ => by rw [smul_smul, Matrix.mulVec_smul]; exact hv i _ (ha i)

end GlobalTheory.ThK.Dbl.Euler

end
end

section -- merged from Development.WeilBound.ThetaLifts.LatticeBasics.EulerA
noncomputable section

namespace GlobalTheory.ThK.Dbl.Euler

open MeasureTheory Set

variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H] [BorelSpace H]
  [LocallyCompactSpace H] [SecondCountableTopology H] {ν : Measure H} [ν.IsHaarMeasure] {K : Subgroup H}

theorem pres_right (hK : MeasurableSet (K : Set H)) (h1 : ν K = 1) {k : H} (hk : k ∈ K) :
    MeasurePreserving (· * k) ν ν := by
  have e := Measure.isMulLeftInvariant_eq_smul (ν.map (· * k)) ν
  have m : Measurable fun x : H => x * k := measurable_mul_const k
  have e2 := congrArg (· (K : Set H)) e
  have p : (fun x : H => x * k) ⁻¹' K = K := Set.ext fun x => K.mul_mem_cancel_right hk
  simp only [Measure.map_apply m hK, p, h1, Measure.coe_nnreal_smul_apply, mul_one] at e2
  refine ⟨m, ?_⟩
  rw [e, show Measure.haarScalarFactor (ν.map (· * k)) ν = 1 by exact_mod_cast e2.symm, one_smul]

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [LocallyCompactSpace G] [SecondCountableTopology G] {μ : Measure G} [μ.IsHaarMeasure]

theorem factor (hK : MeasurableSet (K : Set H)) (h1 : ν K = 1) (i : H →* G) (hi : Continuous i) (π : G → H) (hπ : Continuous π)
    (e : ∀ u g, π (i u * g) = u * π g) {f : G → ℂ} {l : H → ℂ} (hf : Integrable f μ)
    (hl : ∀ u g, π g = 1 → f (i u * g) = l u * f g) (hl1 : ∀ u ∈ K, l u = 1) {A : Set G} (hA : MeasurableSet A)
    (hAi : ∀ u g, i u * g ∈ A ↔ g ∈ A) : ∫ g in A, f g ∂μ = (∫ u, l u ∂ν) * ∫ g in A ∩ π ⁻¹' K, f g ∂μ := by
  let S : Set (H × G) := {p | p.1⁻¹ * π p.2 ∈ K}
  have hS : MeasurableSet S := (continuous_fst.inv.mul (hπ.comp continuous_snd)).measurable hK
  let Φ : H × G → ℂ := S.indicator fun p => A.indicator f p.2
  have vol : ∀ g, ν {u | u⁻¹ * π g ∈ K} = 1 := fun g => by
    rw [← h1, ← measure_preimage_mul ν (π g)⁻¹ K]
    congr 1
    ext u
    exact (K.inv_mem_iff.symm.trans (by simp))
  have mS : ∀ g, MeasurableSet {u | u⁻¹ * π g ∈ K} := fun g => (continuous_inv.mul continuous_const).measurable hK
  have sl : ∀ g, (fun u => Φ (u, g)) = {u | u⁻¹ * π g ∈ K}.indicator fun _ => A.indicator f g := fun g => rfl
  have hfA := hf.indicator hA
  have iΦ : Integrable Φ (ν.prod μ) := by
    refine (integrable_prod_iff' (hfA.1.comp_snd.indicator hS)).2 ⟨Filter.Eventually.of_forall fun g => ?_, ?_⟩
    · rw [sl, integrable_indicator_iff (mS g)]
      exact integrableOn_const (by simp [vol])
    · refine hfA.norm.congr (Filter.Eventually.of_forall fun g => ?_)
      have : (fun u => ‖Φ (u, g)‖) = {u | u⁻¹ * π g ∈ K}.indicator fun _ => ‖A.indicator f g‖ :=
        funext fun u => by rw [congrFun (sl g) u, norm_indicator_eq_indicator_norm]
      show _ = ∫ u, ‖Φ (u, g)‖ ∂ν
      rw [this, integral_indicator_const _ (mS g), Measure.real, vol]
      simp
  have sh : MeasurePreserving (fun p : H × G => (p.1, i p.1 * p.2)) (ν.prod μ) (ν.prod μ) :=
    (MeasurePreserving.id ν).skew_product (g := fun u g => i u * g) ((hi.comp continuous_fst).mul continuous_snd).measurable
      (Filter.Eventually.of_forall fun u => map_mul_left_eq_self μ (i u))
  have i2 := sh.integrable_comp_of_integrable iΦ
  have mB : MeasurableSet (A ∩ π ⁻¹' K) := hA.inter (hπ.measurable hK)
  calc ∫ g in A, f g ∂μ = ∫ g, ∫ u, Φ (u, g) ∂ν ∂μ := by
        rw [← integral_indicator hA]
        refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        simp only [sl]
        rw [integral_indicator_const _ (mS g), Measure.real, vol]
        simp
    _ = ∫ u, ∫ g, Φ (u, i u * g) ∂μ ∂ν := by
        rw [← integral_integral_swap (f := fun u g => Φ (u, g)) iΦ]
        exact integral_congr_ae (Filter.Eventually.of_forall fun u =>
          (integral_mul_left_eq_self (fun g => Φ (u, g)) (i u)).symm)
    _ = ∫ g, ∫ u, Φ (u, i u * g) ∂ν ∂μ := integral_integral_swap (f := fun u g => Φ (u, i u * g)) i2
    _ = _ := by
        rw [← integral_const_mul, ← integral_indicator mB]
        refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        by_cases hg : g ∈ A ∩ π ⁻¹' K
        · have z : π (i (π g)⁻¹ * g) = 1 := by rw [e, inv_mul_cancel]
          have w : ∀ u, f (i u * g) = l (u * π g) * f (i (π g)⁻¹ * g) := fun u => by
            rw [← hl _ _ z, ← mul_assoc, ← map_mul, mul_inv_cancel_right]
          have w1 := w 1
          rw [map_one, one_mul, one_mul, hl1 _ hg.2, one_mul] at w1
          have : ∀ u, Φ (u, i u * g) = l (u * π g) * f g := fun u => by
            simp only [Φ]
            rw [indicator_of_mem (show (u, i u * g) ∈ S by simpa [S, e] using hg.2), indicator_of_mem ((hAi u g).2 hg.1), w, w1]
          simp only [this]
          rw [indicator_of_mem hg, integral_mul_const,
            (pres_right hK h1 hg.2).integral_comp (Homeomorph.mulRight (π g)).measurableEmbedding l]
        · have : ∀ u, Φ (u, i u * g) = 0 := fun u => by
            simp only [Φ]
            by_cases h2 : π g ∈ K
            · exact indicator_apply_eq_zero.2 fun _ => indicator_of_notMem (fun h => hg ⟨(hAi u g).1 h, h2⟩) _
            · exact indicator_of_notMem (by simpa [S, e] using h2) _
          simp only [this]
          rw [indicator_of_notMem hg, integral_zero]

end GlobalTheory.ThK.Dbl.Euler

end
end

noncomputable section

namespace GlobalTheory.ThK.Dbl.Euler

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

section Cut

variable {S R k : Type} [CommRing S] [CommRing R] [Algebra S R] [Fintype k] [DecidableEq k] {e : S}

def cut (e : S) (A : Matrix k k R) : Matrix k k R := (1 - e) • 1 + e • A

theorem mix (he : e * e = e) (A B C D : Matrix k k R) :
    ((1 - e) • A + e • B) * ((1 - e) • C + e • D) = (1 - e) • (A * C) + e • (B * D) := by
  have h1 : (1 - e) * (1 - e) = 1 - e := by linear_combination he
  have h2 : (1 - e) * e = 0 := by linear_combination -he
  have h3 : e * (1 - e) = 0 := by linear_combination -he
  simp only [add_mul, mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul, h1, h2, h3, he, zero_smul, add_zero,
    zero_add]

theorem cut_mul (he : e * e = e) (A B : Matrix k k R) : cut e A * cut e B = cut e (A * B) := by
  rw [cut, cut, mix he, mul_one, cut]

theorem cut_sub (A : Matrix k k R) : cut e A - 1 = e • (A - 1) := by
  rw [cut, sub_smul, one_smul, smul_sub]; abel

theorem cut_eq {A : Matrix k k R} : cut e A = A ↔ e • (A - 1) = A - 1 := by rw [← cut_sub, sub_left_inj]

theorem cut_one : cut e (1 : Matrix k k R) = 1 := cut_eq.2 (by simp)

theorem cut_cut (he : e * e = e) (A : Matrix k k R) : cut e (cut e A) = cut e A :=
  cut_eq.2 (by rw [cut_sub, smul_smul, he])

theorem cut_form (he : e * e = e) (c : R →ₐ[S] R) {J A : Matrix k k R} (h : Aᵀ * J * A.map c = J) :
    (cut e A)ᵀ * J * (cut e A).map c = J := by
  have e1 : (cut e A).map c = (1 - e) • 1 + e • A.map c := by
    ext i j
    simp [cut, Matrix.one_apply, apply_ite c]
  have e2 : J = (1 - e) • J + e • J := by rw [← add_smul, sub_add_cancel, one_smul]
  rw [e1, cut, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul, Matrix.transpose_one]
  conv_lhs => rw [e2]
  rw [mix he, mix he, h, one_mul, mul_one, ← e2]

end Cut

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}

theorem lcsc_UA (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    LocallyCompactSpace (UA σ J) ∧ SecondCountableTopology (UA σ J) ∧ T2Space (UA σ J) := by
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  have := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  have : LocallyCompactSpace (AE F E) := e.isClosedEmbedding.locallyCompactSpace
  have : SecondCountableTopology (AE F E) := e.secondCountableTopology
  have : T2Space (AE F E) := e.isEmbedding.t2Space
  have : LocallyCompactSpace (Matrix (Fin n) (Fin n) (AE F E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → AE F E))
  have : LocallyCompactSpace (Matrix (Fin n) (Fin n) (AE F E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  have : LocallyCompactSpace (GL (Fin n) (AE F E)) :=
    Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) (AE F E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → AE F E))
  have : SecondCountableTopology (Matrix (Fin n) (Fin n) (AE F E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  have : SecondCountableTopology (GL (Fin n) (AE F E)) :=
    Units.isEmbedding_embedProduct.secondCountableTopology
  have : T2Space (GL (Fin n) (AE F E)) := Units.isEmbedding_embedProduct.t2Space
  have hs : Continuous (cA σ : AE F E → AE F E) :=
    IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
  have hc : IsClosed (UG (cA σ) (incM F J) : Set (GL (Fin n) (AE F E))) := by
    have hv : Continuous fun g : GL (Fin n) (AE F E) => (g : Matrix (Fin n) (Fin n) (AE F E)) :=
      Units.continuous_val
    exact isClosed_eq ((hv.matrix_transpose.matrix_mul continuous_const).matrix_mul (hv.matrix_map hs))
      continuous_const
  exact ⟨hc.isClosedEmbedding_subtypeVal.locallyCompactSpace, IsEmbedding.subtypeVal.secondCountableTopology,
    IsEmbedding.subtypeVal.t2Space⟩

variable {Y : Spc F E n} {v : Pl F}

theorem mm (g h : UA σ Y.J) : mat (g * h) = mat g * mat h := rfl

def prj (v : Pl F) : UA σ Y.J →* UA σ Y.J := MonoidHom.mk' (fun g => ⟨⟨cut (idem v) (mat g), cut (idem v) (mat g⁻¹),
    by rw [cut_mul (idem_sq v), ← mm, mul_inv_cancel]; exact cut_one, by rw [cut_mul (idem_sq v), ← mm, inv_mul_cancel]; exact cut_one⟩,
    cut_form (idem_sq v) _ g.2⟩) fun g h => Subtype.ext (Units.ext (cut_mul (idem_sq v) _ _).symm)

theorem mem_loc {g : UA σ Y.J} : g ∈ locGrp σ Y v ↔ prj v g = g := by
  have e : ∀ g : UA σ Y.J, g ∈ UAt σ Y (evFin F v) ↔ prj v g = g := fun g =>
    at_iff.trans (cut_eq.symm.trans ⟨fun h => Subtype.ext (Units.ext h), fun h => congrArg mat h⟩)
  refine ⟨fun h => ?_, fun h => Subgroup.subset_closure ((e g).2 h)⟩
  exact (Subgroup.closure_le ((prj v).eqLocus (MonoidHom.id _))).2 (fun g hg => (e g).1 hg) h

theorem prj_mem (g : UA σ Y.J) : prj v g ∈ locGrp σ Y v := mem_loc.2 (Subtype.ext (Units.ext (cut_cut (idem_sq v) _)))

theorem cont_mat : Continuous fun g : UA σ Y.J => mat g := Units.continuous_val.comp continuous_subtype_val

theorem cont_prj : Continuous (prj v : UA σ Y.J → UA σ Y.J) := by
  have : ContinuousSMul (AF F) (AE F E) := IsModuleTopology.toContinuousSMul _ _
  have : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) _
  have c1 : Continuous fun g : UA σ Y.J => cut (idem v) (mat g) := by
    have := cont_mat (σ := σ) (Y := Y)
    unfold cut
    refine continuous_matrix fun i j => ?_
    have := this.matrix_elem i j
    simp only [Matrix.add_apply, Matrix.smul_apply]
    fun_prop
  have c2 : Continuous fun g : UA σ Y.J => cut (idem v) (mat g⁻¹) := c1.comp continuous_inv
  exact Continuous.subtype_mk (Units.continuous_iff.2 ⟨c1, c2⟩) _

theorem off_of {g : UA σ Y.J} (h : prj v g = 1) : OffAt v g := by
  have e : idem v • (mat g - 1) = 0 := by rw [← cut_sub, show cut (idem v) (mat g) = 1 from congrArg mat h, sub_self]
  have c : ∀ x : AE F E, compFin F E v (idem v • x) = compFin F E v x := fun x => by
    rw [Algebra.smul_def, map_mul, show compFin F E v (algebraMap _ _ (idem v)) = evFin F v (idem v) ⊗ₜ 1 from rfl, ev_self]
    exact one_mul _
  rw [OffAt, ← Matrix.map_one (compFin F E v) (map_zero _) (map_one _)]
  ext i j
  have := c ((mat g - 1) i j)
  rw [show idem v • (mat g - 1) i j = 0 from congrFun (congrFun e i) j, map_zero, Matrix.sub_apply, map_sub] at this
  exact sub_eq_zero.1 this.symm

theorem at_mulVec (A : Matrix (Fin n) (Fin n) (AE F E)) {z : Fin n → AE F E} (h : At (evFin F v) z) : At (evFin F v) (A *ᵥ z) :=
  fun u hu => by rw [← Matrix.mulVec_smul, h u hu, Matrix.mulVec_zero]

theorem prj_mulVec (g : UA σ Y.J) {z : Fin n → AE F E} (h : At (evFin F v) z) : mat (prj v g) *ᵥ z = mat g *ᵥ z := by
  show cut (idem v) (mat g) *ᵥ z = _
  rw [cut, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_smul, one_smul, at_iff.1 h,
    at_iff.1 (at_mulVec _ h), sub_self, zero_add]

theorem int_prj {g : UA σ Y.J} : IntAt v (prj v g) ↔ IntAt v g :=
  forall₂_congr fun z _ => forall_congr' fun h => by rw [← map_inv, prj_mulVec _ h, prj_mulVec _ h]

theorem prj_ne {u : Pl F} (h : u ≠ v) {g : UA σ Y.J} (hg : g ∈ locGrp σ Y v) : prj u g = 1 := by
  refine Subtype.ext (Units.ext (sub_eq_zero.1 ((cut_sub (mat g)).trans ?_)))
  rw [← cut_eq.1 (congrArg mat (mem_loc.1 hg)), smul_smul, mul_idem (ev_ne h.symm), zero_smul]

theorem int_mul_ne {u : Pl F} (h : u ≠ v) {x : UA σ Y.J} (hx : x ∈ locGrp σ Y v) (g : UA σ Y.J) : IntAt u (x * g) ↔ IntAt u g := by
  rw [← int_prj, map_mul, prj_ne h hx, one_mul, int_prj]


variable (σ Y) in
def intGrp (v : Pl F) : Subgroup (UA σ Y.J) where
  carrier := {g | IntAt v g}
  one_mem' := fun z hz _ => by rw [inv_one, show mat (1 : UA σ Y.J) = 1 from rfl, Matrix.one_mulVec]; exact ⟨hz, hz⟩
  mul_mem' := fun ha hb z hz h => by
    rw [mul_inv_rev, mm, mm, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact ⟨(ha _ (hb z hz h).1 (at_mulVec _ h)).1, (hb _ (ha z hz h).2 (at_mulVec _ h)).2⟩
  inv_mem' := fun ha z hz h => by rw [inv_inv]; exact (ha z hz h).symm

theorem isClosed_int (hL : Y.L.IsLattice E) (v : Pl F) : IsClosed {g : UA σ Y.J | IntAt v g} := by
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  simp only [IntAt, Set.setOf_forall]
  exact isClosed_iInter fun z => isClosed_iInter fun _ => isClosed_iInter fun _ =>
    ((isClosed_latHat hL).preimage (cont_mat.matrix_mulVec continuous_const)).inter
      ((isClosed_latHat hL).preimage ((cont_mat.comp continuous_inv).matrix_mulVec continuous_const))

theorem isClosed_loc : IsClosed (locGrp σ Y v : Set (UA σ Y.J)) := by
  have := (lcsc_UA σ Y.J).2.2
  rw [show (locGrp σ Y v : Set (UA σ Y.J)) = {g | prj v g = g} from Set.ext fun _ => mem_loc]
  exact isClosed_eq cont_prj continuous_id

theorem lcsc_loc (v : Pl F) : LocallyCompactSpace (locGrp σ Y v) ∧ SecondCountableTopology (locGrp σ Y v) := by
  obtain ⟨a1, a2, a3⟩ := lcsc_UA σ Y.J
  exact ⟨isClosed_loc.isClosedEmbedding_subtypeVal.locallyCompactSpace, IsEmbedding.subtypeVal.secondCountableTopology⟩

theorem step (hL : Y.L.IsLattice E) {μ : Measure (UA σ Y.J)} (hμ : μ.IsHaarMeasure) {ν : Measure (locGrp σ Y v)}
    (hν : ν.IsHaarMeasure) (h1 : ν {g | IntAt v g.1} = 1) {f l : UA σ Y.J → ℂ} (hf : Integrable f μ)
    (hl : ∀ u ∈ locGrp σ Y v, ∀ g, OffAt v g → f (u * g) = l u * f g) (hl1 : ∀ u ∈ locGrp σ Y v, IntAt v u → l u = 1)
    {P : Set (Pl F)} (hv : v ∉ P) :
    ∫ g in {g | ∀ u ∈ P, IntAt u g}, f g ∂μ = (∫ u, l u.1 ∂ν) * ∫ g in {g | ∀ u ∈ insert v P, IntAt u g}, f g ∂μ := by
  obtain ⟨a1, a2, a3⟩ := lcsc_UA σ Y.J
  obtain ⟨b1, b2⟩ := lcsc_loc (σ := σ) (Y := Y) v
  have mA : MeasurableSet {g : UA σ Y.J | ∀ u ∈ P, IntAt u g} := by
    simp only [Set.setOf_forall]
    exact (isClosed_iInter fun u => isClosed_iInter fun _ => isClosed_int hL u).measurableSet
  rw [factor (ν := ν) (K := (intGrp σ Y v).subgroupOf (locGrp σ Y v)) (l := fun u => l u.1)
    ((isClosed_int hL v).preimage continuous_subtype_val).measurableSet h1 (locGrp σ Y v).subtype continuous_subtype_val
    (fun g => ⟨prj v g, prj_mem g⟩) (cont_prj.subtype_mk _)
    (fun u g => Subtype.ext ((map_mul _ _ _).trans (congrArg (· * prj v g) (mem_loc.1 u.2)))) hf
    (fun u g h => hl u u.2 g (off_of (congrArg Subtype.val h))) (fun u hu => hl1 u u.2 hu) mA
    (fun u g => forall₂_congr fun w hw => int_mul_ne (fun e : w = v => hv (e ▸ hw)) u.2 g)]
  congr 3
  ext g
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq, Set.forall_mem_insert]
  rw [and_comm]
  exact and_congr_left' (int_prj (σ := σ) (Y := Y) (v := v) (g := g))

theorem _root_.GlobalTheory.ThK.Dbl.eulerProd : EulerProd := by
  intro F E _ _ _ _ _ σ B n Y r s _ hY T μ hμ μl hl f fl hf h
  classical
  let A : Finset {v : Pl F // v ∉ T} → Set (UA σ Y.J) := fun S => {g | ∀ u ∈ {u | ∃ h : u ∉ T, ⟨u, h⟩ ∉ S}, IntAt u g}
  have e : ∀ S, (∏ v ∈ S, ∫ u, fl v.1 u.1 ∂μl v.1) * ∫ g in {g | ∀ v ∉ T, IntAt v g}, f g ∂μ = ∫ g in A S, f g ∂μ := fun S => by
    induction S using Finset.induction_on with
    | empty => simp [A]
    | insert v S hv ih =>
      rw [Finset.prod_insert hv, mul_assoc, ih]
      refine Eq.trans ?_ (step hY.lat.toIsLattice hμ (hl v).1 (hl v).2 hf (h v v.2).1 (h v v.2).2.1
        (P := {u | ∃ h : u ∉ T, ⟨u, h⟩ ∉ insert v S}) (by rintro ⟨_, h'⟩; exact h' (Finset.mem_insert_self _ _))).symm
      congr 3
      ext g
      refine forall_congr' fun u => imp_congr_left ⟨fun ⟨h1, h2⟩ => ?_, ?_⟩
      · by_cases e : u = v.1
        · exact .inl e
        · exact .inr ⟨h1, fun h3 => (Finset.mem_insert.1 h3).elim (fun h4 => e (congrArg Subtype.val h4)) h2⟩
      · rintro (rfl | ⟨h1, h2⟩)
        · exact ⟨v.2, hv⟩
        · exact ⟨h1, fun h3 => h2 (Finset.mem_insert_of_mem h3)⟩
  have u : ⋃ S, A S = Set.univ := Set.eq_univ_of_forall fun g => by
    have c := Filter.eventually_cofinite.1 ((ae_mulVec hY.lat (mat g)).and (ae_mulVec hY.lat (mat g⁻¹)))
    refine Set.mem_iUnion.2 ⟨c.toFinset.subtype _, fun u ⟨_, h2⟩ => ?_⟩
    rw [Finset.mem_subtype, Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at h2
    exact fun z hz h3 => ⟨h2.1 z hz h3, h2.2 z hz h3⟩
  have := GlobalTheory.AdelicUnitaryTop.countable_heightOneSpectrum F
  have := tendsto_setIntegral_of_monotone (s := A) (f := f) (μ := μ) (fun S => by
    simp only [A, Set.setOf_forall]
    exact (isClosed_iInter fun u => isClosed_iInter fun _ => isClosed_int hY.lat.toIsLattice u).measurableSet)
    (fun S S' hS g hg u ⟨h1, h2⟩ => hg u ⟨h1, fun h3 => h2 (hS h3)⟩) hf.integrableOn
  simpa only [e, u, Measure.restrict_univ] using this

end GlobalTheory.ThK.Dbl.Euler

end
