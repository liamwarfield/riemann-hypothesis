module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.Assemble

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.IndexDet
noncomputable section

open NumberField Matrix

namespace PI.UnitaryGroupMassFormula.LCG

namespace DetIdxW

variable {K : Type} [Field K] [NumberField K] {k : ℕ}

def ιc (K : Type) [Field K] [NumberField K] (k : ℕ) : (Fin k → 𝓞 K) →+ (Fin k → K) :=
  (LinearMap.compLeft (Algebra.linearMap (𝓞 K) K) (Fin k)).toAddMonoidHom

lemma ιc_apply (t : Fin k → 𝓞 K) (i : Fin k) : ιc K k t i = algebraMap (𝓞 K) K (t i) := rfl

lemma ιc_inj : Function.Injective (ιc K k) := fun x y h => funext fun c =>
  IsFractionRing.injective (𝓞 K) K (by have := congrFun h c; rwa [ιc_apply, ιc_apply] at this)

lemma oLat_eq : (oLat K k).toAddSubgroup = (⊤ : AddSubgroup (Fin k → 𝓞 K)).map (ιc K k) := by
  ext x
  simp [oLat, ιc, AddSubgroup.mem_map, LinearMap.mem_range]

def vm (M : Matrix (Fin k) (Fin k) K) : (Fin k → K) →+ (Fin k → K) where
  toFun s := s ᵥ* M
  map_zero' := Matrix.zero_vecMul M
  map_add' a b := by simp [Matrix.add_vecMul]

lemma vm_apply (M : Matrix (Fin k) (Fin k) K) (s : Fin k → K) : vm M s = s ᵥ* M := rfl

lemma idx_int (γ : Matrix (Fin k) (Fin k) (𝓞 K)) (hγ : γ.det ≠ 0) :
    ((oLat K k).toAddSubgroup.map (vm (γ.map (algebraMap (𝓞 K) K)))).relIndex (oLat K k).toAddSubgroup =
      (Algebra.norm ℤ γ.det).natAbs := by
  classical
  have hGinj : Function.Injective γᵀ.mulVecLin := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro t ht
    by_contra hne
    exact hγ (Matrix.det_transpose γ ▸ Matrix.exists_mulVec_eq_zero_iff.1 ⟨t, hne, ht⟩)
  let Gz : (Fin k → 𝓞 K) →ₗ[ℤ] (Fin k → 𝓞 K) := γᵀ.mulVecLin.restrictScalars ℤ
  have hGz : Function.Injective Gz := hGinj
  let e := LinearEquiv.ofInjective Gz hGz
  have hcard := Submodule.natAbs_det_equiv (LinearMap.range Gz) e
  have hcomp : (LinearMap.range Gz).subtype ∘ₗ
      (e : (Fin k → 𝓞 K) →+ LinearMap.range Gz).toIntLinearMap = Gz := by
    ext x
    rfl
  have hdetG : LinearMap.det γᵀ.mulVecLin = γ.det := by
    rw [← Matrix.det_transpose γ]
    exact LinearMap.det_toLin' γᵀ
  rw [hcomp, LinearMap.det_restrictScalars, hdetG] at hcard
  have hcomm : (vm (γ.map (algebraMap (𝓞 K) K))).comp (ιc K k) = (ιc K k).comp Gz.toAddMonoidHom := by
    refine AddMonoidHom.ext fun t => funext fun j => ?_
    simp only [AddMonoidHom.comp_apply, vm_apply, ιc_apply, LinearMap.toAddMonoidHom_coe]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Gz, Matrix.vecMul, dotProduct, ιc_apply, map_sum, map_mul, mul_comm]
  have hr : (⊤ : AddSubgroup (Fin k → 𝓞 K)).map Gz.toAddMonoidHom = (LinearMap.range Gz).toAddSubgroup := by
    ext x
    simp [LinearMap.mem_range]
  rw [oLat_eq, AddSubgroup.map_map, hcomm, ← AddSubgroup.map_map,
    AddSubgroup.relIndex_map_map_of_injective _ _ ιc_inj, AddSubgroup.relIndex_top_right, hr, hcard,
    AddSubgroup.index_eq_card]
  rfl

lemma natAbs_norm_real (x : 𝓞 K) :
    ((Algebra.norm ℤ x).natAbs : ℝ) = |((Algebra.norm ℚ (algebraMap (𝓞 K) K x) : ℚ) : ℝ)| := by
  have h1 : ((Algebra.norm ℤ x : ℤ) : ℚ) = Algebra.norm ℚ (algebraMap (𝓞 K) K x) := Algebra.coe_norm_int x
  rw [Nat.cast_natAbs, Int.cast_abs, ← h1, Rat.cast_intCast]

lemma vecMul_inj (N : Matrix (Fin k) (Fin k) K) (hN : N.det ≠ 0) {s s' : Fin k → K}
    (h : s ᵥ* N = s' ᵥ* N) : s = s' := by
  have hu : IsUnit N.det := isUnit_iff_ne_zero.mpr hN
  have := congrArg (fun v => v ᵥ* N⁻¹) h
  simpa only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hu, Matrix.vecMul_one] using this

end DetIdxW

open DetIdxW in
theorem determinant_index_formula : DetIdx := by
  intro K _ _ k N Q D hOQ hOQ0 hDO hDO0 hDQ
  classical
  by_cases hN : N.det = 0
  · rw [hN, Algebra.norm_zero, Rat.cast_zero, abs_zero]
    positivity
  set O := (oLat K k).toAddSubgroup with hOdef

  obtain ⟨⟨d, hd⟩, hdT⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 K))
    (Finset.univ.image fun p : Fin k × Fin k => N p.1 p.2)
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  set dK := algebraMap (𝓞 K) K d with hdKdef
  have hdK : dK ≠ 0 := by
    rw [hdKdef, Ne, ← map_zero (algebraMap (𝓞 K) K)]
    exact fun h => hd0 (IsFractionRing.injective (𝓞 K) K h)
  have hG : ∀ i j, ∃ x : 𝓞 K, algebraMap (𝓞 K) K x = dK * N i j := by
    intro i j
    obtain ⟨x, hx⟩ := hdT (N i j) (Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩)
    exact ⟨x, by rw [hx, Algebra.smul_def]⟩
  choose G hGe using hG
  let Gm : Matrix (Fin k) (Fin k) (𝓞 K) := Matrix.of G
  have hGmap : Gm.map (algebraMap (𝓞 K) K) = dK • N := by
    ext i j
    simp [Gm, hGe]
  have hdetG : algebraMap (𝓞 K) K Gm.det = dK ^ k * N.det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hGmap, Matrix.det_smul, Fintype.card_fin]
  have hGdet0 : Gm.det ≠ 0 := by
    intro h
    have h2 := hdetG
    rw [h, map_zero] at h2
    exact (mul_ne_zero (pow_ne_zero _ hdK) hN) h2.symm
  let Dm : Matrix (Fin k) (Fin k) (𝓞 K) := d • (1 : Matrix (Fin k) (Fin k) (𝓞 K))
  have hDmap : Dm.map (algebraMap (𝓞 K) K) = dK • (1 : Matrix (Fin k) (Fin k) K) := by
    ext i j
    by_cases h : i = j <;> simp [Dm, h, hdKdef]
  have hDdet : Dm.det = d ^ k := by simp [Dm]
  have hDdet0 : Dm.det ≠ 0 := by rw [hDdet]; exact pow_ne_zero _ hd0
  set T := vm (Gm.map (algebraMap (𝓞 K) K)) with hTdef
  set S := vm (Dm.map (algebraMap (𝓞 K) K)) with hSdef
  have hT : ∀ s, T s = dK • (s ᵥ* N) := by
    intro s; rw [hTdef, vm_apply, hGmap, Matrix.vecMul_smul]
  have hS : ∀ s, S s = dK • s := by
    intro s; rw [hSdef, vm_apply, hDmap, Matrix.vecMul_smul, Matrix.vecMul_one]
  have hTinj : Function.Injective T := by
    intro s s' h
    rw [hT, hT] at h
    exact vecMul_inj N hN (smul_right_injective _ hdK h)
  have hSinj : Function.Injective S := by
    intro s s' h
    rw [hS, hS] at h
    exact smul_right_injective _ hdK h
  set X := O.map T with hX
  set Y := Q.map T with hY
  set Z := D.map S with hZ
  set dO := O.map S with hdO
  have hXO : X.relIndex O = (Algebra.norm ℤ Gm.det).natAbs := idx_int Gm hGdet0
  have hdOO : dO.relIndex O = (Algebra.norm ℤ Dm.det).natAbs := idx_int Dm hDdet0
  have hXY : X.relIndex Y = O.relIndex Q := AddSubgroup.relIndex_map_map_of_injective _ _ hTinj
  have hZdO : Z.relIndex dO = D.relIndex O := AddSubgroup.relIndex_map_map_of_injective _ _ hSinj
  have hZle_dO : Z ≤ dO := AddSubgroup.map_mono hDO
  have hdO_le : dO ≤ O := by
    rintro _ ⟨s, hs, rfl⟩
    rw [hS]
    have := (oLat K k).smul_mem d hs
    rwa [← algebraMap_smul K d s] at this
  have hZO_le : Z ≤ O := hZle_dO.trans hdO_le
  have hZY : Z ≤ Y := by
    rintro _ ⟨r, hr, rfl⟩
    obtain ⟨s, hs, hsr⟩ := hDQ r hr
    exact ⟨s, hs, by rw [hT, hS, hsr]⟩
  have hZO : Z.relIndex O = D.relIndex O * (Algebra.norm ℤ Dm.det).natAbs := by
    rw [← AddSubgroup.relIndex_mul_relIndex (hHK := hZle_dO) (hKL := hdO_le), hZdO, hdOO]
  have hXY0 : X.relIndex Y ≠ 0 := hXY ▸ hOQ0
  have hXZ0 : X.relIndex Z ≠ 0 := mt (AddSubgroup.relIndex_eq_zero_of_le_right (hKL := hZY)) hXY0
  have hZO0 : Z.relIndex O ≠ 0 := by
    rw [hZO]
    exact mul_ne_zero hDO0 (Int.natAbs_ne_zero.mpr (Algebra.norm_ne_zero_iff.mpr hDdet0))
  have hmul : (X ⊓ Z).relIndex O = X.relIndex Z * Z.relIndex O := by
    rw [← AddSubgroup.relIndex_mul_relIndex (hHK := (inf_le_right : X ⊓ Z ≤ Z)) (hKL := hZO_le),
      AddSubgroup.inf_relIndex_right]
  have h1 : X.relIndex O ≤ (X ⊓ Z).relIndex O :=
    AddSubgroup.relIndex_le_of_le_left (hHK := (inf_le_left : X ⊓ Z ≤ X)) (hHL := by rw [hmul]; exact mul_ne_zero hXZ0 hZO0)
  have h2 : X.relIndex Z ≤ X.relIndex Y := AddSubgroup.relIndex_le_of_le_right (hKL := hZY) (hHL := hXY0)
  have key : X.relIndex O ≤ X.relIndex Y * Z.relIndex O := by
    rw [hmul] at h1
    exact h1.trans (Nat.mul_le_mul_right _ h2)
  rw [hXO, hXY, hZO] at key
  have keyR : ((Algebra.norm ℤ Gm.det).natAbs : ℝ) ≤
      (O.relIndex Q : ℝ) * ((D.relIndex O : ℝ) * ((Algebra.norm ℤ Dm.det).natAbs : ℝ)) := by
    exact_mod_cast key
  rw [natAbs_norm_real, natAbs_norm_real, hdetG, hDdet, map_pow, map_mul, map_pow] at keyR
  simp only [Rat.cast_mul, Rat.cast_pow, abs_mul, abs_pow] at keyR
  have ha : 0 < |((Algebra.norm ℚ dK : ℚ) : ℝ)| ^ k := by
    apply pow_pos
    rw [abs_pos, Rat.cast_ne_zero]
    exact Algebra.norm_ne_zero_iff.mpr hdK
  have : |((Algebra.norm ℚ dK : ℚ) : ℝ)| ^ k * |((Algebra.norm ℚ N.det : ℚ) : ℝ)| ≤
      |((Algebra.norm ℚ dK : ℚ) : ℝ)| ^ k * ((O.relIndex Q : ℝ) * (D.relIndex O : ℝ)) := by
    calc _ ≤ _ := keyR
      _ = _ := by ring
  exact le_of_mul_le_mul_left this ha

end PI.UnitaryGroupMassFormula.LCG
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeCountingBound.IndexOf
noncomputable section

open NumberField Matrix

namespace PI.UnitaryGroupMassFormula.LCG

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [StarRing E] {n : ℕ}

def sv (w : Fin n → E) : Fin n → E := fun i => starRingEnd E (w i)

theorem hform_dot (J : Matrix (Fin n) (Fin n) E) (w z : Fin n → E) :
    Formalism.UG.hform (starRingEnd E) J w z = (sv w ᵥ* J) ⬝ᵥ z := by
  unfold Formalism.UG.hform
  simp only [dotProduct, vecMul, sv, Finset.sum_mul]
  exact Finset.sum_comm

theorem hform_herm (J : Matrix (Fin n) (Fin n) E) (hJ : Formalism.UG.IsHerm (starRingEnd E) J) (w z : Fin n → E) :
    starRingEnd E (Formalism.UG.hform (starRingEnd E) J w z) = Formalism.UG.hform (starRingEnd E) J z w := by
  have hJ' : ∀ i j, starRingEnd E (J i j) = J j i := by
    intro i j
    have := congrFun (congrFun hJ j) i
    simpa [Formalism.UG.cT] using this
  unfold Formalism.UG.hform
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, starRingEnd_self_apply, hJ']
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

end SlopeTestRemainingChoices

section Aux2

variable {E : Type} [Field E] [NumberField E]

theorem star_range [StarRing E] {x : E} (hx : x ∈ (algebraMap (𝓞 E) E).range) :
    starRingEnd E x ∈ (algebraMap (𝓞 E) E).range := by
  obtain ⟨o, rfl⟩ := RingHom.mem_range.mp hx
  have hint : IsIntegral ℤ (starRingEnd E (algebraMap (𝓞 E) E o)) := by
    first
    | exact (RingOfIntegers.isIntegral_coe o).map (starRingEnd E).toIntAlgHom
    | exact (o.2).map (starRingEnd E).toIntAlgHom
  exact RingHom.mem_range.mpr ⟨⟨_, hint⟩, rfl⟩

theorem mem_oLat {k : ℕ} (v : Fin k → E) :
    v ∈ oLat E k ↔ ∃ x : Fin k → 𝓞 E, (fun c => algebraMap (𝓞 E) E (x c)) = v := by
  unfold oLat
  first
  | (rw [LinearMap.mem_range]; rfl)
  | exact Iff.rfl
  | (simp [LinearMap.mem_range, LinearMap.compLeft]; rfl)

theorem dualL_oLat (k : ℕ) : dualL (oLat E k) = oLat E k := by
  ext t
  constructor
  · intro ht
    have ht' : ∀ s ∈ oLat E k, s ⬝ᵥ t ∈ (algebraMap (𝓞 E) E).range := ht
    have h1 : ∀ c, t c ∈ (algebraMap (𝓞 E) E).range := by
      intro c
      have hs : (Pi.single c 1 : Fin k → E) ∈ oLat E k := by
        rw [mem_oLat]
        exact ⟨Pi.single c 1, by funext d; by_cases h : d = c <;> simp [Pi.single_apply, h]⟩
      have := ht' _ hs
      simpa [dotProduct, Pi.single_apply] using this
    choose x hx using fun c => RingHom.mem_range.mp (h1 c)
    rw [mem_oLat]
    exact ⟨x, funext hx⟩
  · intro ht
    show ∀ s ∈ oLat E k, s ⬝ᵥ t ∈ (algebraMap (𝓞 E) E).range
    intro s hs
    obtain ⟨x, rfl⟩ := (mem_oLat t).mp ht
    obtain ⟨y, rfl⟩ := (mem_oLat s).mp hs
    refine RingHom.mem_range.mpr ⟨∑ c, y c * x c, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      simp [dotProduct, map_sum, map_mul]

theorem card_quot_relIndex {M : Type*} [AddCommGroup M] [Module (𝓞 E) M] (S B : Submodule (𝓞 E) M) :
    Nat.card (B ⧸ S.comap B.subtype) = S.toAddSubgroup.relIndex B.toAddSubgroup := rfl

end Aux2

private theorem relIndex_comap_eq_of_le_range {G H : Type*} [AddGroup G] [AddGroup H] (f : G →+ H)
    (A B : AddSubgroup H) (hB : B ≤ f.range) : (A.comap f).relIndex (B.comap f) = A.relIndex B := by
  rw [AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq, inf_eq_right.2 hB]

private theorem sum_smul_mem_span_iff_of_linearIndependent {K : Type} [Field K] [NumberField K] {n k : ℕ} (v : Fin k → Fin n → K)
    (hv : LinearIndependent K v) (t : Fin k → K) :
    (∑ c, t c • v c) ∈ Submodule.span (𝓞 K) (Set.range v) ↔ ∀ c, t c ∈ (algebraMap (𝓞 K) K).range := by
  constructor
  · intro h
    obtain ⟨o, ho⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).1 h
    have h0 : ∑ c, (algebraMap (𝓞 K) K (o c) - t c) • v c = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, algebraMap_smul]
      rw [ho, sub_self]
    have h1 := Fintype.linearIndependent_iff.1 hv _ h0
    intro c
    exact ⟨o c, sub_eq_zero.1 (h1 c)⟩
  · intro h
    refine Submodule.sum_mem _ fun c _ => ?_
    obtain ⟨o, ho⟩ := RingHom.mem_range.1 (h c)
    rw [← ho, algebraMap_smul]
    exact Submodule.smul_mem _ o (Submodule.subset_span ⟨c, rfl⟩)

theorem lattice_indexOf : IndexOf := by
  unfold IndexOf
  intro hDual hDet
  unfold IndexIneq
  intro I Λ hfg hspan hdual δ k u b' hu hδu hδspan hb' hb'li hperp hperpspan hidx1 hidx2
  let v : Fin k → Fin I.n → I.E := fun c => δ *ᵥ u c

  let ιL : (Fin k → I.E) →ₗ[𝓞 I.E] (Fin I.n → I.E) :=
    { toFun := fun t => ∑ c, t c • v c
      map_add' := fun s t => by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun o t => by simp only [Pi.smul_apply, smul_assoc, RingHom.id_apply, Finset.smul_sum] }
  let β : (Fin k → I.E) →+ (Fin I.n → I.E) :=
    AddMonoidHom.mk' (fun s => ∑ a, starRingEnd I.E (s a) • b' a) (fun s t => by
      simp only [Pi.add_apply, map_add (f := _), add_smul, Finset.sum_add_distrib])
  have hι : ∀ t, ιL t = ∑ c, t c • v c := fun t => rfl
  have hβ : ∀ s, β s = ∑ a, starRingEnd I.E (s a) • b' a := fun s => rfl
  have hint_v : ∀ t : Fin k → I.E, ιL t ∈ Submodule.span (𝓞 I.E) (Set.range v) ↔ t ∈ oLat I.E k := by
    intro t
    rw [hι, sum_smul_mem_span_iff_of_linearIndependent v hδu t, mem_oLat]
    constructor
    · intro h
      choose x hx using fun c => RingHom.mem_range.1 (h c)
      exact ⟨x, funext hx⟩
    · rintro ⟨x, rfl⟩ c
      exact ⟨x c, rfl⟩
  have hint_b : ∀ s : Fin k → I.E, β s ∈ Submodule.span (𝓞 I.E) (Set.range b') ↔ s ∈ oLat I.E k := by
    intro s
    rw [hβ, sum_smul_mem_span_iff_of_linearIndependent b' hb'li, mem_oLat]
    constructor
    · intro h
      have h' : ∀ c, s c ∈ (algebraMap (𝓞 I.E) I.E).range := by
        intro c
        have h2 := star_range (h c)
        rwa [starRingEnd_self_apply] at h2
      choose x hx using fun c => RingHom.mem_range.1 (h' c)
      exact ⟨x, funext hx⟩
    · rintro ⟨x, rfl⟩ c
      exact star_range ⟨x c, rfl⟩
  have hrange_v : (imSub I Λ δ).toAddSubgroup ≤ ιL.toAddMonoidHom.range := by
    intro y hy
    simp only [imSub, Submodule.mem_toAddSubgroup, Submodule.mem_map] at hy
    obtain ⟨z, -, rfl⟩ := hy
    obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun I.E).1 (hδspan z)
    exact AddMonoidHom.mem_range.2 ⟨g, hg⟩
  have hrange_b : (perpSub I Λ δ).toAddSubgroup ≤ β.range := by
    intro w hw
    have hw' : PerpKer I δ w := by
      simp only [perpSub, Submodule.mem_toAddSubgroup, Submodule.mem_inf, Submodule.restrictScalars_mem] at hw
      exact hw.2
    obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun I.E).1 (hperpspan w hw')
    refine AddMonoidHom.mem_range.2 ⟨fun a => starRingEnd I.E (g a), ?_⟩
    rw [hβ]
    simpa only [starRingEnd_self_apply] using hg
  have hoL_v : (oLat I.E k).toAddSubgroup =
      (Submodule.span (𝓞 I.E) (Set.range v)).toAddSubgroup.comap ιL.toAddMonoidHom := by
    ext t
    simp only [Submodule.mem_toAddSubgroup, AddSubgroup.mem_comap, LinearMap.toAddMonoidHom_coe]
    exact (hint_v t).symm
  have hoL_b : (oLat I.E k).toAddSubgroup =
      (Submodule.span (𝓞 I.E) (Set.range b')).toAddSubgroup.comap β := by
    ext s
    simp only [Submodule.mem_toAddSubgroup, AddSubgroup.mem_comap]
    exact (hint_b s).symm
  let R : Submodule (𝓞 I.E) (Fin k → I.E) := (imSub I Λ δ).comap ιL
  let Q : AddSubgroup (Fin k → I.E) := (perpSub I Λ δ).toAddSubgroup.comap β
  have hRQ : R.toAddSubgroup = (imSub I Λ δ).toAddSubgroup.comap ιL.toAddMonoidHom := by
    ext t
    exact Iff.rfl
  have hidxv : idx I (imSub I Λ δ) v =
      (Submodule.span (𝓞 I.E) (Set.range v)).toAddSubgroup.relIndex (imSub I Λ δ).toAddSubgroup :=
    card_quot_relIndex _ _
  have hidxb : idx I (perpSub I Λ δ) b' =
      (Submodule.span (𝓞 I.E) (Set.range b')).toAddSubgroup.relIndex (perpSub I Λ δ).toAddSubgroup :=
    card_quot_relIndex _ _
  have hRidx : (oLat I.E k).toAddSubgroup.relIndex R.toAddSubgroup = idx I (imSub I Λ δ) v := by
    rw [hidxv, hoL_v, hRQ, relIndex_comap_eq_of_le_range _ _ _ hrange_v]
  have hQidx : (oLat I.E k).toAddSubgroup.relIndex Q = idx I (perpSub I Λ δ) b' := by
    rw [hidxb, hoL_b, relIndex_comap_eq_of_le_range _ _ _ hrange_b]
  have hoR : oLat I.E k ≤ R := by
    intro t ht
    obtain ⟨x, rfl⟩ := (mem_oLat t).1 ht
    show ιL _ ∈ imSub I Λ δ
    rw [hι]
    simp only [imSub, Submodule.mem_map, LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply]
    refine ⟨∑ c, x c • u c, Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (hu c), ?_⟩
    rw [Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [Matrix.mulVec_smul, algebraMap_smul, v]
  have hspanperp : Submodule.span (𝓞 I.E) (Set.range b') ≤ perpSub I Λ δ := by
    rw [Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    simp only [perpSub, SetLike.mem_coe, Submodule.mem_inf, Submodule.restrictScalars_mem]
    exact ⟨hb' a, hperp a⟩
  have hoQ : (oLat I.E k).toAddSubgroup ≤ Q := by
    intro s hs
    show β s ∈ perpSub I Λ δ
    exact hspanperp ((hint_b s).2 hs)
  have hDo : dualL R ≤ oLat I.E k := by
    conv_rhs => rw [← dualL_oLat k]
    intro t ht
    show ∀ s ∈ oLat I.E k, s ⬝ᵥ t ∈ (algebraMap (𝓞 I.E) I.E).range
    intro s hs
    exact ht s (hoR hs)

  have hadd : ∀ x y z, hf I (x + y) z = hf I x z + hf I y z := by
    intro x y z
    simp only [hf, Formalism.UG.hform, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]
  have hsmul : ∀ (a : I.E) x z, hf I (a • x) z = starRingEnd I.E a * hf I x z := by
    intro a x z
    simp only [hf, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc]
    simp only [← Finset.mul_sum]
  have hsum : ∀ z (g : Fin k → I.E), hf I (∑ a, g a • b' a) z = ∑ a, starRingEnd I.E (g a) * hf I (b' a) z := by
    intro z g
    let φ : (Fin I.n → I.E) →+ I.E := AddMonoidHom.mk' (fun x => hf I x z) (fun x y => hadd x y z)
    have e := map_sum φ (fun a => g a • b' a) Finset.univ
    simp only [φ, AddMonoidHom.mk'_apply, hsmul] at e
    exact e

  have hkey : ∀ r ∈ (dualL R).toAddSubgroup, ∃ s ∈ Q, s ᵥ* pairM I b' u = r := by
    intro r hr
    have hr' : ∀ t ∈ R, t ⬝ᵥ r ∈ (algebraMap (𝓞 I.E) I.E).range := hr
    let G : (Fin I.n → I.E) →ₗ[I.E] (Fin k →₀ I.E) :=
      hδu.repr.comp ((Matrix.mulVecLin δ).codRestrict (Submodule.span I.E (Set.range v)) hδspan)
    have hG : ∀ z, δ *ᵥ z = ∑ c, G z c • v c := by
      intro z
      have e : Finsupp.linearCombination I.E v (hδu.repr ⟨δ *ᵥ z, hδspan z⟩) = δ *ᵥ z := by
        first
        | exact hδu.linearCombination_repr _
        | exact hδu.total_repr _
      rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)] at e
      exact e.symm
    have hGu : ∀ c, G (u c) = Finsupp.single c 1 := fun c => hδu.repr_eq_single c _ rfl
    let gL : (Fin I.n → I.E) →ₗ[I.E] I.E := ∑ c, r c • ((Finsupp.lapply c).comp G)
    have hgL : ∀ z, gL z = ∑ c, r c * G z c := by
      intro z
      simp only [gL, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
        Finsupp.lapply_apply, smul_eq_mul]
    let ℓ : Fin I.n → I.E := fun j => gL (fun j' => if j = j' then 1 else 0)
    have hgℓ : ∀ z, gL z = ℓ ⬝ᵥ z := by
      intro z
      rw [LinearMap.pi_apply_eq_sum_univ gL z, dotProduct]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_eq_mul, mul_comm]
    let m : Fin I.n → I.E := ℓ ᵥ* I.J⁻¹
    let w : Fin I.n → I.E := sv m
    have hJ : I.J⁻¹ * I.J = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 I.J_det)
    have hw : ∀ z, hf I w z = gL z := by
      intro z
      have hsv : sv w = m := by
        funext i
        simp [w, sv]
      rw [hf, hform_dot, hsv, hgℓ]
      simp only [m, Matrix.vecMul_vecMul, hJ, Matrix.vecMul_one]
    have hwΛ : w ∈ Λ := by
      apply hdual
      intro y hy
      have e : hf I y w = starRingEnd I.E (hf I w y) := by
        simp only [hf]
        rw [hform_herm I.J I.J_herm w y]
      rw [e]
      apply star_range
      rw [hw, hgL]
      have htR : (fun c => G y c) ∈ R := by
        show ιL _ ∈ imSub I Λ δ
        rw [hι]
        simp only [imSub, Submodule.mem_map, LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply]
        exact ⟨y, hy, hG y⟩
      have h2 := hr' _ htR
      rw [show (∑ c, r c * G y c) = ∑ c, G y c * r c from Finset.sum_congr rfl fun c _ => mul_comm _ _]
      exact h2
    have hwperp : PerpKer I δ w := by
      intro z hz
      rw [hw, hgL]
      have h0 : (Matrix.mulVecLin δ).codRestrict (Submodule.span I.E (Set.range v)) hδspan z = 0 :=
        Subtype.ext hz
      have hG0 : G z = 0 := by
        simp only [G, LinearMap.comp_apply, h0, map_zero]
      simp [hG0]
    have hwperpSub : w ∈ perpSub I Λ δ := by
      simp only [perpSub, Submodule.mem_inf, Submodule.restrictScalars_mem]
      exact ⟨hwΛ, hwperp⟩
    obtain ⟨g, hg⟩ := (Submodule.mem_span_range_iff_exists_fun I.E).1 (hperpspan w hwperp)
    refine ⟨fun a => starRingEnd I.E (g a), ?_, ?_⟩
    · show β _ ∈ perpSub I Λ δ
      rw [hβ]
      simp only [starRingEnd_self_apply]
      rw [hg]
      exact hwperpSub
    · funext c
      simp only [Matrix.vecMul, dotProduct, pairM, Matrix.of_apply]
      rw [← hsum (u c) g, hg, hw, hgL, hGu]
      simp [Finsupp.single_apply]
  have hd := hDual I.E k (oLat I.E k) R hoR (by rw [hRidx]; exact hidx1)
  rw [dualL_oLat] at hd
  have hmain := hDet I.E k (pairM I b' u) Q (dualL R).toAddSubgroup hoQ (by rw [hQidx]; exact hidx2)
    (fun x hx => hDo hx) hd.1 hkey
  have h3 : (dualL R).toAddSubgroup.relIndex (oLat I.E k).toAddSubgroup ≤ idx I (imSub I Λ δ) v := by
    rw [← hRidx]
    exact hd.2
  calc |((Algebra.norm ℚ (pairM I b' u).det : ℚ) : ℝ)|
      ≤ ((oLat I.E k).toAddSubgroup.relIndex Q : ℝ) *
          ((dualL R).toAddSubgroup.relIndex (oLat I.E k).toAddSubgroup : ℝ) := hmain
    _ ≤ (idx I (perpSub I Λ δ) b' : ℝ) * (idx I (imSub I Λ δ) v : ℝ) := by
        rw [hQidx]
        gcongr
    _ = _ := mul_comm _ _

end PI.UnitaryGroupMassFormula.LCG
end
end

theorem lattice_count_all : PI.LatCountG.LatCountAll :=
  PI.UnitaryGroupMassFormula.LCG.latCountAll_of_idx PI.UnitaryGroupMassFormula.LCG.determinant_index_formula PI.UnitaryGroupMassFormula.LCG.lattice_indexOf
