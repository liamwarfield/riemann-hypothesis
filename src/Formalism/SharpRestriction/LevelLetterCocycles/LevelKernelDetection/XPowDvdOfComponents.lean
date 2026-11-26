module

public import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfJumpsBdd
public import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfLvBasis

@[expose] public section

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.KerEqOfSpan
noncomputable section

namespace Formalism.MainNotions.N.Ln03.K8

open Formalism.ExponentWindows

abbrev GrQ {LL D : Type} [Field LL] [AddCommGroup D] [Module LL D] (F : ℤ → Submodule LL D) : Type :=
  ↥(Submodule.pi Set.univ fun k : ℤ => F (-k)) ⧸
    ((Submodule.pi Set.univ fun k : ℤ => F (1 - k)).comap (Submodule.pi Set.univ fun k : ℤ => F (-k)).subtype)

theorem finrank_grQ {LL D : Type} [Field LL] [AddCommGroup D] [Module LL D] [FiniteDimensional LL D]
    (F : ℤ → Submodule LL D) (hF : IsFilt F) :
    FiniteDimensional LL (GrQ F) ∧ Module.finrank LL (GrQ F) = Module.finrank LL D := by
  classical
  obtain ⟨hanti, ⟨lo, hlo⟩, ⟨b, hb⟩⟩ := hF
  set a : ℤ := min lo (b - 1) with ha_def
  have hab : a < b := by omega
  have htop : ∀ i, i ≤ a → F i = ⊤ := fun i hi => top_unique (hlo ▸ hanti (le_trans hi (min_le_left _ _)))
  have hbot : ∀ i, b ≤ i → F i = ⊥ := fun i hi => eq_bot_iff.2 (hb ▸ hanti hi)
  set N : ℕ := (b - a).toNat with hN
  let S : Finset ℤ := (Finset.range N).image fun j : ℕ => 1 - b + j
  have hmemS : ∀ k : ℤ, k ∈ S ↔ 1 - b ≤ k ∧ k ≤ -a := by
    intro k
    simp only [S, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨j, hj, rfl⟩; omega
    · intro h; exact ⟨(k - (1 - b)).toNat, by omega, by omega⟩
  let P0 := Submodule.pi Set.univ fun k : ℤ => F (-k)
  let P1 := Submodule.pi Set.univ fun k : ℤ => F (1 - k)
  have memP0 : ∀ (x : P0) (k : ℤ), (x : ℤ → D) k ∈ F (-k) :=
    fun x k => (Submodule.mem_pi.1 x.2) k (Set.mem_univ _)
  let Qk : ℤ → Type := fun k => ↥(F (-k)) ⧸ (F (1 - k)).comap (F (-k)).subtype
  let φ : P0 →ₗ[LL] ∀ k : S, Qk k :=
    LinearMap.pi fun k => (Submodule.mkQ _) ∘ₗ
      ((LinearMap.proj (R := LL) (φ := fun _ : ℤ => D) (k : ℤ)) ∘ₗ P0.subtype).codRestrict (F (-(k : ℤ)))
        (fun x => memP0 x (k : ℤ))
  have hφ : ∀ (x : P0) (k : S), φ x k =
      (Submodule.Quotient.mk (⟨(x : ℤ → D) k, memP0 x k⟩ : ↥(F (-(k : ℤ)))) : Qk k) := fun x k => rfl
  have hker : LinearMap.ker φ = P1.comap P0.subtype := by
    ext x
    rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply, Submodule.mem_pi]
    constructor
    · intro hx k _
      show (x : ℤ → D) k ∈ F (1 - k)
      by_cases hk : k ∈ S
      · have := congrFun hx ⟨k, hk⟩
        rw [hφ, Pi.zero_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at this
        exact this
      · rw [hmemS] at hk
        rcases not_and_or.1 hk with h | h
        · have h0 : (x : ℤ → D) k ∈ F (-k) := memP0 x k
          rw [hbot (-k) (by omega)] at h0
          rw [(Submodule.mem_bot LL).1 h0]
          exact Submodule.zero_mem _
        · rw [htop (1 - k) (by omega)]
          exact Submodule.mem_top
    · intro hx
      funext k
      rw [hφ, Pi.zero_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
      exact hx (k : ℤ) (Set.mem_univ _)
  have hsurj : Function.Surjective φ := by
    intro y
    have hy : ∀ k : S, ∃ z : ↥(F (-(k : ℤ))), (Submodule.Quotient.mk z : Qk k) = y k :=
      fun k => Submodule.Quotient.mk_surjective _ (y k)
    choose z hz using hy
    refine ⟨⟨fun k => if h : k ∈ S then (z ⟨k, h⟩ : D) else 0, ?_⟩, ?_⟩
    · rw [Submodule.mem_pi]
      intro k _
      by_cases h : k ∈ S
      · simp only [dif_pos h]; exact (z ⟨k, h⟩).2
      · simp only [dif_neg h]; exact Submodule.zero_mem _
    · funext k
      rw [hφ, ← hz k]
      congr 1
      apply Subtype.ext
      simp [k.2]
  let e : GrQ F ≃ₗ[LL] ∀ k : S, Qk k :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans (φ.quotKerEquivOfSurjective hsurj)
  have hFD : FiniteDimensional LL (GrQ F) := LinearEquiv.finiteDimensional e.symm
  refine ⟨hFD, ?_⟩
  have hle : ∀ k : ℤ, F (1 - k) ≤ F (-k) := fun k => hanti (by omega)
  have hQk : ∀ k : ℤ, (Module.finrank LL (Qk k) : ℤ) =
      (Module.finrank LL (F (-k)) : ℤ) - Module.finrank LL (F (1 - k)) := by
    intro k
    have h1 := Submodule.finrank_quotient_add_finrank ((F (1 - k)).comap (F (-k)).subtype)
    have h2 : Module.finrank LL ((F (1 - k)).comap (F (-k)).subtype) = Module.finrank LL (F (1 - k)) :=
      (Submodule.comapSubtypeEquivOfLe (hle k)).finrank_eq
    simp only [Qk]
    omega
  rw [e.finrank_eq, Module.finrank_pi_fintype]
  have hsum : ((∑ k : S, Module.finrank LL (Qk k) : ℕ) : ℤ) = Module.finrank LL D := by
    push_cast
    rw [Finset.sum_coe_sort S (fun k => (Module.finrank LL (Qk k) : ℤ))]
    simp only [S]
    rw [Finset.sum_image (fun i _ j _ h => by exact_mod_cast (add_left_cancel h : ((i : ℤ)) = j))]
    simp only [hQk]
    have hrw : ∀ j : ℕ, ((Module.finrank LL (F (-(1 - b + (j : ℤ)))) : ℤ) -
        Module.finrank LL (F (1 - (1 - b + (j : ℤ))))) =
        (Module.finrank LL (F (b - ((j + 1 : ℕ) : ℤ))) : ℤ) - Module.finrank LL (F (b - ((j : ℕ) : ℤ))) := by
      intro j
      rw [show -(1 - b + (j : ℤ)) = b - ((j + 1 : ℕ) : ℤ) by push_cast; ring,
        show 1 - (1 - b + (j : ℤ)) = b - ((j : ℕ) : ℤ) by ring]
    simp only [hrw]
    rw [Finset.sum_range_sub (fun j : ℕ => (Module.finrank LL (F (b - (j : ℤ))) : ℤ)) N]
    have h1 : b - ((N : ℕ) : ℤ) = a := by omega
    rw [h1, Nat.cast_zero, sub_zero, htop a le_rfl, hbot b le_rfl, finrank_top, finrank_bot]
    rfl
  exact_mod_cast hsum

end Formalism.MainNotions.N.Ln03.K8
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.GradedClassDecomposition
noncomputable section

namespace Formalism.MainNotions.N.Ln03.K8

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G TensorProduct

section Gr

variable {LL D : Type} [Field LL] [AddCommGroup D] [Module LL D]

def singleCoeffElement (F : ℤ → Submodule LL D) (k : ℤ) (w : D) (hw : w ∈ F (-k)) :
    ↥(Submodule.pi Set.univ fun k : ℤ => F (-k)) :=
  ⟨Pi.single k w, Submodule.mem_pi.2 fun j _ => by
    by_cases hj : j = k
    · subst hj
      simpa using hw
    · rw [Pi.single_eq_of_ne hj]
      exact zero_mem _⟩

def singleCoeffClass (F : ℤ → Submodule LL D) (k : ℤ) (w : D) (hw : w ∈ F (-k)) : GrQ F :=
  Submodule.Quotient.mk (singleCoeffElement F k w hw)

theorem graded_class_decomposition (F : ℤ → Submodule LL D)
    (g : ↥(Submodule.pi Set.univ fun k : ℤ => F (-k))) (a b : ℤ)
    (ha : ∀ j < a, (g : ℤ → D) j ∈ F (1 - j)) (hb : ∀ j ≥ b, (g : ℤ → D) j ∈ F (1 - j)) :
    (Submodule.Quotient.mk g : GrQ F) =
      ∑ j ∈ Finset.Ico a b, singleCoeffClass F j ((g : ℤ → D) j) (Submodule.mem_pi.1 g.2 j (Set.mem_univ j)) := by
  have e : ∑ j ∈ Finset.Ico a b, singleCoeffClass F j ((g : ℤ → D) j) (Submodule.mem_pi.1 g.2 j (Set.mem_univ j)) =
      Submodule.mkQ _ (∑ j ∈ Finset.Ico a b,
        singleCoeffElement F j ((g : ℤ → D) j) (Submodule.mem_pi.1 g.2 j (Set.mem_univ j))) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    rfl
  rw [e, Submodule.mkQ_apply, Submodule.Quotient.eq, Submodule.mem_comap, Submodule.mem_pi]
  intro i _
  have e2 : ((Submodule.pi Set.univ fun k : ℤ => F (-k)).subtype (g - ∑ j ∈ Finset.Ico a b,
      singleCoeffElement F j ((g : ℤ → D) j) (Submodule.mem_pi.1 g.2 j (Set.mem_univ j)))) i =
      (g : ℤ → D) i - ∑ j ∈ Finset.Ico a b, (Pi.single j ((g : ℤ → D) j) : ℤ → D) i := by
    simp only [Submodule.subtype_apply, Submodule.coe_sub, Submodule.coe_sum, Pi.sub_apply, Finset.sum_apply]
    rfl
  rw [e2, Finset.sum_pi_single]
  by_cases hi : i ∈ Finset.Ico a b
  · rw [if_pos hi, sub_self]
    exact zero_mem _
  · rw [if_neg hi, sub_zero]
    rw [Finset.mem_Ico, not_and_or, not_le, not_lt] at hi
    rcases hi with hi | hi
    · exact ha i hi
    · exact hb i hi

end Gr

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {Lb : LevB W} {hR : Ring9 W} {uZ : ℤ_[PD.p]ˣ} {ιZ : ℤ_[PD.p] →+* O}
    {T : LocLat G Qp LL O} {C : Coord W (baseIdOf hR) T} {c : ZMod n}

def classAtRoot (c : ZMod n) (hP4 : LevelMapHodgeFiltration W) (hcrys : IsCrys PD T.ρ)
    (hLb : ∀ (i : ZMod n) (ζ : LL) (x : ↥(W.N T)) (k : ℤ),
      W.levN T i ζ x k = ιV PD (LL := LL) (V := T.V) (Lb.levB T i ζ x k))
    (s : ℕ) (ζ : Rs LL PD.p s) : ↥(W.N T) →+ GrQ (FilD W T c s) where
  toFun x := Submodule.Quotient.mk
    ⟨fun k => (⟨Lb.levB T c ζ x k, Lb.mem T c ζ x k⟩ : Dc W T c), fun k _ => levB_mem_fil hP4 hcrys hLb s ζ x k⟩
  map_zero' := by
    rw [← Submodule.Quotient.mk_zero]
    congr 1
    apply Subtype.ext
    funext k
    apply Subtype.ext
    simp
  map_add' x y := by
    rw [← Submodule.Quotient.mk_add]
    congr 1
    apply Subtype.ext
    funext k
    apply Subtype.ext
    simp

theorem classes_span_top (hP4 : LevelMapHodgeFiltration W) (hcrys : IsCrys PD T.ρ)
    (hLb : ∀ (i : ZMod n) (ζ : LL) (x : ↥(W.N T)) (k : ℤ),
      W.levN T i ζ x k = ιV PD (LL := LL) (V := T.V) (Lb.levB T i ζ x k))
    (s : ℕ) (hfilt : IsFilt (FilD W T c s)) (ζ : Rs LL PD.p s) :
    Submodule.span LL (Set.range (classAtRoot c hP4 hcrys hLb s ζ)) = ⊤ := by
  set F := FilD W T c s with hFdef
  set U := Submodule.span LL (Set.range (classAtRoot c hP4 hcrys hLb s ζ)) with hU
  obtain ⟨hanti, ⟨lo, hlo⟩, ⟨hi, hhi⟩⟩ := hfilt
  have hprim : IsPrimitiveRoot (ζ : LL) (PD.p ^ (s + 1)) :=
    (mem_primitiveRoots (pow_pos PD.hp.pos _)).1 ζ.2
  have htop : ∀ j : ℤ, 1 - lo ≤ j → F (1 - j) = ⊤ := by
    intro j hj
    exact eq_top_iff.2 (hlo ▸ hanti (by omega))
  have hbot : ∀ j : ℤ, j < -hi → F (-j) = ⊥ := by
    intro j hj
    exact eq_bot_iff.2 (hhi ▸ hanti (by omega))

  have hsingle : ∀ (m : ℕ) (k : ℤ), (1 - lo - k).toNat = m → ∀ (w : Dc W T c) (hw : w ∈ F (-k)),
      singleCoeffClass F k w hw ∈ U := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
    intro k hk w hw
    by_cases hK : 1 - lo ≤ k
    · have h0 : singleCoeffClass F k w hw = 0 := by
        unfold singleCoeffClass
        rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.mem_pi]
        intro j _
        show (Pi.single k w : ℤ → Dc W T c) j ∈ F (1 - j)
        by_cases hj : j = k
        · subst hj
          rw [htop j hK]
          exact Submodule.mem_top
        · rw [Pi.single_eq_of_ne hj]
          exact zero_mem _
      rw [h0]
      exact zero_mem _
    · rw [not_le] at hK
      obtain ⟨x, a, ha0, hlow, hk0⟩ := (hP4 T hcrys c s ζ hprim).2 k
        (ιV PD (LL := LL) (V := T.V) (w : T.V ⊗[Qp] B)) hw
      let gx : ↥(Submodule.pi Set.univ fun k : ℤ => F (-k)) :=
        ⟨fun k => (⟨Lb.levB T c ζ x k, Lb.mem T c ζ x k⟩ : Dc W T c),
          fun k _ => levB_mem_fil hP4 hcrys hLb s ζ x k⟩
      let h := a • gx - singleCoeffElement F k w hw
      have hcls : (Submodule.Quotient.mk h : GrQ F) =
          a • classAtRoot c hP4 hcrys hLb s ζ x - singleCoeffClass F k w hw := by
        rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul]
        rfl
      have hval : ∀ j, ((h : ℤ → Dc W T c) j : T.V ⊗[Qp] B) =
          a • Lb.levB T c ζ x j - ((Pi.single k w : ℤ → Dc W T c) j : T.V ⊗[Qp] B) := by
        intro j
        rfl
      have hlowh : ∀ j < k + 1, (h : ℤ → Dc W T c) j ∈ F (1 - j) := by
        intro j hj
        show ιV PD (LL := LL) (V := T.V) (((h : ℤ → Dc W T c) j : T.V ⊗[Qp] B)) ∈ FilLev W T c s (1 - j)
        rw [hval, map_sub, map_smul, ← hLb]
        by_cases hjk : j = k
        · subst hjk
          rw [Pi.single_eq_same, ← neg_add_eq_sub]
          exact hk0
        · rw [Pi.single_eq_of_ne hjk, ZeroMemClass.coe_zero, map_zero, sub_zero, ← neg_add_eq_sub]
          exact hlow j (by omega)
      have hhigh : ∀ j ≥ 1 - lo, (h : ℤ → Dc W T c) j ∈ F (1 - j) := by
        intro j hj
        rw [htop j hj]
        exact Submodule.mem_top
      have hdec := graded_class_decomposition F h (k + 1) (1 - lo) hlowh hhigh
      have hsk : singleCoeffClass F k w hw = a • classAtRoot c hP4 hcrys hLb s ζ x -
          Submodule.Quotient.mk h := by
        rw [hcls]
        abel
      rw [hsk]
      refine sub_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)) ?_
      rw [hdec]
      refine Submodule.sum_mem _ fun j hj => ?_
      rw [Finset.mem_Ico] at hj
      exact ih (1 - lo - j).toNat (by omega) j rfl _ _
  rw [eq_top_iff]
  intro q _
  obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  have hlow' : ∀ j < -hi, (g : ℤ → Dc W T c) j ∈ F (1 - j) := by
    intro j hj
    have h0 : (g : ℤ → Dc W T c) j ∈ F (-j) := Submodule.mem_pi.1 g.2 j (Set.mem_univ j)
    rw [hbot j hj, Submodule.mem_bot] at h0
    rw [h0]
    exact zero_mem _
  have hhigh' : ∀ j ≥ 1 - lo, (g : ℤ → Dc W T c) j ∈ F (1 - j) := by
    intro j hj
    rw [htop j hj]
    exact Submodule.mem_top
  rw [graded_class_decomposition F g (-hi) (1 - lo) hlow' hhigh']
  exact Submodule.sum_mem _ fun j _ => hsingle _ j rfl _ _

theorem classAtRoot_smul (hP4 : LevelMapHodgeFiltration W) (hcrys : IsCrys PD T.ρ)
    (hLb : ∀ (i : ZMod n) (ζ : LL) (x : ↥(W.N T)) (k : ℤ),
      W.levN T i ζ x k = ιV PD (LL := LL) (V := T.V) (Lb.levB T i ζ x k))
    (s : ℕ) (hfilt : IsFilt (FilD W T c s)) (ζ : Rs LL PD.p s) (a : LetA O n) (x : ↥(W.N T)) :
    classAtRoot c hP4 hcrys hLb s ζ (a • x) =
      PowerSeries.constantCoeff (W.lev c ζ a) • classAtRoot c hP4 hcrys hLb s ζ x := by
  show Submodule.Quotient.mk _ = _ • Submodule.Quotient.mk _
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, Submodule.mem_comap, Submodule.mem_pi]
  intro k _
  show ιV PD (LL := LL) (V := T.V) (Lb.levB T c ζ (a • x) k -
      PowerSeries.constantCoeff (W.lev c ζ a) • Lb.levB T c ζ x k) ∈ FilLev W T c s (1 - k)
  rw [map_sub, LinearMap.map_smul (ιV PD (LL := LL) (V := T.V)), ← hLb, ← hLb, W.levN_smul]
  obtain ⟨m, hm⟩ := W.levN_supp T c ζ x
  have hsupp : Function.support (fun j : ℕ => PowerSeries.coeff j (W.lev c ζ a) • W.levN T c ζ x (k - j)) ⊆
      ↑(Finset.range ((k - m).toNat + 1)) := by
    intro j hj
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra hlt
    apply hj
    show PowerSeries.coeff j (W.lev c ζ a) • W.levN T c ζ x (k - j) = 0
    rw [hm (k - j) (by omega), smul_zero]
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_range_succ',
    PowerSeries.coeff_zero_eq_constantCoeff_apply, Nat.cast_zero, sub_zero, add_sub_cancel_right]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [hLb]
  refine Submodule.smul_mem _ _ ?_
  have h1 := levB_mem_fil (c := c) hP4 hcrys hLb s ζ x (k - ((j + 1 : ℕ) : ℤ))
  exact hfilt.1 (show 1 - k ≤ -(k - ((j + 1 : ℕ) : ℤ)) by push_cast; omega) h1

theorem level_idempotent_eq_one (ζ : LL) : W.lev c ζ (letE c : LetA O n) = 1 := by
  have h := W.lev_letter c ζ (1 - letE c) (by simp [letE])
  rw [map_sub, map_one, sub_eq_zero] at h
  exact h.symm

theorem coord_t_finset_sum {κ' : Type} (t : Finset κ') (f : κ' → C.V) :
    C.t c (∑ i ∈ t, f i) = ∑ i ∈ t, C.t c (f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [Coord.t_zero]
  | insert i t hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, C.t_add, ih]

theorem span_classes (hP4 : LevelMapHodgeFiltration W) (hcrys : IsCrys PD T.ρ)
    (hLb : ∀ (i : ZMod n) (ζ : LL) (x : ↥(W.N T)) (k : ℤ),
      W.levN T i ζ x k = ιV PD (LL := LL) (V := T.V) (Lb.levB T i ζ x k))
    (hmod : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀) (s : ℕ) (hfilt : IsFilt (FilD W T c s)) (ζ : Rs LL PD.p s)
    {r : ℕ} (e : Fin r → C.V) (he : ∀ j, e j ∈ (latOf C).N c)
    (hspan : Submodule.span (PowerSeries O) (Set.range e) = (latOf C).N c) :
    Submodule.span LL (Set.range fun j => (Submodule.Quotient.mk
      ⟨fun k => (⟨Lb.levB T c ζ ⟨C.t c (e j), he j⟩ k, Lb.mem T c ζ ⟨C.t c (e j), he j⟩ k⟩ : Dc W T c),
        fun k _ => levB_mem_fil hP4 hcrys hLb s ζ _ k⟩ : GrQ (FilD W T c s))) = ⊤ := by
  set cls := classAtRoot c hP4 hcrys hLb s ζ with hcls
  have hfun : (fun j => (Submodule.Quotient.mk
      ⟨fun k => (⟨Lb.levB T c ζ ⟨C.t c (e j), he j⟩ k, Lb.mem T c ζ ⟨C.t c (e j), he j⟩ k⟩ : Dc W T c),
        fun k _ => levB_mem_fil hP4 hcrys hLb s ζ _ k⟩ : GrQ (FilD W T c s))) =
      fun j => cls ⟨C.t c (e j), he j⟩ := rfl
  rw [hfun, eq_top_iff, ← classes_span_top hP4 hcrys hLb s hfilt ζ, Submodule.span_le]
  set U := Submodule.span LL (Set.range fun j => cls ⟨C.t c (e j), he j⟩) with hU
  have hsm : ∀ (a : LetA O n) (x : ↥(W.N T)), cls (a • x) = PowerSeries.constantCoeff (W.lev c ζ a) • cls x :=
    fun a x => classAtRoot_smul hP4 hcrys hLb s hfilt ζ a x
  obtain ⟨⟨r', b, hbΔ, huniq, -⟩, -⟩ := hmod

  have hb : ∀ j, ∃ y : ↥(W.N T), (y : W.DD T) = (letE c : LetA O n) • b j ∧ cls y ∈ U := by
    intro j
    have hN : (letE c : LetA O n) • b j ∈ W.N T := (W.N T).smul_mem _ (hbΔ j).1
    obtain ⟨e', he'⟩ := C.t_surj c ((letE c : LetA O n) • b j)
      (by rw [smul_smul, letE_mul_self])
      (fun δ hδ => by rw [WachCoordinates.γD_smulA, γA_letE, (hbΔ j).2 δ hδ])
    have he'N : e' ∈ (latOf C).N c := by
      show C.t c e' ∈ W.N T
      rw [he']
      exact hN
    rw [← hspan] at he'N
    obtain ⟨β, hβ⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 he'N
    have hy : (⟨(letE c : LetA O n) • b j, hN⟩ : ↥(W.N T)) =
        ∑ i, (baseIdOf hR).d (β i) • (⟨C.t c (e i), he i⟩ : ↥(W.N T)) := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simp only [Submodule.coe_smul]
      rw [← he', ← hβ, coord_t_finset_sum]
      exact Finset.sum_congr rfl fun i _ => C.t_smul c (β i) (e i)
    refine ⟨⟨_, hN⟩, rfl, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hy, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [hsm]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  choose y hy hyU using hb
  rintro _ ⟨x, rfl⟩
  obtain ⟨α, hα⟩ := (huniq x x.2).exists
  have hx : (letE c : LetA O n) • x = ∑ j, α j • y j := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    simp only [Submodule.coe_smul]
    rw [hα, Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [hy j, smul_comm]
  have hx1 : cls x = cls ((letE c : LetA O n) • x) := by
    rw [hsm, level_idempotent_eq_one, map_one, one_smul]
  show cls x ∈ U
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hx1, hx, map_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [hsm]
  exact Submodule.smul_mem _ _ (hyU j)

end Formalism.MainNotions.N.Ln03.K8

end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.HfracOf
noncomputable section

namespace Formalism.MainNotions.N.Ln03.K8

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G TensorProduct

theorem hfrac_of {O LL : Type} [CommRing O] [Field LL] [Algebra O LL] [IsFractionRing O LL] (a : LL) :
    ∃ y o : O, algebraMap O LL y ≠ 0 ∧ algebraMap O LL y * a = algebraMap O LL o := by
  haveI : Nontrivial O := (algebraMap O LL).domain_nontrivial
  obtain ⟨⟨x, s⟩, hx⟩ := IsLocalization.surj (nonZeroDivisors O) a
  refine ⟨s, x, ?_, ?_⟩
  · exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
  · rw [mul_comm]
    exact hx

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {Lb : LevB W} {hR : Ring9 W} {uZ : ℤ_[PD.p]ˣ} {ιZ : ℤ_[PD.p] →+* O}
    {T : LocLat G Qp LL O} {C : Coord W (baseIdOf hR) T} {c : ZMod n}

theorem rank_eq [IsFractionRing O LL] (hP3 : Formalism.MainNotions.DeltaInvariantLattices.p3 W T) (hmod : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀)
    {r : ℕ} (e : Fin r → C.V)
    (hind : LinearIndependent (PowerSeries O) e)
    (hspan : Submodule.span (PowerSeries O) (Set.range e) = (latOf C).N c) :
    FiniteDimensional LL (Dc W T c) ∧ r = Module.finrank LL (Dc W T c) := by
  classical
  let hBasis : Module.Basis (Fin r) (PowerSeries O) ↥((latOf C).N c) :=
    (Module.Basis.span hind).map (LinearEquiv.ofEq _ _ hspan)
  have hBasis_e : ∀ k, (hBasis k : C.V) = e k := fun k => by
    simp [hBasis, Module.Basis.span_apply]
  have hcmpLI := Pf.lvBasis_cmp_ind hP3 hmod hfrac_of hBasis hBasis_e
  let w : Fin r → Dc W T c := fun k =>
    ⟨W.cmp T ⟨C.t c (e k), Pf.lvBasis_e_mem hBasis hBasis_e k⟩, Pf.lvBasis_cmp_e_letter hBasis hBasis_e k⟩
  have hwLI : LinearIndependent LL w :=
    LinearIndependent.of_comp (DcrisL PD T.ρ (W.emb c)).subtype hcmpLI
  have hwsp : ⊤ ≤ Submodule.span LL (Set.range w) := by
    intro x _
    have hx := Pf.lvBasis_letter_le hP3 hmod hBasis hBasis_e x.2
    have hr : (Set.range fun k => W.cmp T ⟨C.t c (e k), Pf.lvBasis_e_mem hBasis hBasis_e k⟩) =
        (DcrisL PD T.ρ (W.emb c)).subtype '' Set.range w := by
      rw [← Set.range_comp]
      rfl
    rw [hr, Submodule.span_image, Submodule.mem_map] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := Subtype.ext hyx
    rwa [← this]
  let bD := Module.Basis.mk hwLI hwsp
  have hFD : FiniteDimensional LL (Dc W T c) := Module.Finite.of_basis bD
  refine ⟨hFD, ?_⟩
  rw [Module.finrank_eq_card_basis bD, Fintype.card_fin]

end Formalism.MainNotions.N.Ln03.K8
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.DetectPt
noncomputable section

namespace Formalism.MainNotions.N.Ln03.K8

open Formalism.ExponentWindows

theorem detect_pt {LL D : Type} [Field LL] [AddCommGroup D] [Module LL D] [FiniteDimensional LL D]
    (F : ℤ → Submodule LL D) (hF : IsFilt F) {r : ℕ} (hr : r = Module.finrank LL D)
    (g : Fin r → ℤ → D) (hsupp : ∀ j, ∃ m : ℤ, ∀ k < m, g j k = 0) (hg : ∀ j k, g j k ∈ F (-k))
    (hspan : Submodule.span LL (Set.range fun j =>
      (Submodule.Quotient.mk ⟨g j, fun k _ => hg j k⟩ : GrQ F)) = ⊤)
    (a : Fin r → PowerSeries LL) (e : ℕ)
    (h : ∀ k : ℤ, (∑ j, ∑ᶠ i : ℕ, PowerSeries.coeff i (a j) • g j (k - i)) ∈ F ((e : ℤ) - k)) :
    ∀ j, PowerSeries.X ^ e ∣ a j := by
  classical
  have hanti : Antitone F := hF.1
  have hli : LinearIndependent LL
      (fun j => (Submodule.Quotient.mk ⟨g j, fun k _ => hg j k⟩ : GrQ F)) := by
    obtain ⟨_, hrk⟩ := finrank_grQ F hF
    exact linearIndependent_of_top_le_span_of_card_eq_finrank hspan.ge
      (by rw [Fintype.card_fin, hrk, hr])
  have key : ∀ m, m < e → ∀ j, PowerSeries.coeff m (a j) = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hm
      have hcl : ∀ k' : ℤ, (∑ j, PowerSeries.coeff m (a j) • g j k') ∈ F (1 - k') := by
        intro k'
        have hS := h (k' + m)
        have hle : F ((e : ℤ) - (k' + m)) ≤ F (1 - k') := hanti (by omega)
        have hS' := hle hS
        have hR : ∀ j, (∑ᶠ i : ℕ, PowerSeries.coeff i (a j) • g j (k' + m - i)) -
            PowerSeries.coeff m (a j) • g j k' ∈ F (1 - k') := by
          intro j
          obtain ⟨mj, hmj⟩ := hsupp j
          obtain ⟨N, hN1, hN2⟩ : ∃ N : ℕ, m < N ∧ ∀ i : ℕ, N ≤ i → k' + m - i < mj :=
            ⟨(k' + m - mj).toNat + m + 1, by omega, fun i hi => by
              have := Int.self_le_toNat (k' + m - mj); omega⟩
          have hsub : (Function.support fun i : ℕ => PowerSeries.coeff i (a j) • g j (k' + m - i)) ⊆
              ↑(Finset.range N) := by
            intro i hi
            rw [Function.mem_support] at hi
            simp only [Finset.coe_range, Set.mem_Iio]
            by_contra hne
            apply hi
            rw [hmj _ (hN2 i (not_lt.mp hne)), smul_zero]
          rw [finsum_eq_sum_of_support_subset _ hsub,
            ← Finset.add_sum_erase _ _ (Finset.mem_range.mpr hN1)]
          simp only [add_sub_cancel_right, add_sub_cancel_left]
          refine sum_mem fun i hi => ?_
          obtain ⟨hne, -⟩ := Finset.mem_erase.mp hi
          rcases lt_or_gt_of_ne hne with hlt | hgt
          · rw [ih i hlt (by omega) j, zero_smul]
            exact zero_mem _
          · exact Submodule.smul_mem _ _ (hanti (by omega) (hg j (k' + m - i)))
        have hsum := sub_mem hS' (sum_mem (t := Finset.univ) fun j _ => hR j)
        rw [Finset.sum_sub_distrib, sub_sub_cancel] at hsum
        exact hsum
      have hz : ∑ j, PowerSeries.coeff m (a j) •
          (Submodule.Quotient.mk ⟨g j, fun k _ => hg j k⟩ : GrQ F) = 0 := by
        have hmk : ∑ j, PowerSeries.coeff m (a j) •
            (Submodule.Quotient.mk ⟨g j, fun k _ => hg j k⟩ : GrQ F) =
            (Submodule.mkQ _) (∑ j, PowerSeries.coeff m (a j) •
              (⟨g j, fun k _ => hg j k⟩ : ↥(Submodule.pi Set.univ fun k : ℤ => F (-k)))) := by
          set_option synthInstance.maxHeartbeats 100000 in
            simp [map_sum]
        rw [hmk, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
          Submodule.mem_pi]
        intro k _
        simpa using hcl k
      exact fun j => Fintype.linearIndependent_iff.mp hli _ hz j
  intro j
  exact PowerSeries.X_pow_dvd_iff.mpr fun m hm => key m hm j

end Formalism.MainNotions.N.Ln03.K8
end
end

noncomputable section

namespace Formalism.MainNotions.N.Ln03.K8

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G TensorProduct

theorem X_pow_dvd_of_components {ι R : Type} [CommRing R] (F : PowerSeries (ι → R)) (e : ℕ)
    (h : ∀ i, PowerSeries.X ^ e ∣ PowerSeries.map (Pi.evalRingHom (fun _ => R) i) F) :
    PowerSeries.X ^ e ∣ F := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro m hm
  funext i
  have := (PowerSeries.X_pow_dvd_iff.1 (h i)) m hm
  rw [PowerSeries.coeff_map] at this
  simpa using this

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {Lb : LevB W} {hR : Ring9 W} {uZ : ℤ_[PD.p]ˣ} {ιZ : ℤ_[PD.p] →+* O}
    {T : LocLat G Qp LL O} {C : Coord W (baseIdOf hR) T} {c : ZMod n}

theorem detect [IsFractionRing O LL] (hP4 : LevelMapHodgeFiltration W) (hSat : Sat W) (hcrys : IsCrys PD T.ρ)
    (hLb : ∀ (i : ZMod n) (ζ : LL) (x : ↥(W.N T)) (k : ℤ),
      W.levN T i ζ x k = ιV PD (LL := LL) (V := T.V) (Lb.levB T i ζ x k))
    (hmod : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀) (hP3 : Formalism.MainNotions.DeltaInvariantLattices.p3 W T) (hfree : (latOf C).Free c)
    (ϖ : O) (ell : ℕ)
    (hcompl : ∀ s < ell, ∀ (k : ℕ) (a : PowerSeries O), PowerSeries.X ^ k ∣ rhoL hR c s a →
      ∃ (N : ℕ) (z : PowerSeries O), PowerSeries.C (ϖ ^ N) * a = (baseIdOf hR).Bs.p s ^ k * z)
    (hϖ : ∃ (N : ℕ) (u : O), ((PD.p : ℕ) : O) ^ N = ϖ * u)
    (s : ℕ) (hs : s < ell) (hfilt : IsFilt (FilD W T c s)) (e : ℕ) (y : C.V) (hy : y ∈ (latOf C).N c)
    (h : ∀ (ζ : Rs LL PD.p s) (k : ℤ),
      (⟨Lb.levB T c ζ ⟨C.t c y, hy⟩ k, Lb.mem T c ζ ⟨C.t c y, hy⟩ k⟩ : Dc W T c) ∈
        FilD W T c s ((e : ℤ) - k)) :
    ∃ y' ∈ (latOf C).N c, y = (baseIdOf hR).Bs.p s ^ e • y' := by
  classical
  obtain ⟨r, b, hind, hspan⟩ := hfree
  have hb : ∀ j, b j ∈ (latOf C).N c := fun j => hspan ▸ Submodule.subset_span ⟨j, rfl⟩
  obtain ⟨hfd, hr⟩ := rank_eq hP3 hmod b hind hspan
  have hy' : y ∈ Submodule.span (PowerSeries O) (Set.range b) := hspan.symm ▸ hy
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hy'
  have hyN : (⟨C.t c y, hy⟩ : ↥(W.N T)) =
      ∑ j, (baseIdOf hR).d (a j) • (⟨C.t c (b j), hb j⟩ : ↥(W.N T)) := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    simp only [Submodule.coe_smul]
    rw [← ha, coord_t_finset_sum]
    exact Finset.sum_congr rfl fun j _ => C.t_smul c (a j) (b j)

  have hdiv : ∀ (ζ : Rs LL PD.p s) (j : Fin r), PowerSeries.X ^ e ∣ W.lev c ζ ((baseIdOf hR).d (a j)) := by
    intro ζ
    have := hfd
    refine detect_pt (FilD W T c s) hfilt hr
      (fun j k => (⟨Lb.levB T c ζ ⟨C.t c (b j), hb j⟩ k, Lb.mem T c ζ _ k⟩ : Dc W T c))
      (fun j => ?_) (fun j k => levB_mem_fil hP4 hcrys hLb s ζ _ k)
      (span_classes hP4 hcrys hLb hmod s hfilt ζ b hb hspan)
      (fun j => W.lev c ζ ((baseIdOf hR).d (a j))) e ?_
    · obtain ⟨m, hm⟩ := Lb.supp T c ζ ⟨C.t c (b j), hb j⟩
      exact ⟨m, fun k hk => Subtype.ext (hm k hk)⟩
    · intro k
      have hk := h ζ k
      change ιV PD (LL := LL) (V := T.V) (Lb.levB T c ζ ⟨C.t c y, hy⟩ k) ∈
        FilLev W T c s ((e : ℤ) - k) at hk
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hLb, hyN, map_sum, Finset.sum_apply] at hk
      show ((ιV PD (LL := LL) (V := T.V)).comp (DcrisL PD T.ρ (W.emb c)).subtype)
        (∑ j, ∑ᶠ i : ℕ, PowerSeries.coeff i (W.lev c ζ ((baseIdOf hR).d (a j))) •
          (⟨Lb.levB T c ζ ⟨C.t c (b j), hb j⟩ (k - i), Lb.mem T c ζ _ (k - i)⟩ : Dc W T c)) ∈
        FilLev W T c s ((e : ℤ) - k)
      suffices heq : ∀ j, ((ιV PD (LL := LL) (V := T.V)).comp (DcrisL PD T.ρ (W.emb c)).subtype)
          (∑ᶠ i : ℕ, PowerSeries.coeff i (W.lev c ζ ((baseIdOf hR).d (a j))) •
            (⟨Lb.levB T c ζ ⟨C.t c (b j), hb j⟩ (k - i), Lb.mem T c ζ _ (k - i)⟩ : Dc W T c)) =
          W.levN T c ζ ((baseIdOf hR).d (a j) • (⟨C.t c (b j), hb j⟩ : ↥(W.N T))) k by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, Finset.sum_congr rfl fun j _ => heq j]
        exact hk
      intro j
      rw [W.levN_smul]
      obtain ⟨m, hm⟩ := Lb.supp T c ζ ⟨C.t c (b j), hb j⟩
      have hfin : (Function.support fun i : ℕ => PowerSeries.coeff i (W.lev c ζ ((baseIdOf hR).d (a j))) •
          (⟨Lb.levB T c ζ ⟨C.t c (b j), hb j⟩ (k - i), Lb.mem T c ζ _ (k - i)⟩ : Dc W T c)).Finite := by
        refine (Finset.range ((k - m).toNat + 1)).finite_toSet.subset fun i hi => ?_
        rw [Finset.coe_range, Set.mem_Iio]
        by_contra hlt
        apply hi
        have h0 : (⟨Lb.levB T c ζ ⟨C.t c (b j), hb j⟩ (k - i), Lb.mem T c ζ _ (k - i)⟩ : Dc W T c) = 0 :=
          Subtype.ext (hm _ (by omega))
        show _ • _ = 0
        rw [h0, smul_zero]
      rw [map_finsum _ hfin]
      refine finsum_congr fun i => ?_
      rw [map_smul, LinearMap.comp_apply, Submodule.subtype_apply, ← hLb]

  have hcj : ∀ j, ∃ (N : ℕ) (z : PowerSeries O),
      PowerSeries.C (ϖ ^ N) * a j = (baseIdOf hR).Bs.p s ^ e * z := by
    intro j
    refine hcompl s hs e (a j) (X_pow_dvd_of_components _ e fun ζ => ?_)
    rw [map_eval_rhoL]
    exact hdiv ζ j
  choose Nj z hz using hcj
  obtain ⟨N', u, hu⟩ := hϖ
  set Nt := ∑ j, Nj j with hNt
  set K := N' * Nt with hK
  have hlK : ∀ j, PowerSeries.C (((PD.p : ℕ) : O) ^ K) * a j =
      (baseIdOf hR).Bs.p s ^ e * (PowerSeries.C (u ^ Nt * ϖ ^ (Nt - Nj j)) * z j) := by
    intro j
    have hle : Nj j ≤ Nt := Finset.single_le_sum (fun j _ => Nat.zero_le (Nj j)) (Finset.mem_univ j)
    have e1 : ((PD.p : ℕ) : O) ^ K = u ^ Nt * ϖ ^ (Nt - Nj j) * ϖ ^ Nj j := by
      rw [hK, pow_mul, hu, mul_pow, mul_assoc, ← pow_add, Nat.sub_add_cancel hle, mul_comm]
    rw [e1, map_mul, mul_assoc, hz j]
    ring
  set w : C.V := ∑ j, (PowerSeries.C (u ^ Nt * ϖ ^ (Nt - Nj j)) * z j) • b j with hw
  have hwN : w ∈ (latOf C).N c :=
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hb j)
  have hyw : PowerSeries.C (((PD.p : ℕ) : O) ^ K) • y = (baseIdOf hR).Bs.p s ^ e • w := by
    rw [← ha, Finset.smul_sum, hw, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul, smul_smul, hlK j]

  have hd : (baseIdOf hR).d ((baseIdOf hR).Bs.p s ^ e) =
      ∏ s' ∈ Finset.range (s + 1), pS W s' ^ (if s' = s then e else 0) := by
    rw [map_pow, BaseId.d_p, Finset.prod_eq_single s (fun s' _ hs' => by rw [if_neg hs', pow_zero])
      (fun hns => absurd (Finset.mem_range.2 (Nat.lt_succ_self s)) hns), if_pos rfl]
  have hdl : (baseIdOf hR).d (PowerSeries.C (((PD.p : ℕ) : O) ^ K)) = ((PD.p : ℕ) : LetA O n) ^ K := by
    rw [BaseId.d_C, map_pow, map_natCast]
  have hNΔ : ∀ x : W.DD T, x ∈ W.N T → (∀ δ ∈ W.DelF, W.γD T δ x = x) → x ∈ W.NΔ T :=
    fun x h1 h2 => ⟨h1, h2⟩
  have hx : C.t c y ∈ mulSet W T ((baseIdOf hR).d ((baseIdOf hR).Bs.p s ^ e)) (W.NΔ T) := by
    refine hSat T ((baseIdOf hR).d ((baseIdOf hR).Bs.p s ^ e)) 1 hcrys
      ⟨0, (baseIdOf hR).d ((baseIdOf hR).Bs.p s ^ e), ⟨fun s' => if s' = s then e else 0, s + 1, hd⟩, by simp⟩
      ⟨0, 1, ⟨fun _ => 0, 0, by simp⟩, by simp⟩ (C.t c y) (fun δ hδ => C.t_Δ c y δ hδ) ?_ ?_
    · rw [one_smul]
      exact hNΔ _ hy (fun δ hδ => C.t_Δ c y δ hδ)
    · refine ⟨K, C.t c w, hNΔ _ hwN (fun δ hδ => C.t_Δ c w δ hδ), ?_⟩
      rw [← hdl, ← Coord.t_smul, hyw, Coord.t_smul]
  obtain ⟨z', hz', hxz⟩ := hx
  have hlet : (letE c : LetA O n) • ((letE c : LetA O n) • z') = (letE c : LetA O n) • z' := by
    rw [smul_smul, letE_mul_self]
  have hΔ : ∀ δ ∈ W.DelF, W.γD T δ ((letE c : LetA O n) • z') = (letE c : LetA O n) • z' := by
    intro δ hδ
    rw [WachCoordinates.γD_smulA, γA_letE, hz'.2 δ hδ]
  obtain ⟨y'', hy''⟩ := C.t_surj c _ hlet hΔ
  refine ⟨y'', ?_, ?_⟩
  · show C.t c y'' ∈ W.N T
    rw [hy'']
    exact (W.N T).smul_mem _ hz'.1
  · apply C.t_inj c
    rw [Coord.t_smul, hy'', smul_smul, mul_comm, ← smul_smul, ← hxz, C.t_letter]

end Formalism.MainNotions.N.Ln03.K8

end
