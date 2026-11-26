module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSerrePolyLaurent
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSerrePolyLaurentCohom
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PGradedPres
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PExtension
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTwistFinite
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PProjDegreePositive
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.BaseComap
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSectionCountDropFiltKernel
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapperQuotAdd
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PPrimeFiltrationExists
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSurjectiveClosed
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.FiniteHZeroOfExact

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSerreFree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

section FreeGraded

variable {S : Type u} [CommRing S] {N : ℕ}
variable {M : Type v} [AddCommGroup M] [Module (Poly S N) M] [Module S M]
  [IsScalarTower S (Poly S N) M]
variable {M' : Type w} [AddCommGroup M'] [Module (Poly S N) M'] [Module S M']
  [IsScalarTower S (Poly S N) M']


omit [IsScalarTower S (Poly S N) M] in
theorem smul_mem_of_mem_polyGraded (𝓜 : GradedPMod S N M) {a c : ℤ} {p : Poly S N} {m : M}
    (hp : p ∈ (polyGraded S N).piece a) (hm : m ∈ 𝓜.piece c) : p • m ∈ 𝓜.piece (c + a) := by
  change p ∈ weightedHomogeneousSubmodule S (fun _ => (1 : ℤ)) a at hp
  rw [mem_weightedHomogeneousSubmodule] at hp
  rcases le_or_gt 0 a with ha | ha
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le ha
    refine 𝓜.smul_mem n c p m ?_ hm
    intro μ hμ
    have h := hp hμ
    simp only [Finsupp.weight_apply, Finsupp.sum, Pi.one_apply, smul_eq_mul, mul_one,
      nsmul_eq_mul] at h ⊢
    exact_mod_cast h
  · have hp0 : p = 0 := by
      by_contra hne
      obtain ⟨μ, hμ⟩ := MvPolynomial.ne_zero_iff.mp hne
      have h := hp hμ
      simp only [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul, mul_one] at h
      have : (0 : ℤ) ≤ ∑ i ∈ μ.support, (μ i : ℤ) := Finset.sum_nonneg fun i _ => Int.natCast_nonneg _
      omega
    rw [hp0, zero_smul]
    exact zero_mem _

theorem locMap_locResS (f : M →ₗ[Poly S N] M') (I J : StdCell N) (h : I.1 ⊆ J.1)
    (x : LocMod S N M I.1) :
    (locMap f J.1).restrictScalars S (locResS I J h x) =
      locResS I J h ((locMap f I.1).restrictScalars S x) := by
  induction x using LocalizedModule.induction_on with
  | h m s =>
    change locMap f J.1 (locRes h _) = locRes h (locMap f I.1 _)
    rw [locRes_mk, locMap_mk, locMap_mk, locRes_mk]

theorem locMap_mem_degLoc {𝓜 : GradedPMod S N M} {𝓜' : GradedPMod S N M'} (f : M →ₗ[Poly S N] M')
    (t : ℤ) (hf : ∀ (a : ℤ) (m : M), m ∈ 𝓜.piece a → f m ∈ 𝓜'.piece (a + t)) {c c' : ℤ}
    (hc : c' = c + t) (I : StdCell N) (x : LocMod S N M I.1) (hx : x ∈ degLoc 𝓜 c I) :
    (locMap f I.1).restrictScalars S x ∈ degLoc 𝓜' c' I := by
  refine Submodule.span_induction (p := fun x _ => (locMap f I.1).restrictScalars S x ∈
    degLoc 𝓜' c' I) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨m, s, a, e, hm, hs, hae, rfl⟩
    refine Submodule.subset_span ⟨f m, s, a + t, e, hf a m hm, hs, by omega, ?_⟩
    exact locMap_mk f I.1 m s
  · simp
  · intro x y _ _ hx hy; simpa using add_mem hx hy
  · intro r x _ hx; simpa using Submodule.smul_mem _ r hx

def cohomMapShift {𝓜 : GradedPMod S N M} {𝓜' : GradedPMod S N M'} (f : M →ₗ[Poly S N] M') (t : ℤ)
    (hf : ∀ (a : ℤ) (m : M), m ∈ 𝓜.piece a → f m ∈ 𝓜'.piece (a + t)) (i : ℕ) {c c' : ℤ}
    (hc : c' = c + t) : cohom 𝓜 i c →ₗ[S] cohom 𝓜' i c' :=
  Cech.mapHdeg (degLoc 𝓜 c) (degLoc 𝓜' c') (fun I => (locMap f I.1).restrictScalars S)
    (locMap_locResS f) (locMap_mem_degLoc f t hf hc) i

variable (𝓜 : GradedPMod S N M) {r : ℕ} (b : Module.Basis (Fin r) (Poly S N) M) (d : Fin r → ℤ)


omit [IsScalarTower S (Poly S N) M] in
theorem coord_mem_piece (hb : ∀ j, b j ∈ 𝓜.piece (d j)) {a : ℤ} {m : M} (hm : m ∈ 𝓜.piece a)
    (j : Fin r) : b.coord j m ∈ (polyGraded S N).piece (a - d j) := by
  classical
  let _ := 𝓜.isInternal.chooseDecomposition
  let _ := (polyGraded S N).isInternal.chooseDecomposition

  have key : ∀ (k : Fin r) (p : Poly S N),
      (DirectSum.decompose 𝓜.piece (p • b k) a : M) =
        (DirectSum.decompose (polyGraded S N).piece p (a - d k) : Poly S N) • b k := by
    intro k p
    induction p using DirectSum.Decomposition.inductionOn (ℳ := (polyGraded S N).piece) with
    | zero => simp
    | @homogeneous e p =>
      have hpk : (p : Poly S N) • b k ∈ 𝓜.piece (d k + e) :=
        smul_mem_of_mem_polyGraded 𝓜 p.2 (hb k)
      by_cases he : d k + e = a
      · subst he
        rw [DirectSum.decompose_of_mem_same _ hpk, show d k + e - d k = e by omega,
          DirectSum.decompose_of_mem_same _ p.2]
      · rw [DirectSum.decompose_of_mem_ne _ hpk he,
          DirectSum.decompose_of_mem_ne _ p.2 (show e ≠ a - d k by omega), zero_smul]
    | add p q hp hq =>
      rw [add_smul, DirectSum.decompose_add, DirectSum.decompose_add, DirectSum.add_apply,
        DirectSum.add_apply, Submodule.coe_add, Submodule.coe_add, add_smul, hp, hq]
  have hsum : m = ∑ k, (DirectSum.decompose (polyGraded S N).piece (b.coord k m) (a - d k) :
      Poly S N) • b k := by
    conv_lhs => rw [← DirectSum.decompose_of_mem_same 𝓜.piece hm, ← b.sum_repr m]
    rw [DirectSum.decompose_sum, DFinsupp.finsetSum_apply, Submodule.coe_sum]
    exact Finset.sum_congr rfl fun k _ => key k _
  have hj : b.coord j m =
      (DirectSum.decompose (polyGraded S N).piece (b.coord j m) (a - d j) : Poly S N) := by
    conv_lhs => rw [hsum]
    rw [Module.Basis.coord_apply, ← Module.Basis.equivFun_symm_apply, ← Module.Basis.equivFun_apply,
      LinearEquiv.apply_symm_apply]
  rw [hj]
  exact Submodule.coe_mem _

theorem cohomMapShift_mk {𝓜 : GradedPMod S N M} {𝓜' : GradedPMod S N M'} (f : M →ₗ[Poly S N] M')
    (t : ℤ) (hf : ∀ (a : ℤ) (m : M), m ∈ 𝓜.piece a → f m ∈ 𝓜'.piece (a + t)) (i : ℕ) {c c' : ℤ}
    (hc : c' = c + t) (z : Cech.cocyDeg (locSys S N M) (degLoc 𝓜 c) locResS i) :
    ∃ z' : Cech.cocyDeg (locSys S N M') (degLoc 𝓜' c') locResS i,
      cohomMapShift f t hf i hc (Submodule.Quotient.mk z : cohom 𝓜 i c) =
        (Submodule.Quotient.mk z' : cohom 𝓜' i c') ∧ ∀ I, z'.1 I = locMap f I.1.1 (z.1 I) :=
  ⟨_, rfl, fun _ => rfl⟩


omit [Module S M] [IsScalarTower S (Poly S N) M] in
theorem sum_locMap_basis (I : Finset (Fin (N + 1))) (y : LocMod S N M I) :
    ∑ j, locMap (LinearMap.toSpanSingleton (Poly S N) M (b j)) I (locMap (b.coord j) I y) = y := by
  have h1 : ∀ j, locMap (LinearMap.toSpanSingleton (Poly S N) M (b j)) I (locMap (b.coord j) I y) =
      locMap ((LinearMap.toSpanSingleton (Poly S N) M (b j)).comp (b.coord j)) I y := fun j => by
    simp only [locMap]
    rw [IsLocalizedModule.map_comp' (monos (S := S) I) (LocalizedModule.mkLinearMap (monos (S := S) I) M)
      (LocalizedModule.mkLinearMap (monos (S := S) I) (Poly S N))
      (LocalizedModule.mkLinearMap (monos (S := S) I) M)]
    rfl
  have h2 : ∑ j, (LinearMap.toSpanSingleton (Poly S N) M (b j)).comp (b.coord j) = LinearMap.id := by
    ext m
    simp only [LinearMap.sum_apply, LinearMap.comp_apply,
      LinearMap.toSpanSingleton_apply, Module.Basis.coord_apply, LinearMap.id_apply]
    exact b.sum_repr m
  calc ∑ j, locMap (LinearMap.toSpanSingleton (Poly S N) M (b j)) I (locMap (b.coord j) I y)
      = ∑ j, locMap ((LinearMap.toSpanSingleton (Poly S N) M (b j)).comp (b.coord j)) I y :=
        Finset.sum_congr rfl fun j _ => h1 j
    _ = locMap (∑ j, (LinearMap.toSpanSingleton (Poly S N) M (b j)).comp (b.coord j)) I y := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [locMap, map_sum]
        exact (LinearMap.sum_apply Finset.univ _ y).symm
    _ = y := by
        rw [h2]
        simp only [locMap, IsLocalizedModule.map_id]
        rfl

variable (hb : ∀ j, b j ∈ 𝓜.piece (d j))
include hb

def freeIncl (i : ℕ) (c : ℤ) (j : Fin r) : cohom (polyGraded S N) i (c - d j) →ₗ[S] cohom 𝓜 i c :=
  cohomMapShift (LinearMap.toSpanSingleton (Poly S N) M (b j)) (d j)
    (fun _ _ hp => by
      rw [LinearMap.toSpanSingleton_apply, add_comm]
      exact smul_mem_of_mem_polyGraded 𝓜 hp (hb j)) i (by ring)

def freeCoord (i : ℕ) (c : ℤ) (j : Fin r) : cohom 𝓜 i c →ₗ[S] cohom (polyGraded S N) i (c - d j) :=
  cohomMapShift (b.coord j) (-d j)
    (fun _ _ hm => by rw [← sub_eq_add_neg]; exact coord_mem_piece 𝓜 b d hb hm j) i (by ring)

theorem sum_freeIncl_freeCoord (i : ℕ) (c : ℤ) (x : cohom 𝓜 i c) :
    ∑ j, freeIncl 𝓜 b d hb i c j (freeCoord 𝓜 b d hb i c j x) = x := by
  induction x using Submodule.Quotient.induction_on with
  | H z =>
    have e : ∀ j, ∃ w : Cech.cocyDeg (locSys S N M) (degLoc 𝓜 c) locResS i,
        freeIncl 𝓜 b d hb i c j (freeCoord 𝓜 b d hb i c j (Submodule.Quotient.mk z)) =
          (Submodule.Quotient.mk w : cohom 𝓜 i c) ∧
        ∀ I, w.1 I = locMap (LinearMap.toSpanSingleton (Poly S N) M (b j)) I.1.1
          (locMap (b.coord j) I.1.1 (z.1 I)) := by
      intro j
      obtain ⟨z1, h1, h1'⟩ := cohomMapShift_mk (𝓜 := 𝓜) (𝓜' := polyGraded S N) (b.coord j) (-d j)
        (fun _ _ hm => by rw [← sub_eq_add_neg]; exact coord_mem_piece 𝓜 b d hb hm j) i
        (show c - d j = c + -d j by ring) z
      obtain ⟨z2, h2, h2'⟩ := cohomMapShift_mk (𝓜 := polyGraded S N) (𝓜' := 𝓜)
        (LinearMap.toSpanSingleton (Poly S N) M (b j)) (d j)
        (fun _ _ hp => by
          rw [LinearMap.toSpanSingleton_apply, add_comm]
          exact smul_mem_of_mem_polyGraded 𝓜 hp (hb j)) i (show c = c - d j + d j by ring) z1
      refine ⟨z2, ?_, fun I => by rw [h2', h1']⟩
      change cohomMapShift _ _ _ i _ (cohomMapShift _ _ _ i _ _) = _
      rw [h1, h2]
    choose w hw hw' using e
    have hz : ∑ j, w j = z := by
      apply Subtype.ext
      funext I
      rw [Submodule.coe_sum, Finset.sum_apply]
      simp only [hw']
      exact sum_locMap_basis b I.1.1 (z.1 I)
    refine (Finset.sum_congr rfl fun j _ => hw j).trans ?_
    exact (map_sum (Submodule.mkQ _) w Finset.univ).symm.trans (congrArg _ hz)


omit [IsScalarTower S (Poly S N) M] in
theorem smul_basis_mem (c : ℤ) (j : Fin r) (p : (polyGraded S N).piece (c - d j)) :
    (p : Poly S N) • b j ∈ 𝓜.piece c := by
  have h := smul_mem_of_mem_polyGraded 𝓜 p.2 (hb j)
  rwa [show d j + (c - d j) = c by ring] at h

theorem freeInclusion_toH0 (c : ℤ) (j : Fin r) (p : (polyGraded S N).piece (c - d j)) :
    freeIncl 𝓜 b d hb 0 c j (toH0 (polyGraded S N) (c - d j) p) =
      toH0 𝓜 c ⟨(p : Poly S N) • b j, smul_basis_mem 𝓜 b d hb c j p⟩ := by
  obtain ⟨w, hw, hw'⟩ := cohomMapShift_mk (𝓜 := polyGraded S N) (𝓜' := 𝓜)
    (LinearMap.toSpanSingleton (Poly S N) M (b j)) (d j)
    (fun _ _ hp => by
      rw [LinearMap.toSpanSingleton_apply, add_comm]
      exact smul_mem_of_mem_polyGraded 𝓜 hp (hb j)) 0 (show c = c - d j + d j by ring)
    ⟨constCochain (p : Poly S N), constCochain_mem _ _ _ p.2⟩
  refine hw.trans ?_
  exact congrArg Submodule.Quotient.mk (Subtype.ext (funext fun I => (hw' I).trans (locMap_mk _ _ _ _)))

theorem freeCoordinate_toH0 (c : ℤ) (j : Fin r) (m : 𝓜.piece c) :
    freeCoord 𝓜 b d hb 0 c j (toH0 𝓜 c m) =
      toH0 (polyGraded S N) (c - d j) ⟨b.coord j m, coord_mem_piece 𝓜 b d hb m.2 j⟩ := by
  obtain ⟨w, hw, hw'⟩ := cohomMapShift_mk (𝓜 := 𝓜) (𝓜' := polyGraded S N) (b.coord j) (-d j)
    (fun _ _ hm => by rw [← sub_eq_add_neg]; exact coord_mem_piece 𝓜 b d hb hm j) 0
    (show c - d j = c + -d j by ring) ⟨constCochain (m : M), constCochain_mem _ _ _ m.2⟩
  refine hw.trans ?_
  exact congrArg Submodule.Quotient.mk (Subtype.ext (funext fun I => (hw' I).trans (locMap_mk _ _ _ _)))

end FreeGraded

theorem SerreFree.proof (hP : SerrePoly.Statement.{u}) : SerreFree.Statement.{u, v} := by
  intro S _ _ N M _ _ _ _ 𝓜 r b d hb
  obtain ⟨hfin, hpos⟩ := hP S N
  refine ⟨fun i c => ?_, fun c hc => ⟨fun i hi => ?_, ?_, ?_⟩⟩
  · have : ∀ j, Module.Finite S (cohom (polyGraded S N) i (c - d j)) := fun j => hfin i _
    let Φ : ((j : Fin r) → cohom (polyGraded S N) i (c - d j)) →ₗ[S] cohom 𝓜 i c :=
      ∑ j, (freeIncl 𝓜 b d hb i c j).comp (LinearMap.proj j)
    refine Module.Finite.of_surjective Φ fun x => ⟨fun j => freeCoord 𝓜 b d hb i c j x, ?_⟩
    simp only [Φ, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
    exact sum_freeIncl_freeCoord 𝓜 b d hb i c x
  · refine ⟨fun x y => ?_⟩
    rw [← sum_freeIncl_freeCoord 𝓜 b d hb i c x, ← sum_freeIncl_freeCoord 𝓜 b d hb i c y]
    refine Finset.sum_congr rfl fun j _ => ?_
    have : Subsingleton (cohom (polyGraded S N) i (c - d j)) :=
      (hpos (c - d j) (by linarith [hc j])).1 i hi
    rw [Subsingleton.elim (freeCoord 𝓜 b d hb i c j x) (freeCoord 𝓜 b d hb i c j y)]
  · rw [injective_iff_map_eq_zero]
    intro m hm
    apply Subtype.ext
    rw [Submodule.coe_zero, ← b.sum_repr m]
    refine Finset.sum_eq_zero fun j _ => ?_
    have h0 := freeCoordinate_toH0 𝓜 b d hb c j m
    rw [hm, map_zero] at h0
    have hinj := (hpos (c - d j) (by linarith [hc j])).2.1
    have : (⟨b.coord j m, coord_mem_piece 𝓜 b d hb m.2 j⟩ : (polyGraded S N).piece (c - d j)) = 0 :=
      hinj (h0.symm.trans (map_zero _).symm)
    rw [← Module.Basis.coord_apply, show b.coord j m = 0 from congrArg Subtype.val this, zero_smul]
  · intro y
    have hsurj := fun j => (hpos (c - d j) (by linarith [hc j])).2.2
    choose p hp using fun j => hsurj j (freeCoord 𝓜 b d hb 0 c j y)
    refine ⟨∑ j, ⟨(p j : Poly S N) • b j, smul_basis_mem 𝓜 b d hb c j (p j)⟩, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, ← sum_freeIncl_freeCoord 𝓜 b d hb 0 c y]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hp j, freeInclusion_toH0]

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSerreOnto
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w w'

section Grading

theorem isInternal_of_proj {R : Type*} {A : Type*} {ι : Type*} [Ring R] [AddCommGroup A] [Module R A]
    [DecidableEq ι]     (p : ι → Submodule R A) (π : ι → A →ₗ[R] A) (h1 : ∀ i a, a ∈ p i → π i a = a)
    (h2 : ∀ i j a, i ≠ j → a ∈ p j → π i a = 0) (h3 : ⨆ i, p i = ⊤) : DirectSum.IsInternal p := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  refine ⟨fun i => ?_, h3⟩
  rw [Submodule.disjoint_def]
  intro a ha ha'
  have hle : (⨆ (j) (_ : j ≠ i), p j) ≤ LinearMap.ker (π i) :=
    iSup_le fun j => iSup_le fun hj b hb => h2 i j b (Ne.symm hj) hb
  rw [← h1 i a ha]
  exact hle ha'

variable {S : Type u} [CommRing S] {N : ℕ}

theorem eq_zero_or_isHomogeneous_of_mem_piece {p : Poly S N} {e : ℤ}
    (hp : p ∈ (polyGraded S N).piece e) : p = 0 ∨ ∃ n : ℕ, (n : ℤ) = e ∧ p.IsHomogeneous n := by
  classical
  change p ∈ weightedHomogeneousSubmodule S _ e at hp
  rw [mem_weightedHomogeneousSubmodule] at hp
  by_cases h0 : p = 0
  · exact Or.inl h0
  right
  have key : ∀ s : Fin (N + 1) →₀ ℕ, Finsupp.weight (fun _ => (1 : ℤ)) s =
      ((Finsupp.weight (1 : Fin (N + 1) → ℕ) s : ℕ) : ℤ) := by
    intro s
    simp only [Finsupp.weight_apply, Finsupp.sum, Pi.one_apply, smul_eq_mul, mul_one]
    push_cast
    exact Finset.sum_congr rfl fun _ _ => nsmul_one _
  obtain ⟨s0, hs0⟩ := ne_zero_iff.mp h0
  refine ⟨Finsupp.weight (1 : Fin (N + 1) → ℕ) s0, by rw [← key, hp hs0], fun s hs => ?_⟩
  have := (hp hs).trans (hp hs0).symm
  rw [key, key] at this
  exact_mod_cast this

variable {M : Type v} [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
variable {M' : Type w} [AddCommGroup M'] [Module (Poly S N) M'] [Module S M']
  [IsScalarTower S (Poly S N) M']


omit [IsScalarTower S (Poly S N) M] in
theorem GradedPMod.smul_mem_int (𝓜 : GradedPMod S N M) {p : Poly S N} {e a : ℤ} {m : M}
    (hp : p ∈ (polyGraded S N).piece e) (hm : m ∈ 𝓜.piece a) : p • m ∈ 𝓜.piece (a + e) := by
  rcases eq_zero_or_isHomogeneous_of_mem_piece hp with rfl | ⟨n, rfl, hn⟩
  · rw [zero_smul]; exact zero_mem _
  · exact 𝓜.smul_mem n a p m hn hm

def GradedPMod.transport (𝓜 : GradedPMod S N M) (e : M ≃ₗ[Poly S N] M') : GradedPMod S N M' where
  piece c := (𝓜.piece c).map ((e.restrictScalars S : M ≃ₗ[S] M') : M →ₗ[S] M')
  isInternal := by
    have hi := (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mp 𝓜.isInternal
    rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
    refine ⟨hi.1.map_orderIso (Submodule.orderIsoMapComap (e.restrictScalars S)), ?_⟩
    rw [← Submodule.map_iSup, hi.2, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr (e.restrictScalars S).surjective
  smul_mem d c p m hp hm := by
    obtain ⟨m0, hm0, rfl⟩ := hm
    exact ⟨p • m0, 𝓜.smul_mem d c p m0 hp hm0, by simp⟩

def GradedPMod.toTransport (𝓜 : GradedPMod S N M) (e : M ≃ₗ[Poly S N] M') :
    GradedHom 𝓜 (𝓜.transport e) where
  toLin := e.toLinearMap
  map_piece _ m hm := ⟨m, hm, rfl⟩

def GradedPMod.ofTransport (𝓜 : GradedPMod S N M) (e : M ≃ₗ[Poly S N] M') :
    GradedHom (𝓜.transport e) 𝓜 where
  toLin := e.symm.toLinearMap
  map_piece _ m hm := by
    obtain ⟨m0, hm0, rfl⟩ := hm
    simpa using hm0

end Grading

section Free

variable {S : Type u} [CommRing S] {N : ℕ}


variable (S N) in
def freeGraded {r : ℕ} (deg : Fin r → ℤ) : GradedPMod S N (Fin r → Poly S N) where
  piece c := Submodule.pi Set.univ fun j => (polyGraded S N).piece (c - deg j)
  isInternal := by
    classical
    refine isInternal_of_proj _ (fun c => LinearMap.pi fun j =>
      (weightedHomogeneousComponent (fun _ : Fin (N + 1) => (1 : ℤ)) (c - deg j)).comp
        (LinearMap.proj j)) ?_ ?_ ?_
    · intro c f hf
      funext j
      have hj : f j ∈ (polyGraded S N).piece (c - deg j) := (Submodule.mem_pi.mp hf) j (Set.mem_univ _)
      change weightedHomogeneousComponent _ (c - deg j) (f j) = f j
      rw [weightedHomogeneousComponent_of_mem hj, if_pos rfl]
    · intro c c' f hcc' hf
      funext j
      have hj : f j ∈ (polyGraded S N).piece (c' - deg j) := (Submodule.mem_pi.mp hf) j (Set.mem_univ _)
      change weightedHomogeneousComponent _ (c - deg j) (f j) = 0
      rw [weightedHomogeneousComponent_of_mem hj, if_neg (by omega)]
    · rw [eq_top_iff]
      rintro f -
      rw [← Finset.univ_sum_single f]
      refine Submodule.sum_mem _ fun j _ => ?_
      have hall : f j ∈ ⨆ e, (polyGraded S N).piece e := by
        rw [((DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mp
          (polyGraded S N).isInternal).2]
        trivial
      have hmap : Pi.single j (f j) ∈
          (⨆ e, (polyGraded S N).piece e).map (LinearMap.single S (fun _ => Poly S N) j) :=
        ⟨f j, hall, rfl⟩
      rw [Submodule.map_iSup] at hmap
      have hsub : ∀ e, ((polyGraded S N).piece e).map (LinearMap.single S (fun _ => Poly S N) j) ≤
          Submodule.pi Set.univ fun j' => (polyGraded S N).piece (e + deg j - deg j') := by
        intro e
        rintro _ ⟨p, hp, rfl⟩
        rw [Submodule.mem_pi]
        intro j' _
        by_cases h : j' = j
        · subst h
          rw [LinearMap.single_apply, Pi.single_eq_same, add_sub_cancel_right]
          exact hp
        · rw [LinearMap.single_apply, Pi.single_eq_of_ne h]
          exact zero_mem _
      have hle : (⨆ e, ((polyGraded S N).piece e).map (LinearMap.single S (fun _ => Poly S N) j)) ≤
          ⨆ c, Submodule.pi Set.univ fun j' => (polyGraded S N).piece (c - deg j') :=
        iSup_mono' fun e => ⟨e + deg j, hsub e⟩
      exact hle hmap
  smul_mem e c p f hp hf := by
    rw [Submodule.mem_pi] at hf ⊢
    intro j _
    have := (polyGraded S N).smul_mem e (c - deg j) p (f j) hp (hf j (Set.mem_univ _))
    rw [show c + (e : ℤ) - deg j = c - deg j + e by ring]
    exact this

theorem single_one_mem_freeGraded {r : ℕ} (deg : Fin r → ℤ) (j : Fin r) :
    (Pi.single j 1 : Fin r → Poly S N) ∈ (freeGraded S N deg).piece (deg j) := by
  classical
  change _ ∈ Submodule.pi _ _
  rw [Submodule.mem_pi]
  intro j' _
  by_cases h : j' = j
  · subst h
    rw [Pi.single_eq_same, sub_self]
    change (1 : Poly S N) ∈ weightedHomogeneousSubmodule S _ _
    rw [mem_weightedHomogeneousSubmodule]
    exact isWeightedHomogeneous_one _ _
  · rw [Pi.single_eq_of_ne h]
    exact zero_mem _

variable {M : Type v} [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]


variable (S N) in
def freeMap {r : ℕ} (g : Fin r → M) : (Fin r → Poly S N) →ₗ[Poly S N] M :=
  ∑ j, (LinearMap.proj j).smulRight (g j)

omit [Module S M] [IsScalarTower S (Poly S N) M] in
theorem freeMap_apply {r : ℕ} (g : Fin r → M) (f : Fin r → Poly S N) :
    freeMap (S := S) (N := N) g f = ∑ j, f j • g j := by
  simp [freeMap]


omit [IsScalarTower S (Poly S N) M] in
theorem GradedPMod.exists_gens (𝓜 : GradedPMod S N M) (hM : Module.Finite (Poly S N) M) :
    ∃ (r : ℕ) (g : Fin r → M) (deg : Fin r → ℤ), (∀ j, g j ∈ 𝓜.piece (deg j)) ∧
      Submodule.span (Poly S N) (Set.range g) = ⊤ := by
  classical
  let _ := 𝓜.isInternal.chooseDecomposition
  obtain ⟨s, hs⟩ := hM.fg_top
  let J := Σ m : s, ((DirectSum.decompose 𝓜.piece (m : M)).support : Finset ℤ)
  let e := Fintype.equivFin J
  refine ⟨Fintype.card J, fun j => (DirectSum.decompose 𝓜.piece ((e.symm j).1 : M) (e.symm j).2 : M),
    fun j => ((e.symm j).2 : ℤ), fun j => (DirectSum.decompose 𝓜.piece _ _).2, ?_⟩
  rw [eq_top_iff, ← hs, Submodule.span_le]
  intro m hm
  rw [← DirectSum.sum_support_decompose 𝓜.piece m]
  refine Submodule.sum_mem _ fun c hc => Submodule.subset_span ⟨e ⟨⟨m, hm⟩, ⟨c, hc⟩⟩, ?_⟩
  dsimp only
  rw [Equiv.symm_apply_apply]

omit [IsScalarTower S (Poly S N) M] in
theorem freeMap_mem {r : ℕ} (𝓜 : GradedPMod S N M) {g : Fin r → M} {deg : Fin r → ℤ}
    (hg : ∀ j, g j ∈ 𝓜.piece (deg j)) (c : ℤ) {f : Fin r → Poly S N}
    (hf : f ∈ (freeGraded S N deg).piece c) : freeMap (S := S) (N := N) g f ∈ 𝓜.piece c := by
  rw [freeMap_apply]
  refine Submodule.sum_mem _ fun j _ => ?_
  have hj : f j ∈ (polyGraded S N).piece (c - deg j) := (Submodule.mem_pi.mp hf) j (Set.mem_univ _)
  have := 𝓜.smul_mem_int hj (hg j)
  rwa [add_sub_cancel] at this

omit [Module S M] [IsScalarTower S (Poly S N) M] in
theorem freeMap_surjective {r : ℕ} {g : Fin r → M} (hg : Submodule.span (Poly S N) (Set.range g) = ⊤) :
    Function.Surjective (freeMap (S := S) (N := N) g) := by
  classical
  rw [← LinearMap.range_eq_top, eq_top_iff, ← hg, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  refine ⟨Pi.single j 1, ?_⟩
  rw [freeMap_apply, Finset.sum_eq_single j (fun j' _ h => by rw [Pi.single_eq_of_ne h, zero_smul])
    (fun h => absurd (Finset.mem_univ j) h), Pi.single_eq_same, one_smul]

end Free

section Kernel

variable {S : Type u} [CommRing S] {N : ℕ}
variable {M : Type v} [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
variable {M' : Type w} [AddCommGroup M'] [Module (Poly S N) M'] [Module S M']
  [IsScalarTower S (Poly S N) M']
variable {𝓕 : GradedPMod S N M} {𝓜 : GradedPMod S N M'}


omit [IsScalarTower S (Poly S N) M] [IsScalarTower S (Poly S N) M'] in
theorem GradedHom.map_decompose (φ : GradedHom 𝓕 𝓜) [DirectSum.Decomposition 𝓕.piece]
    [DirectSum.Decomposition 𝓜.piece] (c : ℤ) (m : M) :
    φ.toLin (DirectSum.decompose 𝓕.piece m c : M) = (DirectSum.decompose 𝓜.piece (φ.toLin m) c : M') := by
  classical
  induction m using DirectSum.Decomposition.inductionOn 𝓕.piece with
  | zero => simp
  | @homogeneous i m =>
    by_cases h : i = c
    · subst h
      rw [DirectSum.decompose_of_mem_same _ m.2, DirectSum.decompose_of_mem_same _ (φ.map_piece _ _ m.2)]
    · rw [DirectSum.decompose_of_mem_ne _ m.2 h, DirectSum.decompose_of_mem_ne _ (φ.map_piece _ _ m.2) h,
        map_zero]
  | add m m' hm hm' =>
    simp only [map_add (f := _), DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add, hm, hm']

def GradedHom.kerGraded (φ : GradedHom 𝓕 𝓜) : GradedPMod S N (LinearMap.ker φ.toLin) where
  piece c := (𝓕.piece c).comap ((LinearMap.ker φ.toLin).subtype.restrictScalars S)
  isInternal := by
    classical
    let _ := 𝓕.isInternal.chooseDecomposition
    let _ := 𝓜.isInternal.chooseDecomposition
    have hker : ∀ (c : ℤ) (k : LinearMap.ker φ.toLin),
        (DirectSum.decompose 𝓕.piece (k : M) c : M) ∈ LinearMap.ker φ.toLin := by
      intro c k
      rw [LinearMap.mem_ker, φ.map_decompose, LinearMap.mem_ker.mp k.2, DirectSum.decompose_zero]
      rfl
    let π : ℤ → LinearMap.ker φ.toLin →ₗ[S] LinearMap.ker φ.toLin := fun c =>
      { toFun := fun k => ⟨_, hker c k⟩
        map_add' := fun a b => by
          apply Subtype.ext
          simp [DirectSum.decompose_add]
        map_smul' := fun s a => by
          apply Subtype.ext
          simp [DirectSum.decompose_smul, DirectSum.smul_apply] }
    refine isInternal_of_proj _ π ?_ ?_ ?_
    · intro c k hk
      exact Subtype.ext (DirectSum.decompose_of_mem_same _ hk)
    · intro c c' k hcc' hk
      exact Subtype.ext (DirectSum.decompose_of_mem_ne _ hk (Ne.symm hcc'))
    · rw [eq_top_iff]
      rintro k -
      have hk : k = ∑ c ∈ (DirectSum.decompose 𝓕.piece (k : M)).support, π c k := by
        apply Subtype.ext
        rw [Submodule.coe_sum]
        exact (DirectSum.sum_support_decompose 𝓕.piece (k : M)).symm
      rw [hk]
      exact Submodule.sum_mem _ fun c _ =>
        Submodule.mem_iSup_of_mem c (DirectSum.decompose 𝓕.piece (k : M) c).2
  smul_mem d c p k hp hk := 𝓕.smul_mem d c p k hp hk

def GradedHom.kerIncl (φ : GradedHom 𝓕 𝓜) : GradedHom φ.kerGraded 𝓕 where
  toLin := (LinearMap.ker φ.toLin).subtype
  map_piece _ _ hk := hk

end Kernel

section Cohom

variable {S : Type u} [CommRing S] {N : ℕ}
variable {M : Type v} [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
variable {M' : Type w} [AddCommGroup M'] [Module (Poly S N) M'] [Module S M']
  [IsScalarTower S (Poly S N) M']

theorem cohomMap_toH0 {𝓜 : GradedPMod S N M} {𝓜' : GradedPMod S N M'} (f : GradedHom 𝓜 𝓜') (c : ℤ)
    (m : 𝓜.piece c) : cohomMap f 0 c (toH0 𝓜 c m) = toH0 𝓜' c ⟨f.toLin m, f.map_piece c m m.2⟩ := by
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
  congr 1
  apply Subtype.ext
  funext I
  change locMap f.toLin I.1.1 (LocalizedModule.mk (m : M) 1) = LocalizedModule.mk (f.toLin m) 1
  exact locMap_mk _ _ _ _

theorem cohomMap_leftInverse {𝓜 : GradedPMod S N M} {𝓜' : GradedPMod S N M'} (f : GradedHom 𝓜 𝓜')
    (g : GradedHom 𝓜' 𝓜) (hfg : ∀ m, g.toLin (f.toLin m) = m) (i : ℕ) (c : ℤ) (y : cohom 𝓜 i c) :
    cohomMap g i c (cohomMap f i c y) = y := by
  obtain ⟨s, rfl⟩ := Submodule.mkQ_surjective _ y
  change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
  congr 1
  apply Subtype.ext
  funext I
  change locMap g.toLin I.1.1 (locMap f.toLin I.1.1 ((s : Cech.Cochain (locSys S N M) i) I)) =
    (s : Cech.Cochain (locSys S N M) i) I
  generalize ((s : Cech.Cochain (locSys S N M) i) I) = z
  induction z using LocalizedModule.induction_on with
  | h m t => rw [locMap_mk, locMap_mk, hfg]

end Cohom

section Main

theorem toH0_surjective_of_exact (hC : CechExact.Statement.{u, w}) {S : Type u} [CommRing S]
    [IsNoetherianRing S] {N : ℕ} {K F M : Type w}
    [AddCommGroup K] [Module (Poly S N) K] [Module S K] [IsScalarTower S (Poly S N) K]
    [AddCommGroup F] [Module (Poly S N) F] [Module S F] [IsScalarTower S (Poly S N) F]
    [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
    {𝓚 : GradedPMod S N K} {𝓕 : GradedPMod S N F} {𝓜 : GradedPMod S N M}
    (ι : GradedHom 𝓚 𝓕) (φ : GradedHom 𝓕 𝓜) (hι : Function.Injective ι.toLin)
    (hφ : Function.Surjective φ.toLin) (hex : Function.Exact ι.toLin φ.toLin) (c : ℤ)
    (hF : Function.Surjective (toH0 𝓕 c)) (hK : Subsingleton (cohom 𝓚 1 c)) :
    Function.Surjective (toH0 𝓜 c) := by
  obtain ⟨-, h⟩ := hC S N K F M 𝓚 𝓕 𝓜 ι φ hι hφ hex c
  obtain ⟨-, δ, hδ, -⟩ := h 0
  intro y
  obtain ⟨z, hz⟩ := (hδ y).mp (Subsingleton.elim _ _)
  obtain ⟨f, rfl⟩ := hF z
  exact ⟨⟨φ.toLin f, φ.map_piece c f f.2⟩, by rw [← cohomMap_toH0, hz]⟩

theorem SerreOnto.proof (hC : CechExact.Statement.{u, max u v})
    (hF : SerreFree.Statement.{u, max u v}) (hV : SerreVanish.Statement.{u, max u v}) :
    SerreOnto.Statement.{u, v} := by
  intro S _ _ N M _ _ _ _ 𝓜 hM
  obtain ⟨r, g, deg, hg, hspan⟩ := 𝓜.exists_gens hM

  let eM : M ≃ₗ[Poly S N] ULift.{u} M := ULift.moduleEquiv.symm
  let eF : (Fin r → Poly S N) ≃ₗ[Poly S N] ULift.{v} (Fin r → Poly S N) := ULift.moduleEquiv.symm
  let 𝓜L := 𝓜.transport eM
  let 𝓕 := (freeGraded S N deg).transport eF
  let φ : GradedHom 𝓕 𝓜L :=
    { toLin := eM.toLinearMap ∘ₗ freeMap (S := S) (N := N) g ∘ₗ eF.symm.toLinearMap
      map_piece := by
        rintro c _ ⟨f, hf, rfl⟩
        exact ⟨freeMap (S := S) (N := N) g f, freeMap_mem 𝓜 hg c hf, by simp [eF]⟩ }
  have hφ : Function.Surjective φ.toLin := by
    change Function.Surjective (⇑eM.toLinearMap ∘ ⇑(freeMap (S := S) (N := N) g) ∘ ⇑eF.symm.toLinearMap)
    exact eM.surjective.comp ((freeMap_surjective hspan).comp eF.symm.surjective)

  have hKfin : Module.Finite (Poly S N) (LinearMap.ker φ.toLin) := by
    have : Module.Finite (Poly S N) (ULift.{v} (Fin r → Poly S N)) := Module.Finite.equiv eF
    have : IsNoetherian (Poly S N) (ULift.{v} (Fin r → Poly S N)) :=
      isNoetherian_of_isNoetherianRing_of_finite _ _
    infer_instance
  obtain ⟨c₁, hc₁⟩ := hV S N _ φ.kerGraded hKfin

  let b : Module.Basis (Fin r) (Poly S N) (ULift.{v} (Fin r → Poly S N)) :=
    (Pi.basisFun (Poly S N) (Fin r)).map eF
  have hb : ∀ j, b j ∈ 𝓕.piece (deg j) := fun j =>
    ⟨Pi.single j 1, single_one_mem_freeGraded deg j, by simp [b, eF]⟩
  have hFc := (hF S N _ 𝓕 r b deg hb).2
  refine ⟨max c₁ (∑ j, |deg j|), fun c hc => ?_⟩
  have hcd : ∀ j, deg j ≤ c := fun j => (le_abs_self _).trans
    ((Finset.single_le_sum (fun j _ => abs_nonneg (deg j)) (Finset.mem_univ j)).trans
      ((le_max_right _ _).trans hc))
  have hsurjL : Function.Surjective (toH0 𝓜L c) :=
    toH0_surjective_of_exact hC φ.kerIncl φ (LinearMap.ker φ.toLin).injective_subtype hφ
      (LinearMap.exact_subtype_ker_map _) c (hFc c hcd).2.surjective
      (hc₁ 1 le_rfl c ((le_max_left _ _).trans hc))

  intro y
  obtain ⟨z, hz⟩ := hsurjL (cohomMap (𝓜.toTransport eM) 0 c y)
  refine ⟨⟨(𝓜.ofTransport eM).toLin z, (𝓜.ofTransport eM).map_piece c z z.2⟩, ?_⟩
  rw [← cohomMap_toH0 (𝓜.ofTransport eM), hz, cohomMap_leftInverse]
  intro m
  simp [GradedPMod.toTransport, GradedPMod.ofTransport]

end Main

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCechFlat
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open TensorProduct MvPolynomial

noncomputable section

universe u v

namespace FlatBC

variable {S S' : Type*} [CommRing S] [CommRing S'] [Algebra S S']

variable {X Y X' Y' : Type*} [AddCommGroup X] [Module S X] [AddCommGroup Y] [Module S Y]
  [AddCommGroup X'] [Module S' X'] [AddCommGroup Y'] [Module S' Y']

variable [Module.Flat S S']

end FlatBC

namespace FlatBC

section Hom

variable {R : Type*} [CommRing R] {X Y Z : Type*} [AddCommGroup X] [Module R X] [AddCommGroup Y]
  [Module R Y] [AddCommGroup Z] [Module R Z]

end Hom

end FlatBC

namespace FlatBC

variable {S S' : Type*} [CommRing S] [CommRing S'] [Algebra S S'] [Module.Flat S S']
variable {X Y Z X' Y' Z' : Type*} [AddCommGroup X] [Module S X] [AddCommGroup Y] [Module S Y]
  [AddCommGroup Z] [Module S Z] [AddCommGroup X'] [Module S' X'] [AddCommGroup Y'] [Module S' Y']
  [AddCommGroup Z'] [Module S' Z']

end FlatBC

namespace FlatBC

section CechDeg

open Cech

variable {n : ℕ} {U : Finset (Fin n)} {R : Type*} [CommRing R] {G : Cell U → Type*}
  [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)] {deg : ∀ I, Submodule R (G I)}
  {ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J}

end CechDeg

section Poly

variable (S : Type u) [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S'] (N : ℕ)

variable {S S' N}

end Poly

end FlatBC

namespace FlatBC

section Loc

variable {S : Type u} [CommRing S] {N : ℕ}

variable {M : Type v} [AddCommGroup M] [Module (Poly S N) M] [Module S M]
  [IsScalarTower S (Poly S N) M]

variable {S' : Type u} [CommRing S'] [Algebra S S']
  {M' : Type v} [AddCommGroup M'] [Module (Poly S' N) M'] [Module S' M']
  [IsScalarTower S' (Poly S' N) M'] [Module S M'] [IsScalarTower S S' M']
  (f : M →ₗ[S] M')
  (hX : ∀ (i : Fin (N + 1)) (m : M), f ((X i : Poly S N) • m) = (X i : Poly S' N) • f m)



end Loc

end FlatBC

namespace FlatBC

section Grade

variable {S : Type u} [CommRing S] {N : ℕ}
  {M : Type v} [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
  {S' : Type u} [CommRing S'] [Algebra S S']
  {M' : Type v} [AddCommGroup M'] [Module (Poly S' N) M'] [Module S' M']
  [IsScalarTower S' (Poly S' N) M'] [Module S M'] [IsScalarTower S S' M']
  (f : M →ₗ[S] M')
  (hX : ∀ (i : Fin (N + 1)) (m : M), f ((X i : Poly S N) • m) = (X i : Poly S' N) • f m)
  (hf : IsBaseChange S' f) (𝓜 : GradedPMod S N M) (𝓜' : GradedPMod S' N M')
  (hdeg : ∀ (c : ℤ) (m : M), m ∈ 𝓜.piece c → f m ∈ 𝓜'.piece c)




end Grade

end FlatBC

namespace FlatBC

section Final

variable {S : Type u} [CommRing S] {N : ℕ}
  {M : Type v} [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]
  {S' : Type u} [CommRing S'] [Algebra S S'] [Module.Flat S S']
  {M' : Type v} [AddCommGroup M'] [Module (Poly S' N) M'] [Module S' M']
  [IsScalarTower S' (Poly S' N) M'] [Module S M'] [IsScalarTower S S' M']
  (f : M →ₗ[S] M')
  (hX : ∀ (i : Fin (N + 1)) (m : M), f ((X i : Poly S N) • m) = (X i : Poly S' N) • f m)
  (hf : IsBaseChange S' f) (𝓜 : GradedPMod S N M) (𝓜' : GradedPMod S' N M')
  (hdeg : ∀ (c : ℤ) (m : M), m ∈ 𝓜.piece c → f m ∈ 𝓜'.piece c) (c : ℤ)

end Final

end FlatBC

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCechTop
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

theorem CechTop.idx_isEmpty (N i : ℕ) (hi : N < i) :
    IsEmpty (Cech.Idx (Finset.univ : Finset (Fin (N + 1))) i) := by
  refine ⟨fun I => ?_⟩
  have h1 : I.1.1.card ≤ N + 1 := by
    simpa using Finset.card_le_univ I.1.1
  have h2 := I.2
  omega

theorem CechTop.proof : CechTop.Statement := by
  intro S _ _ N M _ _ _ _ 𝓜 i c hi
  have := CechTop.idx_isEmpty N i hi
  have hC : Subsingleton (Cech.Cochain (locSys S N M) i) := inferInstance
  constructor
  intro a b
  change (a : Cech.Hdeg _ _ _ i) = b
  induction a using Submodule.Quotient.induction_on with
  | H x =>
    induction b using Submodule.Quotient.induction_on with
    | H y =>
      congr 1
      exact Subtype.ext (hC.elim _ _)

end GroundTheory.Heights₂.Heights.Kleiman
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

universe u v w

theorem CechDSq.full : CechDSq.Statement.{u, v} := CechDSq.proof
theorem DegLocExact.full : DegLocExact.Statement.{u, v} := DegLocExact.proof
theorem CechExact.full : CechExact.Statement.{u, v} := CechExact.proof CechDSq.full DegLocExact.full
theorem CechTop.full : CechTop.Statement.{u, v} := CechTop.proof
theorem Cech.Cone.full : Cech.Cone.Statement.{u, v} := Cech.Cone.proof
theorem Cech.Transport.full : Cech.Transport.Statement.{u, v, w} := Cech.Transport.proof
theorem SerrePoly.Laurent.full : SerrePoly.Laurent.Statement.{u} := SerrePoly.Laurent.proof
theorem SerrePoly.LaurentCohom.full : SerrePoly.LaurentCohom.Statement.{u} :=
  SerrePoly.LaurentCohom.proof Cech.Cone.full
theorem SerrePoly.full : SerrePoly.Statement.{u} :=
  SerrePoly.proof SerrePoly.Laurent.full Cech.Transport.full SerrePoly.LaurentCohom.full
theorem SerreFree.full : SerreFree.Statement.{u, v} := SerreFree.proof SerrePoly.full
theorem GradedPres.full : GradedPres.Statement.{u, v} := GradedPres.proof
theorem GradedULift.full : GradedULift.Statement.{u, v} := GradedULift.proof
theorem CohomRetract.full : CohomRetract.Statement.{u, v, w} := CohomRetract.proof

theorem SerreFinite.full : SerreFinite.Statement.{u, v} :=
  SerreFinite.proof CechExact.full CechTop.full SerreFree.full GradedPres.full GradedULift.full
    CohomRetract.full

theorem SerreVanish.full : SerreVanish.Statement.{u, v} :=
  SerreVanish.proof CechExact.full CechTop.full SerreFree.full GradedPres.full GradedULift.full
    CohomRetract.full

theorem SerreOnto.full : SerreOnto.Statement.{u, v} :=
  SerreOnto.proof CechExact.full SerreFree.full SerreVanish.full

theorem SerreTail.full : SerreTail.Statement.{u, v} := SerreTail.proof SerreFinite.full SerreOnto.full

theorem Extension.full : Extension.Statement.{u, v, w} := Extension.proof
theorem Generated.full : Generated.Statement.{u, w} := Generated.proof Extension.full
theorem TwistFinite.full : TwistFinite.Statement.{u, w} := TwistFinite.proof Extension.full SerreFinite.full
theorem TwistSections.full : TwistSections.Statement.{u, w} := TwistSections.proof SerreOnto.full
theorem ProjDegreePositive.full : ProjDegreePositive.Statement.{u} := ProjDegreePositive.proof
theorem HilbertPositive.full : HilbertPositive.Statement.{u, w} :=
  HilbertPositive.proof ProjDegreePositive.full TwistSections.full
theorem PrimeFiltration.Point.full : PrimeFiltration.Point.Statement.{u, w} := PrimeFiltration.Point.proof
theorem PrimeFiltration.Restrict.full : PrimeFiltration.Restrict.Statement.{u, w} :=
  PrimeFiltration.Restrict.proof

theorem StepThree.Away.full : StepThree.Away.Statement.{u, w} := StepThree.Away.proof
theorem RestrictTwist.full : RestrictTwist.Statement.{u, w} := RestrictTwist.proof
theorem StepData.JProper.full : StepData.JProper.Statement.{u, w} := StepData.JProper.proof
theorem SubvarDrop.full : SubvarDrop.Statement.{u, w} := SubvarDrop.proof

theorem TwistVanish.assembled (hS : TwistSplit.Statement.{u, w}) : TwistVanish.Statement.{u, w} :=
  TwistVanish.proof Extension.full SerreVanish.full hS

theorem NefRestrict.assembled (hRL : RestrLenRestrict.Statement.{u, w}) : NefRestrict.Statement.{u, w} :=
  NefRestrict.proof RestrictTwist.full hRL

theorem SectionCount.Drop.assembled (hF : SectionCount.Drop.Filt.Statement.{u, w})
    (hT : SectionCount.Drop.Term.Statement.{u, w}) (hH : SectionCount.Drop.HilbW.Statement.{u, w})
    (hR : GenericPointSectionInput.Statement.{u, w}) : SectionCount.Drop.Statement.{u, w} :=
  SectionCount.Drop.proof hF hT hH hR

theorem SectionCount.assembled (hTop : SectionCount.Top.Statement.{u, w})
    (hF : SectionCount.Drop.Filt.Statement.{u, w}) (hT : SectionCount.Drop.Term.Statement.{u, w})
    (hH : SectionCount.Drop.HilbW.Statement.{u, w}) (hR : GenericPointSectionInput.Statement.{u, w}) :
    SectionCount.Statement.{u, w} :=
  SectionCount.proof hTop (SectionCount.Drop.assembled hF hT hH hR)

theorem StepThree.assembled (hL : StepThree.OnW.Lift.Statement.{u, w})
    (hG : StepThree.OnW.Gen.Statement.{u, w}) : StepThree.Statement.{u, w} :=
  StepThree.proof StepThree.Away.full (StepThree.OnW.proof hL hG)

end GroundTheory.Heights₂.Heights.Kleiman
