module

public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.FamilyGroupSumFactorsWeightAmplitude
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRationalFramesPrescribedLocalClasses
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeightedCountGluedLatticesEqMassMulLocal
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlueUnimodularLatticeRepsMoveIsometryFrames
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMaximalIntegralHermitianLatticeOrthonormal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalPairingClassStableUnitriangularChange
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalPairingClassStableUnitriangularChange
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt Formalism.L2.SG.NGData Formalism.L2.SG.NGLocModel Formalism.L2.SG.FamDefs GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.ClsStable

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E]
  [TopologicalSpace E] [MeasurableSpace E]

theorem h_smul_right {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V)
    (c : E) (x y : V) : H.h x (c • y) = M.L.cj c * H.h x y := by
  rw [H.h_herm (c • y) x, H.h_smul_left, map_mul, ← H.h_herm]

theorem h_sum_left {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V)
    {ι : Type} (s : Finset ι) (v : ι → V) (y : V) : H.h (∑ i ∈ s, v i) y = ∑ i ∈ s, H.h (v i) y := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have := H.h_smul_left 0 0 y
    simpa using this
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, H.h_add_left, ih]

theorem h_sum_right {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V)
    {ι : Type} (s : Finset ι) (v : ι → V) (x : V) : H.h x (∑ i ∈ s, v i) = ∑ i ∈ s, H.h x (v i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [H.h_herm, h_sum_left, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← H.h_herm]

theorem zhat_chg {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (r : ℕ)
    (f f' g g' : Fin (r + 1) → V) (A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hg : GlobalTheory.LocOver.Chg f A g) (hg' : GlobalTheory.LocOver.Chg f' A' g') :
    H.Zhat g g' = A.transpose.map M.L.cj * H.Zhat f f' * A' := by
  ext a b
  simp only [Loc.HermSp.Zhat, Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply]
  rw [hg a, hg' b, h_sum_left]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [H.h_smul_left, h_sum_right, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [h_smul_right]
  ring

theorem intUni_mul {M : Loc.Model F E} {r : ℕ} {B A : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
    (hB : IntUni M B) (hA : IntUni M A) : IntUni M (B * A) := by
  refine ⟨fun a b hab => ?_, fun a => ?_, fun a b => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rcases lt_or_ge c a with h | h
    · rw [hB.1 a c h, zero_mul]
    · rw [hA.1 c b (lt_of_lt_of_le hab h), mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [hB.2.1, hA.2.1, one_mul]
    · intro c _ hc
      rcases lt_or_gt_of_ne hc with h | h
      · rw [hB.1 a c h, zero_mul]
      · rw [hA.1 c a h, mul_zero]
    · intro h; exact absurd (Finset.mem_univ a) h
  · rw [Matrix.mul_apply]
    exact Subring.sum_mem _ fun c _ => Subring.mul_mem _ (hB.2.2 a c) (hA.2.2 c b)

theorem span_mul_mem {M : Loc.Model F E} {t x o : E} (hx : x ∈ Submodule.span M.L.O {t}) (ho : o ∈ M.L.O) :
    x * o ∈ Submodule.span M.L.O {t} ∧ o * x ∈ Submodule.span M.L.O {t} := by
  have h1 : (⟨o, ho⟩ : M.L.O) • x ∈ Submodule.span M.L.O {t} := Submodule.smul_mem _ _ hx
  have h2 : (⟨o, ho⟩ : M.L.O) • x = o * x := rfl
  rw [h2] at h1
  exact ⟨by rw [mul_comm]; exact h1, h1⟩

theorem zhat_mem_clsLoc_of_chg : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Loc.Model F E) {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (r : ℕ) (Y0 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (f f' g g' : Fin (r + 1) → V) (A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E), Uni A → Uni A' → (∀ a b, A a b ∈ M.L.O ∧ A' a b ∈ M.L.O ∧ A a b - A' a b ∈ Submodule.span M.L.O {algebraMap F E (LocNG.theta M)}) → Chg f A g → Chg f' A' g' → H.Zhat f f' ∈ clsLoc M Y0 → H.Zhat g g' ∈ clsLoc M Y0 := by
  intro F _ _ _ E _ _ _ _ M V _ _ H r Y0 f f' g g' A A' hA hA' hint hg hg' hY
  obtain ⟨B, B', hB, hB', hBB, hZ⟩ := hY
  have hIA : IntUni M A := ⟨hA.1, hA.2, fun a b => (hint a b).1⟩
  have hIA' : IntUni M A' := ⟨hA'.1, hA'.2, fun a b => (hint a b).2.1⟩
  refine ⟨B * A, B' * A', intUni_mul hB hIA, intUni_mul hB' hIA', fun a b => ?_, ?_⟩
  · have e : (B * A) a b - (B' * A') a b =
        ∑ c, (B a c - B' a c) * A c b + ∑ c, B' a c * (A c b - A' c b) := by
      simp only [Matrix.mul_apply, ← Finset.sum_add_distrib]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      ring
    rw [e]
    refine Submodule.add_mem _ (Submodule.sum_mem _ fun c _ => ?_) (Submodule.sum_mem _ fun c _ => ?_)
    · exact (span_mul_mem (hBB a c) (hIA.2.2 c b)).1
    · exact (span_mul_mem (hint c b).2.2 (hB'.2.2 a c)).2
  · rw [zhat_chg H r f f' g g' A A' hg hg', hZ, Matrix.transpose_mul, Matrix.map_mul]
    simp only [Matrix.mul_assoc]

end GlobalTheory.ClsStable
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalPairingClassStableUnitriangularChangeStatement
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt Formalism.L2.SG.NGData Formalism.L2.SG.NGLocModel Formalism.L2.SG.FamDefs GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localPairingClass_stable_unitriangularChange : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Loc.Model F E) {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (r : ℕ) (Y0 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (f f' g g' : Fin (r + 1) → V) (A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E), Uni A → Uni A' → (∀ a b, A a b ∈ M.L.O ∧ A' a b ∈ M.L.O ∧ A a b - A' a b ∈ Submodule.span M.L.O {algebraMap F E (LocNG.theta M)}) → Chg f A g → Chg f' A' g' → H.Zhat f f' ∈ clsLoc M Y0 → H.Zhat g g' ∈ clsLoc M Y0 := by
  first | exact @GlobalTheory.ClsStable.zhat_mem_clsLoc_of_chg | exact GlobalTheory.ClsStable.zhat_mem_clsLoc_of_chg | (intros; apply GlobalTheory.ClsStable.zhat_mem_clsLoc_of_chg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagPairValueInvariantUnitriangularChange
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagPairValueInvariantUnitriangularChange
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt Formalism.L2.SG.NGData Formalism.L2.SG.NGLocModel Formalism.L2.SG.FamDefs GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.UniChange

theorem sum_castLE {R : Type} [AddCommMonoid R] {l N : ℕ} (h : l ≤ N) (f : Fin N → R)
    (hf : ∀ c : Fin N, l ≤ c.val → f c = 0) :
    ∑ c, f c = ∑ i : Fin l, f (Fin.castLE h i) := by
  symm
  refine Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ _ ?_ (fun _ => rfl)
  intro c hc
  apply hf
  by_contra hlt
  exact hc ⟨⟨c.val, by omega⟩, rfl⟩

theorem leadMinorE_mul_uni {K : Type} [Field K] {N : ℕ} (L Z A : Matrix (Fin N) (Fin N) K)
    (hL0 : ∀ a b : Fin N, a < b → L a b = 0) (hL1 : ∀ a : Fin N, L a a = 1)
    (hA0 : ∀ a b : Fin N, b < a → A a b = 0) (hA1 : ∀ a : Fin N, A a a = 1) (l : ℕ) :
    leadMinorE (L * Z * A) l = leadMinorE Z l := by
  unfold leadMinorE
  split_ifs with h
  · set e := Fin.castLE h with he
    have hsub : (L * Z * A).submatrix e e =
        L.submatrix e e * Z.submatrix e e * A.submatrix e e := by
      ext i j
      simp only [Matrix.submatrix_apply, Matrix.mul_apply]
      rw [sum_castLE h]
      · refine Finset.sum_congr rfl (fun d _ => ?_)
        congr 1
        rw [sum_castLE h]
        intro c hc
        rw [hL0 _ _ (by rw [Fin.lt_def]; simp [he]; omega), zero_mul]
      · intro d hd
        rw [hA0 _ _ (by rw [Fin.lt_def]; simp [he]; omega), mul_zero]
    have hLd : (L.submatrix e e).det = 1 := by
      rw [Matrix.det_of_lowerTriangular]
      · exact Finset.prod_eq_one (fun i _ => by simp only [Matrix.submatrix_apply]; exact hL1 _)
      · intro i j hij
        simp only [Matrix.submatrix_apply]
        apply hL0
        rw [Fin.lt_def]
        exact (show (i:ℕ) < j from OrderDual.toDual_lt_toDual.mp hij)
    have hAd : (A.submatrix e e).det = 1 := by
      rw [Matrix.det_of_upperTriangular]
      · exact Finset.prod_eq_one (fun i _ => by simp only [Matrix.submatrix_apply]; exact hA1 _)
      · intro i j hij
        simp only [Matrix.submatrix_apply]
        apply hA0
        rw [Fin.lt_def]
        exact (show (j:ℕ) < i from hij)
    rw [hsub, Matrix.det_mul, Matrix.det_mul, hLd, hAd, one_mul, mul_one]
  · rfl

end GlobalTheory.UniChange

open GlobalTheory.UniChange in
theorem GlobalTheory.LocOver.gval_uni_change : ∀ (D : D7) {T T' : D.host.E} (F G : LFlag (D.sp.Y 0) D.R.rS T) (F' G' : LFlag (D.sp.Y 0) D.R.rS T') (A A' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E), Uni A → Uni A' → ZhatL G G' = A.transpose.map star * ZhatL F F' * A' → Gval G G' = Gval F F' := by
  intro D T T' F G F' G' A A' hA hA' hZ
  have key : ∀ l, leadMinorE (ZhatL G G') l = leadMinorE (ZhatL F F') l := by
    intro l
    rw [hZ]
    refine leadMinorE_mul_uni _ _ _ ?_ ?_ hA'.1 hA'.2 l
    · intro a b hab
      simp [Matrix.map_apply, Matrix.transpose_apply, hA.1 b a hab]
    · intro a
      simp [Matrix.map_apply, Matrix.transpose_apply, hA.2 a]
  have k1 := key (D.R.rS + 1)
  have k2 := key D.R.rS
  simp only [Gval, Gflag, Dl]
  simp only [ZhatL] at k1 k2
  rw [k1, k2]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagPairValueInvariantUnitriangularChangeStatement
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt Formalism.L2.SG.NGData Formalism.L2.SG.NGLocModel Formalism.L2.SG.FamDefs GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagPairValue_invariant_unitriangularChange : ∀ (D : D7) {T T' : D.host.E} (F G : LFlag (D.sp.Y 0) D.R.rS T) (F' G' : LFlag (D.sp.Y 0) D.R.rS T') (A A' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E), Uni A → Uni A' → ZhatL G G' = A.transpose.map star * ZhatL F F' * A' → Gval G G' = Gval F F' := by
  first | exact @GlobalTheory.LocOver.gval_uni_change | exact GlobalTheory.LocOver.gval_uni_change | (intros; apply GlobalTheory.LocOver.gval_uni_change <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassClassEqWeightCount
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassClassEqWeightCount
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.LocGenMass

open GlobalTheory.HL.PairingClass

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {V : Type} [AddCommGroup V] [Module E V]

theorem frames_in_class (M : Model F E) (hM : M.OK) (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r)
    (hrk : Module.finrank E V = k + 2 * r + 1) (hP : P.RelG (LocNG.theta M))
    (d₁ : LocNG.Datum P) (t₁ : Term V M r) (ht₁ : LocNG.IsTermOver P d₁ t₁)
    (f f' : Fin (r + 1) → V) (hf : ∃ n ∈ P.A.N, f = fun b => n (P.A.f b))
    (hf' : ∃ n' ∈ P.B.N, f' = fun b => n' (P.B.f b))
    (Y0 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (c1 : Set (Matrix (Fin (r + 1)) (Fin (r + 1)) E))
    (hc1 : c1 = {Y | ∃ A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ((∀ a b, b < a → A a b = 0) ∧ (∀ a, A a a = 1) ∧ ∀ a b, A a b ∈ M.L.O) ∧ ((∀ a b, b < a → A' a b = 0) ∧ (∀ a, A' a a = 1) ∧ ∀ a b, A' a b ∈ M.L.O) ∧ (∀ a b, A a b - A' a b ∈ Submodule.span M.L.O {algebraMap F E (LocNG.theta M)}) ∧ Y = (A.transpose.map M.L.cj) * Y0 * A'}) (hZ1 : H.Zhat t₁.f t₁.f' ∈ c1) (hZ : H.Zhat f f' ∈ c1) :
    ∃ s ∈ P.St, ∃ A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E,
      Tied M.L.O (algebraMap F E (LocNG.theta M)) A A' ∧
      f = act (fun i => s (t₁.f i)) A ∧ f' = act (fun i => s (t₁.f' i)) A' := by
  have := hM.loc
  have := hM.char0
  obtain ⟨S, ⟨c⟩⟩ := CoordExist.exists_coord M hM H r k P hrk hP
  obtain ⟨-, hN, hN', hSt, -⟩ := CoordUnip.transport M hM H r k P S c
  obtain ⟨on, on', -⟩ := FrameOnto.unipotent_onto M.L r k S
  obtain ⟨-, stab⟩ := FrameStab.stab_eq M.L r k S
  have hmem : ∀ Y, Y ∈ c1 ↔ ∃ A A', Tied M.L.O (algebraMap F E (LocNG.theta M)) A A' ∧
      Y = cT M.L A * Y0 * A' := by
    intro Y
    rw [hc1]
    constructor
    · rintro ⟨A, A', h1, h2, h3, h4⟩
      exact ⟨A, A', (tied_iff_span _ _ _ _).1 ⟨h1, h2, h3⟩, h4⟩
    · rintro ⟨A, A', h, h4⟩
      obtain ⟨h1, h2, h3⟩ := (tied_iff_span _ _ _ _).2 h
      exact ⟨A, A', h1, h2, h3, h4⟩
  have hfr : ∀ g g' : Fin (r + 1) → V, (∃ n ∈ P.A.N, g = fun b => n (P.A.f b)) →
      (∃ n' ∈ P.B.N, g' = fun b => n' (P.B.f b)) →
      ∃ u u' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, UT u ∧ UT u' ∧ g = act P.A.f u ∧ g' = act P.B.f u' := by
    rintro g g' ⟨n, hn, e⟩ ⟨n', hn', e'⟩
    obtain ⟨u, hu, h⟩ := on _ ((hN n).1 hn)
    obtain ⟨u', hu', h'⟩ := on' _ ((hN' n').1 hn')
    exact ⟨u, u', hu, hu', e.trans (pull c n _ _ c.f_eq u h), e'.trans (pull c n' _ _ c.f'_eq u' h')⟩
  have hZ0 : S.Zh = H.Zhat P.A.f P.B.f := by
    ext a b
    simp only [Frames.Zh, HermSp.Zhat, Matrix.of_apply, c.f_eq, c.f'_eq, c.h_eq]
  obtain ⟨a₁, a₁', ha₁, e₁⟩ := (hmem _).1 hZ1
  obtain ⟨a, a', ha, e⟩ := (hmem _).1 hZ
  obtain ⟨b₁, b₁', hb₁, p1, -, p1', -⟩ := ha₁.inv
  have hA := hb₁.mul ha
  have eZ : H.Zhat f f' = cT M.L (b₁ * a) * H.Zhat t₁.f t₁.f' * (b₁' * a') := by
    have : cT M.L (b₁ * a) * H.Zhat t₁.f t₁.f' * (b₁' * a') =
        cT M.L (a₁ * b₁ * a) * Y0 * (a₁' * b₁' * a') := by
      simp only [e₁, cT_mul, mul_assoc]
    rw [this, p1, p1', one_mul, one_mul, e]
  generalize b₁ * a = A at hA eZ
  generalize b₁' * a' = A' at hA eZ
  obtain ⟨B, B', hB, q1, q2, q1', q2'⟩ := hA.inv
  obtain ⟨-, -, ⟨n₁, hn₁, e₁f, -⟩, ⟨n₁', hn₁', e₁f', -⟩, -⟩ := ht₁
  obtain ⟨u₁, u₁', hu₁, hu₁', f₁, f₁'⟩ := hfr _ _ ⟨n₁, hn₁, e₁f⟩ ⟨n₁', hn₁', e₁f'⟩
  obtain ⟨u, u', hu, hu', f₀, f₀'⟩ := hfr _ _ hf hf'
  obtain ⟨v, hv, w1, w2, -⟩ := hu₁.inv
  obtain ⟨v', hv', w1', w2', -⟩ := hu₁'.inv
  rw [f₀, f₀', f₁, f₁', Zhat_act, Zhat_act, ← hZ0] at eZ
  have key : cT M.L (u * B * v) * S.Zh * (u' * B' * v') = S.Zh := by
    have h1 : cT M.L (u * B * v) * S.Zh * (u' * B' * v') =
        cT M.L (B * v) * (cT M.L u * S.Zh * u') * (B' * v') := by
      simp only [cT_mul, mul_assoc]
    have h2 : cT M.L (B * v) * (cT M.L A * (cT M.L u₁ * S.Zh * u₁') * A') * (B' * v') =
        cT M.L (u₁ * (A * B) * v) * S.Zh * (u₁' * (A' * B') * v') := by
      simp only [cT_mul, mul_assoc]
    rw [h1, eZ, h2, q1, q1', mul_one, mul_one, w1, w1', cT_one, one_mul, mul_one]
  obtain ⟨h, hh, g1, g2⟩ := (stab _ _ ((hu.mul hB.1).mul hv) ((hu'.mul hB.2.1).mul hv')).1 key
  obtain ⟨s, rfl⟩ := c.grp.surjective h
  have k1 := pull c s _ _ c.f_eq _ g1
  have k2 := pull c s _ _ c.f'_eq _ g2
  refine ⟨s, (hSt s).2 hh, A, A', hA, ?_, ?_⟩
  · rw [f₀, f₁, map_act, k1, act_act, act_act]
    congr 1
    have : u * B * v * (u₁ * A) = u * (B * (v * u₁) * A) := by simp only [mul_assoc]
    rw [this, w2, mul_one, q2, mul_one]
  · rw [f₀', f₁', map_act, k2, act_act, act_act]
    congr 1
    have : u' * B' * v' * (u₁' * A') = u' * (B' * (v' * u₁') * A') := by simp only [mul_assoc]
    rw [this, w2', mul_one, q2', mul_one]

end GlobalTheory.HL.LocGenMass

namespace GlobalTheory.HL.LocGenMass

open GlobalTheory.HL.PairingClass

theorem act_one' {E : Type} [CommRing E] {V : Type} [AddCommGroup V] [Module E V] {n : ℕ}
    (g : Fin n → V) : act g (1 : Matrix (Fin n) (Fin n) E) = g := by
  funext j
  simp [act, Matrix.one_apply]

theorem span_act_eq {E : Type} [CommRing E] {V : Type} [AddCommGroup V] [Module E V] {n : ℕ}
    (O : Subring E) (g₀ : Fin n → V) (C : Matrix (Fin n) (Fin n) E) (hU : UT C) (hC : IntM O C) :
    Submodule.span O (Set.range (act g₀ C)) = Submodule.span O (Set.range g₀) := by
  have key : ∀ (g : Fin n → V) (D : Matrix (Fin n) (Fin n) E), IntM O D →
      Submodule.span O (Set.range (act g D)) ≤ Submodule.span O (Set.range g) := by
    intro g D hD
    refine Submodule.span_le.2 ?_
    rintro _ ⟨j, rfl⟩
    refine Submodule.sum_mem _ fun i _ => ?_
    exact Submodule.smul_mem _ (⟨D i j, hD i j⟩ : O) (Submodule.subset_span ⟨i, rfl⟩)
  refine le_antisymm (key _ _ hC) ?_
  obtain ⟨B, -, hCB, -, hint⟩ := hU.inv
  have e : act (act g₀ C) B = g₀ := by rw [act_act, hCB, act_one']
  have := key (act g₀ C) B (hint O hC)
  rwa [e] at this

theorem relift {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) (r k : ℕ)
    (S : Frames L r k) (δ : S.Datum) (Λ : Submodule L.O S.V) (m₀ m₀' m m' : S.GLV)
    (hW : S.IsTermW δ Λ m₀ m₀') (hm : m ∈ S.N) (hm' : m' ∈ S.N')
    (hc : ((fun b => m (S.f b)), (fun b => m' (S.f' b))) ∈
      S.frameCls (fun b => m₀ (S.f b)) (fun b => m₀' (S.f' b))) :
    ∃ m₂ ∈ S.N, ∃ m₂' ∈ S.N', (∀ b, m₂ (S.f b) = m (S.f b)) ∧ (∀ b, m₂' (S.f' b) = m' (S.f' b)) ∧
      S.IsTermW δ Λ m₂ m₂' := by
  obtain ⟨hA, hA', hn₀, hn₀', e, e', hth, hgr⟩ := hW
  obtain ⟨C, C', a3, a4, a12, adiag, aθ, p1, p2⟩ := hc
  have p1 : ∀ j, m (S.f j) = ∑ i, C i j • m₀ (S.f i) := p1
  have p2 : ∀ j, m' (S.f' j) = ∑ i, C' i j • m₀' (S.f' i) := p2
  have pf : (fun b => m (S.f b)) = act (fun b => m₀ (S.f b)) C := funext p1
  have pf' : (fun b => m' (S.f' b)) = act (fun b => m₀' (S.f' b)) C' := funext p2
  have hU : UT C := ⟨fun i j h => (a12 i j h).1, fun i => (adiag i).1⟩
  have hU' : UT C' := ⟨fun i j h => (a12 i j h).2, fun i => (adiag i).2⟩
  have hg : ∀ a (j : Fin r), hf L S.Hm (S.f a) (S.f j.castSucc) = 0 := fun a j => by
    simp [S.gram, Fin.castSucc_ne_last]
  have hg' : ∀ a (j : Fin r), hf L S.Hm (S.f' a) (S.f' j.castSucc) = 0 := fun a j => by
    simp [S.gram', Fin.castSucc_ne_last]
  have hs : {i : Fin (r + 1) | (i : ℕ) < r + 1} = Set.univ := by
    ext i; simpa using i.2
  obtain ⟨s1, s2, s3⟩ := StdLat.stdLat_spec L r k S _ _ (Or.inl ⟨rfl, rfl⟩) _ hA
  obtain ⟨s1', s2', s3'⟩ := StdLat.stdLat_spec L r k S _ _ (Or.inr ⟨rfl, rfl⟩) _ hA'
  have hSD : IsSD L S.Hm Λ := by
    have := TermBasic.isSD_smul S hn₀.1.1 s1
    rwa [← e] at this
  have tr : ∀ x, (x ∈ Λ ∧ x ∈ S.spanTo S.f (r + 1)) ↔
      x ∈ Submodule.span L.O (Set.range fun b => m₀ (S.f b)) := by
    intro x
    have := TermBasic.trace_smul hg hn₀ (s2 (r + 1) le_rfl) x
    rwa [← e, hs, Set.image_univ] at this
  have tr' : ∀ x, (x ∈ Λ ∧ x ∈ S.spanTo S.f' (r + 1)) ↔
      x ∈ Submodule.span L.O (Set.range fun b => m₀' (S.f' b)) := by
    intro x
    have := TermBasic.trace_smul hg' hn₀' (s2' (r + 1) le_rfl) x
    rwa [← e', hs, Set.image_univ] at this
  have prim : ∀ x, (x ∈ Λ ∧ x ∈ S.spanTo S.f (r + 1)) ↔
      x ∈ Submodule.span L.O (Set.range fun b => m (S.f b)) := by
    intro x
    rw [tr, pf, span_act_eq L.O _ C hU a3]
  have prim' : ∀ x, (x ∈ Λ ∧ x ∈ S.spanTo S.f' (r + 1)) ↔
      x ∈ Submodule.span L.O (Set.range fun b => m' (S.f' b)) := by
    intro x
    rw [tr', pf', span_act_eq L.O _ C' hU' a4]
  obtain ⟨A₁, hA₁, n₁, hn₁, hfix, hΛ₁⟩ :=
    GlobalTheory.HL.FrameLift.lift L r k S S.f S.es (Or.inl ⟨rfl, rfl⟩) Λ hSD m hm prim
  obtain ⟨A₁', hA₁', n₁', hn₁', hfix', hΛ₁'⟩ :=
    GlobalTheory.HL.FrameLift.lift L r k S S.f' S.es' (Or.inr ⟨rfl, rfl⟩) Λ hSD m' hm' prim'
  have eA : A₁ = δ.1 := by
    ext x
    rw [(StdLat.stdLat_spec L r k S _ _ (Or.inl ⟨rfl, rfl⟩) _ hA₁).2.2 x, s3 x,
      TermBasic.inner_smul S hn₁ (Λ := S.stdLat S.f S.es A₁),
      TermBasic.inner_smul S hn₀ (Λ := S.stdLat S.f S.es δ.1), ← hΛ₁, ← e]
  have eA' : A₁' = δ.2.1 := by
    ext x
    rw [(StdLat.stdLat_spec L r k S _ _ (Or.inr ⟨rfl, rfl⟩) _ hA₁').2.2 x, s3' x,
      TermBasic.inner_smul S hn₁' (Λ := S.stdLat S.f' S.es' A₁'),
      TermBasic.inner_smul S hn₀' (Λ := S.stdLat S.f' S.es' δ.2.1), ← hΛ₁', ← e']
  subst eA eA'
  refine ⟨n₁, hn₁, n₁', hn₁', hfix, hfix', hA, hA', hn₁, hn₁', hΛ₁, hΛ₁', fun j => ?_, hgr⟩
  rw [hfix, hfix', p1, p2]
  choose y hy hyeq using hth
  choose cc hcc hcceq using aθ
  have hmem : ∀ i, m₀ (S.f i) ∈ Λ := fun i => ((tr _).2 (Submodule.subset_span ⟨i, rfl⟩)).1
  refine ⟨∑ i, ((⟨C' i j, a4 i j⟩ : L.O) • y i + (⟨cc i j, hcc i j⟩ : L.O) • m₀ (S.f i)),
    Submodule.sum_mem _ fun i _ => Submodule.add_mem _ (Submodule.smul_mem _ _ (hy i))
      (Submodule.smul_mem _ _ (hmem i)), ?_⟩
  rw [← Finset.sum_sub_distrib, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : m₀' (S.f' i) = m₀ (S.f i) + algebraMap F E S.th • y i := by
    rw [← hyeq i, add_sub_cancel]
  have h2 : C' i j = C i j + algebraMap F E S.th * cc i j := by
    rw [← hcceq i j, add_sub_cancel]
  rw [h1, Subring.smul_def, Subring.smul_def]
  simp only [h2]
  module

end GlobalTheory.HL.LocGenMass

namespace GlobalTheory.HL.LocGenMass

theorem mass_class_eq_weight_count : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), 4 * r + 7 ≤ k → Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → ∀ (R : LocNG.Reps P) (d0 : LocNG.Datum P), ∀ (f f' : Fin (r + 1) → V), (∃ n ∈ P.A.N, f = fun b => n (P.A.f b)) → (∃ n' ∈ P.B.N, f' = fun b => n' (P.B.f b)) → ∀ (Y0 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (c1 : Set (Matrix (Fin (r + 1)) (Fin (r + 1)) E)), c1 = {Y | ∃ A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ((∀ a b, b < a → A a b = 0) ∧ (∀ a, A a a = 1) ∧ ∀ a b, A a b ∈ M.L.O) ∧ ((∀ a b, b < a → A' a b = 0) ∧ (∀ a, A' a a = 1) ∧ ∀ a b, A' a b ∈ M.L.O) ∧ (∀ a b, A a b - A' a b ∈ Submodule.span M.L.O {algebraMap F E (LocNG.theta M)}) ∧ Y = (A.transpose.map M.L.cj) * Y0 * A'} → H.Zhat f f' ∈ c1 → (∃ (d : LocNG.Datum P) (t : Term V M r), LocNG.IsTermOver P d t ∧ H.Zhat t.f t.f' ∈ c1) → ∃ w : ℝ, 0 < w ∧ w ≤ P.Hp ^ (3 * (r + 1) ^ 2) ∧ (∑' d : R.RD, ENNReal.ofReal (LocNG.Datum.wt d0 d.1) * ∑' t : R.RT d.1, (if ¬ LocNG.BBne (H := H) t.1 ∧ H.Zhat t.1.f t.1.f' ∈ c1 then ENNReal.ofReal (LocNG.mu P t.1) else 0)) = ENNReal.ofReal w * ∑' d : R.RD, ENNReal.ofReal (LocNG.Datum.wt d0 d.1) * (({Λ | LocNG.IsTermOver P d.1 (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r) ∧ ¬ LocNG.BBne (H := H) (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r)} : Set (Submodule M.L.O V)).encard : ℝ≥0∞) := by
  intro F _ _ _ E _ _ _ _ M hM V _ _ H r k P hk hrank hrel R d0 f f' hf hf' Y0 c1 hc1 hZ hex
  letI := hM.loc
  letI := hM.char0
  obtain ⟨d₁, t₁, ht₁, hZ₁⟩ := hex
  obtain ⟨S, ⟨c⟩⟩ := GlobalTheory.HL.CoordExist.exists_coord M hM H r k P hrank hrel
  obtain ⟨hT1, hT2, -⟩ := GlobalTheory.HL.CoordTermWt.terms_correspond M hM H r k P S c
  obtain ⟨hth, hN, hN', hSt, -⟩ := GlobalTheory.HL.CoordUnip.transport M hM H r k P S c
  obtain ⟨-, -, hbij, -⟩ := GlobalTheory.HL.CoordMass.transport M hM H r k P S c
  have aS := GlobalTheory.FrameAct.stabiliser_acts_on_terms M.L r k S
  have cls := GlobalTheory.HL.FrameClass.frame_classes M.L r k S
  have trm := GlobalTheory.HL.TermBasic.term_basic M.L r k S
  have vol := (GlobalTheory.HL.volSt M.L r k S).2
  obtain ⟨s₀, hs₀, A, A', hAA, ef, ef'⟩ :=
    frames_in_class M hM H r k P hrank hrel d₁ t₁ ht₁ f f' hf hf' Y0 c1 hc1 hZ₁ hZ
  obtain ⟨n, hn, rfl⟩ := hf
  obtain ⟨n', hn', rfl⟩ := hf'
  have h₁ := (hT1 d₁ t₁ ht₁).1
  have hs₀' : c.grp s₀ ∈ S.St := (hSt s₀).1 hs₀
  have hΛ₁t : S.IsTerm (c.dat d₁) (c.grp s₀ • c.lat t₁.abelian₂) := (aS _ _ h₁ _ hs₀').1
  set C₂ := S.Fr (c.dat d₁) (c.grp s₀ • c.lat t₁.abelian₂) with hC₂
  have hC₂' : C₂ = S.frameCls (fun b => c.e (n (P.A.f b))) (fun b => c.e (n' (P.B.f b))) := by
    rw [hC₂, (aS _ _ h₁ _ hs₀').2.2.2.2.1, GlobalTheory.HL.AbsGenMass.fr_eq hM c d₁ t₁ ht₁, (cls _ _).2.2]
    obtain ⟨a1, a2, a3, a4, C, hC, e1⟩ := hAA
    refine ((cls (fun b => c.grp s₀ (c.e (t₁.f b))) (fun b => c.grp s₀ (c.e (t₁.f' b)))).2.1
      (fun b => c.e (n (P.A.f b)), fun b => c.e (n' (P.B.f b))) ⟨A, A', a3, a4, fun i j h => ⟨a1.1 i j h, a2.1 i j h⟩,
      fun i => ⟨a1.2 i, a2.2 i⟩, fun i j => ⟨C i j, hC i j, ?_⟩, fun j => ?_, fun j => ?_⟩).1.symm
    · rw [e1, ← hth]
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    · have := congrFun ef j
      simp only [PairingClass.act] at this
      simp [this, CoordUnip.grp_apply]
    · have := congrFun ef' j
      simp only [PairingClass.act] at this
      simp [this, CoordUnip.grp_apply]
  have hI : S.IsIntCls C₂ := (trm _ _ hΛ₁t).2.2.2.2.2.2.1
  obtain ⟨-, -, hw1, hwinv⟩ := vol C₂ hI.1
  refine ⟨S.wC C₂, by linarith, ?_, ?_⟩
  · have hsum := GlobalTheory.HL.TotalWeight.sumCls_one_le M.L r k S ⟨_, _, hΛ₁t⟩
    have hle : ENNReal.ofReal (S.wC C₂) ≤ S.sumCls fun _ => 1 := by
      unfold Frames.sumCls
      refine le_trans ?_ (ENNReal.le_tsum (Quotient.mk (MulAction.orbitRel S.St (Set S.FrP)) C₂))
      have hrl : (MulAction.orbitRel S.St (Set S.FrP))
          (Quotient.mk (MulAction.orbitRel S.St (Set S.FrP)) C₂).out C₂ := Quotient.mk_out C₂
      obtain ⟨⟨h, hh⟩, e⟩ := MulAction.orbitRel_apply.1 hrl
      have e' : (Quotient.mk (MulAction.orbitRel S.St (Set S.FrP)) C₂).out = h • C₂ := e.symm
      have hint : S.IsIntCls (h • C₂) := by
        rw [hC₂, ← (aS _ _ hΛ₁t h hh).2.2.2.2.1]
        exact (trm _ _ (aS _ _ hΛ₁t h hh).1).2.2.2.2.2.2.1
      rw [e', if_pos hint, hwinv h hh, mul_one]
    rw [(GlobalTheory.HL.CoordHeight.height_eq M hM H r k P S c).1]
    have := hle.trans hsum
    exact (ENNReal.ofReal_le_ofReal_iff (by unfold Frames.Hp; positivity)).1 this
  · have conv : ∀ (s : Set (Term V M r)) (p : Term V M r → Prop) [∀ t, Decidable (p t)] (g : Term V M r → ℝ≥0∞),
        (∑' t : s, if p t.1 then g t.1 else 0) = ∑' t : {t // t ∈ s ∧ p t}, g t.1 := by
      intro s p _ g
      rw [tsum_subtype s (fun t => if p t then g t else 0)]
      rw [show (∑' t : {t // t ∈ s ∧ p t}, g t.1) = ∑' t : ({t | t ∈ s ∧ p t} : Set _), g t.1 from rfl,
        tsum_subtype]
      refine tsum_congr fun t => ?_
      by_cases h1 : t ∈ s <;> by_cases h2 : p t <;> simp [Set.indicator, h1, h2]
    have orb : ∀ X : Set S.FrP, (∃ s ∈ S.St, X = s • S.Fr (c.dat d₁) (c.lat t₁.abelian₂)) ↔
        ∃ s ∈ S.St, X = s • C₂ := by
      intro X
      rw [hC₂, (aS _ _ h₁ _ hs₀').2.2.2.2.1]
      constructor
      · rintro ⟨s, hs, e⟩
        refine ⟨s * (c.grp s₀)⁻¹, S.St.mul_mem hs (S.St.inv_mem hs₀'), ?_⟩
        rw [e, mul_smul, inv_smul_smul]
      · rintro ⟨s, hs, e⟩
        refine ⟨s * c.grp s₀, S.St.mul_mem hs hs₀', ?_⟩
        rw [e, mul_smul]
    have hC₁ := GlobalTheory.HL.AbsGenMass.fr_eq hM c d₁ t₁ ht₁
    have hclass : ∀ d t, LocNG.IsTermOver P d t →
        (H.Zhat t.f t.f' ∈ c1 ↔ ∃ s ∈ S.St, S.Fr (c.dat d) (c.lat t.abelian₂) = s • C₂) := by
      intro d t ht
      rw [GlobalTheory.HL.PairingClass.mem_class_iff M hM H r k P hrank hrel d₁ d t₁ t ht₁ ht Y0 c1 hc1 hZ₁,
        ← orb, GlobalTheory.HL.AbsGenMass.fr_eq hM c d t ht, hC₁]
      constructor
      · rintro ⟨s, hs, A, A', a1, a2, a3, a4, a5⟩
        refine ⟨c.grp s, (hSt s).1 hs, ?_⟩
        rw [(cls _ _).2.2]
        refine ((cls _ _).2.1 (fun b => c.e (t.f b), fun b => c.e (t.f' b))
          ⟨A, A', fun i j => (a1 i j).1, fun i j => (a1 i j).2.1, a2, a3,
            fun i j => hth ▸ (a1 i j).2.2, fun j => ?_, fun j => ?_⟩).1
        · simp [a4, Coord.grp]
        · simp [a5, Coord.grp]
      · rintro ⟨s, hs, e⟩
        have hm := (cls (fun b => c.e (t.f b)) (fun b => c.e (t.f' b))).1
        rw [e, (cls _ _).2.2] at hm
        obtain ⟨A, A', a1, a1', a2, a3, a6, a4, a5⟩ := hm
        refine ⟨c.grp.symm s, (hSt _).2 (by simpa using hs), A, A',
          fun i j => ⟨a1 i j, a1' i j, hth ▸ a6 i j⟩, a2, a3, fun j => c.e.injective ?_,
          fun j => c.e.injective ?_⟩
        · refine (a4 j).trans ?_
          simp [Coord.grp]
        · refine (a5 j).trans ?_
          simp [Coord.grp]
    have hstab : ∀ δ : S.Datum, ∀ s ∈ S.St, ∀ Λ, S.IsTerm δ Λ →
        (S.BBzero δ Λ ∧ ∃ s ∈ S.St, S.Fr δ Λ = s • C₂) →
        (S.BBzero δ (s • Λ) ∧ ∃ s' ∈ S.St, S.Fr δ (s • Λ) = s' • C₂) := by
      rintro δ h hh Λ hΛ ⟨hb, s, hs, e⟩
      refine ⟨(aS δ Λ hΛ h hh).2.2.2.2.2.2.2.1.2 hb, h * s, S.St.mul_mem hh hs, ?_⟩
      rw [(aS δ Λ hΛ h hh).2.2.2.2.1, e, mul_smul]
    rw [← ENNReal.tsum_mul_left]
    refine tsum_congr fun d => ?_
    rw [mul_left_comm]
    congr 1
    have e0 := conv (R.RT d.1) (fun t => ¬ LocNG.BBne (H := H) t ∧ H.Zhat t.f t.f' ∈ c1)
      (fun t => ENNReal.ofReal (LocNG.mu P t))
    beta_reduce at e0
    rw [e0, GlobalTheory.HL.AbsGenMass.sum_eq_mass hM c R d.1 _
      (fun Λ => S.BBzero (c.dat d.1) Λ ∧ ∃ s ∈ S.St, S.Fr (c.dat d.1) Λ = s • C₂) (hstab _) (fun t ht => by
        rw [(hT1 _ t ht).2.2, not_not, hclass _ t ht]),
      hC₂, GlobalTheory.HL.MassOrbit.mass_orbit_class M.L r k S _ _ hΛ₁t, ← hC₂]
    unfold Frames.nT
    congr 2
    refine Eq.trans ?_ (hbij.1.encard_image _)
    congr 1
    ext Λ'
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨hT, hB, hF⟩
      obtain ⟨⟨Λ, g, g', T, T'⟩, ht, rfl⟩ := hT2 d.1 Λ' hT
      have ht' := ht
      obtain ⟨h1, h2, ⟨n₀, hn₀, hg, hΛ⟩, ⟨n₀', hn₀', hg', hΛ'⟩, -⟩ := ht'
      dsimp only at h1 h2 hg hΛ hg' hΛ'
      subst h1 h2 hg hg'
      have hW := (GlobalTheory.HL.CoordTerm.isTermW_iff M hM H r k P S c d.1 n₀ n₀' Λ).1 ⟨ht, hn₀, hn₀', hΛ, hΛ'⟩
      have hmem : ((fun b => c.grp n (S.f b)), (fun b => c.grp n' (S.f' b))) ∈
          S.frameCls (fun b => c.grp n₀ (S.f b)) (fun b => c.grp n₀' (S.f' b)) := by
        rw [← (GlobalTheory.HL.WitIndep.witness_independence M.L r k S _ _ _ _ hW).2.2.1, hF, hC₂']
        have e1 : (fun b => c.grp n (S.f b)) = fun b => c.e (n (P.A.f b)) :=
          funext fun b => by rw [c.f_eq, CoordUnip.grp_apply]
        have e2 : (fun b => c.grp n' (S.f' b)) = fun b => c.e (n' (P.B.f b)) :=
          funext fun b => by rw [c.f'_eq, CoordUnip.grp_apply]
        rw [e1, e2]
        exact (cls _ _).1
      obtain ⟨m₂, hm₂, m₂', hm₂', e2, e2', hW2⟩ :=
        relift M.L r k S _ _ _ _ _ _ hW ((hN n).1 hn) ((hN' n').1 hn') hmem
      obtain ⟨n₂, rfl⟩ := c.grp.surjective m₂
      obtain ⟨n₂', rfl⟩ := c.grp.surjective m₂'
      have key := (GlobalTheory.HL.CoordTerm.isTermW_iff M hM H r k P S c d.1 n₂ n₂' Λ).2 hW2
      have q1 : (fun b => n (P.A.f b)) = fun b => n₂ (P.A.f b) := funext fun b => c.e.injective (by
        rw [← CoordUnip.grp_apply c n, ← CoordUnip.grp_apply c n₂, ← c.f_eq, e2])
      have q2 : (fun b => n' (P.B.f b)) = fun b => n₂' (P.B.f b) := funext fun b => c.e.injective (by
        rw [← CoordUnip.grp_apply c n', ← CoordUnip.grp_apply c n₂', ← c.f'_eq, e2'])
      refine ⟨Λ, ⟨?_, fun hb => ?_⟩, rfl⟩
      · rw [q1, q2]
        exact key.1
      · rw [q1, q2] at hb
        exact (hT1 _ _ key.1).2.2.1 hb hB
    · rintro ⟨Λ, ⟨ht, hb⟩, rfl⟩
      refine ⟨(hT1 _ _ ht).1, ?_, ?_⟩
      · by_contra hB
        exact hb ((hT1 _ _ ht).2.2.2 hB)
      · exact (GlobalTheory.HL.AbsGenMass.fr_eq hM c d.1 _ ht).trans hC₂'.symm

end GlobalTheory.HL.LocGenMass
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassClassEqWeightCountStatement
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mass_class_eq_weight_count_alt : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r k : ℕ) (P : LocNG.FPair H r), 4 * r + 7 ≤ k → Module.finrank E V = k + 2 * r + 1 → P.RelG (LocNG.theta M) → ∀ (R : LocNG.Reps P) (d0 : LocNG.Datum P), ∀ (f f' : Fin (r + 1) → V), (∃ n ∈ P.A.N, f = fun b => n (P.A.f b)) → (∃ n' ∈ P.B.N, f' = fun b => n' (P.B.f b)) → ∀ (Y0 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (c1 : Set (Matrix (Fin (r + 1)) (Fin (r + 1)) E)), c1 = {Y | ∃ A A' : Matrix (Fin (r + 1)) (Fin (r + 1)) E, ((∀ a b, b < a → A a b = 0) ∧ (∀ a, A a a = 1) ∧ ∀ a b, A a b ∈ M.L.O) ∧ ((∀ a b, b < a → A' a b = 0) ∧ (∀ a, A' a a = 1) ∧ ∀ a b, A' a b ∈ M.L.O) ∧ (∀ a b, A a b - A' a b ∈ Submodule.span M.L.O {algebraMap F E (LocNG.theta M)}) ∧ Y = (A.transpose.map M.L.cj) * Y0 * A'} → H.Zhat f f' ∈ c1 → (∃ (d : LocNG.Datum P) (t : Term V M r), LocNG.IsTermOver P d t ∧ H.Zhat t.f t.f' ∈ c1) → ∃ w : ℝ, 0 < w ∧ w ≤ P.Hp ^ (3 * (r + 1) ^ 2) ∧ (∑' d : R.RD, ENNReal.ofReal (LocNG.Datum.wt d0 d.1) * ∑' t : R.RT d.1, (if ¬ LocNG.BBne (H := H) t.1 ∧ H.Zhat t.1.f t.1.f' ∈ c1 then ENNReal.ofReal (LocNG.mu P t.1) else 0)) = ENNReal.ofReal w * ∑' d : R.RD, ENNReal.ofReal (LocNG.Datum.wt d0 d.1) * (({Λ | LocNG.IsTermOver P d.1 (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r) ∧ ¬ LocNG.BBne (H := H) (⟨Λ, f, f', P.A.T, P.B.T⟩ : Term V M r)} : Set (Submodule M.L.O V)).encard : ℝ≥0∞) := by
  first | exact @GlobalTheory.HL.LocGenMass.mass_class_eq_weight_count | exact GlobalTheory.HL.LocGenMass.mass_class_eq_weight_count | (intros; apply GlobalTheory.HL.LocGenMass.mass_class_eq_weight_count <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenericMassLeHeightPowMulGluedCount
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt Formalism.L2.SG.NGData Formalism.L2.SG.NGLocModel Formalism.L2.SG.FamDefs GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GenMassBound

theorem tri_trans : ∀ (K W : Type) [CommRing K] [AddCommGroup W] [Module K W] (n : ℕ) (f g h : Fin n → W), Tri K f g → Tri K g h → Tri K f h := by
  intro K W _ _ _ n f g h ⟨A, hA, hfg⟩ ⟨B, hB, hgh⟩
  refine ⟨A * B, ⟨fun a b hba => ?_, fun a => ?_⟩, fun b => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases hca : c < a
    · rw [hA.1 a c hca, zero_mul]
    · rw [hB.1 c b (lt_of_lt_of_le hba (not_lt.1 hca)), mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [hA.2 a, hB.2 a, one_mul]
    · intro c _ hc
      rcases lt_or_gt_of_ne hc with h1 | h1
      · rw [hA.1 a c h1, zero_mul]
      · rw [hB.1 c a h1, mul_zero]
    · intro h; exact absurd (Finset.mem_univ a) h
  · rw [hgh b]
    have e : ∀ c, g c = ∑ a, A a c • f a := hfg
    simp only [e, Finset.smul_sum, smul_smul]
    simp only [Matrix.mul_apply, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    rw [mul_comm]

theorem mapLF_frame : ∀ (D : D7) {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T) (m : GV D), m ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → (∀ a, frame (Formalism.L2.SG.TermOp.mapLF m F) a = m (frame F a)) ∧ (Formalism.L2.SG.TermOp.mapLF m F).zt = m F.zt ∧ (Formalism.L2.SG.TermOp.mapLF m F).fl.z = m F.fl.z := by
  intro D T F m hm
  rw [Formalism.L2.SG.TermOp.mapLF, dif_pos hm]
  refine ⟨fun a => ?_, rfl, rfl⟩
  simp only [frame, Formalism.MainNotions.S.FlagG.fvec, Formalism.L2.SG.TermOp.mapFlag]
  refine Fin.lastCases ?_ (fun i => ?_) a
  · simp
  · simp

theorem zhat_isom : ∀ (D : D7) {T T' : D.host.E} (F G : LFlag (D.sp.Y 0) D.R.rS T) (F' G' : LFlag (D.sp.Y 0) D.R.rS T') (m : GV D), m ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → (∀ a, frame G a = m (frame F a)) → (∀ a, frame G' a = m (frame F' a)) → ZhatL G G' = ZhatL F F' := by
  intro D T T' F G F' G' m hm hG hG'
  funext a b
  have h1 : G.fl.fvec a = m (F.fl.fvec a) := hG a
  have h2 : G'.fl.fvec b = m (F'.fl.fvec b) := hG' b
  simp only [ZhatL, Formalism.MainNotions.S.Zhat, Formalism.MainNotions.S.brS, h1, h2]
  rw [hm]

theorem zhat_chg : ∀ (D : D7) {T T' : D.host.E} (F G : LFlag (D.sp.Y 0) D.R.rS T) (F' G' : LFlag (D.sp.Y 0) D.R.rS T') (A A' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E), Chg (frame F) A (frame G) → Chg (frame F') A' (frame G') → ZhatL G G' = A.transpose.map star * ZhatL F F' * A' := by
  intro D T T' F G F' G' A A' hc hc'
  funext a b
  have h1 : G.fl.fvec a = ∑ c, A c a • F.fl.fvec c := hc a
  have h2 : G'.fl.fvec b = ∑ c, A' c b • F'.fl.fvec c := hc' b
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [ZhatL, Formalism.MainNotions.S.Zhat, Formalism.MainNotions.S.brS, h1, h2, map_sum, map_smulₛₗ, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply,
    Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  simp only [starRingEnd_apply, RingHom.id_apply]
  ring

theorem cell_chg : ∀ {K : Type} [CommRing K] {r : ℕ} (Z L U : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (w : Point K (r + 1)), IsLoUni L → Uni U → ZhatOM Z = ptMat w → IsInCell (ZhatOM (L * Z * U)) w := by
  intro K _ r Z L U w hL hU hZ
  set s : Fin (r + 1) → K := fun b => (-1 : K) ^ (r - b.val) with hsdef
  have hs : ∀ b, s b * s b = 1 := by
    intro b
    simp only [hsdef, ← mul_pow, neg_one_mul, neg_neg, one_pow]
  have hZS : ∀ M : Matrix (Fin (r + 1)) (Fin (r + 1)) K, ZhatOM M = M * Matrix.diagonal s := by
    intro M
    funext a b
    simp [ZhatOM, Matrix.mul_diagonal, hsdef, mul_comm]
  have hDD : Matrix.diagonal s * Matrix.diagonal s = 1 := by
    rw [Matrix.diagonal_mul_diagonal, show (fun i => s i * s i) = fun _ => (1 : K) from funext hs, Matrix.diagonal_one]
  refine ⟨L, Matrix.diagonal s * U * Matrix.diagonal s, hL, fun i j => ⟨fun hji => ?_, fun hij => ?_⟩, ?_⟩
  · simp [Matrix.diagonal_mul, Matrix.mul_diagonal, hU.1 i j hji]
  · subst hij
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, hU.2 i, mul_one]
    exact hs i
  · rw [← hZ, hZS, hZS]
    rw [show L * (Z * Matrix.diagonal s) * (Matrix.diagonal s * U * Matrix.diagonal s) =
      L * Z * (Matrix.diagonal s * Matrix.diagonal s) * U * Matrix.diagonal s by simp only [Matrix.mul_assoc], hDD,
      Matrix.mul_one]

theorem frameN : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E]
    [TopologicalSpace E] [MeasurableSpace E] (M : Loc.Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V]
    (H : Loc.HermSp M V) (r : ℕ) (Fr : LocNG.FrameD H r), Fr.T ≠ 0 → ∀ (g0 g : Fin (r + 1) → V)
    (A : Matrix (Fin (r + 1)) (Fin (r + 1)) E), (∃ n ∈ Fr.N, g0 = fun b => n (Fr.f b)) → Uni A → Chg g0 A g →
    ∃ n ∈ Fr.N, g = fun b => n (Fr.f b) := by
  intro F _ _ _ E _ _ _ _ M hOK V _ _ H r Fr hT g0 g A hg0 hA hc
  have u := GlobalTheory.T.frameDual_unipotentGroup_acts_unitriangular_onto M hOK H r Fr hT
  obtain ⟨n, hn, rfl⟩ := hg0
  exact u.2.2 g (tri_trans E V (r + 1) _ _ _ (u.2.1 n hn) ⟨A, hA, hc⟩)

theorem genericMass_le_heightPow_mul_glueSum : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), 4 * D.R.rS + 7 ≤ D.R.k → ∀ {K : Type} (Fm : LocFam (zOf Y) K (NuC D)) (γ : PN.Pts D.host.E D.R.rS), 0 < Fm.V0 → (∃ (w : Point D.host.E (D.R.rS + 1)) (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (Y0 : ∀ p : PlF D, Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep), toPts w = γ ∧ (∃ n ∈ NRat (lf D (X.Fu u)), ∀ a, frame F a = n (frame (lf D (X.Fu u)) a)) ∧ ZhatOM (ZhatL F F') = ptMat w ∧ TotPos (Gval F F') ∧ BaseOK (Tu D u) (Tu D u') F F' Fm.P Fm.d0 ∧ MassLaw F F' Fm.P Fm.d0 Fm.V0 ∧ ∀ p ∈ Fm.P, Fm.ngenL p = (ngenLoc (Fm.R p) (Fm.d0 p) (clsLoc ((zOf Y).M p) (Y0 p))).toReal ∧ ∃ (d : LocNG.Datum (Fm.FP p)) (t : Loc.Term (Vp D p) ((zOf Y).M p) D.R.rS), LocNG.IsTermOver (Fm.FP p) d t ∧ (locH (zOf Y) p).Zhat t.f t.f' ∈ clsLoc ((zOf Y).M p) (Y0 p)) → 0 < Fm.toL.ngenTot ∧ (∀ p ∈ Fm.P, 1 ≤ (Fm.FP p).Hp) ∧ ∃ (w : Point D.host.E (D.R.rS + 1)) (G' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)), toPts w = γ ∧ G'.zt = G'.fl.z ∧ TotPos (Gval (lf D (X.Fu u)) G') ∧ IsInCell (ZhatOM (ZhatL (lf D (X.Fu u)) G')) w ∧ ∀ s : Finset (LV D), Glue (lf D (X.Fu u)) G' s → s.Nonempty ∧ Fm.toL.ngenTot ≤ Fm.toL.Htot ^ (3 * (D.R.rS + 1) ^ 2) * glueSum (lf D (X.Fu u)) G' s := by
  intro D X Y u u' hk K Fm γ hV0 hyp
  obtain ⟨w, F, F', Y0, hw, hFn, hZw, hTP, hBase, hML, hloc⟩ := hyp
  have hBased := hBase.1
  have hRel := hBase.2.1
  have hd0 := hBase.2.2.2.1

  have hOK : ∀ p : PlF D, ((zOf Y).M p).OK := fun p => ((zOf Y).agree p).1
  have hpos : ∀ p ∈ Fm.P, 0 < Fm.ngenL p ∧ ngenLoc (Fm.R p) (Fm.d0 p) (clsLoc ((zOf Y).M p) (Y0 p)) ≠ ⊤ ∧
      1 ≤ (Fm.FP p).Hp := by
    intro p hp
    obtain ⟨hng, d, t, ht, hc⟩ := hloc p hp
    obtain ⟨g0, g1, -, -⟩ := GlobalTheory.mass_pairingClass_bounds ((zOf Y).M p) (hOK p) (locH (zOf Y) p) D.R.rS D.R.k (Fm.FP p)
      hk (rank_Vp p) (hRel p) (Fm.R p) (Fm.d0 p) (hd0 p) d t ht (Y0 p) (clsLoc ((zOf Y).M p) (Y0 p)) rfl hc _ rfl
    refine ⟨?_, g1, ?_⟩
    · rw [hng]; exact ENNReal.toReal_pos g0.ne' g1
    · obtain ⟨⟨a0, a1⟩, ⟨b0, b1⟩, c0, c1⟩ := Formalism.MainNotions.KappaEndpoints.ng_factors (hOK p) (hRel p).2.2.1 ht
      unfold LocNG.FPair.Hp
      refine Real.one_le_rpow_of_pos_of_le_one_of_nonpos (mul_pos (mul_pos a0 b0) c0) ?_ (by norm_num)
      exact mul_le_one₀ (mul_le_one₀ a1 b0.le b1) c0.le c1
  have hTot : 0 < Fm.toL.ngenTot := by
    show 0 < Fm.V0 * ∏ p : {p // p ∈ Fm.P}, Fm.ngenL p.1
    exact mul_pos hV0 (Finset.prod_pos fun p _ => (hpos p.1 p.2).1)
  refine ⟨hTot, fun p hp => (hpos p hp).2.2, ?_⟩

  choose dd tt htt hcls using fun p (hp : p ∈ Fm.P) => (hloc p hp).2
  let f : ∀ p : PlF D, Fin (D.R.rS + 1) → Vp D p := fun p =>
    if hp : p ∈ Fm.P then (tt p hp).f else scaled (zOf Y) p (frame F)
  let f' : ∀ p : PlF D, Fin (D.R.rS + 1) → Vp D p := fun p =>
    if hp : p ∈ Fm.P then (tt p hp).f' else scaled (zOf Y) p (frame F')
  have hAf : ∀ p, (Fm.FP p).A.f = scaled (zOf Y) p (frame F) := fun p => (hBased p).1
  have hBf : ∀ p, (Fm.FP p).B.f = scaled (zOf Y) p (frame F') := fun p => (hBased p).2.1
  have hAT : ∀ p, (Fm.FP p).A.T ≠ 0 := fun p => (hRel p).2.2.2.2.2.2.2.1
  have hBT : ∀ p, (Fm.FP p).B.T ≠ 0 := fun p => (hRel p).2.2.2.2.2.2.2.2.2.1
  have htri : ∀ p ∈ Fm.P, Tri (D.s.atP p).Ep (scaled (zOf Y) p (frame F)) (f p) ∧
      Tri (D.s.atP p).Ep (scaled (zOf Y) p (frame F')) (f' p) := by
    intro p hp
    obtain ⟨-, -, ⟨n, hn, hfn, -⟩, ⟨n', hn', hfn', -⟩, -⟩ := htt p hp
    have u1 := GlobalTheory.T.frameDual_unipotentGroup_acts_unitriangular_onto ((zOf Y).M p) (hOK p) (locH (zOf Y) p) D.R.rS (Fm.FP p).A (hAT p)
    have u2 := GlobalTheory.T.frameDual_unipotentGroup_acts_unitriangular_onto ((zOf Y).M p) (hOK p) (locH (zOf Y) p) D.R.rS (Fm.FP p).B (hBT p)
    have e1 : f p = (tt p hp).f := dif_pos hp
    have e2 : f' p = (tt p hp).f' := dif_pos hp
    rw [e1, e2, ← hAf p, ← hBf p, hfn, hfn']
    exact ⟨u1.2.1 n hn, u2.2.1 n' hn'⟩
  obtain ⟨G, G'', hStd, hch⟩ := GlobalTheory.T.exists_rational_frames_prescribed_local_classes D (zOf Y) u u' F F' Fm.P f f' htri

  have hlocw : ∀ p ∈ Fm.P, ∃ wp : ℝ, 0 < wp ∧ wp ≤ (Fm.FP p).Hp ^ (3 * (D.R.rS + 1) ^ 2) ∧
      ngenLoc (Fm.R p) (Fm.d0 p) (clsLoc ((zOf Y).M p) (Y0 p)) =
        ENNReal.ofReal wp * locSum G G'' p (Fm.R p) (Fm.d0 p) := by
    intro p hp
    obtain ⟨A, A', hA, hA', hint, hc1, hc2⟩ := hch p hp
    have e1 : f p = (tt p hp).f := dif_pos hp
    have e2 : f' p = (tt p hp).f' := dif_pos hp
    rw [e1] at hc1
    rw [e2] at hc2
    obtain ⟨-, -, ⟨n, hn, hfn, -⟩, ⟨n', hn', hfn', -⟩, -⟩ := htt p hp
    have hN := frameN ((zOf Y).M p) (hOK p) (locH (zOf Y) p) D.R.rS (Fm.FP p).A (hAT p) _ _ A ⟨n, hn, hfn⟩ hA hc1
    have hN' := frameN ((zOf Y).M p) (hOK p) (locH (zOf Y) p) D.R.rS (Fm.FP p).B (hBT p) _ _ A' ⟨n', hn', hfn'⟩ hA' hc2
    have hZc := GlobalTheory.T.localPairingClass_stable_unitriangularChange ((zOf Y).M p) (locH (zOf Y) p) D.R.rS (Y0 p) _ _ _ _ A A' hA hA' hint hc1 hc2 (hcls p hp)
    obtain ⟨wp, h0, h1, h2⟩ := GlobalTheory.T.mass_class_eq_weight_count_alt ((zOf Y).M p) (hOK p) (locH (zOf Y) p) D.R.rS D.R.k (Fm.FP p) hk
      (rank_Vp p) (hRel p) (Fm.R p) (Fm.d0 p) _ _ hN hN' (Y0 p) (clsLoc ((zOf Y).M p) (Y0 p)) rfl hZc
      ⟨dd p hp, tt p hp, htt p hp, hcls p hp⟩
    exact ⟨wp, h0, h1, h2⟩

  have hTu : ((Tu D u : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (D.mem u).A.T_prime.ne_zero
  have fc := GlobalTheory.T.unitriangularChange_rationalFlag_iff_rationalUnipotent D (lf D (X.Fu u)) hTu
  have hTri1 : Tri D.host.E (frame (lf D (X.Fu u))) (frame F) := (fc.2 F).2 hFn
  obtain ⟨m, hm, hGm⟩ := (fc.2 G).1 (tri_trans _ _ _ _ _ _ hTri1 hStd.1)
  have hmI : m ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := hm.1
  have hmI' : m⁻¹ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := inv_mem hmI
  obtain ⟨hfr, hzt, hz⟩ := mapLF_frame D G'' m⁻¹ hmI'
  have hG''m : ∀ a, frame G'' a = m (frame (Formalism.L2.SG.TermOp.mapLF m⁻¹ G'') a) := by
    intro a
    rw [hfr a]
    exact (DFunLike.congr_fun (mul_inv_cancel m) (frame G'' a)).symm
  have hzt' : (Formalism.L2.SG.TermOp.mapLF m⁻¹ G'').zt = (Formalism.L2.SG.TermOp.mapLF m⁻¹ G'').fl.z := by
    rw [hzt, hz, hStd.2.2.2.1]
  obtain ⟨A, hA, hcA⟩ := hStd.1
  obtain ⟨A', hA', hcA'⟩ := hStd.2.1
  have hZG := zhat_chg D F G F' G'' A A' hcA hcA'
  have hZiso : ZhatL G G'' = ZhatL (lf D (X.Fu u)) (Formalism.L2.SG.TermOp.mapLF m⁻¹ G'') :=
    zhat_isom D _ G _ G'' m hmI hGm hG''m
  refine ⟨w, Formalism.L2.SG.TermOp.mapLF m⁻¹ G'', hw, hzt', ?_, ?_, ?_⟩
  · have e : Gval (lf D (X.Fu u)) (Formalism.L2.SG.TermOp.mapLF m⁻¹ G'') = Gval G G'' := by
      have h' : Formalism.MainNotions.S.Zhat (lf D (X.Fu u)).fl (Formalism.L2.SG.TermOp.mapLF m⁻¹ G'').fl = Formalism.MainNotions.S.Zhat G.fl G''.fl :=
        hZiso.symm
      unfold Gval Formalism.MainNotions.S.Gflag Formalism.MainNotions.S.Dl
      rw [h']
    rw [e, GlobalTheory.T.flagPairValue_invariant_unitriangularChange D F G F' G'' A A' hA hA' hZG]
    exact hTP
  · rw [← hZiso, hZG]
    refine cell_chg _ _ _ w ?_ hA' hZw
    intro i j
    refine ⟨fun hij => ?_, fun hij => ?_⟩
    · simp [Matrix.map_apply, Matrix.transpose_apply, hA.1 j i hij]
    · subst hij
      simp [Matrix.map_apply, Matrix.transpose_apply, hA.2 i]
  · intro s hs
    obtain ⟨s', hs', hsum⟩ := GlobalTheory.T.glueUnimodularLatticeReps_move_isometry_frames D _ _ (lf D (X.Fu u)) G (Formalism.L2.SG.TermOp.mapLF m⁻¹ G'') G'' m hmI hGm
      hG''m s hs
    have hcnt := GlobalTheory.T.weighted_count_glued_lattices_eq_mass_mul_local D (zOf Y) Fm.FP u u' F G F' G'' Fm.P Fm.d0 hk hBase hStd hTP Fm.R Fm.V0 hV0.le hML s' hs'
    choose! wp hwp0 hwpH hwpE using hlocw
    have hglue : glueSum G G'' s' = Fm.V0 * ∏ p ∈ Fm.P, (locSum G G'' p (Fm.R p) (Fm.d0 p)).toReal := by
      have hg0 : 0 ≤ glueSum G G'' s' := Finset.sum_nonneg fun _ _ => inv_nonneg.2 (Nat.cast_nonneg _)
      have h := congrArg ENNReal.toReal hcnt
      rwa [ENNReal.toReal_ofReal hg0, ENNReal.toReal_mul, ENNReal.toReal_ofReal hV0.le, ENNReal.toReal_prod] at h
    have hng : ∀ p ∈ Fm.P, Fm.ngenL p = wp p * (locSum G G'' p (Fm.R p) (Fm.d0 p)).toReal := by
      intro p hp
      rw [(hloc p hp).1, hwpE p hp, ENNReal.toReal_mul, ENNReal.toReal_ofReal (hwp0 p hp).le]
    have hle : Fm.toL.ngenTot ≤ Fm.toL.Htot ^ (3 * (D.R.rS + 1) ^ 2) *
        glueSum (lf D (X.Fu u)) (Formalism.L2.SG.TermOp.mapLF m⁻¹ G'') s := by
      rw [← hsum]
      refine le_of_le_of_eq ?_ (congrArg _ hglue.symm)
      show Fm.V0 * ∏ p : {p // p ∈ Fm.P}, Fm.ngenL p.1 ≤
        (∏ p : {p // p ∈ Fm.P}, (Fm.FP p.1).Hp) ^ (3 * (D.R.rS + 1) ^ 2) * _
      rw [← Finset.prod_pow, Finset.prod_coe_sort Fm.P (fun p => Fm.ngenL p),
        Finset.prod_coe_sort Fm.P (fun p => (Fm.FP p).Hp ^ (3 * (D.R.rS + 1) ^ 2)), Finset.prod_congr rfl hng]
      calc Fm.V0 * ∏ p ∈ Fm.P, (wp p * (locSum G G'' p (Fm.R p) (Fm.d0 p)).toReal)
          ≤ Fm.V0 * ∏ p ∈ Fm.P, ((Fm.FP p).Hp ^ (3 * (D.R.rS + 1) ^ 2) *
              (locSum G G'' p (Fm.R p) (Fm.d0 p)).toReal) := by
            refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun p hp => ?_) (fun p hp => ?_)) hV0.le
            · exact mul_nonneg (hwp0 p hp).le ENNReal.toReal_nonneg
            · exact mul_le_mul_of_nonneg_right (hwpH p hp) ENNReal.toReal_nonneg
        _ = _ := by rw [Finset.prod_mul_distrib]; ring
    refine ⟨?_, hle⟩
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    subst hne
    simp only [glueSum, Finset.sum_empty, mul_zero] at hle
    linarith

end GlobalTheory.GenMassBound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GenericMassLeHeightPowMulGluedCountStatement
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.TermLoc Formalism.L2.SG.RowsConc Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic Formalism.FourierDecayAlt Formalism.L2.SG.NGData Formalism.L2.SG.NGLocModel Formalism.L2.SG.FamDefs GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericMass_le_heightPow_mul_gluedCount : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), 4 * D.R.rS + 7 ≤ D.R.k → ∀ {K : Type} (Fm : LocFam (zOf Y) K (NuC D)) (γ : PN.Pts D.host.E D.R.rS), 0 < Fm.V0 → (∃ (w : Point D.host.E (D.R.rS + 1)) (F : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (Y0 : ∀ p : PlF D, Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (D.s.atP p).Ep), toPts w = γ ∧ (∃ n ∈ NRat (lf D (X.Fu u)), ∀ a, frame F a = n (frame (lf D (X.Fu u)) a)) ∧ ZhatOM (ZhatL F F') = ptMat w ∧ TotPos (Gval F F') ∧ BaseOK (Tu D u) (Tu D u') F F' Fm.P Fm.d0 ∧ MassLaw F F' Fm.P Fm.d0 Fm.V0 ∧ ∀ p ∈ Fm.P, Fm.ngenL p = (ngenLoc (Fm.R p) (Fm.d0 p) (clsLoc ((zOf Y).M p) (Y0 p))).toReal ∧ ∃ (d : LocNG.Datum (Fm.FP p)) (t : Loc.Term (Vp D p) ((zOf Y).M p) D.R.rS), LocNG.IsTermOver (Fm.FP p) d t ∧ (locH (zOf Y) p).Zhat t.f t.f' ∈ clsLoc ((zOf Y).M p) (Y0 p)) → 0 < Fm.toL.ngenTot ∧ (∀ p ∈ Fm.P, 1 ≤ (Fm.FP p).Hp) ∧ ∃ (w : Point D.host.E (D.R.rS + 1)) (G' : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)), toPts w = γ ∧ G'.zt = G'.fl.z ∧ TotPos (Gval (lf D (X.Fu u)) G') ∧ IsInCell (ZhatOM (ZhatL (lf D (X.Fu u)) G')) w ∧ ∀ s : Finset (LV D), Glue (lf D (X.Fu u)) G' s → s.Nonempty ∧ Fm.toL.ngenTot ≤ Fm.toL.Htot ^ (3 * (D.R.rS + 1) ^ 2) * glueSum (lf D (X.Fu u)) G' s := by
  first | exact @GlobalTheory.GenMassBound.genericMass_le_heightPow_mul_glueSum | exact GlobalTheory.GenMassBound.genericMass_le_heightPow_mul_glueSum | (intros; apply GlobalTheory.GenMassBound.genericMass_le_heightPow_mul_glueSum <;> assumption)
end
