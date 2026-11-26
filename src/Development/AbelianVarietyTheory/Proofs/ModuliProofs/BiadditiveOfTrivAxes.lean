module

public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivPullCompIff
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsBasisMemOfSpanEqTopOfSemilocal
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FiniteOfNotLinearIndependent
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NonemptyPerfectSectionsComplexOfSmoothProj
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPullbackIdCompCancel
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.RelativeGroupHatForm
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushInvertibleOfDensePart

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.BiadditiveOfTrivAxes
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.BiadditiveOfTrivAxes
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM GlobalTheory.AbLaw GlobalTheory.AbLaw.CubeGen

namespace GlobalTheory.Biadditive

section Tools

variable {X Y : Scheme.{0}} {K K' : Type} [Fintype K] [Fintype K'] {L : LB X}

theorem triv_of_formal (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    (H : Triv (LB.LinComb L φ ε))
    (h : ∀ (U : Type) [CommGroup U] (k : (Y ⟶ X) → U), ∏ i, k (φ i) ^ ε i = ∏ i, k (φ' i) ^ ε' i) :
    Triv (LB.LinComb L φ' ε') := by
  obtain ⟨t, ht⟩ := H
  obtain ⟨t', ht', -⟩ := exists_gen hL (φ' := φ') (ε' := ε') h t ht
  exact ⟨t', ht'⟩

theorem triv_mul {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    (H : Triv (LB.LinComb L φ ε)) (H' : Triv (LB.LinComb L φ' ε')) :
    Triv (LB.LinComb L (K := K ⊕ K') (Sum.elim φ φ') (Sum.elim ε ε')) := by
  obtain ⟨t, ht⟩ := H
  obtain ⟨t', ht'⟩ := H'
  exact ⟨_, DVR.mulGen_isGen _ _ _ _ _ _ _ ht ht'⟩

theorem triv_inv {φ : K → (Y ⟶ X)} {ε : K → ℤ} (H : Triv (LB.LinComb L φ ε)) :
    Triv (LB.LinComb L φ (fun k => - ε k)) := by
  obtain ⟨t, ht⟩ := H
  exact ⟨_, DVR.invGen_isGen _ _ _ _ ht⟩

theorem triv_pull_comp {f : Y ⟶ X} (H : Triv (L.pull f)) {Z : Scheme.{0}} (r : Z ⟶ Y) :
    Triv (L.pull (r ≫ f)) := by
  obtain ⟨t, ht⟩ := H
  exact ⟨_, DVR.pullGen_isGen _ _ _ t ht r⟩

end Tools

section Cube

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem triv_of_faces (hG : Out.GlobalFnsSt) (hA : IsAbelianScheme A) {H₀ : LB A.left} (hH : H₀.IsLB)
    (hamp : Out.RelAmple A H₀) {X : Scheme.{0}} {M : LB X} (hM : M.IsLB) {K : Type} [Fintype K]
    (φ : K → ((G3 A).left ⟶ X)) (ε : K → ℤ)
    (face : ∀ {Z : Scheme.{0}} (r : Z ⟶ (G3 A).left) (i : Fin 3) (b : Z ⟶ S),
      r ≫ (x3 A i).left = b ≫ η[A].left → TrivAt M φ ε r)
    (formal : ∀ {Z : Scheme.{0}} (r : Z ⟶ (G3 A).left) (b : Z ⟶ S),
      r ≫ (x3 A 0).left = b ≫ η[A].left → ∀ (U : Type) [CommGroup U] (k : (Z ⟶ X) → U),
        ∏ i, k (r ≫ φ i) ^ ε i = 1) :
    Triv (LB.LinComb M φ ε) := by
  have := hA.geomConnected
  have isLB_pw {Y : Scheme.{0}} {H : LB Y} (hH : H.IsLB) (t : ℤ) :
      (pw H t).IsLB := by
    refine ⟨hH.cover, ?_, ?_⟩
    · intro i
      have h := congrArg (· ^ t) (hH.g_self i)
      simp only [one_zpow, ← map_zpow] at h
      exact h
    · intro i j k
      have h := congrArg (· ^ t) (hH.cocycle i j k)
      simp only [mul_zpow, ← map_zpow] at h
      exact h
  have H := fibTriv_clopen M φ ε (x3 A 2).left (fun R _ j => by
    obtain ⟨q, hq, q₀, q₁⟩ := exists_cube_chart A j
    have hB := isAb_baseChange hA (j ≫ A.hom)
    have one := one_left_fst (A := A) (j ≫ A.hom)
    have pB : IsProjBy ((Over.pullback (j ≫ A.hom)).obj A).hom :=
      (AmpleBaseChange.isProjBy_smooth_isProper_geometricallyIntegral S A H₀ hA hH hamp R (j ≫ A.hom) _ _ _
        (IsPullback.of_hasPullback _ _)).1
    let B := (Over.pullback (j ≫ A.hom)).obj A
    have : Smooth B.hom := hB.smooth
    have : IsProper B.hom := hB.proper
    have : GeometricallyConnected B.hom := hB.geomConnected
    have sm : Smooth (B ⊗ B).hom := by
      change Smooth (pullback.fst B.hom B.hom ≫ B.hom); infer_instance
    have pr : IsProper (B ⊗ B).hom := by
      change IsProper (pullback.fst B.hom B.hom ≫ B.hom); infer_instance
    have gc : GeometricallyConnected (B ⊗ B).hom := by
      change GeometricallyConnected (pullback.fst B.hom B.hom ≫ B.hom)
      exact GeometricallyConnected.comp _ _
    have hN : (LB.LinComb M (fun k => q ≫ φ k) ε).IsLB := DVR.linComb_isLB _ hM _ _
    have pf := GlobalTheory.T.nonempty_perfectSectionsComplex_of_smooth_proj R _ _ sm (isProjBy_tensor R B B pB pB)
    refine ⟨_, q, (B ⊗ B).hom, hq, TrivLocus.isClosed_trivLocus R _ _ _ hN (pf _ hN) (pf _ (isLB_pw hN _)) pr
      (forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ sm gc),
      fun F _ g Z π f' => CubeOpen.triv_basicOpen_of_triv_fibre hG Seesaw.seesaw
        (SmallExtLift.exists_gen_of_small_extension hG KuennethOne.kuenneth_injective)
        R B hB _ hN (pf _ hN) ?_ ?_ F g Z π f'⟩
    · rw [triv_pull_comp_iff]
      refine face _ 1 (B.hom ≫ j ≫ A.hom) ?_
      rw [Category.assoc, q₁, ← Category.assoc, ← Over.comp_left, lift_snd]
      exact one B
    · rw [triv_pull_comp_iff]
      refine face _ 0 (B.hom ≫ j ≫ A.hom) ?_
      rw [Category.assoc, q₀, ← Category.assoc, ← Over.comp_left, lift_fst]
      exact one B)
  have hclopen : IsClopen (fibTriv M φ ε (x3 A 2).left) :=
    ⟨H.2, by rw [H.1.antisymm (locTriv_subset _ _ _ _)]; exact isOpen_locTriv _ _ _ _⟩
  have all : ∀ t, t ∈ fibTriv M φ ε (x3 A 2).left := fun t => by
    have hr : Set.range (S.fromSpecResidueField (A.hom t)) = {A.hom t} := Scheme.range_fromSpecResidueField _
    obtain ⟨y, hy⟩ := hr.ge rfl
    let g := S.fromSpecResidueField (A.hom t) ≫ η[A].left
    have gw : g ≫ A.hom = S.fromSpecResidueField (A.hom t) := by
      rw [Category.assoc, Over.w]; exact Category.comp_id _
    refine (A.hom.isConnected_preimage_singleton (A.hom t)).isPreconnected.subset_isClopen hclopen
      ⟨g y, (congrArg (fun m : Spec (S.residueField (A.hom t)) ⟶ S => m y) gw).trans hy, ?_⟩ rfl
    exact ⟨S.residueField (A.hom t), inferInstance, g, _, _, _, ⟨y, rfl⟩,
      IsPullback.of_hasPullback (x3 A 2).left g,
      face _ 2 (pullback.snd _ g ≫ S.fromSpecResidueField (A.hom t))
        (pullback.condition.trans (Category.assoc _ _ _).symm)⟩
  let e : A ⟶ G3 A := lift 1 (lift 1 (𝟙 _))
  have e₀ : e ≫ x3 A 0 = 1 := by simp [e, x3]
  have e₂ : e ≫ x3 A 2 = 𝟙 _ := by simp [e, x3]
  refine triv_of_local hM φ ε (x3 A 2).left e.left (congrArg (fun q => q.left) e₂)
    (fun Z b => formal _ (b ≫ A.hom) ?_) (fun V => ?_) (fun s => H.1 (all s))
  · rw [Category.assoc, ← Over.comp_left, e₀, Category.assoc]
    rfl
  · obtain ⟨q, hq, -⟩ := exists_cube_chart A V.ι
    have hB := isAb_baseChange hA (V.ι ≫ A.hom)
    refine ⟨_, q, _, hq, ?_⟩
    rw [← Over.w (snd _ _)]
    exact surj_comp (surj_snd hG hB _) (hG _ _ hB).2

variable {B : Over S} (F : A ⊗ A ⟶ B)

def fourPts {T : Over S} (x x' y : T ⟶ A) : Fin 4 → (T.left ⟶ B.left) :=
  ![(lift (x * x') y ≫ F).left, (lift x y ≫ F).left, (lift x' y ≫ F).left, (lift 1 y ≫ F).left]

theorem comp_fourPts {T T' : Over S} (r : T' ⟶ T) (x x' y : T ⟶ A) (i : Fin 4) :
    r.left ≫ fourPts F x x' y i = fourPts F (r ≫ x) (r ≫ x') (r ≫ y) i := by
  fin_cases i <;>
  · simp only [fourPts, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val]
    rw [← Over.comp_left, ← Category.assoc, comp_lift]
    try simp only [MonObj.comp_mul, MonObj.comp_one]

theorem exists_over {Z : Scheme.{0}} (r : Z ⟶ (G3 A).left) (i : Fin 3) (b : Z ⟶ S)
    (h : r ≫ (x3 A i).left = b ≫ η[A].left) :
    ∃ x : Over.mk (r ≫ (G3 A).hom) ⟶ G3 A, x.left = r ∧ x ≫ x3 A i = 1 := by
  have hb : b = r ≫ (G3 A).hom := by
    have := congrArg (· ≫ A.hom) h
    simp only [Category.assoc, Over.w] at this
    exact (this.trans (Category.comp_id _)).symm
  refine ⟨Over.homMk r rfl, rfl, ?_⟩
  apply Over.OverMorphism.ext
  rw [Hom.one_def]
  exact h.trans (by rw [hb]; rfl)

theorem prod_fourPts {T : Over S} {x x' : T ⟶ A} (y : T ⟶ A) (h : x = 1 ∨ x' = 1)
    (U : Type) [CommGroup U] (k : (T.left ⟶ B.left) → U) :
    ∏ i, k (fourPts F x x' y i) ^ (![1, -1, -1, 1] : Fin 4 → ℤ) i = 1 := by
  rcases h with rfl | rfl
  · simp [Fin.prod_univ_four, fourPts, -Over.comp_left]
  · simp [Fin.prod_univ_four, fourPts, -Over.comp_left, mul_comm]

theorem triv_add (hG : Out.GlobalFnsSt) (hA : IsAbelianScheme A) {H₀ : LB A.left} (hH : H₀.IsLB)
    (hamp : Out.RelAmple A H₀) {M : LB B.left} (hM : M.IsLB)
    (h₁ : Triv (M.pull (lift (1 : A ⟶ A) (𝟙 A) ≫ F).left))
    (h₂ : Triv (M.pull (lift (𝟙 A) (1 : A ⟶ A) ≫ F).left)) {T : Over S} (x x' y : T ⟶ A) :
    Triv (LB.LinComb M (K := Fin 3)
      ![(lift (x * x') y ≫ F).left, (lift x y ≫ F).left, (lift x' y ≫ F).left] ![1, -1, -1]) := by
  have a₁ : ∀ {T : Over S} (y : T ⟶ A), Triv (M.pull (lift 1 y ≫ F).left) := fun y => by
    have := triv_pull_comp h₁ y.left
    rwa [← Over.comp_left, ← Category.assoc, comp_lift, MonObj.comp_one, Category.comp_id] at this
  have a₂ : ∀ {T : Over S} (y : T ⟶ A), Triv (M.pull (lift y 1 ≫ F).left) := fun y => by
    have := triv_pull_comp h₂ y.left
    rwa [← Over.comp_left, ← Category.assoc, comp_lift, MonObj.comp_one, Category.comp_id] at this
  have formal : ∀ {Z : Scheme.{0}} (r : Z ⟶ (G3 A).left) (i : Fin 3) (b : Z ⟶ S), i = 0 ∨ i = 1 →
      r ≫ (x3 A i).left = b ≫ η[A].left → ∀ (U : Type) [CommGroup U] (k : (Z ⟶ B.left) → U),
        ∏ i, k (r ≫ fourPts F (x3 A 0) (x3 A 1) (x3 A 2) i) ^ (![1, -1, -1, 1] : Fin 4 → ℤ) i = 1 := by
    intro Z r i b hi h U _ k
    obtain ⟨w, hw, h'⟩ := exists_over r i b h
    have := prod_fourPts F (x := w ≫ x3 A 0) (x' := w ≫ x3 A 1) (w ≫ x3 A 2)
      (hi.imp (fun e => e ▸ h') (fun e => e ▸ h')) U k
    simp only [← comp_fourPts, hw] at this
    exact this
  have cube := triv_of_faces hG hA hH hamp hM (fourPts F (x3 A 0) (x3 A 1) (x3 A 2)) ![1, -1, -1, 1]
    (fun r i b h => by
      by_cases hi : i = 0 ∨ i = 1
      · exact trivAt_of_formal hM r (formal r i b hi h)
      · obtain rfl : i = 2 := by omega
        obtain ⟨w, hw, h'⟩ := exists_over r 2 b h
        have e : (fun k => r ≫ fourPts F (x3 A 0) (x3 A 1) (x3 A 2) k) =
            fourPts F (w ≫ x3 A 0) (w ≫ x3 A 1) 1 := funext fun k => by
          rw [← h', ← comp_fourPts, hw]
        unfold TrivAt
        rw [e]
        refine triv_of_formal hM (triv_mul (triv_mul (a₂ (w ≫ x3 A 0 * w ≫ x3 A 1)) (triv_inv (a₂ (w ≫ x3 A 0))))
          (triv_mul (triv_inv (a₂ (w ≫ x3 A 1))) (a₂ (T := Over.mk (r ≫ (G3 A).hom)) 1))) fun U _ k => ?_
        simp [Fin.prod_univ_four, fourPts, -Over.comp_left, Fintype.prod_sum_type, _root_.mul_assoc])
    (fun r b h => formal r 0 b (Or.inl rfl) h)
  have c₀ : TrivAt M (fourPts F (x3 A 0) (x3 A 1) (x3 A 2)) ![1, -1, -1, 1] (lift x (lift x' y)).left := by
    obtain ⟨t, ht⟩ := cube
    exact ⟨_, DVR.pullGen_isGen _ _ _ t ht _⟩
  have e : (fun k => (lift x (lift x' y)).left ≫ fourPts F (x3 A 0) (x3 A 1) (x3 A 2) k) =
      fourPts F x x' y := funext fun k => by
    rw [comp_fourPts]
    simp [x3]
  unfold TrivAt at c₀
  rw [e] at c₀
  refine triv_of_formal hM (triv_mul c₀ (triv_inv (a₁ y))) fun U _ k => ?_
  simp [Fin.prod_univ_four, Fin.prod_univ_three, fourPts, -Over.comp_left, Fintype.prod_sum_type]

end Cube

theorem biadditive_of_triv_axes :
    Out.GlobalFnsSt → ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (H₀ : LB A.left), IsAbelianScheme A → H₀.IsLB → Out.RelAmple A H₀ → ∀ (Pb : LB (G2 A).left), Pb.IsLB → (∃ t : (Pb.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (Pb.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → ∀ (T : Over S) (x x' y : T ⟶ A), (∃ t : (LB.LinComb Pb (K := Fin 3) ![(lift (x * x') y).left, (lift x y).left, (lift x' y).left] ![1, -1, -1]).Gen, t.IsGen) ∧ ∃ t : (LB.LinComb Pb (K := Fin 3) ![(lift y (x * x')).left, (lift y x).left, (lift y x').left] ![1, -1, -1]).Gen, t.IsGen := by
  intro hG S A _ _ H₀ hA hH hamp Pb hP h₁ h₂ T x x' y
  constructor
  · have := triv_add (𝟙 (A ⊗ A)) hG hA hH hamp hP (by rw [Category.comp_id]; exact h₁)
      (by rw [Category.comp_id]; exact h₂) x x' y
    simp only [Category.comp_id] at this
    exact this
  · have sw : ∀ {T : Over S} (a b : T ⟶ A), lift a b ≫ lift (snd A A) (fst A A) = lift b a := fun a b => by
      rw [comp_lift, lift_snd, lift_fst]
    have := triv_add (lift (snd A A) (fst A A)) hG hA hH hamp hP (by rw [sw]; exact h₂)
      (by rw [sw]; exact h₁) x x' y
    simp only [sw] at this
    exact this

end GlobalTheory.Biadditive
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.BiadditiveOfTrivAxesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.biadditive_of_trivial_on_axes : Out.GlobalFnsSt → ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (H₀ : LB A.left), IsAbelianScheme A → H₀.IsLB → Out.RelAmple A H₀ → ∀ (Pb : LB (G2 A).left), Pb.IsLB → (∃ t : (Pb.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (Pb.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → ∀ (T : Over S) (x x' y : T ⟶ A), (∃ t : (LB.LinComb Pb (K := Fin 3) ![(lift (x * x') y).left, (lift x y).left, (lift x' y).left] ![1, -1, -1]).Gen, t.IsGen) ∧ ∃ t : (LB.LinComb Pb (K := Fin 3) ![(lift y (x * x')).left, (lift y x).left, (lift y x').left] ![1, -1, -1]).Gen, t.IsGen := by
  first | exact @GlobalTheory.Biadditive.biadditive_of_triv_axes | exact GlobalTheory.Biadditive.biadditive_of_triv_axes | (intros; apply GlobalTheory.Biadditive.biadditive_of_triv_axes <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPrePullbackPrincipalRingChange
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPrePullbackPrincipalRingChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.SiegelRingChange

variable {h k : ℕ} {B B' : Type} [CommRing B] [CommRing B'] {ζ : B} {ζ' : B'} {S : Scheme.{0}}

theorem spMap_comp' {R₁ R₂ R₃ : Type} [CommRing R₁] [CommRing R₂] [CommRing R₃] (a : R₁ →+* R₂) (b : R₂ →+* R₃) :
    spMap (b.comp a) = spMap b ≫ spMap a := by
  simp only [spMap, ← Spec.map_comp]
  rfl

theorem exists_spMap {R₁ R₂ : Type} [CommRing R₁] [CommRing R₂] (x : Sp R₂ ⟶ Sp R₁) :
    ∃ a : R₁ →+* R₂, spMap a = x := by
  obtain ⟨a, ha⟩ := Spec.map_surjective x
  exact ⟨a.hom, ha⟩

theorem spMap_inj {R₁ R₂ : Type} [CommRing R₁] [CommRing R₂] {a b : R₁ →+* R₂} (e : spMap a = spMap b) : a = b := by
  have := Spec.map_injective e
  exact congrArg CommRingCat.Hom.hom this

def down (j : B →+* B') (hj : j ζ = ζ') {s' : S ⟶ Sp B'} (c : SiegPre h k ζ' s') : SiegPre h k ζ (s' ≫ spMap j) :=
  { A := c.A, ab := c.ab, P := c.P, isLB := c.isLB, rig₁ := c.rig₁, rig₂ := c.rig₂, symm := c.symm
    lev := c.lev, lev_add := c.lev_add, lev_tors := c.lev_tors
    geom := fun K _ _ x β z hx hz => by
      obtain ⟨β', hβ'⟩ := exists_spMap (x ≫ s')
      have e : β'.comp j = β := by
        apply spMap_inj
        rw [spMap_comp', hβ', Category.assoc, hx]
      refine c.geom K x β' z hβ'.symm ?_
      rw [hz, ← e, ← hj]; rfl }

def up (j : B →+* B') (hj : j ζ = ζ') {s' : S ⟶ Sp B'} (c : SiegPre h k ζ (s' ≫ spMap j)) : SiegPre h k ζ' s' :=
  { A := c.A, ab := c.ab, P := c.P, isLB := c.isLB, rig₁ := c.rig₁, rig₂ := c.rig₂, symm := c.symm
    lev := c.lev, lev_add := c.lev_add, lev_tors := c.lev_tors
    geom := fun K _ _ x β z hx hz => by
      refine c.geom K x (β.comp j) z ?_ ?_
      · rw [spMap_comp', ← hx, Category.assoc]
      · rw [hz, ← hj]; rfl }

theorem siegPre_pull_ringChange : ∀ (h k : ℕ) (B B' : Type) [CommRing B] [CommRing B'] (ζ : B) (ζ' : B') (j : B →+* B') (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (f : S' ⟶ S), j ζ = ζ' → f ≫ s = s' ≫ spMap j → (∀ c : SiegPre h k ζ s, ∃ c' : SiegPre h k ζ' s', SiegPB c' c f) ∧ (∀ (c : SiegPre h k ζ s) (c' : SiegPre h k ζ' s'), SiegPB c' c f → c.Principal → c'.Principal) ∧ ∀ c' : SiegPre h k ζ' s', ∃ c₀ : SiegPre h k ζ (s' ≫ spMap j), SiegPB c' c₀ (𝟙 _) ∧ SiegPB c₀ c' (𝟙 _) := by
  intro h k B B' _ _ ζ ζ' j S S' s s' f hj hf
  refine ⟨fun c => ?_, fun c c' hc hp => ?_, fun c' => ?_⟩
  · obtain ⟨c₀, h₀⟩ := (GlobalTheory.T.siegelObject_pullback_exists_and_principal h k B ζ S S' s _ f c hf).1
    exact ⟨up j hj c₀, h₀⟩
  · exact (GlobalTheory.T.siegelObject_pullback_exists_and_principal h k B ζ S S' s _ f c hf).2 (down j hj c') hc hp
  · have e := (GlobalTheory.T.siegelPullback_id_comp_cancel h k B' B' B' ζ' ζ' ζ' S' S' S' s' s' s' c' c' c' (𝟙 _) (𝟙 _)).1
    exact ⟨down j hj c', e, e⟩

end GlobalTheory.SiegelRingChange
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelPrePullbackPrincipalRingChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelPre_pullback_principal_ringChange : ∀ (h k : ℕ) (B B' : Type) [CommRing B] [CommRing B'] (ζ : B) (ζ' : B') (j : B →+* B') (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (f : S' ⟶ S), j ζ = ζ' → f ≫ s = s' ≫ spMap j → (∀ c : SiegPre h k ζ s, ∃ c' : SiegPre h k ζ' s', SiegPB c' c f) ∧ (∀ (c : SiegPre h k ζ s) (c' : SiegPre h k ζ' s'), SiegPB c' c f → c.Principal → c'.Principal) ∧ ∀ c' : SiegPre h k ζ' s', ∃ c₀ : SiegPre h k ζ (s' ≫ spMap j), SiegPB c' c₀ (𝟙 _) ∧ SiegPB c₀ c' (𝟙 _) := by
  first | exact @GlobalTheory.SiegelRingChange.siegPre_pull_ringChange | exact GlobalTheory.SiegelRingChange.siegPre_pull_ringChange | (intros; apply GlobalTheory.SiegelRingChange.siegPre_pull_ringChange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.EventuallySectionAndRelAmplePowDiv
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.EventuallySectionAndRelAmplePowDiv
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV

namespace GlobalTheory.AmpleDominates

open GlobalTheory.CechPic GlobalTheory.AbLaw

variable {X : Scheme.{0}} {M N : LB X}

theorem eventually_isGenerated {R : Type} [CommRing R] (f : X ⟶ Sp R) [IsProper f] (hM : IsAmpleLB M)
    (hN : N.IsLB) : ∀ᶠ t : ℕ in Filter.atTop, IsGenerated (LB.div (lbPow M t) N) := by
  obtain ⟨d, hd, m, s, hs⟩ := hM.exists_veryAmpleBy f
  have hH := isLB_lbPow hM.isLB d
  have hD : ∀ i, (LB.div (lbPow M i) N).IsLB := fun i => LB.isLB_div (isLB_lbPow hM.isLB i) hN
  choose t₀ ht₀ using fun i => TwistGen.twist_generated R X f _ m s hH hs _ (hD i)
  refine Filter.eventually_atTop.2 ⟨d * (Finset.range d).sup fun i => (t₀ i).toNat, fun t ht => ?_⟩
  have h₁ : (t₀ (t % d)).toNat ≤ t / d :=
    (Finset.le_sup (f := fun i => (t₀ i).toNat) (Finset.mem_range.2 (Nat.mod_lt t hd))).trans
      ((Nat.le_div_iff_mul_le hd).2 (by rwa [Nat.mul_comm]))
  obtain ⟨n, u, hu⟩ := ht₀ (t % d) (t / d : ℕ) (Int.toNat_le.1 h₁)
  have hG : IsGenerated (tw (LB.div (lbPow M (t % d)) N) (lbPow M d) (t / d : ℕ)) := ⟨_, u, hu⟩
  refine hG.of_lbIso (hD t) ((cls_eq_iff (hD t) hG.isLB).1 ?_)
  have e : cls _ hG.isLB = cls _ (hD (t % d)) - cls _ (isLB_pw hH (-((t / d : ℕ) : ℤ))) :=
    cls_div (hD _) (isLB_pw hH _) _
  rw [e, AmpleStabFinite.cls_pw hH, cls_div (isLB_lbPow hM.isLB t) hN, cls_div (isLB_lbPow hM.isLB _) hN,
    cls_lbPow hM.isLB, cls_lbPow hM.isLB, cls_lbPow hM.isLB]
  generalize cls M hM.isLB = a
  generalize cls N hN = b
  conv_lhs => rw [← Nat.mod_add_div t d]
  simp only [add_nsmul, mul_nsmul, neg_zsmul, natCast_zsmul]
  abel

theorem eventually_isAmpleLB {R : Type} [CommRing R] (f : X ⟶ Sp R) [IsProper f] (hM : IsAmpleLB M)
    (hN : N.IsLB) : ∀ᶠ t : ℕ in Filter.atTop, IsAmpleLB (LB.div (lbPow M t) N) := by
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.1 (eventually_isGenerated f hM hN)
  refine Filter.eventually_atTop.2 ⟨a + 1, fun t ht => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
  have hG := ha k (by omega)
  have h₀ := LB.isLB_div (isLB_lbPow hM.isLB (k + 1)) hN
  have h₁ := LB.isLB_div h₀ hM.isLB
  refine hM.tensor_isGenerated hG h₀ ((cls_eq_zero_iff (LB.isLB_div h₁ hG.isLB)).1 ?_)
  rw [cls_div h₁ hG.isLB, cls_div h₀ hM.isLB, cls_div (isLB_lbPow hM.isLB _) hN,
    cls_div (isLB_lbPow hM.isLB _) hN, cls_lbPow hM.isLB, cls_lbPow hM.isLB]
  simp only [add_nsmul, one_nsmul]
  abel

theorem exists_sec_ne_zero [Nonempty X] {L : LB X} (h : IsGenerated L) : ∃ s : L.Sec, ∃ j, s.f j ≠ 0 := by
  obtain ⟨s, hs⟩ := h.exists_mem (Classical.arbitrary X)
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hs
  refine ⟨s, j, fun e => ?_⟩
  rw [e, Scheme.basicOpen_zero] at hj
  exact hj

theorem eventually_sec_and_relAmple : ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (M N : LB P.A.left), M.IsLB → N.IsLB → Out.RelAmple P.A M → ∀ᶠ t : ℕ in Filter.atTop, (∃ s : (LB.div (lbPow M t) N).Sec, ∃ j, s.f j ≠ 0) ∧ Out.RelAmple P.A (LB.div (lbPow M t) N) := by
  intro K _ _ P M N hM hN h
  have := P.isAb.proper
  have := polAV_isIntegral_of_isAlgClosed K P
  have hA := isAmpleLB_of_relAmple_of_isAffine P.A hM h
  filter_upwards [eventually_isGenerated P.A.hom hA hN, eventually_isAmpleLB P.A.hom hA hN] with t h₁ h₂
  exact ⟨exists_sec_ne_zero h₁, (relAmple_iff_isAmpleLB_of_isAffine P.A h₂.isLB).2 h₂⟩

end GlobalTheory.AmpleDominates
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.EventuallySectionAndRelAmplePowDivStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV
theorem _root_.GlobalTheory.T.eventually_section_and_relAmple_pow_div : ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (M N : LB P.A.left), M.IsLB → N.IsLB → Out.RelAmple P.A M → ∀ᶠ t : ℕ in Filter.atTop, (∃ s : (LB.div (lbPow M t) N).Sec, ∃ j, s.f j ≠ 0) ∧ Out.RelAmple P.A (LB.div (lbPow M t) N) := by
  first | exact @GlobalTheory.AmpleDominates.eventually_sec_and_relAmple | exact GlobalTheory.AmpleDominates.eventually_sec_and_relAmple | (intros; apply GlobalTheory.AmpleDominates.eventually_sec_and_relAmple <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverBaseChangeAndFiniteRestrict
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory

theorem isQProjOver_of_isPullback_spMap {R R' : Type} [CommRing R] [CommRing R'] (j : R →+* R') {Y Y' : Scheme.{0}}
    {s : Y ⟶ Sp R} {p : Y' ⟶ Y} {s' : Y' ⟶ Sp R'} (sq : IsPullback p s' s (spMap j)) (h : IsQProjOver s) :
    IsQProjOver s' := by
  obtain ⟨N, i, hi, hq, rfl⟩ := h
  have P := ProjSpace.isPullback_baseChange N j
  have w : (p ≫ i) ≫ PSpace.str R N = s' ≫ spMap j := by rw [Category.assoc]; exact sq.w
  have Q : IsPullback p (P.lift (p ≫ i) s' w) i (ProjSpace.baseChange N j) :=
    IsPullback.of_bot (by rw [P.lift_snd]; exact sq) (P.lift_fst _ _ w).symm P
  exact ⟨N, P.lift (p ≫ i) s' w, MorphismProperty.of_isPullback (P := @IsImmersion) Q hi,
    MorphismProperty.of_isPullback (P := @QuasiCompact) Q hq, P.lift_snd _ _ w⟩

theorem isQProjOver_comp_spMap_of_finiteType {R R' : Type} [CommRing R] [CommRing R'] {j : R →+* R'}
    (hj : j.FiniteType) {Y : Scheme.{0}} {s' : Y ⟶ Sp R'} (h : IsQProjOver s') : IsQProjOver (s' ≫ spMap j) := by
  obtain ⟨N, i, _, _, rfl⟩ := h
  have := isProper_str R' N
  have : LocallyOfFiniteType (spMap j) := HasRingHomProperty.Spec_iff.2 hj
  exact ((isAmple_projective_O_one R' N).pull_of_isImmersion i).isQProjOver _

theorem isQProjOver_baseChange_and_finite_restrict :
    ∀ (R R' : Type) [CommRing R] [CommRing R'] (j : R →+* R') (Y : Scheme.{0}) (s : Y ⟶ Sp R),
      (IsQProjOver s → IsQProjOver (pullback.snd s (spMap j))) ∧
        ∀ s' : Y ⟶ Sp R', j.Finite → IsQProjOver s' → IsQProjOver (s' ≫ spMap j) :=
  fun _ _ _ _ j _ _ => ⟨fun h => isQProjOver_of_isPullback_spMap j (IsPullback.of_hasPullback _ _) h,
    fun _ hj h => isQProjOver_comp_spMap_of_finiteType hj.finiteType h⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.MapToUniversalObjectUnique
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.MapToUniversalObjectUnique
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.LevUniq

theorem exists_sab_cast {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}}
    {t : SAB H S} {t' : SAB H S'} {f g : S' ⟶ S} (m : SABMap t' t f) (h : f = g) :
    ∃ n : SABMap t' t g, n.φ = m.φ := by
  subst h
  exact ⟨m, rfl⟩

theorem map_to_univ_unique : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l₀ l : Level H) (Xo : Moduli D l₀) (B : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s) (r r' : S ⟶ Xo.X) (ν : SABMap o.t Xo.univ.t r) (ν' : SABMap o.t Xo.univ.t r'), IsReduced S → r ≫ Xo.s = r' ≫ Xo.s → LevComp o Xo.univ r ν → LevComp o Xo.univ r' ν' → r = r' ∧ ν.φ = ν'.φ := by
  intro hL _ _ E _ _ _ H D l₀ l Xo B _ b S s o r r' ν ν' hS hs hν hν'
  obtain ⟨o₁, ⟨m₁⟩⟩ := obj_pull E H D l₀ (KA l₀) (KA l₀) (baseKA l₀) (baseKA l₀) (RingHom.id _) Xo.X S Xo.s
    (r ≫ Xo.s) r rfl rfl (by
      rw [show spMap (RingHom.id (KA l₀)) = 𝟙 (Sp (KA l₀)) from Spec.map_id _, Category.comp_id]) Xo.univ
  obtain ⟨n₁, hn₁⟩ := exists_sab_cast m₁.toSABMap (Category.id_comp r).symm
  obtain ⟨k, hk⟩ := ObjMaps.exists_sab_cancel ν n₁
  have hk' : m₁.toSABMap.φ = k.φ ≫ ν.φ := hn₁.symm.trans hk
  have pk : IsPullback k.φ o₁.t.G.hom o.t.G.hom (𝟙 S) := k.cart.1
  have pν : IsPullback ν.φ o.t.G.hom Xo.univ.t.G.hom r := ν.cart.1
  have key : ∀ (x : 𝟙_ (Over S) ⟶ o₁.t.G) (y : 𝟙_ (Over S) ⟶ o.t.G),
      x.left ≫ m₁.toSABMap.φ = y.left ≫ ν.φ → x.left ≫ k.φ = y.left := by
    intro x y h
    refine pν.hom_ext ?_ ?_
    · rw [Category.assoc, ← hk', h]
    · rw [Category.assoc, pk.w, Category.comp_id, Over.w x, Over.w y]
  obtain ⟨n₂, hn₂⟩ := ObjMaps.exists_sab_comp ν' k
  obtain ⟨n₃, hn₃⟩ := exists_sab_cast n₂ (Category.id_comp r')
  have h₃ : n₃.φ = k.φ ≫ ν'.φ := hn₃.trans hn₂
  have e₁ : ∀ a, (o₁.eta a).left ≫ n₃.φ = r' ≫ (Xo.univ.eta a).left := by
    intro a
    rw [h₃, ← Category.assoc, key _ _ ((m₁.eta a).trans (hν.1 a).symm), hν'.1 a]
  have e₂ : ∀ a, (o₁.etaA a).left ≫ n₃.φ = r' ≫ (Xo.univ.etaA a).left := by
    intro a
    rw [h₃, ← Category.assoc, key _ _ ((m₁.etaA a).trans (hν.2 a).symm), hν'.2 a]
  have hr : r = r' := (Xo.rep S (r ≫ Xo.s) hS o₁).unique ⟨rfl, ⟨m₁⟩⟩ ⟨hs.symm, ⟨⟨n₃, e₁, e₂⟩⟩⟩
  subst hr
  refine ⟨rfl, ?_⟩
  have hφ : m₁.toSABMap.φ = n₃.φ :=
    obj_rigid_closed hL E H D l₀ (KA l₀) (KA l₀) (baseKA l₀) (baseKA l₀) Xo.X S Xo.s (r ≫ Xo.s) Xo.univ o₁ r
      (Or.inl hS) m₁.toSABMap n₃ (fun a => ⟨_, m₁.eta a, e₁ a⟩)
  have : IsIso k.φ := pk.isIso_fst_of_isIso
  rw [← cancel_epi k.φ, ← hk', ← h₃, hφ]

end GlobalTheory.LevUniq
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.MapToUniversalObjectUniqueStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.map_to_universalObject_unique : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l₀ l : Level H) (Xo : Moduli D l₀) (B : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s) (r r' : S ⟶ Xo.X) (ν : SABMap o.t Xo.univ.t r) (ν' : SABMap o.t Xo.univ.t r'), IsReduced S → r ≫ Xo.s = r' ≫ Xo.s → LevComp o Xo.univ r ν → LevComp o Xo.univ r' ν' → r = r' ∧ ν.φ = ν'.φ := by
  first | exact @GlobalTheory.LevUniq.map_to_univ_unique | exact GlobalTheory.LevUniq.map_to_univ_unique | (intros; apply GlobalTheory.LevUniq.map_to_univ_unique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubicalBundlePairingCompatiblePullback
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubicalBundlePairingCompatiblePullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem cubV_of_pmaps {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] [IsCommMonObj G] {G' : Over S'}
    [GrpObj G'] [IsCommMonObj G'] (m : CubeMap G' G) (hw : m.F ≫ G.hom = G'.hom ≫ f) {L : RigLB G} {L' : RigLB G'}
    {c : CubicalStr G L} {c' : CubicalStr G' L'} {w : LB.Iso L'.L (L.L.pull m.F)}
    (H : PMaps w (thφ G' (x3 G')) (thφ G (x3 G)) thε c'.t c.t m.F3) {T : Over S'} {z : T.left} {J J'}
    (hJ : Good L.L z J) (hJ' : Good L'.L z J') (a b d : T ⟶ G') :
    @id (T.left.presheaf.stalk z)ˣ (cubV c (T := Over.mk (T.hom ≫ f)) z J (Out.toBase hw a) (Out.toBase hw b)
      (Out.toBase hw d)) =
      (∏ I : thK.{0}, (fun q => gw w q z (J (q ≫ m.F)) (J' q)) ((lift a (lift b d)).left ≫ thφ G' (x3 G') I) ^ thε I) *
        cubV c' z J' a b d := by
  have co : ∀ i : Fin 3, m.F3 ≫ (x3 G i).left = (x3 G' i).left ≫ m.F := fun i => by
    have h := m.psum_comm {i}
    rw [psum_single, psum_single] at h
    exact h.symm
  have q : (lift a (lift b d)).left ≫ m.F3 =
      (lift (Out.toBase hw a) (lift (Out.toBase hw b) (Out.toBase hw d))).left := hom_ext_triple _ fun i => by
    rw [Category.assoc, co, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
    fin_cases i <;> simp [x3] <;> rfl
  have e := H _ (lift a (lift b d)).left z (fun I => J (((lift a (lift b d)).left ≫ thφ G' (x3 G') I) ≫ m.F))
    (fun I => J' ((lift a (lift b d)).left ≫ thφ G' (x3 G') I)) (fun I => hJ _) (fun I => hJ' _)
  refine Eq.trans ?_ e
  refine (congrArg (fun r => val (L := L.L) (φ := thφ G (x3 G)) (ε := thε) c.t r z J) q.symm).trans ?_
  refine val_of _ _ _ _ _ fun I => congrArg J ?_
  rw [Category.assoc, Category.assoc]
  exact congrArg _ (m.psum_comm I.down).symm

theorem cubWeil_of_isPullCubical : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] (G' : Over S') [GrpObj G'] [IsCommMonObj G'] (m : CubeMap G' G) (hw : m.F ≫ G.hom = G'.hom ≫ f), (∀ (T : Over S') (x y : T ⟶ G'), Out.toBase hw (x * y) = Out.toBase hw x * Out.toBase hw y) → ∀ (L : RigLB G) (L' : RigLB G') (c : CubicalStr G L) (c' : CubicalStr G' L'), m.IsPullCubical c' c → ∀ (N : ℕ) (T : Over S') (x y : T ⟶ G') (ζ : Γ(T.left, ⊤)ˣ), CubWeil c' N x y ζ → CubWeil c N (Out.toBase hw x) (Out.toBase hw y) ζ := by
  intro S S' f G _ _ G' _ _ m hw mul L L' c c' h N T x y ζ hζ
  obtain ⟨w, -, -, H⟩ := (isPullCubical_iff m c c').1 h
  let β := toBaseHom mul T
  refine ⟨(map_pow β x N).symm.trans ((congrArg β hζ.1).trans (map_one β)),
    (map_pow β y N).symm.trans ((congrArg β hζ.2.1).trans (map_one β)), fun z J hJ => ?_⟩
  obtain ⟨J', hJ'⟩ := exists_good_pt L'.isLB (Z := T.left) z
  obtain ⟨W, hW⟩ : ∃ W : (T.left ⟶ G'.left) → (T.left.presheaf.stalk z)ˣ,
    W = fun q => gw w q z (J (q ≫ m.F)) (J' q) := ⟨_, rfl⟩
  let θ : (Over.mk (T.hom ≫ f) ⟶ G) → (Over.mk (T.hom ≫ f) ⟶ G) → (Over.mk (T.hom ≫ f) ⟶ G) →
    (T.left.presheaf.stalk z)ˣ := cubV c (T := Over.mk (T.hom ≫ f)) z J
  have a' : ∀ a b d : T ⟶ G', θ (β a) (β b) (β d) * W (a * b).left * W (a * d).left * W (b * d).left *
      W (1 : T ⟶ G').left = W (a * b * d).left * W a.left * W b.left * W d.left * cubV c' z J' a b d := by
    intro a b d
    have e := (cubV_of_pmaps m hw H (T := T) (z := z) hJ hJ' a b d).trans (congrArg₂ (· * ·)
      ((congrArg (fun V : (T.left ⟶ G'.left) → (T.left.presheaf.stalk z)ˣ =>
        ∏ I : thK.{0}, V ((lift a (lift b d)).left ≫ thφ G' (x3 G') I) ^ thε I) hW.symm).trans (prod_cub a b d W)) rfl)
    have e' : θ (β a) (β b) (β d) = _ := e
    rw [e']
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  exact cubN_ratio_twist β (fun x => W x.left) a' hζ.1 hζ.2.1 (hζ.2.2 z J' hJ')

end GlobalTheory.UU
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubicalBundlePairingCompatiblePullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cubicalBundlePairing_compatible_pullback : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] (G' : Over S') [GrpObj G'] [IsCommMonObj G'] (m : CubeMap G' G) (hw : m.F ≫ G.hom = G'.hom ≫ f), (∀ (T : Over S') (x y : T ⟶ G'), Out.toBase hw (x * y) = Out.toBase hw x * Out.toBase hw y) → ∀ (L : RigLB G) (L' : RigLB G') (c : CubicalStr G L) (c' : CubicalStr G' L'), m.IsPullCubical c' c → ∀ (N : ℕ) (T : Over S') (x y : T ⟶ G') (ζ : Γ(T.left, ⊤)ˣ), CubWeil c' N x y ζ → CubWeil c N (Out.toBase hw x) (Out.toBase hw y) ζ := by
  first | exact @GlobalTheory.UU.cubWeil_of_isPullCubical | exact GlobalTheory.UU.cubWeil_of_isPullCubical | (intros; apply GlobalTheory.UU.cubWeil_of_isPullCubical <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasFramesOfAmpFrames
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.LN

noncomputable section

namespace GlobalTheory.ModelSum

theorem image_inf_le {Z' Z : Scheme.{0}} (f : Z' ⟶ Z) [IsOpenImmersion f] (U V : Z'.Opens) :
    f ''ᵁ U ⊓ f ''ᵁ V ≤ f ''ᵁ (U ⊓ V) := by

  rintro x ⟨⟨a, ha, rfl⟩, ⟨b, hb, hba⟩⟩
  obtain rfl : b = a := f.isOpenEmbedding.injective hba
  exact ⟨b, ⟨ha, hb⟩, rfl⟩

def pushLB {Z' Z : Scheme.{0}} (f : Z' ⟶ Z) [IsOpenImmersion f] (A : LB Z') : LB Z :=
  ⟨A.ι, fun i => f ''ᵁ A.U i, fun i j => res (image_inf_le f (A.U i) (A.U j))
    (Units.map (f.appIso (A.U i ⊓ A.U j)).inv.hom.toMonoidHom (A.g i j))⟩

def sumLB {Z : Scheme.{0}} (A B : LB Z) : LB Z :=
  ⟨A.ι ⊕ B.ι, Sum.elim A.U B.U, fun p q => match p, q with
    | .inl i, .inl j => A.g i j
    | .inr i, .inr j => B.g i j
    | .inl _, .inr _ => 1
    | .inr _, .inl _ => 1⟩

def AmpleFam {Z : Scheme.{0}} (A : LB Z) : Prop :=
  ∀ z : Z, ∃ (d : ℕ) (s : H0 A d), 1 ≤ d ∧ z ∈ nonzeroLocus s ∧ IsAffineOpen (nonzeroLocus s)

def HasFrames {Z : Scheme.{0}} (G : Over Z) (L : LB G.left) (N : ℕ) (A : LB Z) (n : ℕ) (r s : ℤ) : Prop :=
  ∃ (th : ∀ i : A.ι, LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk (A.U i).ι)))
    (b : ∀ i : A.ι, Fin n → LB.Sec (LPow G L (N : ℤ) (Over.mk (A.U i).ι))),
  (∀ i j : A.ι, ∃ (c : Γ((A.U i ⊓ A.U j).toScheme, ⊤)ˣ) (M : GL (Fin n) Γ((A.U i ⊓ A.U j).toScheme, ⊤)),
    (∃ t, Lin G L 1 (Over.homMk (Z.homOfLE inf_le_left) (by simp) : Over.mk (A.U i ⊓ A.U j).ι ⟶ Over.mk (A.U i).ι)
        (fun _ : Fin 1 => th i) (fun _ => 1) t ∧
      Lin G L 1 (Over.homMk (Z.homOfLE inf_le_right) (by simp) : Over.mk (A.U i ⊓ A.U j).ι ⟶ Over.mk (A.U j).ι)
        (fun _ : Fin 1 => th j) (fun _ => c.val) t) ∧
    (∀ k, ∃ t, Lin G L N (Over.homMk (Z.homOfLE inf_le_left) (by simp) : Over.mk (A.U i ⊓ A.U j).ι ⟶ Over.mk (A.U i).ι)
        (fun _ : Fin 1 => b i k) (fun _ => 1) t ∧
      Lin G L N (Over.homMk (Z.homOfLE inf_le_right) (by simp) : Over.mk (A.U i ⊓ A.U j).ι ⟶ Over.mk (A.U j).ι)
        (b j) (fun k' => M.val k k') t) ∧
    (A.U i ⊓ A.U j).topIso.inv.hom (A.g i j).val = (c ^ r * Matrix.GeneralLinearGroup.det M ^ s).val) ∧
  ∀ (i : A.ι) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ χ : Sp W ⟶ (A.U i).toScheme,
    Set.range (jK W ≫ χ ≫ (A.U i).ι) ⊆ abLocus G →
    BasisAlong G L 1 (Over.homMk χ rfl : Over.mk (χ ≫ (A.U i).ι) ⟶ Over.mk (A.U i).ι) (fun _ : Fin 1 => th i) ∧
    BasisAlong G L N (Over.homMk χ rfl : Over.mk (χ ≫ (A.U i).ι) ⟶ Over.mk (A.U i).ι) (b i)

variable {Z : Scheme.{0}} {G : Over Z} {L : LB G.left} {N : ℕ}

theorem hasFrames_of_ampFrames (F : AmpFrames G L N) : HasFrames G L N F.A F.n F.r F.s := by
  refine ⟨F.th, F.b, ?_, ?_⟩
  · intro i j
    exact F.trans i j
  · intro i W _ _ _ hW χ hχ
    exact F.trait i W hW χ hχ

theorem exists_ampFrames {A : LB Z} {n : ℕ} {r s : ℤ} (hA : A.IsLB) (ha : AmpleFam A) (h : HasFrames G L N A n r s) :
    ∃ F : AmpFrames G L N, F.A = A ∧ F.n = n ∧ F.r = r ∧ F.s = s := by

  obtain ⟨th, b, htr, htrait⟩ := h
  exact ⟨⟨A, hA, ha, n, th, b, r, s, htr, htrait⟩, rfl, rfl, rfl, rfl⟩

end GlobalTheory.ModelSum

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjOverCompFinite
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjOverCompFinite
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

theorem isProjOver_comp_of_finite :
    ∀ (R : Type) [CommRing R] (X Y : Scheme.{0}) (f : Y ⟶ X) (s : X ⟶ Sp R), IsFinite f → IsProjOver s → IsProjOver (f ≫ s) := by
  intro R _ X Y f s hf hs
  exact GlobalTheory.isProjOver_comp_of_isFinite f hs

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjOverCompFiniteStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
theorem _root_.GlobalTheory.T.isProjOver_comp_finite : ∀ (R : Type) [CommRing R] (X Y : Scheme.{0}) (f : Y ⟶ X) (s : X ⟶ Sp R), IsFinite f → IsProjOver s → IsProjOver (f ≫ s) := by
  first | exact @GlobalTheory.isProjOver_comp_of_finite | exact GlobalTheory.isProjOver_comp_of_finite | (intros; apply GlobalTheory.isProjOver_comp_of_finite <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsTransitionUnique
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.TransitionUnique

open GlobalTheory.ModelCompare

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

theorem isReduced_XF (Xo : Moduli D l) (c : Coeff l) : IsReduced (Xo.XF c) :=
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _
    (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) inferInstance).1

theorem map_unique {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) {S : Scheme.{0}} [IsReduced S]
    {t : SAB H S} {r r' : S ⟶ Xo.XF c} (ν : SABMap t Y.oF.t r) (ν' : SABMap t Y.oF.t r')
    (hr : r ≫ pullback.snd _ _ = r' ≫ pullback.snd _ _)
    (hM : ∀ a, ∃ x : 𝟙_ (Over S) ⟶ t.G,
      x.left ≫ ν.φ = r ≫ (Y.oF.eta a).left ∧ x.left ≫ ν'.φ = r' ≫ (Y.oF.eta a).left)
    (hA : ∀ a, ∃ x : 𝟙_ (Over S) ⟶ t.G,
      x.left ≫ ν.φ = r ≫ (Y.oF.etaA a).left ∧ x.left ≫ ν'.φ = r' ≫ (Y.oF.etaA a).left) : r = r' := open GlobalTheory.ObjPull in by
  let o : Obj D l _ (r ≫ _) :=
    have hL : LBIso t.PP.L (Y.oF.t.PP.L.pull ν.cm.F) := by
      obtain ⟨w, hw, -⟩ := ν.lin
      exact ⟨w, hw⟩
    have hpr := Y.oF.proper
    have hp := GlobalTheory.PolPull.pol_pull_of_relAmple_local GlobalTheory.AmpleLocal.relAmple_of_locally
      (Xo.XF c) S Y.oF.t.G t.G r ν.cm.F Y.oF.t.PP.L t.PP.L Y.oF.t.PP.isLB t.PP.isLB
      (AbelianSchemeGerms.isAbelianScheme_of_proper Y.oF.t.G Y.oF.t.semi) ν.cart hL
    { t := t
      proper := MorphismProperty.of_isPullback (P := @IsProper) ν.cart.1 hpr
      ample := hp.2.1 Y.oF.ample
      ktriv := hp.2.2 Y.oF.ktriv
      eta := fun a => GlobalTheory.ObjPull.secPull ν.cart (Y.oF.eta a)
      eta_add := fun a c => by rw [Y.oF.eta_add, map_mul]
      eta_ker := fun a ha => by rw [Y.oF.eta_ker a ha, map_one]
      etaA := fun a => GlobalTheory.ObjPull.secPull ν.cart (Y.oF.etaA a)
      etaA_add := fun a c => by rw [Y.oF.etaA_add, map_mul]
      etaA_ker := fun a => by rw [Y.oF.etaA_ker a, map_one]
      geom := fun k _ _ x β hx => by
        obtain ⟨hdet, I, hI, hA, hM⟩ := Y.oF.geom k (x ≫ r) β (by rw [Category.assoc, hx])
        refine ⟨fun τ => ?_, tateMove (pushEquiv ν.cart (Over.mk x)) (fun c g => ?_) (fun n g g' u hc => ?_) I,
          hI, fun a => ?_, fun a ha => ?_⟩
        · rw [GlobalTheory.LiePull.lieMult_pull _ (Xo.XF c) S Y.oF.t.G t.G r ν.cm.F Y.oF.t.act t.act ν.cart ν.act k x τ,
            GlobalTheory.LiePull.lieMult_pull _ (Xo.XF c) S Y.oF.t.G t.G r ν.cm.F Y.oF.t.act t.act ν.cart ν.act k x τ]
          exact hdet τ
        · apply Over.OverMorphism.ext
          show (g.left ≫ _) ≫ _ = (g.left ≫ _) ≫ _
          rw [Category.assoc, ν.act, Category.assoc]
        · exact (GlobalTheory.weilIs_grpPullback_of_comm (Xo.XF c) S Y.oF.t.G t.G r ν.cm.F Y.oF.t.PP.L t.PP.L Y.oF.t.PP.isLB t.PP.isLB
            ν.cart hL (Over.mk x) n g g' _ _ _ rfl rfl).2 hc
        · exact (MulEquiv.eq_symm_apply _).2 ((pushEquiv_secPull ν.cart _ _).trans (hA a))
        · exact (MulEquiv.eq_symm_apply _).2 ((pushEquiv_secPull ν.cart _ _).trans (hM a ha)) }
  let n : ObjMap o Y.oF r := ⟨ν, fun _ => secPull_left ν.cart _, fun _ => secPull_left ν.cart _⟩
  have sec_eq {e : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G} {e' : 𝟙_ (Over S) ⟶ t.G}
      (h : e'.left ≫ ν.φ = r ≫ e.left) : e' = GlobalTheory.ObjPull.secPull ν.cart e := by
    apply Over.OverMorphism.ext
    apply ν.cart.1.hom_ext
    · exact h.trans (secPull_left ν.cart _).symm
    · rw [Over.w, Over.w]
  let n' : ObjMap o Y.oF r' := ⟨ν', fun a => by
      obtain ⟨x, h, h'⟩ := hM a
      exact (congrArg (fun z => z.left ≫ ν'.φ) (sec_eq h)).symm.trans h', fun a => by
      obtain ⟨x, h, h'⟩ := hA a
      exact (congrArg (fun z => z.left ≫ ν'.φ) (sec_eq h)).symm.trans h'⟩
  obtain ⟨k, -⟩ := ObjComp.objMap_comp Y.m0 n
  obtain ⟨k', -⟩ := ObjComp.objMap_comp Y.m0 n'
  refine pullback.hom_ext ((Xo.rep S _ ‹_› o).unique ⟨Category.assoc _ _ _, ⟨k⟩⟩ ⟨?_, ⟨k'⟩⟩) hr
  rw [Category.assoc, pullback.condition, ← Category.assoc, ← hr, Category.assoc]

end GlobalTheory.TransitionUnique
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushforwardPolarisationBundleInvertibleOnModel
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushforwardPolarisationBundleInvertibleOnModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.PushInv

theorem pushInvertible_of_model : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B F O : Type) [CommRing B] [Field F] [CommRing O] (b : Base l B) (U : Scheme.{0}) (s : U ⟶ Sp B) (o : Obj D l b s) (c : U ⟶ Sp F) (β : O →+* F) (C : Cpt c o.t β), IsDedFrac β → HasTheta C.t.G C.t.PP.L → PushInvertible C.t.G C.t.PP.L := by
  intro hL hL2 hL3 E _ _ _ H D l B F O _ _ _ b U s o c β C hβ hθ
  have hS : Out.SecBaseChangeAnySt := by cases hL; cases hL2; cases hL3; assumption
  have hH : Out.GlobalSectionsRankAlgClosed := by cases hL; cases hL2; cases hL3; assumption
  obtain ⟨⟨hDom, hDed⟩, -, hFr⟩ := hβ
  let _ : Algebra O F := β.toAlgebra
  obtain ⟨hN, -, -, hPre, hFl, hDo, hQC⟩ :=
    GlobalTheory.genericPart_dense_proOpen O F C.X U C.s C.jQ C.flat C.proj C.jQ_open C.jQ_dense
  have hPB : IsPullback C.m.φ o.t.G.hom C.t.G.hom (C.jQ ≫ pullback.fst C.s (spMap β)) := C.m.cart.1
  obtain ⟨w, hw, -⟩ := C.m.lin
  have hIso : LBIso o.t.PP.L (C.t.PP.L.pull C.m.φ) := ⟨w, hw⟩
  have hSm : Smooth C.t.G.hom := by
    have sa := C.t.semi
    first | infer_instance | exact sa.1 | (cases sa; assumption)
  have hGI : GeometricallyIntegral C.t.G.hom := by
    have sa := C.t.semi
    have _ := hSm
    have _ : GeometricallyConnected C.t.G.hom := by
      first | infer_instance | (cases sa; assumption)
    exact GlobalTheory.grpObj_geometricallyIntegral_of_smooth C.X C.t.G
  exact @GlobalTheory.PushInv.pushInvertible_of_densePart C.X U hN (C.jQ ≫ pullback.fst C.s (spMap β)) ⟨fun y => (C.normal y).1, fun y => (C.normal y).2⟩ hPre hFl hDo hQC
    C.t.G o.t.G C.m.φ C.t.PP.L o.t.PP.L hSm hGI hPB C.t.PP.isLB o.t.PP.isLB hIso
    (GlobalTheory.PushInv.pushInvertible_any hS hH U (GlobalTheory.Obj.toPolAV o)) hθ

end GlobalTheory.PushInv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushforwardPolarisationBundleInvertibleOnModelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
theorem _root_.GlobalTheory.T.pushforward_polarisationBundle_invertible_on_model : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B F O : Type) [CommRing B] [Field F] [CommRing O] (b : Base l B) (U : Scheme.{0}) (s : U ⟶ Sp B) (o : Obj D l b s) (c : U ⟶ Sp F) (β : O →+* F) (C : Cpt c o.t β), IsDedFrac β → HasTheta C.t.G C.t.PP.L → PushInvertible C.t.G C.t.PP.L := by
  first | exact @GlobalTheory.PushInv.pushInvertible_of_model | exact GlobalTheory.PushInv.pushInvertible_of_model | (intros; apply GlobalTheory.PushInv.pushInvertible_of_model <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverCompOfIsFiniteNoetherianBase
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverCompOfIsFiniteNoetherianBase
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory

theorem isQProjOver_comp_of_isFinite_general {R : Type} [CommRing R] {X Y : Scheme.{0}} (f : X ⟶ Y) [IsFinite f]
    {s : Y ⟶ Sp R} (h : IsQProjOver s) : IsQProjOver (f ≫ s) := by
  obtain ⟨N, i, hi, hq, rfl⟩ := h
  have hO : IsAmpleLB (ProjSpace.O1 R N) := isAmple_projective_O_one R N
  have hY : IsAmpleLB ((ProjSpace.O1 R N).pull i) := hO.pull_of_isImmersion i
  have hX : IsAmpleLB (((ProjSpace.O1 R N).pull i).pull f) := hY.pull_of_isFinite f
  have := isProper_str R N
  have : LocallyOfFiniteType (f ≫ i ≫ PSpace.str R N) := inferInstance
  exact hX.isQProjOver _

theorem isQProjOver_comp_of_isFinite_noetherian :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X Y : Scheme.{0}) (f : X ⟶ Y) (s : Y ⟶ Sp R),
      IsFinite f → IsQProjOver s → IsQProjOver (f ≫ s) := by
  intro R _ _ X Y f s hf h
  exact isQProjOver_comp_of_isFinite_general f h

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverCompOfIsFiniteNoetherianBaseStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isQProjOver_comp_of_isFinite_noetherianBase : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X Y : Scheme.{0}) (f : X ⟶ Y) (s : Y ⟶ Sp R), IsFinite f → IsQProjOver s → IsQProjOver (f ≫ s) := by
  first | exact @GlobalTheory.isQProjOver_comp_of_isFinite_noetherian | exact GlobalTheory.isQProjOver_comp_of_isFinite_noetherian | (intros; apply GlobalTheory.isQProjOver_comp_of_isFinite_noetherian <;> assumption)
end
end
