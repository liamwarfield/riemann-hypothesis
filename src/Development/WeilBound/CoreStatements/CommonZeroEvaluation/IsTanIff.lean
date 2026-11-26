module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianMapLieModelFieldPoint

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.CommonZeroEvaluation.CombComb
noncomputable section

namespace ModelDimension.Near

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Chart (dualMapR)
open scoped CategoryTheory.Obj

variable {X X' : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']

def GT (G : Over X) [GrpObj G] (x : Sp R ⟶ X) (w : Sp (DualNumber R) ⟶ G.left) : Prop :=
  w ≫ G.hom = spMap (algebraMap R (DualNumber R)) ≫ x ∧
    spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ w = (1 : Over.mk x ⟶ G).left

def GC (G : Over X) [GrpObj G] (x : Sp R ⟶ X) {m : ℕ} (v : Fin m → (Sp (DualNumber R) ⟶ G.left)) (cf : Fin m → R)
    (w : Sp (DualNumber R) ⟶ G.left) : Prop :=
  ∃ u : Fin m → (Over.mk (spMap (algebraMap R (DualNumber R)) ≫ x) ⟶ G),
    (∀ i, (u i).left = spMap (epsScaleR (cf i)) ≫ v i) ∧ (List.ofFn u).prod.left = w

variable {G : Over X} [GrpObj G] {G' : Over X'} [GrpObj G'] {f : X' ⟶ X} {φ : G'.left ⟶ G.left}

theorem one_push (h : IsGrpPullback G' G f φ) {S : Scheme.{0}} (x : S ⟶ X') :
    (1 : Over.mk x ⟶ G').left ≫ φ = (1 : Over.mk (x ≫ f) ⟶ G).left := by
  have e := GlobalTheory.LieCombBaseChange.prod_left_comp h (T := Over.mk (x ≫ f)) (T' := Over.mk x) (𝟙 S)
    (Category.id_comp _) (n := 0) (fun i => i.elim0) (fun i => i.elim0) (fun i => i.elim0)
  simp only [List.ofFn_zero, List.prod_nil] at e
  exact e.trans (Category.id_comp _)

theorem gt_push (h : IsGrpPullback G' G f φ) {x : Sp R ⟶ X'} {w : Sp (DualNumber R) ⟶ G'.left} (hw : GT G' x w) :
    GT G (x ≫ f) (w ≫ φ) :=
  ⟨by rw [Category.assoc, h.1.w, ← Category.assoc, hw.1, Category.assoc],
    by rw [← Category.assoc, hw.2, one_push h]⟩

theorem alg_fst : spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ spMap (algebraMap R (DualNumber R)) = 𝟙 _ := by
  rw [← spMap_comp]
  have : (TrivSqZeroExt.fstHom R R R).toRingHom.comp (algebraMap R (DualNumber R)) = RingHom.id R := by
    ext r
    simp [TrivSqZeroExt.algebraMap_eq_inl]
  rw [this]
  exact Spec.map_id _

theorem gt_pull (h : IsGrpPullback G' G f φ) {x : Sp R ⟶ X'} {w : Sp (DualNumber R) ⟶ G'.left}
    (h1 : w ≫ G'.hom = spMap (algebraMap R (DualNumber R)) ≫ x) (hw : GT G (x ≫ f) (w ≫ φ)) : GT G' x w := by
  refine ⟨h1, h.1.hom_ext ?_ ?_⟩
  · rw [Category.assoc, hw.2, one_push h]
  · rw [Category.assoc, h1, ← Category.assoc, alg_fst, Category.id_comp]
    exact (Over.w (1 : Over.mk x ⟶ G')).symm

theorem gt_bc (ψ : R →+* R') {x : Sp R ⟶ X} {w : Sp (DualNumber R) ⟶ G.left} (hw : GT G x w) :
    GT G (spMap ψ ≫ x) (spMap (dualMapR ψ) ≫ w) := by
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, hw.1, ← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ x) (GlobalTheory.LieCombBaseChange.dualMap_over ψ)
  · have e : spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ spMap (dualMapR ψ) =
        spMap ψ ≫ spMap (TrivSqZeroExt.fstHom R R R).toRingHom := by
      rw [← spMap_comp, ← spMap_comp]
      congr 1
      refine RingHom.ext fun r => ?_
      simp [dualMapR]
    rw [← Category.assoc, e, Category.assoc, hw.2]
    let D : Over.mk (spMap ψ ≫ x) ⟶ Over.mk x := Over.homMk (spMap ψ) rfl
    exact congrArg CommaMorphism.left (MonObj.comp_one (M := G) D)

theorem gc_push (h : IsGrpPullback G' G f φ) {x : Sp R ⟶ X'} {m : ℕ} {v : Fin m → (Sp (DualNumber R) ⟶ G'.left)}
    {cf : Fin m → R} {w : Sp (DualNumber R) ⟶ G'.left} (hw : GC G' x v cf w) :
    GC G (x ≫ f) (fun i => v i ≫ φ) cf (w ≫ φ) := by
  obtain ⟨u, hu, rfl⟩ := hw
  let u' : Fin m → (Over.mk (spMap (algebraMap R (DualNumber R)) ≫ x ≫ f) ⟶ G) := fun i =>
    Over.homMk ((u i).left ≫ φ) (by
      have e : (u i).left ≫ G'.hom = spMap (algebraMap R (DualNumber R)) ≫ x := Over.w (u i)
      show ((u i).left ≫ φ) ≫ G.hom = spMap (algebraMap R (DualNumber R)) ≫ x ≫ f
      rw [Category.assoc, h.1.w, ← Category.assoc, e, Category.assoc])
  refine ⟨u', fun i => ?_, ?_⟩
  · show (u i).left ≫ φ = _
    rw [hu, Category.assoc]
  · have e := GlobalTheory.LieCombBaseChange.prod_left_comp h (𝟙 (Sp (DualNumber R)))
      ((Category.id_comp _).trans (Category.assoc _ _ _).symm) u' u (fun i => (Category.id_comp _).symm)
    exact (e.trans (Category.id_comp _)).symm

theorem gc_pull (h : IsGrpPullback G' G f φ) {x : Sp R ⟶ X'} {m : ℕ} {v : Fin m → (Sp (DualNumber R) ⟶ G'.left)}
    {cf : Fin m → R} {w : Sp (DualNumber R) ⟶ G'.left}
    (hv : ∀ i, v i ≫ G'.hom = spMap (algebraMap R (DualNumber R)) ≫ x)
    (h1 : w ≫ G'.hom = spMap (algebraMap R (DualNumber R)) ≫ x)
    (hw : GC G (x ≫ f) (fun i => v i ≫ φ) cf (w ≫ φ)) : GC G' x v cf w := by
  obtain ⟨u, hu, hw⟩ := hw
  let u' : Fin m → (Over.mk (spMap (algebraMap R (DualNumber R)) ≫ x) ⟶ G') := fun i =>
    Over.homMk (spMap (epsScaleR (cf i)) ≫ v i) (by
      show (spMap (epsScaleR (cf i)) ≫ v i) ≫ G'.hom = spMap (algebraMap R (DualNumber R)) ≫ x
      rw [Category.assoc, hv, ← Category.assoc]
      exact congrArg (· ≫ x) (GlobalTheory.LieCombBaseChange.epsScale_over (cf i)))
  refine ⟨u', fun i => rfl, h.1.hom_ext ?_ ?_⟩
  · have e := GlobalTheory.LieCombBaseChange.prod_left_comp h (𝟙 (Sp (DualNumber R)))
      ((Category.id_comp _).trans (Category.assoc _ _ _).symm) u u' (fun i =>
        (Category.assoc _ _ _).trans ((hu i).symm.trans (Category.id_comp _).symm))
    exact e.trans ((Category.id_comp _).trans hw)
  · rw [h1]
    exact Over.w _

theorem gc_bc (ψ : R →+* R') {x : Sp R ⟶ X} {m : ℕ} {v : Fin m → (Sp (DualNumber R) ⟶ G.left)}
    {cf : Fin m → R} {w : Sp (DualNumber R) ⟶ G.left} (hw : GC G x v cf w) :
    GC G (spMap ψ ≫ x) (fun i => spMap (dualMapR ψ) ≫ v i) (fun i => ψ (cf i)) (spMap (dualMapR ψ) ≫ w) := by
  obtain ⟨u, hu, rfl⟩ := hw
  let D : Over.mk (spMap (algebraMap R' (DualNumber R')) ≫ spMap ψ ≫ x) ⟶
      Over.mk (spMap (algebraMap R (DualNumber R)) ≫ x) := Over.homMk (spMap (dualMapR ψ)) (by
    show spMap (dualMapR ψ) ≫ spMap (algebraMap R (DualNumber R)) ≫ x = _ ≫ spMap ψ ≫ x
    rw [← Category.assoc, ← Category.assoc]
    exact congrArg (· ≫ x) (GlobalTheory.LieCombBaseChange.dualMap_over ψ))
  refine ⟨fun i => D ≫ u i, fun i => ?_, ?_⟩
  · show spMap (dualMapR ψ) ≫ (u i).left = _
    rw [hu, ← Category.assoc, GlobalTheory.LieCombBaseChange.dualMap_epsScale, Category.assoc]
  · exact (congrArg (fun q => q.left) ((map_list_prod (preHom D) (List.ofFn u)).trans
      (by rw [List.map_ofFn]))).symm

section Ring

open GlobalTheory.Reg.VecEig GlobalTheory.GrpTangent

variable {A : Over (Sp R)} [GrpObj A] [IsCommMonObj A]

theorem comb_comb {n r : ℕ} {v : Fin n → (epsR R ⟶ A)} (hv : ∀ i, IsTangent (v i)) (u : Matrix (Fin n) (Fin r) R)
    (a : Fin r → R) : comb (fun i => comb v fun j => u j i) a = comb v (u.mulVec a) := by
  rw [comb]
  simp only [epsScale_comb]
  simp only [comb, Matrix.mulVec, dotProduct, epsScale_sum_comp (hv _)]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, mul_comm]

theorem exists_prim [IsDomain R] {n r : ℕ} {v : Fin n → (epsR R ⟶ A)} (hv : IsLieBasis v) {I : Type}
    (g : I → (A ⟶ A)) (hg : ∀ i, IsMonHom (g i)) (z : I → R) (ub : Fin r → (epsR R ⟶ A)) (ht : ∀ i, IsTangent (ub i))
    (he : ∀ i k, (ub i ≫ g k).left = spMap (epsScaleR (z k)) ≫ (ub i).left)
    (hb : ∀ w : epsR R ⟶ A, IsTangent w → (∀ k, (w ≫ g k).left = spMap (epsScaleR (z k)) ≫ w.left) →
      ∃! a : Fin r → R, IsLieComb a ub w) :
    ∃ u : Matrix (Fin n) (Fin r) R, (∀ i, IsLieComb (fun j => u j i) v (ub i)) ∧
      ∀ (p : R) (a : Fin r → R) (cv : Fin n → R), p ≠ 0 → u.mulVec a = p • cv → ∃ a', a = p • a' := by
  choose cu hcu using fun i => (hv.2 _ (ht i)).exists
  let u : Matrix (Fin n) (Fin r) R := Matrix.of fun j i => cu i j
  have hub : ub = fun i => comb v fun j => u j i := funext fun i => (isLieComb_iff_comb _ _ _).1 (hcu i)
  refine ⟨u, hcu, fun p a cv hp hcv => ?_⟩
  choose ρ hρ using fun k j => (hv.2 _ (haveI := hg k; isTangent_comp (hv.1 j) (g k))).exists
  have eig : ∀ k (x : Fin n → R), ((comb v x ≫ g k).left = spMap (epsScaleR (z k)) ≫ (comb v x).left) ↔
      (Matrix.of fun i j => ρ k j i).mulVec x = z k • x := by
    intro k x
    haveI := hg k
    rw [← (comb_injective hv).eq_iff, ← epsScale_comb,
      ← comb_comp hv.1 (g k) (Matrix.of fun i j => ρ k j i) (fun j => (isLieComb_iff_comb _ _ _).1 (hρ k j)) x]
    exact ⟨fun h => Over.OverMorphism.ext h, fun h => congrArg CommaMorphism.left h⟩
  have eigu : ∀ k (b : Fin r → R), (Matrix.of fun i j => ρ k j i).mulVec (u.mulVec b) = z k • u.mulVec b := by
    intro k b
    have e : u.mulVec b = ∑ i, b i • fun j => u j i := by
      funext j
      simp [Matrix.mulVec, dotProduct, Finset.sum_apply, _root_.mul_comm]
    rw [e, Matrix.mulVec_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 := he i k
    rw [congrFun hub i] at h1
    rw [Matrix.mulVec_smul, (eig k _).1 h1, smul_comm]
  have key : ∀ x : Fin n → R, (∀ k, (Matrix.of fun i j => ρ k j i).mulVec x = z k • x) →
      ∃! b : Fin r → R, u.mulVec b = x := by
    intro x hx
    have h1 := hb (comb v x) (isTangent_comb hv.1 x) fun k => (eig k x).2 (hx k)
    refine (existsUnique_congr fun b => ?_).1 h1
    rw [isLieComb_iff_comb, hub, comb_comb hv.1, (comb_injective hv).eq_iff, eq_comm]
  obtain ⟨a', ha', -⟩ := key cv fun k => by
    have h1 := eigu k a
    rw [hcv, Matrix.mulVec_smul, smul_comm] at h1
    exact smul_right_injective _ hp h1
  refine ⟨a', (key _ fun k => eigu k a).unique rfl ?_⟩
  rw [Matrix.mulVec_smul, ha', hcv]

end Ring

section Coord

variable [IsCommMonObj G] {x : Sp R ⟶ X} {n : ℕ} {V : Fin n → (Sp (DualNumber R) ⟶ G.left)}

def IsBas (G : Over X) [GrpObj G] (x : Sp R ⟶ X) {n : ℕ} (V : Fin n → (Sp (DualNumber R) ⟶ G.left)) : Prop :=
  ∃ (A : Over (Sp R)) (_ : GrpObj A) (_ : IsCommMonObj A) (φ : A.left ⟶ G.left) (_ : IsGrpPullback A G x φ)
    (v : Fin n → (epsR R ⟶ A)), (∀ j, (v j).left ≫ φ = V j) ∧ IsLieBasis v

omit [IsCommMonObj G]

theorem gc_iff {A : Over (Sp R)} [GrpObj A] {φ : A.left ⟶ G.left} (h : IsGrpPullback A G x φ) {m : ℕ} (c : Fin m → R)
    (v : Fin m → (epsR R ⟶ A)) (w : epsR R ⟶ A) :
    IsLieComb c v w ↔ GC G x (fun i => (v i).left ≫ φ) c (w.left ≫ φ) :=
  ReciprocityTheory.ChartRestriction.G.Chart.comb_push h c v w

theorem exists_lift {A : Over (Sp R)} [GrpObj A] {φ : A.left ⟶ G.left} (h : IsGrpPullback A G x φ)
    {w : Sp (DualNumber R) ⟶ G.left} (hw : w ≫ G.hom = spMap (algebraMap R (DualNumber R)) ≫ x) :
    ∃ w' : epsR R ⟶ A, w'.left ≫ φ = w :=
  ⟨Over.homMk (h.1.lift w (spMap (algebraMap R (DualNumber R))) hw) (h.1.lift_snd _ _ _), h.1.lift_fst _ _ _⟩

theorem GC.over {m : ℕ} {v : Fin m → (Sp (DualNumber R) ⟶ G.left)} {cf : Fin m → R}
    {w : Sp (DualNumber R) ⟶ G.left} (h : GC G x v cf w) :
    w ≫ G.hom = spMap (algebraMap R (DualNumber R)) ≫ x := by
  obtain ⟨u, -, rfl⟩ := h
  exact Over.w _

theorem IsBas.exists (hV : IsBas G x V) {w : Sp (DualNumber R) ⟶ G.left} (hw : GT G x w) : ∃ cv, GC G x V cv w := by
  obtain ⟨A, _, _, φ, h, v, hv, hb⟩ := hV
  obtain rfl : (fun j => (v j).left ≫ φ) = V := funext hv
  obtain ⟨w', rfl⟩ := exists_lift h hw.1
  obtain ⟨cv, hcv⟩ := (hb.2 w' ((ReciprocityTheory.ChartRestriction.G.Chart.tan_push h w').2 hw.2)).exists
  exact ⟨cv, (gc_iff h _ _ _).1 hcv⟩

theorem IsBas.unique (hV : IsBas G x V) {w : Sp (DualNumber R) ⟶ G.left} {a b : Fin n → R} (ha : GC G x V a w)
    (hb : GC G x V b w) : a = b := by
  obtain ⟨A, _, _, φ, h, v, hv, hB⟩ := hV
  obtain rfl : (fun j => (v j).left ≫ φ) = V := funext hv
  obtain ⟨w', rfl⟩ := exists_lift h ha.over
  exact GlobalTheory.Reg.VecEig.comb_injective hB
    (((GlobalTheory.Reg.VecEig.isLieComb_iff_comb _ _ _).1 ((gc_iff h _ _ _).2 ha)).symm.trans
      ((GlobalTheory.Reg.VecEig.isLieComb_iff_comb _ _ _).1 ((gc_iff h _ _ _).2 hb)))

theorem IsBas.comb (hV : IsBas G x V) {r : ℕ} {w : Fin r → (Sp (DualNumber R) ⟶ G.left)}
    {u : Matrix (Fin n) (Fin r) R} (hu : ∀ i, GC G x V (fun j => u j i) (w i)) {a : Fin r → R}
    {w' : Sp (DualNumber R) ⟶ G.left} (ha : GC G x w a w') : GC G x V (u.mulVec a) w' := by
  obtain ⟨A, _, _, φ, h, v, hv, hB⟩ := hV
  obtain rfl : (fun j => (v j).left ≫ φ) = V := funext hv
  choose w₁ hw₁ using fun i => exists_lift h (hu i).over
  obtain rfl : (fun j => (w₁ j).left ≫ φ) = w := funext hw₁
  obtain ⟨w₂, rfl⟩ := exists_lift h ha.over
  have e1 : w₁ = fun i => GlobalTheory.Reg.VecEig.comb v fun j => u j i :=
    funext fun i => (GlobalTheory.Reg.VecEig.isLieComb_iff_comb _ _ _).1 ((gc_iff h _ _ _).2 (hu i))
  have e2 := (GlobalTheory.Reg.VecEig.isLieComb_iff_comb _ _ _).1 ((gc_iff h _ _ _).2 ha)
  rw [e1, comb_comb hB.1] at e2
  exact (gc_iff h _ _ _).1 ((GlobalTheory.Reg.VecEig.isLieComb_iff_comb _ _ _).2 e2)

end Coord

end ModelDimension.Near
end
end

section -- merged from Development.WeilBound.CoreStatements.CommonZeroEvaluation.ExistsLeftInv
noncomputable section

namespace ModelDimension.Near

open Formalism.L2.Pj Filter Topology

def Prim {V : Type} [CommRing V] {n r : ℕ} (u : Matrix (Fin n) (Fin r) V) : Prop :=
  ∀ (p : V) (a : Fin r → V) (cv : Fin n → V), p ≠ 0 → u.mulVec a = p • cv → ∃ a', a = p • a'

section Lin

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {n r : ℕ}

theorem exists_left_inv {u u' : Matrix (Fin n) (Fin r) V} (hu : Prim u)
    (hc : ∀ i j, u' i j - u i j ∈ IsLocalRing.maximalIdeal V) : ∃ B : Matrix (Fin r) (Fin n) V, B * u' = 1 := by
  classical
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hmax := hπ.maximalIdeal_eq
  have hπm : IsLocalRing.residue V π = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, hmax]
    exact Ideal.mem_span_singleton_self π
  have hinj : LinearMap.ker (Matrix.toLin' (u.map (IsLocalRing.residue V))) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    rw [Matrix.toLin'_apply] at hx
    choose a ha using fun j => IsLocalRing.residue_surjective (x j)
    have hm : ∀ i, u.mulVec a i ∈ IsLocalRing.maximalIdeal V := by
      intro i
      rw [← IsLocalRing.residue_eq_zero_iff, RingHom.map_mulVec]
      have e1 : (⇑(IsLocalRing.residue V) ∘ a) = x := funext ha
      rw [e1]
      exact congrFun hx i
    rw [hmax] at hm
    choose cv hcv using fun i => Ideal.mem_span_singleton'.mp (hm i)
    have hmul : u.mulVec a = π • cv := by
      funext i
      rw [Pi.smul_apply, smul_eq_mul, mul_comm, hcv i]
    obtain ⟨a', ha'⟩ := hu π a cv hπ.ne_zero hmul
    funext j
    rw [← ha j, ha', Pi.smul_apply, smul_eq_mul, map_mul, hπm, zero_mul]
    rfl
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hinj
  have hBb : LinearMap.toMatrix' g * u.map (IsLocalRing.residue V) = 1 := by
    have h1 := congrArg LinearMap.toMatrix' hg
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at h1
  have hsurj : ∀ i j, ∃ b, IsLocalRing.residue V b = LinearMap.toMatrix' g i j :=
    fun i j => IsLocalRing.residue_surjective _
  choose B₁ hB₁ using hsurj
  obtain ⟨B₀, hB₀⟩ : ∃ B₀ : Matrix (Fin r) (Fin n) V,
      ∀ i j, IsLocalRing.residue V (B₀ i j) = LinearMap.toMatrix' g i j := ⟨Matrix.of B₁, hB₁⟩
  have hred : (B₀ * u').map (IsLocalRing.residue V) = 1 := by
    rw [Matrix.map_mul]
    have e1 : B₀.map (IsLocalRing.residue V) = LinearMap.toMatrix' g := by
      ext i j
      exact hB₀ i j
    have e2 : u'.map (IsLocalRing.residue V) = u.map (IsLocalRing.residue V) := by
      ext i j
      simp only [Matrix.map_apply]
      rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
      exact hc i j
    rw [e1, e2, hBb]
  have hdet : IsUnit (B₀ * u').det := by
    rw [← IsLocalRing.notMem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff, RingHom.map_det]
    have e3 : (IsLocalRing.residue V).mapMatrix (B₀ * u') = 1 := hred
    rw [e3, Matrix.det_one]
    exact one_ne_zero
  refine ⟨(B₀ * u')⁻¹ * B₀, ?_⟩
  rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet]

variable {K : Type} [Field K] [Algebra V K] [IsFractionRing V K]

omit [IsDiscreteValuationRing V] in
theorem Prim.integral {u : Matrix (Fin n) (Fin r) V} (hu : Prim u) (a : Fin r → K) (cv : Fin n → V)
    (h : (u.map (algebraMap V K)).mulVec a = fun j => algebraMap V K (cv j)) (i : Fin r) :
    a i ∈ (algebraMap V K).range := by
  obtain ⟨p, hp⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors V) Finset.univ a
  have hp' : ∀ j, ∃ y, algebraMap V K y = (p : V) • a j := fun j => hp j (Finset.mem_univ j)
  choose a'' ha'' using hp'
  have hp0 : (p : V) ≠ 0 := nonZeroDivisors.ne_zero p.2
  have hpK : algebraMap V K p ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective V K)).mpr hp0
  have hmul : u.mulVec a'' = (p : V) • cv := by
    funext j
    apply IsFractionRing.injective V K
    rw [RingHom.map_mulVec]
    have e1 : (algebraMap V K ∘ a'') = (p : V) • a := funext ha''
    rw [e1, Matrix.mulVec_smul, h]
    simp [Algebra.smul_def]
  obtain ⟨a', ha'⟩ := hu (p : V) a'' cv hp0 hmul
  refine ⟨a' i, ?_⟩
  apply mul_left_cancel₀ hpK
  have e2 : algebraMap V K (a'' i) = algebraMap V K p * algebraMap V K (a' i) := by
    rw [ha', Pi.smul_apply, smul_eq_mul, map_mul]
  rw [← e2, ha'' i, Algebra.smul_def]

theorem vV_eq_zero {x : K} (hx : x ≠ 0) (h1 : x ∈ (algebraMap V K).range) (h2 : x⁻¹ ∈ (algebraMap V K).range) :
    vV V x = 0 := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  have hle : valV V x ≤ 1 := by
    rw [← ha]
    exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ a
  have hle' : valV V x⁻¹ ≤ 1 := by
    rw [← hb]
    exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ b
  have hge : 1 ≤ valV V x := by
    calc (1 : _) = valV V (x * x⁻¹) := by rw [mul_inv_cancel₀ hx, map_one]
      _ = valV V x * valV V x⁻¹ := map_mul _ _ _
      _ ≤ valV V x * 1 := by gcongr
      _ = valV V x := mul_one _
  unfold vV
  rw [le_antisymm hle hge, WithZero.log_one, neg_zero]

theorem diag_mul {A B : Matrix (Fin r) (Fin r) K} (hA : A.BlockTriangular id) (hB : B.BlockTriangular id) (i : Fin r) :
    (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [hA h, zero_mul]
    · rw [hB h, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem vV_diag_eq {g : Matrix (Fin n) (Fin r) K} {C C' : Matrix (Fin r) (Fin r) K} (hC : C.BlockTriangular id)
    (hC' : C'.BlockTriangular id) (h0 : ∀ i, C i i ≠ 0) (h0' : ∀ i, C' i i ≠ 0) {u u' : Matrix (Fin n) (Fin r) V}
    {B : Matrix (Fin r) (Fin n) V} (hB : B * u = 1) (hu' : Prim u') (e : g * C = u.map (algebraMap V K))
    (e' : g * C' = u'.map (algebraMap V K)) (i : Fin r) : vV V (C' i i) = vV V (C i i) := by
  classical
  have hdetC : IsUnit C.det := by
    rw [Matrix.det_of_isUpperTriangular hC]
    exact Ne.isUnit (Finset.prod_ne_zero_iff.mpr fun i _ => h0 i)
  have hdetC' : IsUnit C'.det := by
    rw [Matrix.det_of_isUpperTriangular hC']
    exact Ne.isUnit (Finset.prod_ne_zero_iff.mpr fun i _ => h0' i)
  letI := C.invertibleOfIsUnitDet hdetC
  letI := C'.invertibleOfIsUnitDet hdetC'
  have hCi : (C⁻¹).BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hC
  have hCi' : (C'⁻¹).BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hC'
  obtain ⟨X, hX⟩ : ∃ X, X = C⁻¹ * C' := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y, Y = C'⁻¹ * C := ⟨_, rfl⟩
  have hXY : X * Y = 1 := by
    rw [hX, hY, Matrix.mul_assoc, ← Matrix.mul_assoc C', Matrix.mul_nonsing_inv _ hdetC', Matrix.one_mul,
      Matrix.nonsing_inv_mul _ hdetC]
  have hXtri : X.BlockTriangular id := hX ▸ hCi.mul hC'
  have hYtri : Y.BlockTriangular id := hY ▸ hCi'.mul hC
  have hXint : ∀ i j, X i j ∈ (algebraMap V K).range := by
    have hBK : B.map (algebraMap V K) * u.map (algebraMap V K) = 1 := by
      rw [← Matrix.map_mul, hB, Matrix.map_one _ (map_zero _) (map_one _)]
    have hBg : B.map (algebraMap V K) * g = C⁻¹ := by
      have h1 : B.map (algebraMap V K) * g * C = 1 := by rw [Matrix.mul_assoc, e, hBK]
      calc B.map (algebraMap V K) * g = B.map (algebraMap V K) * g * C * C⁻¹ := by
            rw [Matrix.mul_assoc (B.map (algebraMap V K) * g), Matrix.mul_nonsing_inv _ hdetC, Matrix.mul_one]
        _ = C⁻¹ := by rw [h1, Matrix.one_mul]
    have hXeq : X = (B * u').map (algebraMap V K) := by
      rw [Matrix.map_mul, ← e', ← Matrix.mul_assoc, hBg, hX]
    intro i j
    rw [hXeq]
    exact ⟨(B * u') i j, rfl⟩
  have hYint : ∀ i j, Y i j ∈ (algebraMap V K).range := by
    intro i j
    have h2 : u'.map (algebraMap V K) * Y = u.map (algebraMap V K) := by
      rw [← e', ← e, hY, Matrix.mul_assoc, ← Matrix.mul_assoc C', Matrix.mul_nonsing_inv _ hdetC', Matrix.one_mul]
    have hcol : (u'.map (algebraMap V K)).mulVec (fun k => Y k j) = fun l => algebraMap V K (u l j) := by
      funext l
      have h3 := congrFun (congrFun h2 l) j
      rw [Matrix.mul_apply] at h3
      simp only [Matrix.mulVec, dotProduct]
      rw [h3]
      rfl
    exact Prim.integral hu' (fun k => Y k j) (fun l => u l j) hcol i
  have hdiag := diag_mul hXtri hYtri i
  rw [hXY, Matrix.one_apply_eq] at hdiag
  have hXi0 : X i i ≠ 0 := left_ne_zero_of_mul_eq_one hdiag.symm
  have hXinv : (X i i)⁻¹ ∈ (algebraMap V K).range := by
    rw [inv_eq_of_mul_eq_one_right hdiag.symm]
    exact hYint i i
  have hv0 : vV V (X i i) = 0 := vV_eq_zero hXi0 (hXint i i) hXinv
  have hCinv : (C⁻¹) i i = (C i i)⁻¹ := by
    have h4 := diag_mul hCi hC i
    rw [Matrix.nonsing_inv_mul _ hdetC, Matrix.one_apply_eq] at h4
    exact eq_inv_of_mul_eq_one_left h4.symm
  have hXii : X i i = (C i i)⁻¹ * C' i i := by
    rw [hX, diag_mul hCi hC' i, hCinv]
  have hC'eq : C' i i = C i i * X i i := by
    rw [hXii, ← mul_assoc, mul_inv_cancel₀ (h0 i), one_mul]
  rw [hC'eq, vV_mul (h0 i) hXi0, hv0, add_zero]

end Lin

section Close

variable (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {K : Type} [Field K] [Algebra V K]
  [IsFractionRing V K] {S : Type} [CommRing S] (ψ : S →+* K)

def closeF : Filter (S →+* K) where
  sets := {P | ∃ (F : Finset S) (n : ℕ), ∀ ψ' : S →+* K,
    (∀ s ∈ F, ψ' s = ψ s ∨ (n : ℤ) ≤ vV V (ψ' s - ψ s)) → ψ' ∈ P}
  univ_sets := ⟨∅, 0, fun _ _ => trivial⟩
  sets_of_superset := fun ⟨F, n, h⟩ hs => ⟨F, n, fun ψ' h' => hs (h ψ' h')⟩
  inter_sets := by
    classical
    rintro P Q ⟨F, n, h⟩ ⟨F', n', h'⟩
    refine ⟨F ∪ F', max n n', fun ψ' hh => ⟨h ψ' fun s hs => ?_, h' ψ' fun s hs => ?_⟩⟩
    · exact (hh s (Finset.mem_union_left _ hs)).imp id fun q => le_trans (by exact_mod_cast le_max_left _ _) q
    · exact (hh s (Finset.mem_union_right _ hs)).imp id fun q => le_trans (by exact_mod_cast le_max_right _ _) q

def Tend (a : (S →+* K) → K) (b : K) : Prop :=
  ∀ c : K, c ≠ 0 → ∀ᶠ ψ' in closeF V ψ, valV V (a ψ' - b) < valV V c

variable {V ψ}

private theorem mem_closeF_lemma {P : Set (S →+* K)} (F : Finset S) (n : ℕ)
    (h : ∀ ψ' : S →+* K, (∀ s ∈ F, ψ' s = ψ s ∨ (n : ℤ) ≤ vV V (ψ' s - ψ s)) → ψ' ∈ P) : P ∈ closeF V ψ :=
  ⟨F, n, h⟩

private theorem valV_lt_of_vV_lt_lemma_2 {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) (h : vV V y < vV V x) :
    valV V x < valV V y := by
  unfold vV at h
  exact (WithZero.log_lt_log (valV_ne_zero hx) (valV_ne_zero hy)).mp (by omega)

theorem tend_val (s : S) : Tend V ψ (fun ψ' => ψ' s) (ψ s) := by
  intro c hc
  refine mem_closeF_lemma {s} (vV V c + 1).toNat fun ψ' h => ?_
  show valV V (ψ' s - ψ s) < valV V c
  have hc0 : 0 < valV V c := zero_lt_iff.mpr (valV_ne_zero hc)
  by_cases hd : ψ' s - ψ s = 0
  · rw [hd, map_zero]
    exact hc0
  · rcases h s (Finset.mem_singleton_self s) with h1 | h1
    · exact absurd (sub_eq_zero.mpr h1) hd
    · apply valV_lt_of_vV_lt_lemma_2 hd hc
      have h2 := Int.self_le_toNat (vV V c + 1)
      omega

theorem Tend.add {a a' : (S →+* K) → K} {b b' : K} (h : Tend V ψ a b) (h' : Tend V ψ a' b') :
    Tend V ψ (fun ψ' => a ψ' + a' ψ') (b + b') := by
  intro c hc
  filter_upwards [h c hc, h' c hc] with ψ' h1 h2
  have e : a ψ' + a' ψ' - (b + b') = (a ψ' - b) + (a' ψ' - b') := by ring
  rw [e]
  exact Valuation.map_add_lt _ h1 h2

theorem tend_const (b : K) : Tend V ψ (fun _ => b) b := by
  intro c hc
  exact Filter.Eventually.of_forall fun _ => by
    show valV V (b - b) < valV V c
    rw [sub_self, map_zero]
    exact zero_lt_iff.mpr (valV_ne_zero hc)

theorem Tend.mul_const {a : (S →+* K) → K} {b : K} (h : Tend V ψ a b) (d : K) :
    Tend V ψ (fun ψ' => a ψ' * d) (b * d) := by
  intro c hc
  by_cases hd : d = 0
  · exact Filter.Eventually.of_forall fun ψ' => by
      show valV V (a ψ' * d - b * d) < valV V c
      rw [hd, mul_zero, mul_zero, sub_self, map_zero]
      exact zero_lt_iff.mpr (valV_ne_zero hc)
  · filter_upwards [h (c / d) (div_ne_zero hc hd)] with ψ' h1
    have hvd : 0 < valV V d := zero_lt_iff.mpr (valV_ne_zero hd)
    have e : a ψ' * d - b * d = (a ψ' - b) * d := by ring
    rw [e, map_mul]
    have e2 : valV V c = valV V (c / d) * valV V d := by rw [← map_mul, div_mul_cancel₀ c hd]
    rw [e2]
    exact mul_lt_mul_of_pos_right h1 hvd

theorem Tend.sum {I : Type} (s : Finset I) {a : I → (S →+* K) → K} {b : I → K} (h : ∀ i, Tend V ψ (a i) (b i)) :
    Tend V ψ (fun ψ' => ∑ i ∈ s, a i ψ') (∑ i ∈ s, b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (tend_const (V := V) (ψ := ψ) (0 : K))
  | insert i s hi ih =>
    have h2 := (h i).add ih
    simpa [Finset.sum_insert hi] using h2

theorem Tend.div {a a' : (S →+* K) → K} {b b' : K} (h : Tend V ψ a b) (h' : Tend V ψ a' b') (hb : b' ≠ 0) :
    Tend V ψ (fun ψ' => a ψ' / a' ψ') (b / b') := by
  intro c hc
  have hvb : valV V b' ≠ 0 := valV_ne_zero hb
  obtain ⟨t, ht, hbt⟩ : ∃ t : K, t ≠ 0 ∧ valV V b * valV V t ≤ valV V c * valV V b' * valV V b' := by
    by_cases hb0 : b = 0
    · exact ⟨1, one_ne_zero, by rw [hb0, map_zero, zero_mul]; exact zero_le⟩
    · refine ⟨c * b' * b' / b, div_ne_zero (mul_ne_zero (mul_ne_zero hc hb) hb) hb0, le_of_eq ?_⟩
      rw [← map_mul, ← map_mul, ← map_mul]
      congr 1
      field_simp
  filter_upwards [h (c * b') (mul_ne_zero hc hb), h' b' hb, h' t ht] with ψ' h1 h2 h3
  have ha' : valV V (a' ψ') = valV V b' := Valuation.map_eq_of_sub_lt _ h2
  have ha'0 : a' ψ' ≠ 0 := by
    intro h0
    rw [h0, map_zero] at ha'
    exact hvb ha'.symm
  have e : a ψ' / a' ψ' - b / b' = (a ψ' - b) / a' ψ' + -(b * (a' ψ' - b') / (a' ψ' * b')) := by
    field_simp
    ring
  rw [e]
  apply Valuation.map_add_lt
  · rw [map_div₀, ha']
    have e3 : valV V c = valV V (c * b') / valV V b' := by
      rw [map_mul, mul_div_assoc, div_self hvb, mul_one]
    rw [e3]
    exact (div_lt_div_iff_of_pos_right (zero_lt_iff.mpr hvb)).mpr h1
  · by_cases hb0 : b = 0
    · rw [hb0, zero_mul, zero_div, neg_zero, map_zero]
      exact zero_lt_iff.mpr (valV_ne_zero hc)
    · rw [Valuation.map_neg, map_div₀, map_mul, map_mul, ha']
      have hpos : 0 < valV V b' * valV V b' := zero_lt_iff.mpr (mul_ne_zero hvb hvb)
      have e4 : valV V c = valV V c * valV V b' * valV V b' / (valV V b' * valV V b') := by
        rw [mul_assoc, mul_div_assoc, div_self (mul_ne_zero hvb hvb), mul_one]
      rw [e4]
      refine (div_lt_div_iff_of_pos_right hpos).mpr (lt_of_lt_of_le ?_ hbt)
      exact mul_lt_mul_of_pos_left h3 (zero_lt_iff.mpr (valV_ne_zero hb0))

theorem eventually_ne {h : S} (hh : ψ h ≠ 0) : ∀ᶠ ψ' in closeF V ψ, ψ' h ≠ 0 := by
  filter_upwards [tend_val h (ψ h) hh] with ψ' h1 h0
  rw [h0, zero_sub, Valuation.map_neg] at h1
  exact lt_irrefl _ h1


open Classical in
def ext (h : S) (χ₀ : Localization.Away h →+* K) (ψ' : S →+* K) : Localization.Away h →+* K :=
  if hh : ψ' h = 0 then χ₀ else IsLocalization.Away.lift h (Ne.isUnit hh)

theorem ext_comp {h : S} (χ₀ : Localization.Away h →+* K) {ψ' : S →+* K} (hh : ψ' h ≠ 0) :
    (ext h χ₀ ψ').comp (algebraMap S _) = ψ' := by
  rw [ext, dite_eq_right hh]
  exact IsLocalization.Away.lift_comp h _

theorem tend_ext {h : S} (hh : ψ h ≠ 0) {χ₀ : Localization.Away h →+* K} (h0 : χ₀.comp (algebraMap S _) = ψ)
    (a : Localization.Away h) : Tend V ψ (fun ψ' => ext h χ₀ ψ' a) (χ₀ a) := by
  obtain ⟨n, s, hs⟩ := IsLocalization.Away.surj h a
  have key : ∀ φ : Localization.Away h →+* K, φ (algebraMap S _ h) ≠ 0 →
      φ a = φ (algebraMap S _ s) / φ (algebraMap S _ h) ^ n := by
    intro φ hφ
    rw [← hs, map_mul, map_pow, mul_div_assoc, div_self (pow_ne_zero _ hφ), mul_one]
  have hχ : ∀ x, χ₀ (algebraMap S _ x) = ψ x := fun x => by rw [← h0]; rfl
  have ht : Tend V ψ (fun ψ' => ψ' s / ψ' h ^ n) (ψ s / ψ h ^ n) := by
    have h1 : Tend V ψ (fun ψ' => ψ' (h ^ n)) (ψ (h ^ n)) := tend_val (h ^ n)
    simp only [map_pow] at h1
    exact (tend_val s).div h1 (pow_ne_zero _ hh)
  rw [key χ₀ (by rw [hχ]; exact hh), hχ, hχ]
  intro c hc
  filter_upwards [ht c hc, eventually_ne hh] with ψ' h1 h2
  have hE : ∀ x, ext h χ₀ ψ' (algebraMap S _ x) = ψ' x := fun x => by
    rw [← RingHom.comp_apply, ext_comp χ₀ h2]
  rw [key _ (by rw [hE]; exact h2), hE, hE]
  exact h1

theorem Tend.cong {a : (S →+* K) → K} {b : V} (h : Tend V ψ a (algebraMap V K b)) :
    ∀ᶠ ψ' in closeF V ψ, ∃ b' : V, algebraMap V K b' = a ψ' ∧ b' - b ∈ IsLocalRing.maximalIdeal V := by
  filter_upwards [h 1 one_ne_zero] with ψ' h1
  rw [map_one] at h1
  have hint : a ψ' - algebraMap V K b ∈ (algebraMap V K).range := by
    apply IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one
    intro w
    have hw : w = IsDiscreteValuationRing.maximalIdeal V := by
      apply IsDedekindDomain.HeightOneSpectrum.ext
      exact IsLocalRing.eq_maximalIdeal (w.isPrime.isMaximal w.ne_bot)
    rw [hw]
    exact le_of_lt h1
  obtain ⟨y, hy⟩ := hint
  refine ⟨b + y, by rw [map_add (f := _), hy, add_sub_cancel], ?_⟩
  rw [add_sub_cancel_left]
  have h3 : valV V (algebraMap V K y) < 1 := by
    rw [hy]
    exact h1
  exact (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem _ y).mp h3

end Close

end ModelDimension.Near
end
end

noncomputable section

namespace ModelDimension.Near

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.ChartRestriction.G.Chart (dualMapR)
open scoped CategoryTheory.Obj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β)
  {R R' : Type} [CommRing R] [CommRing R']

theorem tanY_gt [Algebra c.F R] (y : FrPt Xo c R) (τ : E →+* ℂ) (i : Fin (Dw.mult τ)) :
    GT Y.t.G (Small.ptY Y y) (Small.tanY Y y τ i) :=
  gt_push Y.m.cart (gt_pull Y.m0.cart (Small.tanF_hom Y y τ i) (by
    have e : Small.tanF Y y τ i ≫ Y.m0.cm.F = y.u τ i := Small.tanF_φ Y y τ i
    rw [e, Small.ptF_fst]
    exact y.tan τ i))

theorem ptF_bor [Algebra c.F R] {t : Ix Dw → Rˣ} {y y' : FrPt Xo c R} (h : FrBor t y y') :
    Small.ptF y' = Small.ptF y := by
  apply pullback.hom_ext
  · rw [Small.ptF_fst, Small.ptF_fst, h.1]
  · rw [Small.ptF_snd, Small.ptF_snd]

theorem ptY_bor [Algebra c.F R] {t : Ix Dw → Rˣ} {y y' : FrPt Xo c R} (h : FrBor t y y') :
    Small.ptY Y y' = Small.ptY Y y := by
  rw [Small.ptY, Small.ptY, ptF_bor h]

theorem tanY_bor [Algebra c.F R] {t : Ix Dw → Rˣ} {y y' : FrPt Xo c R} (h : FrBor t y y') (τ : E →+* ℂ) :
    ∃ C : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) R, C.BlockTriangular id ∧ (∀ i, C i i = t (some ⟨τ, i⟩)) ∧
      ∀ i, GC Y.t.G (Small.ptY Y y) (Small.tanY Y y τ) (fun j => C j i) (Small.tanY Y y' τ i) := by
  choose cf h1 h2 h3 using h.2.1 τ
  refine ⟨Matrix.of fun j i => cf i j, fun j i hij => h2 i j hij, h1, fun i => ?_⟩
  refine gc_push Y.m.cart (gc_pull Y.m0.cart (Small.tanF_hom Y y τ) (by rw [Small.tanF_hom, ptF_bor h]) ?_)
  have e : ∀ (y : FrPt Xo c R) i, Small.tanF Y y τ i ≫ Y.m0.cm.F = y.u τ i := fun y i => Small.tanF_φ Y y τ i
  simp only [e, Small.ptF_fst]
  exact h3 i

variable {U : Y.X.Opens} (hU : IsAffineOpen U) {n : ℕ} (v₀ : Fin n → (Sp (DualNumber Γ(Y.X, U)) ⟶ Y.t.G.left))

def IsChart : Prop :=
  ∀ (R' : Type) [CommRing R'] (f : Γ(Y.X, U) →+* R') (G' : Over (Sp R')) [GrpObj G'] (φ : G'.left ⟶ Y.t.G.left),
    IsGrpPullback G' Y.t.G (spMap f ≫ hU.fromSpec) φ →
      ∃ v' : Fin n → (epsR R' ⟶ G'), (∀ j, (v' j).left ≫ φ = spMap (dualMapR f) ≫ v₀ j) ∧ IsLieBasis v'

def Crd (f : Γ(Y.X, U) →+* R) (cv : Fin n → R) (w : Sp (DualNumber R) ⟶ Y.t.G.left) : Prop :=
  GC Y.t.G (spMap f ≫ hU.fromSpec) (fun j => spMap (dualMapR f) ≫ v₀ j) cv w

variable {Y hU v₀}

theorem IsChart.isBas (hC : IsChart Y hU v₀) (f : Γ(Y.X, U) →+* R) :
    IsBas Y.t.G (spMap f ≫ hU.fromSpec) (fun j => spMap (dualMapR f) ≫ v₀ j) := by
  obtain ⟨t, ⟨m⟩⟩ := (GlobalTheory.ModelPoints.model_points_charts E H Dw l Xo c O β Y).2.1 (Sp R) (spMap f ≫ hU.fromSpec)
  obtain ⟨v, hv, hb⟩ := hC R f t.G m.φ m.cart
  exact ⟨t.G, inferInstance, inferInstance, m.φ, m.cart, v, hv, hb⟩

theorem Crd.bc (ψ : R →+* R') {f : Γ(Y.X, U) →+* R} {cv : Fin n → R} {w : Sp (DualNumber R) ⟶ Y.t.G.left}
    (h : Crd Y hU v₀ f cv w) : Crd Y hU v₀ (ψ.comp f) (fun j => ψ (cv j)) (spMap (dualMapR ψ) ≫ w) := by
  have h1 := gc_bc ψ h
  have e : dualMapR (ψ.comp f) = (dualMapR ψ).comp (dualMapR f) := by
    refine RingHom.ext fun x => ?_
    ext <;> simp [dualMapR]
  unfold Crd
  rw [e, spMap_comp, spMap_comp, Category.assoc]
  simpa only [Category.assoc] using h1

theorem IsChart.crd_bor (hC : IsChart Y hU v₀) [Algebra c.F R] {t : Ix Dw → Rˣ} {y y' : FrPt Xo c R}
    (h : FrBor t y y') (τ : E →+* ℂ) :
    ∃ C : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) R, C.BlockTriangular id ∧ (∀ i, C i i = t (some ⟨τ, i⟩)) ∧
      ∀ (f : Γ(Y.X, U) →+* R), Small.ptY Y y = spMap f ≫ hU.fromSpec →
        ∀ (g u : Matrix (Fin n) (Fin (Dw.mult τ)) R), (∀ i, Crd Y hU v₀ f (fun j => g j i) (Small.tanY Y y τ i)) →
          (∀ i, Crd Y hU v₀ f (fun j => u j i) (Small.tanY Y y' τ i)) → g * C = u := by
  obtain ⟨C, h1, h2, h3⟩ := tanY_bor Y h τ
  refine ⟨C, h1, h2, fun f hf g u hg hu => ?_⟩
  rw [hf] at h3
  ext j i
  exact congrFun ((hC.isBas f).unique ((hC.isBas f).comb hg (h3 i)) (hu i)) j

theorem isTan_iff {A : Over (Sp R)} [GrpObj A] (w : epsR R ⟶ A) : IsTan (V := R) (R := R) w ↔ IsTangent w := by
  have e : (1 : ptOver R R ⟶ A).left = η[A].left := by
    show spMap (RingHom.id R) ≫ η[A].left = _
    have : spMap (RingHom.id R) = 𝟙 _ := Spec.map_id _
    rw [this, Category.id_comp]
  unfold IsTan IsTangent
  rw [e]

theorem IsChart.integral (hExt : GlobalTheory.Published.SemiAbelianHomExtension) (hC : IsChart Y hU v₀) {T : CDVR}
    {io : c.F →+* T.Fr} (y : IntFr Xo c T io) (f₀ : Γ(Y.X, U) →+* T.V)
    (hf : letI := io.toAlgebra; Small.ptY Y y.1 = spMap ((algebraMap T.V T.Fr).comp f₀) ≫ hU.fromSpec)
    (τ : E →+* ℂ) :
    letI := io.toAlgebra
    ∃ u : Matrix (Fin n) (Fin (Dw.mult τ)) T.V, Prim u ∧
      ∀ i, Crd Y hU v₀ ((algebraMap T.V T.Fr).comp f₀) (fun j => algebraMap T.V T.Fr (u j i))
        (Small.tanY Y y.1 τ i) := by
  letI := io.toAlgebra
  obtain ⟨G, t', m1, m2, ⟨ub, htan, heig, hbasis, hlift⟩, -⟩ := y.2.2
  have wa : m1.φ ≫ Xo.univ.t.G.hom = (t'.G.hom ≫ Small.ptF y.1) ≫ pullback.fst _ _ := by
    rw [m1.cart.1.w, Category.assoc, Small.ptF_fst]
  let a : t'.G.left ⟶ Y.oF.t.G.left := Y.m0.cart.1.lift m1.φ (t'.G.hom ≫ Small.ptF y.1) wa
  have ha1 : a ≫ Y.m0.toSABMap.φ = m1.φ := IsPullback.lift_fst _ _ _ _
  have ha2 : a ≫ Y.oF.t.G.hom = t'.G.hom ≫ Small.ptF y.1 := IsPullback.lift_snd _ _ _ _
  have gpa : IsGrpPullback t'.G Y.oF.t.G (Small.ptF y.1) a :=
    IsGrpPullback.cancel Y.m0.cart (m1.cart.congr (Small.ptF_fst y.1).symm ha1.symm) ha2
  have hg : Small.ptY Y y.1 = spMap (algebraMap T.V T.Fr) ≫ spMap f₀ ≫ hU.fromSpec := by
    rw [hf, spMap_comp, Category.assoc]
  have gpY : IsGrpPullback t'.G Y.t.G (spMap (algebraMap T.V T.Fr) ≫ spMap f₀ ≫ hU.fromSpec) (a ≫ Y.m.φ) :=
    (gpa.comp Y.m.cart).congr hg rfl
  have acta : ∀ r, (t'.act.act r).left ≫ a = a ≫ (Y.oF.t.act.act r).left := by
    intro r
    apply Y.m0.cart.1.hom_ext
    · rw [Category.assoc, Category.assoc, ha1, Y.m0.act r, ← Category.assoc, ha1, m1.act r]
    · rw [Category.assoc, Category.assoc, ha2, Over.w (Y.oF.t.act.act r), ha2, ← Category.assoc,
        Over.w (t'.act.act r)]
  obtain ⟨Ψ, hΨ, hm2, -⟩ := GlobalTheory.T.complete_dvr_pullback_semiabelian E H hExt Y.X Y.t T (spMap f₀ ≫ hU.fromSpec) G t' m2 (a ≫ Y.m.φ) gpY
    (fun r => by rw [← Category.assoc, acta r, Category.assoc, Y.m.act r, Category.assoc])
  obtain ⟨v, hv, hb⟩ := hC T.V f₀ G.G Ψ hΨ
  obtain ⟨u, hu, hp⟩ := exists_prim hb
    (I := {q : 𝓞 E × T.V // algebraMap T.V T.Fr q.2 = io (embK c τ q.1)})
    (fun q => G.act.act q.1.1) (fun q => G.act.hom _) (fun q => q.1.2) (ub τ)
    (fun i => (isTan_iff _).1 (htan τ i)) (fun i q => heig τ i _ _ q.2)
    (fun w hw he => hbasis τ w ((isTan_iff _).2 hw) fun a z hz => he ⟨(a, z), hz⟩)
  refine ⟨u, hp, fun i => ?_⟩
  have h1 : Crd Y hU v₀ f₀ (fun j => u j i) ((ub τ i).left ≫ Ψ) := by
    have := (gc_iff hΨ _ _ _).1 (hu i)
    simp only [hv] at this
    exact this
  have h2 := h1.bc (algebraMap T.V T.Fr)
  obtain ⟨u', hu1, hu2⟩ := hlift τ i
  have hbase := GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.base_eq T G t' m2 _ u' hu2
  have e : u' ≫ a = Small.tanF Y y.1 τ i := by
    apply Small.eq_tanF
    · rw [Category.assoc, ha1, hu1]
    · rw [Category.assoc, ha2, ← Category.assoc, hbase]
  have e2 : Small.tanY Y y.1 τ i = spMap (dualMapR (algebraMap T.V T.Fr)) ≫ (ub τ i).left ≫ Ψ := by
    rw [Small.tanY, ← e, Category.assoc, ← hm2, ← Category.assoc, hu2, Category.assoc]
    rfl
  rw [e2]
  exact h2

end ModelDimension.Near
