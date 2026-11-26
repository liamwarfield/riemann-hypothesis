module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StCocycle
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InOpenOfThickeningMorphism
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfCechSpectralSequence
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatBaseChangeCohomology
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechCohomologyFullSubcategoryIso
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatDefs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsPullForm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormCocycle
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormCocycle
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
open GlobalTheory.CatH (face toLast)
open GlobalTheory.CompanionTheory.CocProd (tele sa_val)
open GlobalTheory.CompanionTheory.TowerEnd (Q dQ val Vals cl d_cl dQ_apply)

noncomputable section
namespace GlobalTheory.CompanionTheory.GrForm.Coc

theorem alt_sum {B : Type*} [CommRing B] {j : ℕ} (w : Fin j → Fin (j + 2) → B) :
    ∑ i : Fin (j + 2), (-1 : B) ^ (i : ℕ) *
      ∏ k : Fin j, (w k (i.succAbove k.succ) - w k (i.succAbove k.castSucc)) = 0 := by
  classical
  set u : Fin j → B := fun k => w k k.succ.castSucc - w k k.castSucc.castSucc with hu
  set v : Fin j → B := fun k => w k k.succ.succ - w k k.succ.castSucc with hv
  set P : ℕ → B := fun n => ∏ k : Fin j, if (k : ℕ) < n then u k else v k with hP
  set T : Fin (j + 2) → B := fun i =>
    ∏ k : Fin j, (w k (i.succAbove k.succ) - w k (i.succAbove k.castSucc)) with hT
  have cg : ∀ (k : Fin j) {p q p' q' : Fin (j + 2)}, (p : ℕ) = p' → (q : ℕ) = q' →
      w k p - w k q = w k p' - w k q' := by
    intro k p q p' q' h h'
    rw [Fin.ext h, Fin.ext h']
  have hT0 : T (Fin.castSucc 0) = P 0 := by
    refine Finset.prod_congr rfl fun k _ => ?_
    simp only [Nat.not_lt_zero, if_false]
    refine cg k ?_ ?_ <;> simp only [sa_val, Fin.val_succ, Fin.val_castSucc, Fin.val_zero, Fin.val_last] <;> split_ifs <;> omega
  have hTl : T (Fin.last (j + 1)) = P j := by
    refine Finset.prod_congr rfl fun k _ => ?_
    simp only [k.2, if_true]
    refine cg k ?_ ?_ <;> simp only [sa_val, Fin.val_succ, Fin.val_castSucc, Fin.val_zero, Fin.val_last] <;> split_ifs <;> omega
  have hTi : ∀ i : Fin j, T i.succ.castSucc = P (i + 1) + P i := by
    intro i
    have hPa : P (i + 1) = u i * ∏ k ∈ Finset.univ.erase i, (if (k : ℕ) < i + 1 then u k else v k) := by
      have := Finset.mul_prod_erase Finset.univ (fun k : Fin j => if (k : ℕ) < i + 1 then u k else v k) (Finset.mem_univ i)
      simp only [Nat.lt_add_one, if_true] at this
      exact this.symm
    have hPb : P i = v i * ∏ k ∈ Finset.univ.erase i, (if (k : ℕ) < i then u k else v k) := by
      have := Finset.mul_prod_erase Finset.univ (fun k : Fin j => if (k : ℕ) < i then u k else v k) (Finset.mem_univ i)
      simp only [lt_irrefl, if_false] at this
      exact this.symm
    have hTa : T i.succ.castSucc = (u i + v i) * ∏ k ∈ Finset.univ.erase i, (if (k : ℕ) < i then u k else v k) := by
      have := Finset.mul_prod_erase Finset.univ (fun k : Fin j => w k (i.succ.castSucc.succAbove k.succ) -
        w k (i.succ.castSucc.succAbove k.castSucc)) (Finset.mem_univ i)
      refine this.symm.trans ?_
      congr 1
      · have e : u i + v i = w i i.succ.succ - w i i.castSucc.castSucc := by
          rw [hu, hv]; ring
        rw [e]
        refine cg i ?_ ?_ <;> simp only [sa_val, Fin.val_succ, Fin.val_castSucc, Fin.val_zero, Fin.val_last] <;> split_ifs <;> omega
      · refine Finset.prod_congr rfl fun k hk => ?_
        have hki : (k : ℕ) ≠ i := fun h => Finset.ne_of_mem_erase hk (Fin.ext h)
        split_ifs with h
        · refine cg k ?_ ?_ <;> simp only [sa_val, Fin.val_succ, Fin.val_castSucc, Fin.val_zero, Fin.val_last] <;> split_ifs <;> omega
        · refine cg k ?_ ?_ <;> simp only [sa_val, Fin.val_succ, Fin.val_castSucc, Fin.val_zero, Fin.val_last] <;> split_ifs <;> omega
    have hE : ∏ k ∈ Finset.univ.erase i, (if (k : ℕ) < i + 1 then u k else v k) =
        ∏ k ∈ Finset.univ.erase i, (if (k : ℕ) < i then u k else v k) := by
      refine Finset.prod_congr rfl fun k hk => ?_
      have hki : (k : ℕ) ≠ i := fun h => Finset.ne_of_mem_erase hk (Fin.ext h)
      have : (k : ℕ) < i + 1 ↔ (k : ℕ) < i := by omega
      simp only [this]
    rw [hTa, hPa, hPb, hE]
    ring
  change ∑ i : Fin (j + 2), (-1 : B) ^ (i : ℕ) * T i = 0
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_succ]
  have hint : ∑ i : Fin j, (-1 : B) ^ ((i.succ.castSucc : Fin (j + 2)) : ℕ) * T i.succ.castSucc =
      ∑ m ∈ Finset.range j, (-1 : B) ^ (m + 1) * (P (m + 1) + P m) := by
    rw [← Fin.sum_univ_eq_sum_range (fun m => (-1 : B) ^ (m + 1) * (P (m + 1) + P m)) j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hTi]
    simp only [Fin.val_castSucc, Fin.val_succ]
  rw [hint, hT0, hTl]
  simp only [Fin.val_castSucc, Fin.val_zero, Fin.val_last, pow_zero]
  linear_combination tele P j

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C}

def vt (c : ∀ T : C, Φ.A.obj T) {n : ℕ} (s : ComposableArrows C n) (p : Fin (n + 1)) :
    Φ.A.obj (s.obj (Fin.last n)) :=
  (Φ.A.map (s.map (homOfLE (Fin.le_last p)))).hom (c (s.obj p))

theorem vt_last (c : ∀ T : C, Φ.A.obj T) {n : ℕ} (s : ComposableArrows C n) (p : Fin (n + 1))
    (hp : p = Fin.last n) : vt c s p = c (s.obj (Fin.last n)) := by
  subst hp
  have : (homOfLE (Fin.le_last (Fin.last n)) : Fin.last n ⟶ Fin.last n) = 𝟙 _ := Subsingleton.elim _ _
  unfold vt
  rw [this, s.map_id]
  simp

theorem face_vt (c : ∀ T : C, Φ.A.obj T) {j : ℕ} (s : ComposableArrows C (j + 1)) (i : Fin (j + 2)) :
    (Φ.A.map (toLast i s)).hom (c ((face i s).obj (Fin.last j))) = vt c s (i.succAbove (Fin.last j)) := rfl

theorem face_wz {d j : ℕ} (u : Fin d → ∀ T : C, Φ.A.obj T) (I : Fin j → Fin d)
    (s : ComposableArrows C (j + 1)) (i : Fin (j + 2)) :
    (Φ.A.map (toLast i s)).hom (wz u I (face i s)) =
      ∏ k : Fin j, (vt (u (I k)) s (i.succAbove k.succ) - vt (u (I k)) s (i.succAbove k.castSucc)) := by
  have map_map {X Y Z : C} (g : X ⟶ Y) (f : Y ⟶ Z) (y : Φ.A.obj X) :
      (Φ.A.map f).hom ((Φ.A.map g).hom y) = (Φ.A.map (g ≫ f)).hom y := by
    simp
  unfold wz
  rw [map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  simp only [map_sub]
  rw [map_map]
  have e : (face i s).map (homOfLE (Fin.le_last k.succ)) ≫ toLast i s =
      s.map (homOfLE (Fin.le_last (i.succAbove k.succ))) := by
    change s.map _ ≫ s.map _ = _
    rw [← s.map_comp]; rfl
  rw [e, map_map, e, map_map]
  have e2 : (face i s).map (homOfLE (Fin.castSucc_lt_succ (i := k)).le) ≫
      s.map (homOfLE (Fin.le_last (i.succAbove k.succ))) =
      s.map (homOfLE (Fin.le_last (i.succAbove k.castSucc))) := by
    change s.map _ ≫ s.map _ = _
    rw [← s.map_comp]; rfl
  rw [e2]
  rfl

theorem d_mem {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil) {d j : ℕ} (u : Fin d → ∀ T : C, Φ.A.obj T)
    (hu : ∀ i {T T' : C} (φ : T ⟶ T'), u i T' - (Φ.A.map φ).hom (u i T) ∈ Φ.J.S T')
    (y : ∀ T : C, Φ.A.obj T) (hy : ∀ {T T' : C} (φ : T ⟶ T'), y T' - (Φ.A.map φ).hom (y T) ∈ Φ.J.S T')
    (I : Fin j → Fin d) (s : ComposableArrows C (j + 1)) :
    ∑ i : Fin (j + 2), (-1 : ℤ) ^ (i : ℕ) • (Φ.A.map (toLast i s)).hom
      (wz u I (face i s) * y ((face i s).obj (Fin.last j))) ∈ (Fil ((j : ℤ) + 1)).S _ := by
  set Y := y (s.obj (Fin.last (j + 1))) with hY
  set T : Fin (j + 2) → Φ.A.obj (s.obj (Fin.last (j + 1))) := fun i =>
    ∏ k : Fin j, (vt (u (I k)) s (i.succAbove k.succ) - vt (u (I k)) s (i.succAbove k.castSucc)) with hT
  set V : Fin (j + 2) → Φ.A.obj (s.obj (Fin.last (j + 1))) := fun i =>
    vt y s (i.succAbove (Fin.last j)) with hV
  have hVY : ∀ i : Fin (j + 1), V i.castSucc = Y := by
    intro i
    refine vt_last y s _ (Fin.ext ?_)
    have := i.2
    rw [sa_val]
    simp only [Fin.val_last, Fin.val_castSucc]
    split_ifs <;> omega
  have hsum : ∑ i : Fin (j + 2), (-1 : ℤ) ^ (i : ℕ) • (Φ.A.map (toLast i s)).hom
      (wz u I (face i s) * y ((face i s).obj (Fin.last j))) =
      (-1) ^ j * (T (Fin.last (j + 1)) * (Y - V (Fin.last (j + 1)))) := by
    have hterm : ∀ i : Fin (j + 2), (-1 : ℤ) ^ (i : ℕ) • (Φ.A.map (toLast i s)).hom
        (wz u I (face i s) * y ((face i s).obj (Fin.last j))) = (-1) ^ (i : ℕ) * (T i * V i) := by
      intro i
      rw [map_mul, face_wz, face_vt, zsmul_eq_mul]
      push_cast
      rfl
    have h0 := alt_sum (B := Φ.A.obj (s.obj (Fin.last (j + 1)))) (j := j) (fun k p => vt (u (I k)) s p)
    change ∑ i : Fin (j + 2), (-1) ^ (i : ℕ) * T i = 0 at h0
    rw [Fin.sum_univ_castSucc] at h0
    rw [Finset.sum_congr rfl fun i _ => hterm i, Fin.sum_univ_castSucc]
    have h1 : ∑ i : Fin (j + 1), (-1) ^ ((i.castSucc : Fin (j + 2)) : ℕ) * (T i.castSucc * V i.castSucc) =
        (∑ i : Fin (j + 1), (-1) ^ ((i.castSucc : Fin (j + 2)) : ℕ) * T i.castSucc) * Y := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hVY]
      ring
    rw [h1]
    simp only [Fin.val_last] at h0 ⊢
    linear_combination Y * h0
  rw [hsum]
  refine Ideal.mul_mem_left _ _ ?_
  have hA : T (Fin.last (j + 1)) ∈ (Fil (j : ℤ)).S _ := by
    have := (Fil (j : ℤ)).map_mem (toLast (Fin.last (j + 1)) s) (wz_mem hF u hu I (face (Fin.last (j + 1)) s))
    rwa [face_wz] at this
  have hB : Y - V (Fin.last (j + 1)) ∈ (Fil ((1 : ℕ) : ℤ)).S _ := by
    have e : (((1 : ℕ) : ℤ)) = 1 := rfl
    rw [e, hF.one]
    have h := hy (s.map (homOfLE (show (Fin.last j).castSucc ≤ Fin.last (j + 1) from Fin.le_last _)))
    have e2 : V (Fin.last (j + 1)) = (Φ.A.map (s.map (homOfLE (show (Fin.last j).castSucc ≤ Fin.last (j + 1) from Fin.le_last _)))).hom
        (y (s.obj (Fin.last j).castSucc)) := by
      have : (Fin.last (j + 1)).succAbove (Fin.last j) = (Fin.last j).castSucc := Fin.succAbove_last_apply _
      simp only [hV, vt]
      rw [this]
    rw [e2]
    exact h
  have h := hF.mul j 1 _ hA hB
  have e : ((j + 1 : ℕ) : ℤ) = (j : ℤ) + 1 := by push_cast; ring
  rwa [e] at h

end GlobalTheory.CompanionTheory.GrForm.Coc


open GlobalTheory.CompanionTheory.GrForm.Coc in
theorem GlobalTheory.CompanionTheory.GrForm.stCocycle : GlobalTheory.CompanionTheory.GrForm.StCocycle := by
  intro R _ C _ Φ Fil hF d j u hu y hy I
  let z : Q Φ.A j := fun s => (wz u I s * y (s.obj (Fin.last j)) : Φ.A.obj (s.obj (Fin.last j)))
  have hz : Vals (Fil j) z := fun s => Ideal.mul_mem_right _ _ (wz_mem hF u hu I s)
  refine ⟨cl (Fil j) (Fil ((j : ℤ) + 1)) z hz, ?_, fun s => rfl⟩
  rw [d_cl]
  funext s
  apply Subtype.ext
  change Ideal.Quotient.mk _ (val (dQ Φ.A j z) s) = 0
  rw [dQ_apply]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (d_mem hF u hu y hy I s)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormCocycleStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_form_cocycle : GlobalTheory.CompanionTheory.GrForm.StCocycle := by
  first | exact @GlobalTheory.CompanionTheory.GrForm.stCocycle | exact GlobalTheory.CompanionTheory.GrForm.stCocycle | (intros; apply GlobalTheory.CompanionTheory.GrForm.stCocycle <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormExistsOfCocycle
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormExistsOfCocycle
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
noncomputable section
namespace GlobalTheory.CompanionTheory.GrForm

variable {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}

theorem lift_sub_mem {W : X.Opens} {P : ObjectProperty (Thick (LL q))} (hP : ∀ T, P T → InU W T) (f : Γ(X, W))
    (v : ∀ T : Thick (LL q), T.B) (hv : ∀ (T : Thick (LL q)) (h : InU W T), Ideal.Quotient.mk T.J (v T) = ev T h f)
    {T T' : P.FullSubcategory} (φ : T ⟶ T') :
    (show (sP P).A.obj T' from v T'.obj) - ((sP P).A.map φ).hom (show (sP P).A.obj T from v T.obj) ∈ (sP P).J.S T' := by
  have h := hP _ T.property
  have h' := hP _ T'.property
  change v T'.obj - φ.hom.φ (v T.obj) ∈ T'.obj.J
  rw [← Ideal.Quotient.eq, hv _ h', ev_nat φ.hom h h' f, ← hv _ h]
  rfl

theorem exists_of_cocycle : StCocycle → StExists := by
  intro hC O _ X q W d t u hu P hP r x
  have hF := GlobalTheory.CompanionTheory.DPFil.isFil_sFil P
  have hu' : ∀ i {T T' : P.FullSubcategory} (φ : T ⟶ T'),
      (show (sP P).A.obj T' from u i T'.obj) - ((sP P).A.map φ).hom (show (sP P).A.obj T from u i T.obj) ∈ (sP P).J.S T' :=
    fun i _ _ φ => lift_sub_mem hP (t i) (u i) (hu i) φ
  have hy : ∀ (I : Idx r d) {T T' : P.FullSubcategory} (φ : T ⟶ T'),
      (show (sP P).A.obj T' from lft W T'.obj (x I)) -
        ((sP P).A.map φ).hom (show (sP P).A.obj T from lft W T.obj (x I)) ∈ (sP P).J.S T' :=
    fun I _ _ φ => lift_sub_mem hP (x I) (fun T => lft W T (x I)) (fun T h => lft_spec T h (x I)) φ
  choose f hf hz using fun I : Idx r d =>
    hC hF (fun i (T : P.FullSubcategory) => (show (sP P).A.obj T from u i T.obj)) hu'
      (fun T : P.FullSubcategory => (show (sP P).A.obj T from lft W T.obj (x I))) (hy I) I.1
  have hd : CH.d (sq (sFil P r) (sFil P ((r : ℤ) + 1))) r (∑ I, f I) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_eq_zero fun I _ => hf I
  refine ⟨(CH.cx (sq (sFil P r) (sFil P ((r : ℤ) + 1)))).cls (∑ I, f I) hd, ∑ I, f I, hd, rfl, ?_⟩
  intro s
  have e : (show sqM (sFil P r) (sFil P ((r : ℤ) + 1)) _ from (∑ I, f I) s) =
      ∑ I, (show sqM (sFil P r) (sFil P ((r : ℤ) + 1)) _ from f I s) := Finset.sum_apply _ _ _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, AddSubmonoidClass.coe_finsetSum, map_sum]
  exact Finset.sum_congr rfl fun I _ => hz I s

end GlobalTheory.CompanionTheory.GrForm
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormExistsOfCocycleStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_form_exists_of_cocycle : GlobalTheory.CompanionTheory.GrForm.StCocycle → GlobalTheory.CompanionTheory.GrForm.StExists := by
  first | exact @GlobalTheory.CompanionTheory.GrForm.exists_of_cocycle | exact GlobalTheory.CompanionTheory.GrForm.exists_of_cocycle | (intros; apply GlobalTheory.CompanionTheory.GrForm.exists_of_cocycle <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormVanishOfFrame
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormVanishOfFrame
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section
namespace GlobalTheory.CompanionTheory.GrForm

theorem isLift_lft {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} (W : X.Opens) {d : ℕ}
    (t : Fin d → Γ(X, W)) : IsLift (q := q) W t (fun i T => lft W T (t i)) :=
  fun i T h => lft_spec T h (t i)

theorem rep_zero {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R} (a b : IdF A) {j : ℕ}
    (c : CH.H (sq a b) j) (h : Rep a b (fun s => 0) c) : c = 0 := by
  obtain ⟨f, hf, rfl, hz⟩ := h
  have e : f = 0 := by
    funext s
    apply Subtype.ext
    rw [show (show sqM a b _ from f s).1 = _ from hz s]
    simp
  subst e
  rfl

theorem van : StFrame → CrystallineSemistableComparison.Pb.KH.LocGr → CrystallineSemistableComparison.Pb.KH.PolyTf → StVan := by
  intro hFr hL hP O _ l s hb X q W d c r j hrs hjr
  obtain ⟨E, σ, θ, hGr, hbot, -, -, -⟩ := hFr l s hb q c _ (isLift_lft W c.t)
  obtain ⟨Q, hQ⟩ := hP (dividedPowersBot O) q (Ideal.Quotient.mk ⊥) l s {W}
  have hCr : ∀ r' ≤ (r : ℤ) + 1, Q.Crit (sFil (SS q l s W)) r' := fun r' h => (hQ r' (by omega)).1
  have key := hL Q (GlobalTheory.CompanionTheory.DPFil.isFil_sFil (SS q l s W)) E σ hGr (r : ℤ) hCr j
  rcases lt_or_gt_of_ne hjr with hlt | hlt
  · obtain ⟨h1, -⟩ := key.2 (r - j) (by omega)
    have all : ∀ cl : CH.H (gr (sFil (SS q l s W)) (r : ℤ)) j, cl = 0 := by
      intro cl
      obtain ⟨x, hx, hR⟩ := h1 cl
      have x0 : ∀ I, x I = 0 := fun I => by
        have h := hx I
        rw [hbot (r - j) (by omega)] at h
        exact h
      have e : (fun s => ∑ I : Idx j d, E.form σ I.1 (x I) s) = fun s => 0 := by
        funext s
        refine Finset.sum_eq_zero fun I _ => ?_
        simp [x0, Frame.form]
      rw [e] at hR
      exact rep_zero _ _ cl hR
    exact ⟨fun a b => (all a).trans (all b).symm⟩
  · exact key.1 (by exact_mod_cast hlt)

end GlobalTheory.CompanionTheory.GrForm
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormVanishOfFrameStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_form_vanish_of_frame : GlobalTheory.CompanionTheory.GrForm.StFrame → CrystallineSemistableComparison.Pb.KH.LocGr → CrystallineSemistableComparison.Pb.KH.PolyTf → GlobalTheory.CompanionTheory.GrForm.StVan := by
  first | exact @GlobalTheory.CompanionTheory.GrForm.van | exact GlobalTheory.CompanionTheory.GrForm.van | (intros; apply GlobalTheory.CompanionTheory.GrForm.van <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StableFamilyPropertiesStatement
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StableFamilyProperties
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.StFam

theorem st_all :
    (∀ {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} (Q : ObjectProperty (Thick (nlFun γ p X q κ))) {ι : Type} (U : ι → X.Opens) (α : ι) ⦃T T' : Thick (nlFun γ p X q κ)⦄ (φ : T ⟶ T'), St Q {U α} T → (∃ β, St Q {U β} T') → St Q {U α} T') ∧ (∀ {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} (Q : ObjectProperty (Thick (nlFun γ p X q κ))) {ι : Type} (U : ι → X.Opens), (fun T => ∃ α, St Q {U α} T) = St Q (Set.range U)) ∧ (∀ {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} (Q : ObjectProperty (Thick (nlFun γ p X q κ))) {ι : Type} (U : ι → X.Opens) (S : Finset ι), S.Nonempty → capS (fun α => St Q {U α}) S = St Q {⨅ α ∈ S, U α}) ∧ (∀ {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} (Q : ObjectProperty (Thick (nlFun γ p X q κ))) {ι : Type} (U : ι → X.Opens) {n : ℕ} (i : Fin (n + 1) → ι), capT (fun α => St Q {U α}) i = St Q {capO U i}) := by
  have one : ∀ {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ}
      {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I}
      (Q : ObjectProperty (Thick (nlFun γ p X q κ))) (V : X.Opens) (T : Thick (nlFun γ p X q κ)),
      St Q {V} T ↔ Q T ∧ InU V T := by
    intro O _ R _ I γ p X q κ Q V T
    constructor
    · rintro ⟨hQ, W, hW, hT⟩
      rw [Set.mem_singleton_iff] at hW
      subst hW
      exact ⟨hQ, hT⟩
    · rintro ⟨hQ, hT⟩
      exact ⟨hQ, V, rfl, hT⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro O _ R _ I γ p X q κ Q ι U α T T' φ h h'
    obtain ⟨β, hβ⟩ := h'
    exact (one Q _ T').2 ⟨((one Q _ T').1 hβ).1, GlobalTheory.CompanionTheory.ThickPt.inU_map (U α) φ ((one Q _ T).1 h).2⟩
  · intro O _ R _ I γ p X q κ Q ι U
    funext T
    refine propext ⟨?_, ?_⟩
    · rintro ⟨α, hα⟩
      obtain ⟨hQ, hT⟩ := (one Q _ T).1 hα
      exact ⟨hQ, U α, ⟨α, rfl⟩, hT⟩
    · rintro ⟨hQ, V, ⟨α, rfl⟩, hT⟩
      exact ⟨α, (one Q _ T).2 ⟨hQ, hT⟩⟩
  · intro O _ R _ I γ p X q κ Q ι U S hS
    funext T
    refine propext ⟨?_, ?_⟩
    · intro h
      obtain ⟨a, ha⟩ := hS
      exact (one Q _ T).2 ⟨((one Q _ T).1 (h a ha)).1,
        (GlobalTheory.CompanionTheory.Thick.inU_iInf_finset U S T).2 fun α hα => ((one Q _ T).1 (h α hα)).2⟩
    · intro h α hα
      obtain ⟨hQ, hT⟩ := (one Q _ T).1 h
      exact (one Q _ T).2 ⟨hQ, (GlobalTheory.CompanionTheory.Thick.inU_iInf_finset U S T).1 hT α hα⟩
  · intro O _ R _ I γ p X q κ Q ι U n i
    have key : ∀ T : Thick (nlFun γ p X q κ), InU (capO U i) T ↔ ∀ a, InU (U (i a)) T := by
      intro T
      have h := GlobalTheory.CompanionTheory.Thick.inU_iInf_finset (fun a => U (i a)) (Finset.univ : Finset (Fin (n + 1))) T
      have e : (⨅ a ∈ (Finset.univ : Finset (Fin (n + 1))), U (i a)) = capO U i := by
        simp [capO]
      rw [e] at h
      simpa using h
    funext T
    refine propext ⟨?_, ?_⟩
    · intro h
      exact (one Q _ T).2 ⟨((one Q _ T).1 (h 0)).1, (key T).2 fun a => ((one Q _ T).1 (h a)).2⟩
    · intro h a
      obtain ⟨hQ, hT⟩ := (one Q _ T).1 h
      exact (one Q _ T).2 ⟨hQ, (key T).1 hT a⟩

end GlobalTheory.CompanionTheory.StFam
end

set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stable_family_properties : (∀ {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} (Q : ObjectProperty (Thick (nlFun γ p X q κ))) {ι : Type} (U : ι → X.Opens) (α : ι) ⦃T T' : Thick (nlFun γ p X q κ)⦄ (φ : T ⟶ T'), St Q {U α} T → (∃ β, St Q {U β} T') → St Q {U α} T') ∧ (∀ {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} (Q : ObjectProperty (Thick (nlFun γ p X q κ))) {ι : Type} (U : ι → X.Opens), (fun T => ∃ α, St Q {U α} T) = St Q (Set.range U)) ∧ (∀ {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} (Q : ObjectProperty (Thick (nlFun γ p X q κ))) {ι : Type} (U : ι → X.Opens) (S : Finset ι), S.Nonempty → capS (fun α => St Q {U α}) S = St Q {⨅ α ∈ S, U α}) ∧ (∀ {O : Type} [CommRing O] {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} (Q : ObjectProperty (Thick (nlFun γ p X q κ))) {ι : Type} (U : ι → X.Opens) {n : ℕ} (i : Fin (n + 1) → ι), capT (fun α => St Q {U α}) i = St Q {capO U i}) := by
  first | exact @GlobalTheory.CompanionTheory.StFam.st_all | exact GlobalTheory.CompanionTheory.StFam.st_all | (intros; apply GlobalTheory.CompanionTheory.StFam.st_all <;> assumption)
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormRestrict
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormRestrict
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
noncomputable section
namespace GlobalTheory.CompanionTheory.GrForm

variable {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}

theorem lift_cocycle_mem {W : X.Opens} {d : ℕ} {t : Fin d → Γ(X, W)} {u : Fin d → ∀ T : Thick (LL q), T.B}
    (hu : IsLift W t u) {Q : ObjectProperty (Thick (LL q))} (hQ : ∀ T, Q T → InU W T) (i : Fin d)
    {T T' : Q.FullSubcategory} (φ : T ⟶ T') :
    (show (sP Q).A.obj T' from u i T'.obj) - ((sP Q).A.map φ).hom (show (sP Q).A.obj T from u i T.obj) ∈ (sP Q).J.S T' := by
  have h := hQ _ T.property
  have h' := hQ _ T'.property
  change u i T'.obj - φ.hom.φ (u i T.obj) ∈ T'.obj.J
  refine Ideal.Quotient.eq.1 ?_
  rw [hu i T'.obj h', ev_nat φ.hom h h' (t i), ← hu i T.obj h]
  rfl

theorem lft_res_sub_mem {W W' : X.Opens} (hW : W' ≤ W) (T : Thick (LL q)) (h : InU W T) (h' : InU W' T) (f : Γ(X, W)) :
    lft W T f - lft W' T (rs hW f) ∈ T.J := by
  refine Ideal.Quotient.eq.1 ?_
  rw [lft_spec T h f, lft_spec T h' (rs hW f), ev_res hW T h h' f]

theorem stRes : StRes := by
  intro O _ X q W W' hW d t u hu P P' hPP hP hP' r x c hc
  obtain ⟨f, hf, rfl, hz⟩ := hc
  have hF := GlobalTheory.CompanionTheory.DPFil.isFil_sFil P'
  have hP'W : ∀ T, P' T → InU W T := fun T h => hP T (hPP T h)
  refine ⟨(resU (GF q r) hPP).pullC r f, ?_, rfl, ?_⟩
  · have := (resU (GF q r) hPP).d_pullC r f
    refine this.trans ?_
    have hf' : CH.d (P.ι ⋙ GF q r) r f = 0 := hf
    rw [hf', map_zero]
  · intro s
    refine (hz (s ⋙ ObjectProperty.ιOfLE hPP)).trans ?_
    refine Ideal.Quotient.eq.2 ?_
    have hdiff : ∀ I : Idx r d,
        wz (Φ := sP P') (fun i T => u i T.obj) I.1 s *
          ((show (sP P').A.obj (s.obj (Fin.last r)) from lft W (s.obj (Fin.last r)).obj (x I)) -
            (show (sP P').A.obj (s.obj (Fin.last r)) from lft W' (s.obj (Fin.last r)).obj (rs hW (x I)))) ∈
          (sFil P' ((r : ℤ) + 1)).S (s.obj (Fin.last r)) := by
      intro I
      have hw := wz_mem hF (fun i T => u i T.obj)
        (fun i {T T'} φ => lift_cocycle_mem hu hP'W i φ) I.1 s
      have hδ : (show (sP P').A.obj (s.obj (Fin.last r)) from lft W (s.obj (Fin.last r)).obj (x I)) -
          (show (sP P').A.obj (s.obj (Fin.last r)) from lft W' (s.obj (Fin.last r)).obj (rs hW (x I))) ∈
          (sFil P' ((1 : ℕ) : ℤ)).S (s.obj (Fin.last r)) := by
        have e : (sFil P' ((1 : ℕ) : ℤ)).S (s.obj (Fin.last r)) = (sP P').J.S (s.obj (Fin.last r)) := hF.one _
        rw [e]
        exact lft_res_sub_mem hW _ (hP'W _ (s.obj (Fin.last r)).property) (hP' _ (s.obj (Fin.last r)).property) (x I)
      have := hF.mul r 1 _ hw hδ
      simpa using this
    have hsum := Ideal.sum_mem _ (t := Finset.univ) (fun I _ => hdiff I)
    simp only [mul_sub, Finset.sum_sub_distrib] at hsum
    exact hsum

end GlobalTheory.CompanionTheory.GrForm
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GradedFormRestrictStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_form_restrict : GlobalTheory.CompanionTheory.GrForm.StRes := by
  first | exact @GlobalTheory.CompanionTheory.GrForm.stRes | exact GlobalTheory.CompanionTheory.GrForm.stRes | (intros; apply GlobalTheory.CompanionTheory.GrForm.stRes <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeIdealQuotientChain
open DividedPowers CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LatVal

variable {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ)

theorem f_mem_IB : f ξ ∈ Lat.IB f ξ := Ideal.subset_span (Set.mem_singleton _)

theorem η_mem_IB : Lat.η f ξ l M ∈ Lat.IB f ξ := by
  unfold Lat.η
  rw [Algebra.smul_def]
  exact Ideal.mul_mem_left _ _ (f_mem_IB f ξ)

theorem dpE_succ_mem_IB (i : ℕ) : Lat.dpE f ξ l M (i + 1) ∈ Lat.IB f ξ := by
  unfold Lat.dpE
  rw [Algebra.smul_def]
  exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ (η_mem_IB f ξ l M) _ (Nat.succ_pos i))

theorem dpE_zero_eq : Lat.dpE f ξ l M 0 = 1 := by simp [Lat.dpE]

theorem exists_rep_B (x : B) (hx : x ∈ Lat.sub f ξ l M) : ∃ a : W, x - f a ∈ Lat.IB f ξ := by
  unfold Lat.sub at hx
  induction hx using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨w, rfl⟩ | ⟨i, rfl⟩
    · exact ⟨w, by simp⟩
    · cases i with
      | zero => exact ⟨1, by simp [dpE_zero_eq]⟩
      | succ i => exact ⟨0, by simpa using dpE_succ_mem_IB f ξ l M i⟩
  | zero => exact ⟨0, by simp⟩
  | one => exact ⟨1, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨a + b, ?_⟩
    have h := Ideal.add_mem _ ha hb
    have e : x + y - f (a + b) = x - f a + (y - f b) := by rw [map_add (f := _)]; ring
    rw [e]; exact h
  | neg x _ hx =>
    obtain ⟨a, ha⟩ := hx
    refine ⟨-a, ?_⟩
    have h := Ideal.neg_mem_iff _ |>.2 ha
    have e : -x - f (-a) = -(x - f a) := by rw [map_neg]; ring
    rw [e]; exact h
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨a * b, ?_⟩
    have h := Ideal.add_mem _ (Ideal.mul_mem_right y _ ha) (Ideal.mul_mem_left _ (f a) hb)
    have e : x * y - f (a * b) = (x - f a) * y + f a * (y - f b) := by rw [map_mul]; ring
    rw [e]; exact h

theorem exists_rep (x : Lat.A f ξ l M) : ∃ a : W, Lat.ι f ξ l M x - f a ∈ Lat.IB f ξ :=
  exists_rep_B f ξ l M _ x.2

theorem mem_of_dvd {a b : W} {x y : Lat.A f ξ l M}
    (hx : Lat.ι f ξ l M x - f a ∈ Lat.IB f ξ) (hy : Lat.ι f ξ l M y - f b ∈ Lat.IB f ξ)
    (h : Ideal.Quotient.mk (Ideal.span {ξ}) a ∣ Ideal.Quotient.mk (Ideal.span {ξ}) b) :
    y ∈ Ideal.span {x} ⊔ Lat.I f ξ l M := by
  obtain ⟨c', hc⟩ := h
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c'
  rw [← map_mul, Ideal.Quotient.eq, Ideal.mem_span_singleton] at hc
  obtain ⟨d, hd⟩ := hc
  have hI : y - Lat.ofW f ξ l M c * x ∈ Lat.I f ξ l M := by
    show Lat.ι f ξ l M (y - Lat.ofW f ξ l M c * x) ∈ Lat.IB f ξ
    have h1 : f (b - a * c) ∈ Lat.IB f ξ := by
      rw [hd, map_mul]; exact Ideal.mul_mem_right _ _ (f_mem_IB f ξ)
    have h2 := Ideal.add_mem _ (Ideal.sub_mem _ hy (Ideal.mul_mem_left _ (f c) hx)) h1
    have e : Lat.ι f ξ l M (y - Lat.ofW f ξ l M c * x)
        = Lat.ι f ξ l M y - f b - f c * (Lat.ι f ξ l M x - f a) + f (b - a * c) := by
      rw [map_sub, map_mul, Lat.ι_ofW, map_sub, map_mul]; ring
    rw [e]; exact h2
  have hs : Lat.ofW f ξ l M c * x ∈ Ideal.span {x} :=
    Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton _))
  have e : y = Lat.ofW f ξ l M c * x + (y - Lat.ofW f ξ l M c * x) := by ring
  rw [e]
  exact Submodule.add_mem_sup hs hI

theorem val : ∀ {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ) (m : ℕ),
    Lat.Hyp f ξ l m → ∀ x y : Lat.A f ξ l M,
      x ∈ Ideal.span {y} ⊔ Lat.I f ξ l M ∨ y ∈ Ideal.span {x} ⊔ Lat.I f ξ l M := by
  intro W B _ _ _ f ξ l M m h x y
  obtain ⟨a, ha⟩ := exists_rep f ξ l M x
  obtain ⟨b, hb⟩ := exists_rep f ξ l M y
  rcases h.val (Ideal.Quotient.mk _ a) (Ideal.Quotient.mk _ b) with hd | hd
  · exact Or.inr (mem_of_dvd f ξ l M ha hb hd)
  · exact Or.inl (mem_of_dvd f ξ l M hb ha hd)

end GlobalTheory.CompanionTheory.LatVal
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoverCupActionBasis
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoverCupActionBasis
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

namespace GlobalTheory.CompanionTheory.CechVB

theorem vb_basis : ∀ {O : Type} [CommRing O] {X : Scheme.{0}} (str : ∀ V : X.Opens, O →+* Γ(X, V)) {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} O) {ι : Type}
    (U : ι → X.Opens) (U' : ι → ObjectProperty C) (m : ℕ) (κ : ι → Type) [∀ α, Fintype (κ α)]
    (act : ∀ {n : ℕ} (i : Fin (n + 1) → ι), Γ(X, capO U i) →+* AddMonoid.End (HU F (capT U' i) m))
    (b : ∀ {n : ℕ} (i : Fin (n + 1) → ι) (a : Fin (n + 1)), κ (i a) → HU F (capT U' i) m)
    (g : ∀ α β, κ α → κ β → Γ(X, U α ⊓ U β))
    (hfree : ∀ (n : ℕ) (i : Fin (n + 1) → ι) (a : Fin (n + 1)) (h : HU F (capT U' i) m),
      ∃! f : κ (i a) → Γ(X, capO U i), h = ∑ k, act i (f k) (b i a k))
    (hstr : ∀ (n : ℕ) (i : Fin (n + 1) → ι) (c : O) (h : HU F (capT U' i) m), act i (str _ c) h = c • h)
    (hres : ∀ (n : ℕ) (i : Fin (n + 2) → ι) (j : Fin (n + 2)) (f : Γ(X, capO U (i ∘ j.succAbove))) (h : HU F (capT U' (i ∘ j.succAbove)) m),
      (resU F (U := capT U' (i ∘ j.succAbove)) (V := capT U' i) (fun _ h _ => h _)).pull m (act (i ∘ j.succAbove) f h) =
        act i (rs (capO_comp U i j.succAbove) f) ((resU F (U := capT U' (i ∘ j.succAbove)) (V := capT U' i) (fun _ h _ => h _)).pull m h))
    (hb : ∀ (n : ℕ) (i : Fin (n + 2) → ι) (j : Fin (n + 2)) (a : Fin (n + 1)) (k : κ (i (j.succAbove a))),
      (resU F (U := capT U' (i ∘ j.succAbove)) (V := capT U' i) (fun _ h _ => h _)).pull m (b (i ∘ j.succAbove) a k) = b i (j.succAbove a) k)
    (hg : ∀ (n : ℕ) (i : Fin (n + 1) → ι) (a a' : Fin (n + 1)) (k' : κ (i a')),
      b i a' k' = ∑ k, act i (rs (le_inf (capO_le U i a) (capO_le U i a')) (g (i a) (i a') k k')) (b i a k)),
    Nonempty (VB str U (CrystallineSemistableComparison.Pb.cechH F U' m)) := by
  intro O _ X str C _ F ι U U' m κ _ act b g hfree hstr hres hb hg
  simp only [ExistsUnique] at hfree
  choose co h1 h2 using hfree
  have actadd : ∀ {n : ℕ} (i : Fin (n + 1) → ι) (f f' : Γ(X, capO U i)) (h : HU F (capT U' i) m),
      act i (f + f') h = act i f h + act i f' h := by
    intro n i f f' h
    rw [map_add (f := _)]; rfl
  have actmul : ∀ {n : ℕ} (i : Fin (n + 1) → ι) (f f' : Γ(X, capO U i)) (h : HU F (capT U' i) m),
      act i (f * f') h = act i f (act i f' h) := by
    intro n i f f' h
    rw [map_mul]; rfl
  have actsum : ∀ {n : ℕ} (i : Fin (n + 1) → ι) {κ' : Type} (s : Finset κ') (f : κ' → Γ(X, capO U i))
      (h : HU F (capT U' i) m), act i (∑ k ∈ s, f k) h = ∑ k ∈ s, act i (f k) h := by
    intro n i κ' s f h
    exact map_sum ((AddMonoidHom.eval h).comp (act i).toAddMonoidHom) f s
  have coadd : ∀ (n : ℕ) (i : Fin (n + 1) → ι) (a : Fin (n + 1)) (h h' : HU F (capT U' i) m),
      co n i a (h + h') = co n i a h + co n i a h' := by
    intro n i a h h'
    refine (h2 n i a _ _ ?_).symm
    conv_lhs => rw [h1 n i a h, h1 n i a h']
    simp only [Pi.add_apply, actadd, Finset.sum_add_distrib]
  refine ⟨{ κ := κ, g := g, e := fun n a =>
              { toFun := fun x i => co n i a (x i)
                invFun := fun f i => ∑ k, act i (f i k) (b i a k)
                left_inv := fun x => funext fun i => (h1 n i a (x i)).symm
                right_inv := fun f => funext fun i => (h2 n i a _ (f i) rfl).symm
                map_add' := fun x y => funext fun i => coadd n i a (x i) (y i) }
            e_smul := ?_, e_δ := ?_, e_chg := ?_ }⟩
  · intro n a c x i k
    have key : co n i a (c • x i) = fun k => str _ c * co n i a (x i) k := by
      refine (h2 n i a _ _ ?_).symm
      rw [← hstr n i c (x i)]
      conv_lhs => rw [h1 n i a (x i)]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      exact Finset.sum_congr rfl fun k _ => (actmul i _ _ _).symm
    exact congrFun key k
  · intro n a b' x i k
    have key : co (n + 1) i (b'.succAbove a) ((resU F (U := capT U' (i ∘ b'.succAbove)) (V := capT U' i) (fun _ h _ => h _)).pull m (x (i ∘ b'.succAbove))) =
        fun k => rs (capO_comp U i b'.succAbove) (co n (i ∘ b'.succAbove) a (x (i ∘ b'.succAbove)) k) := by
      refine (h2 (n + 1) i (b'.succAbove a) _ _ ?_).symm
      conv_lhs => rw [h1 n (i ∘ b'.succAbove) a (x (i ∘ b'.succAbove))]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hres, hb]
    exact congrFun key k
  · intro n a b' x i k
    have key : co n i a (x i) = fun k => ∑ k' : κ (i b'), rs (le_inf (capO_le U i a) (capO_le U i b')) (g (i a) (i b') k k') * co n i b' (x i) k' := by
      refine (h2 n i a _ _ ?_).symm
      have e1 : ∀ k', act i (co n i b' (x i) k') (b i b' k') =
          ∑ k, act i (rs (le_inf (capO_le U i a) (capO_le U i b')) (g (i a) (i b') k k') * co n i b' (x i) k') (b i a k) := by
        intro k'
        conv_lhs => rw [hg n i a b' k']
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← actmul, mul_comm]
      conv_lhs => rw [h1 n i b' (x i)]
      rw [Finset.sum_congr rfl fun k' _ => e1 k', Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => (actsum i _ _ _).symm
    exact congrFun key k

end GlobalTheory.CompanionTheory.CechVB
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoverCupActionBasisStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cover_cup_action_basis : ∀ {O : Type} [CommRing O] {X : Scheme.{0}} (str : ∀ V : X.Opens, O →+* Γ(X, V)) {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} O) {ι : Type}
    (U : ι → X.Opens) (U' : ι → ObjectProperty C) (m : ℕ) (κ : ι → Type) [∀ α, Fintype (κ α)]
    (act : ∀ {n : ℕ} (i : Fin (n + 1) → ι), Γ(X, capO U i) →+* AddMonoid.End (HU F (capT U' i) m))
    (b : ∀ {n : ℕ} (i : Fin (n + 1) → ι) (a : Fin (n + 1)), κ (i a) → HU F (capT U' i) m)
    (g : ∀ α β, κ α → κ β → Γ(X, U α ⊓ U β))
    (hfree : ∀ (n : ℕ) (i : Fin (n + 1) → ι) (a : Fin (n + 1)) (h : HU F (capT U' i) m),
      ∃! f : κ (i a) → Γ(X, capO U i), h = ∑ k, act i (f k) (b i a k))
    (hstr : ∀ (n : ℕ) (i : Fin (n + 1) → ι) (c : O) (h : HU F (capT U' i) m), act i (str _ c) h = c • h)
    (hres : ∀ (n : ℕ) (i : Fin (n + 2) → ι) (j : Fin (n + 2)) (f : Γ(X, capO U (i ∘ j.succAbove))) (h : HU F (capT U' (i ∘ j.succAbove)) m),
      (resU F (U := capT U' (i ∘ j.succAbove)) (V := capT U' i) (fun _ h _ => h _)).pull m (act (i ∘ j.succAbove) f h) =
        act i (rs (capO_comp U i j.succAbove) f) ((resU F (U := capT U' (i ∘ j.succAbove)) (V := capT U' i) (fun _ h _ => h _)).pull m h))
    (hb : ∀ (n : ℕ) (i : Fin (n + 2) → ι) (j : Fin (n + 2)) (a : Fin (n + 1)) (k : κ (i (j.succAbove a))),
      (resU F (U := capT U' (i ∘ j.succAbove)) (V := capT U' i) (fun _ h _ => h _)).pull m (b (i ∘ j.succAbove) a k) = b i (j.succAbove a) k)
    (hg : ∀ (n : ℕ) (i : Fin (n + 1) → ι) (a a' : Fin (n + 1)) (k' : κ (i a')),
      b i a' k' = ∑ k, act i (rs (le_inf (capO_le U i a) (capO_le U i a')) (g (i a) (i a') k k')) (b i a k)),
    Nonempty (VB str U (CrystallineSemistableComparison.Pb.cechH F U' m)) := by
  first | exact @GlobalTheory.CompanionTheory.CechVB.vb_basis | exact GlobalTheory.CompanionTheory.CechVB.vb_basis | (intros; apply GlobalTheory.CompanionTheory.CechVB.vb_basis <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeIdealIsPrime
set_option autoImplicit false

open DividedPowers CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LatPrime

section
variable {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W) (l M : ℕ)

theorem f_mem_IB : f ξ ∈ Lat.IB f ξ := by
  rw [Lat.IB]
  exact Ideal.mem_span_singleton_self _

theorem eta_mem_IB : Lat.η f ξ l M ∈ Lat.IB f ξ := by
  rw [Lat.η, Algebra.smul_def]
  exact Ideal.mul_mem_left _ _ (f_mem_IB f ξ)

theorem dpE_succ_mem_IB (i : ℕ) : Lat.dpE f ξ l M (i + 1) ∈ Lat.IB f ξ := by
  rw [Lat.dpE, Algebra.smul_def]
  exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ (eta_mem_IB f ξ l M) _ (Nat.succ_pos i))

theorem dpE_zero : Lat.dpE f ξ l M 0 = 1 := by simp [Lat.dpE]

theorem exists_sub_mem_IB {x : B} (hx : x ∈ Lat.sub f ξ l M) :
    ∃ a : W, x - f a ∈ Lat.IB f ξ := by
  unfold Lat.sub at hx
  induction hx using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨w, rfl⟩ | ⟨i, rfl⟩
    · exact ⟨w, by rw [sub_self]; exact zero_mem _⟩
    · cases i with
      | zero => exact ⟨1, by rw [dpE_zero, map_one, sub_self]; exact zero_mem _⟩
      | succ i => exact ⟨0, by rw [map_zero, sub_zero]; exact dpE_succ_mem_IB f ξ l M i⟩
  | zero => exact ⟨0, by rw [map_zero, sub_zero]; exact zero_mem _⟩
  | one => exact ⟨1, by rw [map_one, sub_self]; exact zero_mem _⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨a + b, ?_⟩
    have e : x + y - f (a + b) = (x - f a) + (y - f b) := by rw [map_add (f := _)]; ring
    rw [e]
    exact add_mem ha hb
  | neg x _ hx =>
    obtain ⟨a, ha⟩ := hx
    refine ⟨-a, ?_⟩
    have e : -x - f (-a) = -(x - f a) := by rw [map_neg]; ring
    rw [e]
    exact neg_mem ha
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨a * b, ?_⟩
    have e : x * y - f (a * b) = (x - f a) * y + f a * (y - f b) := by rw [map_mul]; ring
    rw [e]
    exact add_mem (Ideal.mul_mem_right _ _ ha) (Ideal.mul_mem_left _ _ hb)

theorem ι_mem_sub (x : Lat.A f ξ l M) : Lat.ι f ξ l M x ∈ Lat.sub f ξ l M := by
  exact (show ↥(Lat.sub f ξ l M) from x).2

theorem dvd_of_mem_IB {m : ℕ} (hyp : Lat.Hyp f ξ l m) {a : W} (ha : f a ∈ Lat.IB f ξ) : ξ ∣ a := by
  rw [Lat.IB, Ideal.mem_span_singleton] at ha
  obtain ⟨b, hb⟩ := ha
  have hm : 0 < m := hyp.one_le
  refine hyp.gr 0 hm a b ?_
  rw [pow_zero, mul_one, zero_add, pow_one]
  exact hb

end

theorem I_isPrime : ∀ {W B : Type} [CommRing W] [CommRing B] [Algebra ℚ B] (f : W →+* B) (ξ : W)
    (l M : ℕ) (m : ℕ), Lat.Hyp f ξ l m → (Lat.I f ξ l M).IsPrime := by
  intro W B _ _ _ f ξ l M m hyp
  haveI := hyp.dom
  have key : ∀ a : W, f a ∈ Lat.IB f ξ ↔ ξ ∣ a := by
    intro a
    refine ⟨fun ha => dvd_of_mem_IB f ξ l hyp ha, ?_⟩
    rintro ⟨c, rfl⟩
    rw [map_mul]
    exact Ideal.mul_mem_right _ _ (f_mem_IB f ξ)
  have hq : ∀ a : W, ξ ∣ a ↔ Ideal.Quotient.mk (Ideal.span {ξ}) a = 0 := by
    intro a
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  refine ⟨?_, ?_⟩
  · intro htop
    rw [Ideal.eq_top_iff_one] at htop
    simp only [Lat.I, Ideal.mem_comap] at htop
    have h2 : f 1 ∈ Lat.IB f ξ := by rwa [map_one, ← map_one f] at htop
    have h3 := (hq 1).1 ((key 1).1 h2)
    rw [map_one] at h3
    exact one_ne_zero h3
  · intro x y hxy
    simp only [Lat.I, Ideal.mem_comap, map_mul] at hxy ⊢
    obtain ⟨a, ha⟩ := exists_sub_mem_IB f ξ l M (ι_mem_sub f ξ l M x)
    obtain ⟨b, hb⟩ := exists_sub_mem_IB f ξ l M (ι_mem_sub f ξ l M y)
    have hab : f (a * b) ∈ Lat.IB f ξ := by
      have e : f (a * b) = Lat.ι f ξ l M x * Lat.ι f ξ l M y
          - ((Lat.ι f ξ l M x - f a) * Lat.ι f ξ l M y + f a * (Lat.ι f ξ l M y - f b)) := by
        rw [map_mul]; ring
      rw [e]
      exact sub_mem hxy (add_mem (Ideal.mul_mem_right _ _ ha) (Ideal.mul_mem_left _ _ hb))
    have h := (hq (a * b)).1 ((key _).1 hab)
    rw [map_mul, mul_eq_zero] at h
    rcases h with h | h
    · left
      have hfa : f a ∈ Lat.IB f ξ := (key a).2 ((hq a).2 h)
      have e : Lat.ι f ξ l M x = (Lat.ι f ξ l M x - f a) + f a := by ring
      rw [e]
      exact add_mem ha hfa
    · right
      have hfb : f b ∈ Lat.IB f ξ := (key b).2 ((hq b).2 h)
      have e : Lat.ι f ξ l M y = (Lat.ι f ξ l M y - f b) + f b := by ring
      rw [e]
      exact add_mem hb hfb

end GlobalTheory.CompanionTheory.LatPrime
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothSectionsAffineFlat
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothSectionsAffineFlat
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.Axis
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Axis

theorem flat_sec_of_smooth : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), Smooth s →
    ∀ U : X.affineOpens, Module.Flat R (Sec s U.1) := by
  intro R _ X s hs U
  haveI : Smooth s := hs
  have hfl : Flat s := inferInstance
  have hT : IsAffineOpen (⊤ : (Sp R).Opens) := isAffineOpen_top (Sp R)
  have h1 := HasRingHomProperty.appLE @Flat s hfl ⟨⊤, hT⟩ U le_top
  have h2 : RingHom.Flat (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom :=
    RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _)
  have h3 := RingHom.Flat.comp h2 h1
  exact h3

end GlobalTheory.CompanionTheory.Axis
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothSectionsAffineFlatStatement
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge GlobalTheory.CompanionTheory.Axis
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_sections_affine_flat : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), Smooth s →
    ∀ U : X.affineOpens, Module.Flat R (Sec s U.1) := by
  first | exact @GlobalTheory.CompanionTheory.Axis.flat_sec_of_smooth | exact GlobalTheory.CompanionTheory.Axis.flat_sec_of_smooth | (intros; apply GlobalTheory.CompanionTheory.Axis.flat_sec_of_smooth <;> assumption)
end
end
