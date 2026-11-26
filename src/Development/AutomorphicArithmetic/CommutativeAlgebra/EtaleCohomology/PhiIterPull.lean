module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.HkOfPush
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.TestFactsAlt
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.TheoryEx

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.SumTransportAlt
section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.SumSecEqZero
noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace UpperTheory.Ru.crystallineComparison

variable {C : Type 1} [Category.{0} C]

private theorem sum_sec_eq_zero (Pa : Parts C) (F : Coef C) (hF : Pa.Add F) {Q P : C ⥤ Type}
    {I : Type} [Fintype I] (a : I → ℤ) (u : I → (Q ⟶ P)) (h : Pa.LocZero a u)
    (c : ∀ A : C, P.obj A → F.obj A) (hc : c ∈ Sec P F) (A : C) (y : Q.obj A) :
    ∑ i, a i • c A ((u i).app A y) = 0 := by
  have hc' : ∀ {A B : C} (φ : A ⟶ B) (y : P.obj A), (F.map φ).hom (c A y) = c B (P.map φ y) := hc
  obtain ⟨S, hS, hs⟩ := h A y
  apply (hF A S hS).1
  funext s
  show (F.map (S.f s)).hom (∑ i, a i • c A ((u i).app A y)) = (F.map (S.f s)).hom 0
  have hnat : ∀ i, (F.map (S.f s)).hom (a i • c A ((u i).app A y)) =
      a i • c (S.B s) ((u i).app _ (Q.map (S.f s) y)) := by
    intro i
    rw [map_zsmul, hc' (S.f s) _, NatTrans.naturality_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_zero, map_sum]
  simp only [hnat]
  rcases hs s with h0 | h0
  · have hL := congrArg
      (Finsupp.liftAddHom fun p : P.obj (S.B s) => zmultiplesHom (F.obj (S.B s)) (c (S.B s) p)) h0
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [map_sum] using hL
  · apply (hF _ _ h0).1
    funext e
    exact e.elim

private theorem locSum_zero (Pa : Parts C) (T : Theory C) (F : Coef C) (hF : Pa.Add F)
    {Q P : C ⥤ Type} {I : Type} [Fintype I] (a : I → ℤ) (u : I → (Q ⟶ P)) (h : Pa.LocZero a u)
    (x : T.H P F 0) : ∑ i, a i • T.pull (u i) F 0 x = 0 := by
  apply (T.zero Q F).injective
  rw [map_zero]
  apply Subtype.ext
  funext A y
  let E : T.H Q F 0 →+ F.obj A := AddMonoidHom.mk' (fun z => (T.zero Q F z).1 A y) (by
    intro z w
    simp [map_add (f := _)])
  show E (∑ i, a i • T.pull (u i) F 0 x) = 0
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  have hE : ∀ i, E (a i • T.pull (u i) F 0 x) = a i • (T.zero P F x).1 A ((u i).app A y) := by
    intro i
    rw [map_zsmul]
    congr 1
    exact T.zero_pull (u i) F x A y
  simp only [hE]
  exact sum_sec_eq_zero Pa F hF a u h _ (T.zero P F x).2 A y

private theorem locSum_shift (T : Theory C) {Q P : C ⥤ Type} {I : Type} [Fintype I] (a : I → ℤ)
    (u : I → (Q ⟶ P)) (S : ShortComplex (Coef C)) (hS : S.ShortExact) (j : ℕ)
    (hsub : Subsingleton (T.H P S.X₂ (j + 1)))
    (ih : ∀ w : T.H P S.X₃ j, ∑ i, a i • T.pull (u i) S.X₃ j w = 0)
    (x : T.H P S.X₁ (j + 1)) : ∑ i, a i • T.pull (u i) S.X₁ (j + 1) x = 0 := by
  obtain ⟨w, rfl⟩ := (T.ex₁ P S hS j x).1 (hsub.elim _ _)
  have hδ : ∑ i, a i • T.δ Q S hS j (T.pull (u i) S.X₃ j w) =
      T.δ Q S hS j (∑ i, a i • T.pull (u i) S.X₃ j w) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_zsmul]
  simp only [T.pull_δ]
  rw [hδ, ih w, map_zero]

end UpperTheory.Ru.crystallineComparison

open UpperTheory.Ru.crystallineComparison in
theorem UpperTheory.Ru.crystallineComparison.locSum :
    UpperTheory.Ru.crystallineComparison.LocSum := by
  intro C _ Pa T F hF Q P I _ a u h j x
  induction j generalizing F with
  | zero => exact locSum_zero Pa T F hF a u h x
  | succ j ih =>
    obtain ⟨K, ι, hm, hK, hKa⟩ := emb C Pa F hF
    let S : ShortComplex (Coef C) := ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι)
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_cokernel ι, mono_f := hm, epi_g := inferInstanceAs (Epi (cokernel.π ι)) }
    have h3 : Pa.Add S.X₃ := quotAdd C Pa S hS hF hKa
    exact locSum_shift T a u S hS j (T.inj P K hK j) (fun w => ih S.X₃ h3 w) x
end
end

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits GroundTheory.PAdicHodge CrystallineSemistableComparison

namespace UpperTheory.Ru.crystallineComparison

private theorem bij_transport {ι X X' : Type*} {Y Y' : ι → Type*} (c : X ≃ X') (d : ∀ i, Y i ≃ Y' i)
    (g : ∀ i, X → Y i) (f : ∀ i, X' → Y' i) (h : ∀ i x, f i (c x) = d i (g i x))
    (hb : Function.Bijective fun x i => g i x) : Function.Bijective fun x i => f i x := by
  obtain ⟨hi, hs⟩ := hb
  refine ⟨fun x y hxy => ?_, fun b => ?_⟩
  · obtain ⟨x, rfl⟩ := c.surjective x
    obtain ⟨y, rfl⟩ := c.surjective y
    refine congrArg c (hi (funext fun i => (d i).injective ?_))
    have := congrFun hxy i
    simpa only [h] using this
  · obtain ⟨x, hx⟩ := hs fun i => (d i).symm (b i)
    refine ⟨c x, funext fun i => ?_⟩
    have := congrFun hx i
    simp only at this
    simp only [h, this, Equiv.apply_symm_apply]

private theorem sum_transport {W Y I : Type*} [AddCommGroup W] [AddCommGroup Y] [Fintype I] (a : I → ℤ) (e : Y ≃+ W)
    (f : I → Y) (g : I → W) (h : ∀ i, e (f i) = g i) (key : ∑ i, a i • g i = 0) : ∑ i, a i • f i = 0 := by
  apply e.injective
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_zero, map_sum]
  simp only [map_zsmul, h]
  exact key

variable {l : ℕ} [Fact l.Prime]

private theorem empty_isDec {A : Test l} (h : Subsingleton A.obj.A) :
    IsDec (⟨Empty, fun e => e.elim, fun e => e.elim⟩ : Fam A) := by
  refine ⟨fun x y _ => Subsingleton.elim x y, fun b => ⟨0, ?_⟩⟩
  funext e
  exact e.elim

private theorem locZero_of {Pa : Parts (Test l)} (hPa : ∀ (A : Test l) (S : Fam A), Pa.Cov S ↔ IsDec S)
    {Q P : PAlg l ⥤ Type} {I : Type} [Fintype I] {a : I → ℤ} {u : I → (Q ⟶ P)} (hz : TZero a u) :
    Pa.LocZero (Q := testι l ⋙ Q) (P := testι l ⋙ P) a (fun i => Functor.whiskerLeft (testι l) (u i)) := by
  intro A y
  obtain ⟨S, hS, hs⟩ := hz A y
  refine ⟨S, (hPa A S).2 hS, fun s => ?_⟩
  rcases hs s with h0 | h0
  · exact Or.inl h0
  · exact Or.inr ((hPa _ _).2 (empty_isDec h0))

private theorem add_of {Pa : Parts (Test l)} (hPa : ∀ (A : Test l) (S : Fam A), Pa.Cov S ↔ IsDec S)
    (n : ℕ) (hacr : AcrAdd) (F' : Coef (Test l)) (c : ∀ A, (testι l ⋙ AcrF l n).obj A ≃+ F'.obj A)
    (hc : ∀ {A B : Test l} (φ : A ⟶ B) (x : (testι l ⋙ AcrF l n).obj A),
      c B (((testι l ⋙ AcrF l n).map φ).hom x) = (F'.map φ).hom (c A x)) : Pa.Add F' := by
  intro A S hS
  exact bij_transport (c A).toEquiv (fun i => (c (S.B i)).toEquiv) (fun i x => PAlg.mapAcr (S.f i).hom n x)
    (fun i x => (F'.map (S.f i)).hom x) (fun i x => (hc (S.f i) x).symm) (hacr l n A S ((hPa A S).1 hS))

end UpperTheory.Ru.crystallineComparison

open UpperTheory.Ru.crystallineComparison in
theorem UpperTheory.Ru.crystallineComparison.sumMH :
    UpperTheory.Ru.crystallineComparison.SumMH := by
  intro l _ Q P I _ a u hz n j x
  refine (partsEx l).elim fun Pa hPa => (theoryEx (Test l)).elim fun T hT => ?_
  refine (hT (Acris l) (testι l ⋙ AcrF l n)).elim fun F' h1 => h1.elim fun c h2 => h2.elim fun e h3 => ?_
  have hAdd : Pa.Add F' := add_of hPa n acrAdd F' c h3.1
  have key := locSum (Test l) Pa T F' hAdd (testι l ⋙ Q) (testι l ⋙ P) I a
    (fun i => Functor.whiskerLeft (testι l) (u i)) (locZero_of hPa hz) j
  have hp : ∀ i, e (testι l ⋙ Q) j (pullH (u i) n j x) =
      T.pull (Functor.whiskerLeft (testι l) (u i)) F' j (e (testι l ⋙ P) j x) := fun i =>
    h3.2 (Functor.whiskerLeft (testι l) (u i)) (pullMor (u i) n) rfl (fun _ _ => HEq.rfl) j x
  exact sum_transport a (e (testι l ⋙ Q) j) _ _ hp (key (e (testι l ⋙ P) j x))
end
end

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GroundTheory.PAdicHodge CrystallineSemistableComparison

namespace UpperTheory.Ru.crystallineComparison

variable {l : ℕ} [Fact l.Prime]

private theorem pull_tri {R : Type} [CommRing R] {C C' C'' : Type 1} [Category.{0} C] [Category.{0} C']
    [Category.{0} C''] {F : C ⥤ ModuleCat.{0} R} {F' : C' ⥤ ModuleCat.{0} R} {F'' : C'' ⥤ ModuleCat.{0} R}
    (a : CH.Mor F F' (RingHom.id R)) (b : CH.Mor F' F'' (RingHom.id R)) (c : CH.Mor F F'' (RingHom.id R)) (j : ℕ)
    (h : ∀ z : CH.Cn F j, c.pullC j z = b.pullC j (a.pullC j z)) (x : CH.H F j) :
    c.pull j x = b.pull j (a.pull j x) := by
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ x
  exact congrArg (Submodule.Quotient.mk (p := ((CH.cx F'').B j).submoduleOf ((CH.cx F'').Z j))) (Subtype.ext (h z.1))

private theorem pull_self {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {F : C ⥤ ModuleCat.{0} R}
    (c : CH.Mor F F (RingHom.id R)) (j : ℕ) (h : ∀ z : CH.Cn F j, c.pullC j z = z) (x : CH.H F j) :
    c.pull j x = x := by
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ x
  exact congrArg (Submodule.Quotient.mk (p := ((CH.cx F).B j).submoduleOf ((CH.cx F).Z j))) (Subtype.ext (h z.1))

private theorem pullH_comp {P P' P'' : PAlg l ⥤ Type} (u : P ⟶ P') (v : P' ⟶ P'') (n j : ℕ) (x : MH P'' n j) :
    pullH (u ≫ v) n j x = pullH u n j (pullH v n j x) :=
  pull_tri (pullMor v n) (pullMor u n) (pullMor (u ≫ v) n) j (fun _ => funext fun _ => rfl) x

private theorem pullH_id (P : PAlg l ⥤ Type) (n j : ℕ) (x : MH P n j) : pullH (𝟙 P) n j x = x :=
  pull_self (pullMor (𝟙 P) n) j (fun _ => funext fun _ => rfl) x

private theorem phi_pull' {P P' : PAlg l ⥤ Type} (u : P ⟶ P') (n j : ℕ) (x : MH P' n j) :
    phiH P n j (pullH u n j x) = pullH u n j (phiH P' n j x) :=
  (frEx l ℤ (Spec (CommRingCat.of ℤ)) (𝟙 _) (Int.castRingHom _) (Int.castRingHom _) 0 0 (fun _ => by simp)).2.2 P P' u n j x

private theorem iter_semi {A B : Type*} (p : B → B) (r : A → A) (h : A → B) (e : ∀ x, p (h x) = h (r x))
    (m : ℕ) (x : A) : p^[m] (h x) = h (r^[m] x) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, e]

private theorem iter_step {A : Type*} (p : A → A) (f k : ℕ) (x : A) : p^[f * (k + 1)] x = p^[f * k] (p^[f] x) := by
  rw [Nat.mul_succ, Function.iterate_add_apply]

private theorem phi_iter_pull {P P' : PAlg l ⥤ Type} (u : P ⟶ P') (n j m : ℕ) (x : MH P' n j) :
    (phiH P n j)^[m] (pullH u n j x) = pullH u n j ((phiH P' n j)^[m] x) :=
  iter_semi _ _ (pullH u n j) (phi_pull' u n j) m x

private theorem itE_succ {P : PAlg l ⥤ Type} (F : P ⟶ P) (k : ℕ) : itE F (k + 1) = F ≫ itE F k := by
  unfold itE
  rw [pow_succ]
  rfl

private theorem phi_iter_itE {P : PAlg l ⥤ Type} (F : P ⟶ P) (f n j : ℕ) (x : MH P n j)
    (hx : (phiH P n j)^[f] x = pullH F n j x) (k : ℕ) :
    (phiH P n j)^[f * k] x = pullH (itE F k) n j x := by
  induction k with
  | zero => exact (pullH_id P n j x).symm
  | succ k ih =>
    refine (iter_step (phiH P n j) f k x).trans ((congrArg _ hx).trans ((phi_iter_pull F n j (f * k) x).trans
      ((congrArg (pullH F n j) ih).trans ?_)))
    exact (pullH_comp F (itE F k) n j x).symm.trans (congrArg (fun w : P ⟶ P => pullH w n j x) (itE_succ F k).symm)

end UpperTheory.Ru.crystallineComparison

open UpperTheory.Ru.crystallineComparison in
theorem UpperTheory.Ru.crystallineComparison.siteAnn :
    UpperTheory.Ru.crystallineComparison.SiteAnn := by
  intro l _ O _ Y q g Q P ρ F f I _ a t k hT n j x hx
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (sumMH l Q (PQ q g) I a (fun i => t i ≫ ρ ≫ itE F (k i)) hT n j x)
  refine congrArg (a i • ·) ?_
  refine (congrArg (pullH (t i) n j) ((phi_iter_pull ρ n j (f * k i) x).trans
    (congrArg (pullH ρ n j) (phi_iter_itE F f n j x hx (k i))))).trans ?_
  exact ((congrArg (pullH (t i) n j) (pullH_comp ρ (itE F (k i)) n j x).symm).trans
    (pullH_comp (t i) (ρ ≫ itE F (k i)) n j x).symm)
