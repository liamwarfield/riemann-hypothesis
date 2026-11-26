module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.DualLiftCompJetSub
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

namespace ReciprocityTheory.ChartRestriction.G.Chart

attribute [local instance] Over.cartesianMonoidalCategory

variable {R : Type} [CommRing R]

private theorem jetAug_zR_lemma {κ : Type} {m : ℕ} (j : κ) : jetAug R κ m (zR m j) = 0 := by
  first
  | (show MvPolynomial.aeval (fun _ : κ => (0 : R)) (MvPolynomial.X j) = 0
     simp)
  | simp [jetAug, zR, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]

theorem sum_smul_zR_mem {a : ℕ} (m : ℕ) (c : Fin a → R) :
    ∑ i, c i • zR (R := R) m i ∈ RingHom.ker (jetAug R (Fin a) m) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [RingHom.mem_ker, map_sum]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [map_smul, jetAug_zR_lemma i, smul_zero]

theorem sum_single {a : ℕ} (c : Fin a → R) : ∑ i, c i • Pi.single i (1 : R) = c := by
  ext k
  simp [Pi.single_apply]

def jetSub {a b : ℕ} (T : (Fin a → R) →ₗ[R] (Fin b → R)) (m : ℕ) : JetR R (Fin b) m →ₐ[R] JetR R (Fin a) m :=
  jetLift (R := R) (RingHom.ker (jetAug R (Fin a) m)) (ker_jetAug_pow (Fin a) m)
    (fun k => ∑ i, T (Pi.single i 1) k • zR m i) (fun k => sum_smul_zR_mem m _)

theorem jetSub_zR {a b : ℕ} (T : (Fin a → R) →ₗ[R] (Fin b → R)) (m : ℕ) (k : Fin b) :
    jetSub T m (zR m k) = ∑ i, T (Pi.single i 1) k • zR m i := by
  rw [jetSub, jetLift_zR]

private theorem jet_ext_lemma_2 {κ : Type} {m : ℕ} {A : Type} [CommRing A] [Algebra R A]
    {f g : JetR R κ m →ₐ[R] A} (h : ∀ j, f (zR m j) = g (zR m j)) : f = g := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro j
  exact h j

theorem jetSub_id {a : ℕ} (m : ℕ) : jetSub (R := R) (LinearMap.id : (Fin a → R) →ₗ[R] (Fin a → R)) m = AlgHom.id R _ := by
  apply jet_ext_lemma_2
  intro k
  rw [jetSub_zR]
  simp [Pi.single_apply]

theorem jetSub_comp {a b c : ℕ} (T : (Fin a → R) →ₗ[R] (Fin b → R)) (S : (Fin c → R) →ₗ[R] (Fin a → R)) (m : ℕ) :
    (jetSub S m).comp (jetSub T m) = jetSub (T.comp S) m := by
  apply jet_ext_lemma_2
  intro k
  set_option synthInstance.maxHeartbeats 100000 in
    rw [AlgHom.comp_apply, jetSub_zR, jetSub_zR, map_sum]
  simp_rw [map_smul, jetSub_zR, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Finset.sum_smul]
  congr 1
  conv_rhs => rw [LinearMap.comp_apply, ← sum_single (S (Pi.single j 1))]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, map_smul, Finset.sum_apply, mul_comm]

theorem jetAug_comp_jetSub {a b : ℕ} (T : (Fin a → R) →ₗ[R] (Fin b → R)) (m : ℕ) :
    (jetAug R (Fin a) m).comp (jetSub T m) = jetAug R (Fin b) m := by
  apply jet_ext_lemma_2
  intro k
  rw [AlgHom.comp_apply, jetSub_zR, jetAug_zR_lemma]
  exact RingHom.mem_ker.mp (sum_smul_zR_mem m _)

private theorem trunc_zR_lemma_3 {κ : Type} (m : ℕ) (j : κ) :
    jetTruncR R κ m (zR (m + 1) j) = zR m j := rfl

private theorem zero_zR_lemma_4 {κ : Type} (m : ℕ) (j : κ) :
    jetZeroR R κ m (zR m j) = zR 0 j := rfl

theorem trunc_comp_jetSub {a b : ℕ} (T : (Fin a → R) →ₗ[R] (Fin b → R)) (m : ℕ) :
    (jetTruncR R (Fin a) m).comp (jetSub T (m + 1)) = (jetSub T m).comp (jetTruncR R (Fin b) m) := by
  apply jet_ext_lemma_2
  intro k
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [AlgHom.comp_apply, jetSub_zR, trunc_zR_lemma_3, map_sum, map_smul]

theorem zero_comp_jetSub {a b : ℕ} (T : (Fin a → R) →ₗ[R] (Fin b → R)) (m : ℕ) :
    (jetZeroR R (Fin a) m).comp (jetSub T m) = (jetSub T 0).comp (jetZeroR R (Fin b) m) := by
  apply jet_ext_lemma_2
  intro k
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [AlgHom.comp_apply, jetSub_zR, zero_zR_lemma_4, map_sum, map_smul]

private theorem sum_inr_lemma_5 {I : Type} (s : Finset I) (f : I → R) :
    ∑ i ∈ s, (TrivSqZeroExt.inr (f i) : DualNumber R) = TrivSqZeroExt.inr (∑ i ∈ s, f i) := by
  first
  | exact (map_sum (TrivSqZeroExt.inrHom R R) f s).symm
  | (induction s using Finset.cons_induction with
     | empty => simp
     | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, ih, TrivSqZeroExt.inr_add])

theorem dualLift_comp_jetSub {a b : ℕ} (T : (Fin a → R) →ₗ[R] (Fin b → R)) (c : Fin a → R) :
    (dualLift c).comp (jetSub T 1) = dualLift (T c) := by
  apply jet_ext_lemma_2
  intro k
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [AlgHom.comp_apply, jetSub_zR, map_sum, map_smul, dualLift_zR]
  simp_rw [← TrivSqZeroExt.inr_smul, sum_inr_lemma_5]
  congr 1
  conv_rhs => rw [← sum_single c]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, map_smul, Finset.sum_apply, mul_comm]

variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G]

theorem isUnivChart_sub {n d : ℕ} {x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin n) m) ⟶ G} (hx : IsUnivChart G n x)
    (T : (Fin d → R) ≃ₗ[R] (Fin n → R)) :
    IsUnivChart G d (fun m => spMap (jetSub T.toLinearMap m) ≫ x m) := by
  refine ⟨fun m => ?_, fun m => ?_, ?_⟩
  · show spMap (jetTruncR R (Fin d) m) ≫ spMap (jetSub T.toLinearMap (m + 1)) ≫ x (m + 1) =
      spMap (jetSub T.toLinearMap m) ≫ x m
    rw [← Category.assoc, spMap_comp, trunc_comp_jetSub, ← spMap_comp, Category.assoc, hx.1 m]
  · show spMap (jetZeroR R (Fin d) m) ≫ spMap (jetSub T.toLinearMap m) ≫ x m = 1
    rw [← Category.assoc, spMap_comp, zero_comp_jetSub, ← spMap_comp, Category.assoc, hx.2.1 m, comp_one']
  · intro A _ _ aug m hA y hy
    obtain ⟨ψ, ⟨hψ1, hψ2⟩, hψu⟩ := hx.2.2 A aug m hA y hy
    have e1 : (jetSub T.symm.toLinearMap m).comp (jetSub T.toLinearMap m) = AlgHom.id R _ := by
      rw [jetSub_comp]
      have h0 : T.toLinearMap.comp T.symm.toLinearMap = LinearMap.id := by
        ext v : 1
        simp
      rw [h0, jetSub_id]
    have e2 : (jetSub T.toLinearMap m).comp (jetSub T.symm.toLinearMap m) = AlgHom.id R _ := by
      rw [jetSub_comp]
      have h0 : T.symm.toLinearMap.comp T.toLinearMap = LinearMap.id := by
        ext v : 1
        simp
      rw [h0, jetSub_id]
    refine ⟨ψ.comp (jetSub T.symm.toLinearMap m), ⟨?_, ?_⟩, ?_⟩
    · rw [← AlgHom.comp_assoc, hψ1, jetAug_comp_jetSub]
    · show y = spMap (ψ.comp (jetSub T.symm.toLinearMap m)) ≫ spMap (jetSub T.toLinearMap m) ≫ x m
      rw [← Category.assoc, spMap_comp, AlgHom.comp_assoc, e1, AlgHom.comp_id]
      exact hψ2
    · rintro φ ⟨hφ1, hφ2⟩
      have hφ2' : y = spMap φ ≫ spMap (jetSub T.toLinearMap m) ≫ x m := hφ2
      have hφ : φ.comp (jetSub T.toLinearMap m) = ψ := by
        apply hψu
        refine ⟨?_, ?_⟩
        · rw [← AlgHom.comp_assoc, hφ1, jetAug_comp_jetSub]
        · rw [hφ2', ← Category.assoc, spMap_comp]
      rw [← hφ, AlgHom.comp_assoc, e2, AlgHom.comp_id]

end ReciprocityTheory.ChartRestriction.G.Chart
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp epsR epsScaleR IsTangent IsLieComb IsLieBasis)

namespace ReciprocityTheory.ChartRestriction.G.Chart

attribute [local instance] Over.cartesianMonoidalCategory

abbrev algOver (R : Type) [CommRing R] (A : Type) [CommRing A] [Algebra R A] : Over (Sp R) :=
  Over.mk (ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap R A))

def algOverHom {R : Type} [CommRing R] {A B : Type} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]
    (ψ : A →ₐ[R] B) : algOver R B ⟶ algOver R A :=
  Over.homMk (ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (ψ : A →+* B)) (by
    dsimp
    simp only [ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact ψ.comp_algebraMap)

def ChartLawLocSt : Prop :=
  ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], Smooth G.hom →
    ∀ (d : ℕ) (v : Fin d → (epsR R ⟶ G)), IsLieBasis v →
    ∃ x : ∀ m : ℕ, algOver R (JetR R (Fin d) m) ⟶ G,
      (∀ m, algOverHom (jetTruncR R (Fin d) m) ≫ x (m + 1) = x m) ∧
      (∀ m, algOverHom (jetZeroR R (Fin d) m) ≫ x m = toUnit _ ≫ η[G]) ∧
      (∀ j : Fin d, ∃ ψ : JetR R (Fin d) 1 →ₐ[R] DualNumber R,
        ψ (zR 1 j) = TrivSqZeroExt.inr 1 ∧ (∀ i, i ≠ j → ψ (zR 1 i) = 0) ∧ algOverHom ψ ≫ x 1 = v j) ∧
      ∀ (κ : Type) (m : ℕ) (y : algOver R (JetR R κ m) ⟶ G),
        algOverHom (jetZeroR R κ m) ≫ y = toUnit _ ≫ η[G] →
        ∃! ψ : JetR R (Fin d) m →ₐ[R] JetR R κ m,
          (∀ j, jetZeroR R κ m (ψ (zR m j)) = 0) ∧ y = algOverHom ψ ≫ x m

variable {R : Type} [CommRing R]

variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G]

theorem isTan_iff (w : sp (R₀ := R) (DualNumber R) ⟶ G) : IsTan w ↔ IsTangent w := by
  constructor
  · intro h
    have := congrArg CommaMorphism.left h
    simp only [Over.comp_left, spMap_left] at this
    show Spec.map _ ≫ w.left = _
    rw [this]
    show (sp R).hom ≫ η[G].left = η[G].left
    simp only [Over.mk_hom]
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
    exact Category.id_comp _
  · intro h
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, spMap_left]
    refine h.trans ?_
    show η[G].left = (sp R).hom ≫ η[G].left
    simp only [Over.mk_hom]
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
    exact (Category.id_comp _).symm

def prodPts {d : ℕ} (c : Fin d → R) (v : Fin d → (sp (R₀ := R) (DualNumber R) ⟶ G)) :
    sp (R₀ := R) (DualNumber R) ⟶ G :=
  (List.ofFn fun i => spMap (scaleD (c i)) ≫ v i).prod

theorem isLieComb_iff {d : ℕ} (c : Fin d → R) (v : Fin d → (epsR R ⟶ G)) (w : epsR R ⟶ G) :
    IsLieComb c v w ↔ w = prodPts c v := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    have : u = fun i => spMap (scaleD (c i)) ≫ v i := by
      funext i
      apply Over.OverMorphism.ext
      rw [hu i]
      rfl
    rw [this]
    rfl
  · intro h
    exact ⟨fun i => spMap (scaleD (c i)) ≫ v i, fun i => rfl, h⟩

variable {n : ℕ} {x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin n) m) ⟶ G} (hx : IsUnivChart G n x)

theorem list_prod_tan : ∀ {k : ℕ} (u : Fin k → (sp (R₀ := R) (DualNumber R) ⟶ G))
    (hu : ∀ i, IsTan (u i)), ∃ h : IsTan (List.ofFn u).prod, tcoord hx _ h = ∑ i, tcoord hx (u i) (hu i) := by
  intro k
  induction k with
  | zero =>
    intro u hu
    have e0 : (List.ofFn u).prod = 1 := by simp
    refine ⟨e0 ▸ isTan_one, ?_⟩
    rw [tcoord_congr hx e0 _ isTan_one, tcoord_one]
    simp
  | succ k ih =>
    intro u hu
    obtain ⟨h, e⟩ := ih (fun i => u i.succ) (fun i => hu i.succ)
    have e0 : (List.ofFn u).prod = u 0 * (List.ofFn fun i => u i.succ).prod := by
      rw [List.ofFn_succ, List.prod_cons]
    refine ⟨e0 ▸ isTan_mul (hu 0) h, ?_⟩
    rw [tcoord_congr hx e0 _ (isTan_mul (hu 0) h), tcoord_mul hx (hu 0) h, e, Fin.sum_univ_succ]

theorem prodPts_tan {d : ℕ} (c : Fin d → R) (v : Fin d → (sp (R₀ := R) (DualNumber R) ⟶ G))
    (hv : ∀ i, IsTan (v i)) :
    ∃ h : IsTan (prodPts c v), tcoord hx _ h = ∑ i, c i • tcoord hx (v i) (hv i) := by
  obtain ⟨h, e⟩ := list_prod_tan hx (fun i => spMap (scaleD (c i)) ≫ v i) (fun i => isTan_scale (c i) (hv i))
  refine ⟨h, e.trans ?_⟩
  exact Finset.sum_congr rfl fun i _ => tcoord_scale hx (c i) (hv i)

theorem tan_ext {w w' : sp (R₀ := R) (DualNumber R) ⟶ G} (h : IsTan w) (h' : IsTan w')
    (e : tcoord hx w h = tcoord hx w' h') : w = w' := by
  rw [tcoord_spec hx w h, tcoord_spec hx w' h', e]

end ReciprocityTheory.ChartRestriction.G.Chart
