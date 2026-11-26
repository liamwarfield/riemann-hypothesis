module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRatA
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DualRestrictSurjectiveOfIsTorsionFreeQuotient
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueLinearLiftOfHolomorphicAbelianVariet
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.MemSpanOfCardLe
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPowSmulMemRangeOfSurjectiveBaseChange

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsRingHomComplexCompEqOfCountable
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsRingHomComplexCompEqOfCountable
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem nonempty_algHom_complex_of_countable (R K : Type) [CommRing R] [IsDomain R] [Countable R]
    [Field K] [Countable K] [Algebra R K] [Algebra R ℂ] [FaithfulSMul R K] [FaithfulSMul R ℂ] :
    Nonempty (K →ₐ[R] ℂ) := by
  obtain ⟨J, v, hv⟩ := exists_isTranscendenceBasis' R K
  obtain ⟨Jc, w, hw⟩ := exists_isTranscendenceBasis' R ℂ
  haveI : Countable J := hv.1.injective.countable
  have hκ : Cardinal.aleph0 < Cardinal.mk Jc := by
    by_contra hlt
    have hle := not_lt.1 hlt
    have h1 := IsAlgClosed.cardinal_le_max_transcendence_basis' w hw
    rw [Cardinal.mk_complex] at h1
    exact absurd (h1.trans (max_le (max_le Cardinal.mk_le_aleph0 hle) le_rfl))
      (not_le.2 Cardinal.aleph0_lt_continuum)
  obtain ⟨e⟩ : Nonempty (J ↪ Jc) :=
    (Cardinal.le_def J Jc).1 (Cardinal.mk_le_aleph0.trans hκ.le)
  let S := Algebra.adjoin R (Set.range v)
  let φ : S →ₐ[R] ℂ := (MvPolynomial.aeval (w ∘ e)).comp hv.1.aevalEquiv.symm.toAlgHom
  have hind : AlgebraicIndependent R (w ∘ e) := hw.1.comp e e.injective
  have hφ : Function.Injective φ := by
    have hind' : Function.Injective (MvPolynomial.aeval (R := R) (w ∘ e)) := hind
    simp only [φ, AlgHom.coe_comp]
    exact hind'.comp hv.1.aevalEquiv.symm.injective
  letI : Algebra S ℂ := φ.toRingHom.toAlgebra
  haveI : Module.IsTorsionFree S ℂ := Module.isTorsionFree_iff_algebraMap_injective.2 hφ
  haveI : Module.IsTorsionFree S K :=
    Module.isTorsionFree_iff_algebraMap_injective.2 Subtype.val_injective
  haveI : Algebra.IsAlgebraic S K := hv.isAlgebraic
  let g : K →ₐ[S] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨{ g.toRingHom with commutes' := fun r => ?_ }⟩
  show g (algebraMap R K r) = algebraMap R ℂ r
  rw [IsScalarTower.algebraMap_apply R S K r, g.commutes]
  exact φ.commutes r

private theorem isJacobsonRing_int' : IsJacobsonRing ℤ := by
  rw [isJacobsonRing_iff_prime_eq]
  intro P hP
  by_cases hbot : P = ⊥
  · subst hbot
    refine le_antisymm (fun x hx => ?_) Ideal.le_jacobson
    obtain ⟨z, hz⟩ := (Ideal.mem_jacobson_iff.1 hx) x
    rw [Ideal.mem_bot] at hz ⊢
    have hu : IsUnit (x * x + 1) := IsUnit.of_mul_eq_one z (by linear_combination hz)
    rcases Int.isUnit_iff.1 hu with h | h
    · exact mul_self_eq_zero.1 (by linarith)
    · nlinarith [mul_self_nonneg x]
  · haveI := hP.isMaximal hbot
    exact Ideal.jacobson_eq_self_of_isMaximal

theorem injective_of_finiteType_int_of_charZero {o K : Type} [CommRing o] [IsDomain o]
    [Ring.DimensionLEOne o] [Algebra.FiniteType ℤ o] [Field K] [CharZero K] (β : o →+* K) :
    Function.Injective β := by
  haveI := isJacobsonRing_int'
  by_contra hβ
  have hker : RingHom.ker β ≠ ⊥ := fun h => hβ ((RingHom.injective_iff_ker_eq_bot β).2 h)
  haveI : (RingHom.ker β).IsMaximal := (RingHom.ker_isPrime β).isMaximal hker
  letI : Field (o ⧸ RingHom.ker β) := Ideal.Quotient.field _
  haveI : Algebra.FiniteType ℤ (o ⧸ RingHom.ker β) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℤ _)
      (Ideal.Quotient.mkₐ_surjective ℤ _)
  haveI : Module.Finite ℤ (o ⧸ RingHom.ker β) := finite_of_finite_type_of_isJacobsonRing ℤ _
  haveI : Algebra.IsIntegral ℤ (o ⧸ RingHom.ker β) := Algebra.IsIntegral.of_finite ℤ _
  have hinj : Function.Injective (algebraMap ℤ (o ⧸ RingHom.ker β)) := by
    intro a b hab
    have hk := congrArg (RingHom.kerLift β) hab
    simp only [eq_intCast, map_intCast] at hk
    exact Int.cast_injective hk
  exact Int.not_isField (isField_of_isIntegral_of_isField hinj (Field.toIsField _))

theorem exists_ringHom_complex_comp_eq_of_countable :
    ∀ (o : Type) [CommRing o] (em : o →+* ℂ) (K₀ : Type) [Field K₀] [CharZero K₀] [Countable K₀] (β : o →+* K₀), IsDedekindDomain o → Algebra.FiniteType ℤ o → Function.Injective em → Countable o ∧ ∃ j : K₀ →+* ℂ, j.comp β = em := by
  intro o _ em K₀ _ _ _ β hD hF hem
  haveI := hD
  haveI := hF
  have hβ : Function.Injective β := injective_of_finiteType_int_of_charZero β
  have hcount : Countable o := by
    obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 hF
    have hc : Countable (MvPolynomial (Fin n) ℤ) := by
      rw [← Cardinal.mk_le_aleph0_iff]
      exact MvPolynomial.cardinalMk_le_max.trans
        (max_le (max_le Cardinal.mk_le_aleph0 Cardinal.mk_le_aleph0) le_rfl)
    exact hf.countable
  refine ⟨hcount, ?_⟩
  haveI := hcount
  letI : Algebra o K₀ := β.toAlgebra
  letI : Algebra o ℂ := em.toAlgebra
  haveI : FaithfulSMul o K₀ := (faithfulSMul_iff_algebraMap_injective o K₀).2 hβ
  haveI : FaithfulSMul o ℂ := (faithfulSMul_iff_algebraMap_injective o ℂ).2 hem
  obtain ⟨g⟩ := nonempty_algHom_complex_of_countable o K₀
  exact ⟨g.toRingHom, RingHom.ext fun x => g.commutes x⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsRingHomComplexCompEqOfCountableStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.exists_ringHom_complex_comp_eq_of_countable_field : ∀ (o : Type) [CommRing o] (em : o →+* ℂ) (K₀ : Type) [Field K₀] [CharZero K₀] [Countable K₀] (β : o →+* K₀), IsDedekindDomain o → Algebra.FiniteType ℤ o → Function.Injective em → Countable o ∧ ∃ j : K₀ →+* ℂ, j.comp β = em := by
  first | exact @GlobalTheory.exists_ringHom_complex_comp_eq_of_countable | exact GlobalTheory.exists_ringHom_complex_comp_eq_of_countable | (intros; apply GlobalTheory.exists_ringHom_complex_comp_eq_of_countable <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueTangentLift
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.LieEtale

theorem existsUnique_dual_lift {X Y : Scheme.{0}} (f : X ⟶ Y) [Etale f] {k : Type} [Field k]
    (s : Sp (DualNumber k) ⟶ Y) (x₀ : Sp k ⟶ X)
    (h : x₀ ≫ f = spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ s) :
    ∃! x : Sp (DualNumber k) ⟶ X,
      spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ x = x₀ ∧ x ≫ f = s := by
  let π : CommRingCat.of (DualNumber k) ⟶ CommRingCat.of k :=
    CommRingCat.ofHom (TrivSqZeroExt.fstHom k k k).toRingHom
  have hπ : Function.Surjective π := fun a => ⟨TrivSqZeroExt.inl a, rfl⟩
  have hsq : ∀ a b : DualNumber k, a.fst = 0 → b.fst = 0 → a * b = 0 := fun a b ha hb => by
    ext <;> simp [ha, hb]
  have hnil : IsNilpotent (RingHom.ker π.hom) :=
    ⟨2, by
      rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
      exact fun a ha b hb => hsq a b ha hb⟩
  have hj : RingHom.ker π.hom ≤ Ideal.jacobson ⊥ := fun a ha =>
    Ideal.mem_sInf.mpr fun {J} hJ => hJ.2.isPrime.mem_of_pow_mem 2 (by
      rw [pow_two, hsq a a ha ha]; exact J.zero_mem)
  refine existsUnique_of_exists_of_unique ?_ fun x₁ x₂ h₁ h₂ =>
    lift_ext_of_unramified f π hπ hj (h₁.1.trans h₂.1.symm) (h₁.2.trans h₂.2.symm)
  have : IsLocalHom π.hom := ⟨fun a ha => TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr ha⟩
  obtain ⟨U, V, hU, hV, hVU, -, hxV⟩ :=
    exists_isAffineOpen_pair f (x₀ (IsLocalRing.closedPoint k)) (O := ⊤) trivial
  refine exists_lift_of_smooth_of_isAffineOpen f hU hV hVU π s x₀ h
    (range_subset_opens_of_isLocalRing s ?_) (range_subset_opens_of_isLocalRing x₀ hxV) ?_
  · have e : f (x₀ (IsLocalRing.closedPoint k)) = s (Spec.map π (IsLocalRing.closedPoint k)) :=
      congr($h (IsLocalRing.closedPoint k))
    rw [← Spec_closedPoint (f := π), ← e]
    exact hVU hxV
  · intro R A _ _ _ _ _ _ π' hπ' φ
    have hs : Function.Surjective π' := fun c => (hπ c).imp fun b hb => (hπ' b).trans hb
    have hk : IsNilpotent (RingHom.ker (π' : CommRingCat.of (DualNumber k) →+* CommRingCat.of k)) := by
      convert hnil using 2
      exact RingHom.ext hπ'
    exact ⟨_, Algebra.FormallySmooth.comp_liftOfSurjective φ π' hs hk⟩

section Formal

variable {S : Scheme.{0}} {O k : Type} {P E : Over S}

def Eig {G : Over S} [GrpObj G] (z : P ⟶ E) (sc : k → (E ⟶ E)) (act : O → (G ⟶ G)) (τ : O → k)
    (v : E ⟶ G) : Prop :=
  z ≫ v = 1 ∧ ∀ a, v ≫ act a = sc (τ a) ≫ v

theorem comp_listProd {G : Over S} [GrpObj G] (z : P ⟶ E) (l : List (E ⟶ G))
    (h : ∀ u ∈ l, z ≫ u = 1) : z ≫ l.prod = 1 := by
  induction l with
  | nil => exact MonObj.comp_one z
  | cons u l ih =>
    rw [List.prod_cons, MonObj.comp_mul, h u (by simp), ih fun w hw => h w (by simp [hw]),
      _root_.mul_one]

theorem ofFn_prod_comp {A B : Over S} [GrpObj A] [GrpObj B] (ψ : A ⟶ B) [IsMonHom ψ] {n : ℕ}
    (u : Fin n → (E ⟶ A)) : (List.ofFn u).prod ≫ ψ = (List.ofFn fun i => u i ≫ ψ).prod :=
  (map_list_prod (IsMonHom.monoidHom ψ E) _).trans (by rw [List.map_ofFn]; rfl)

theorem mult_iff {A B : Over S} [GrpObj A] [GrpObj B] (ψ : A ⟶ B) [IsMonHom ψ]
    (z : P ⟶ E) (sc : k → (E ⟶ E)) (hz : ∀ c, z ≫ sc c = z)
    (a : O → (A ⟶ A)) (b : O → (B ⟶ B)) (ha : ∀ c, IsMonHom (a c))
    (hab : ∀ c, a c ≫ ψ = ψ ≫ b c) (τ : O → k)
    (H : ∀ w : E ⟶ B, z ≫ w = 1 → ∃! v : E ⟶ A, z ≫ v = 1 ∧ v ≫ ψ = w) (n : ℕ) :
    (∃ v : Fin n → (E ⟶ A), (∀ i, Eig z sc a τ (v i)) ∧ ∀ w, Eig z sc a τ w →
      ∃! c : Fin n → k, w = (List.ofFn fun i => sc (c i) ≫ v i).prod) ↔
    (∃ v : Fin n → (E ⟶ B), (∀ i, Eig z sc b τ (v i)) ∧ ∀ w, Eig z sc b τ w →
      ∃! c : Fin n → k, w = (List.ofFn fun i => sc (c i) ≫ v i).prod) := by
  have htan : ∀ v : E ⟶ A, z ≫ v = 1 → z ≫ v ≫ ψ = 1 := fun v hv => by
    rw [← Category.assoc, hv, MonObj.one_comp]
  have hinj : ∀ v v' : E ⟶ A, z ≫ v = 1 → z ≫ v' = 1 → v ≫ ψ = v' ≫ ψ → v = v' :=
    fun v v' hv hv' e => (H _ (htan v' hv')).unique ⟨hv, e⟩ ⟨hv', rfl⟩
  have hsc : ∀ (c : k) (v : E ⟶ A), z ≫ v = 1 → z ≫ sc c ≫ v = 1 := fun c v hv => by
    rw [← Category.assoc, hz, hv]
  have heig : ∀ v : E ⟶ A, z ≫ v = 1 → (Eig z sc a τ v ↔ Eig z sc b τ (v ≫ ψ)) := fun v hv => by
    refine ⟨fun h => ⟨htan v hv, fun c => ?_⟩, fun h => ⟨hv, fun c => hinj _ _ ?_ (hsc _ _ hv) ?_⟩⟩
    · rw [Category.assoc, ← hab, ← Category.assoc, h.2, Category.assoc]
    · have := ha c
      rw [← Category.assoc, hv, MonObj.one_comp]
    · rw [Category.assoc, hab, ← Category.assoc, h.2, Category.assoc]
  have hcomb : ∀ (v : Fin n → (E ⟶ A)) (w : E ⟶ A), (∀ i, z ≫ v i = 1) → z ≫ w = 1 →
      ∀ c : Fin n → k, (w = (List.ofFn fun i => sc (c i) ≫ v i).prod ↔
        w ≫ ψ = (List.ofFn fun i => sc (c i) ≫ v i ≫ ψ).prod) := fun v w hv hw c => by
    have e : (List.ofFn fun i => sc (c i) ≫ v i).prod ≫ ψ =
        (List.ofFn fun i => sc (c i) ≫ v i ≫ ψ).prod := by
      simp only [ofFn_prod_comp, Category.assoc]
    rw [← e]
    refine ⟨fun h => by rw [← h], hinj _ _ hw (comp_listProd z _ fun u hu => ?_)⟩
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hu
    exact hsc _ _ (hv i)
  constructor
  · rintro ⟨v, hv, h⟩
    refine ⟨fun i => v i ≫ ψ, fun i => (heig _ (hv i).1).mp (hv i), fun w hw => ?_⟩
    obtain ⟨w', ⟨hw', rfl⟩, -⟩ := H w hw.1
    exact (existsUnique_congr (hcomb v w' (fun i => (hv i).1) hw')).mp (h w' ((heig _ hw').mpr hw))
  · rintro ⟨v, hv, h⟩
    choose v' hv' using fun i => (H (v i) (hv i).1).exists
    obtain rfl : v = fun i => v' i ≫ ψ := funext fun i => (hv' i).2.symm
    refine ⟨v', fun i => (heig _ (hv' i).1).mpr (hv i), fun w hw => ?_⟩
    exact (existsUnique_congr (hcomb v' w (fun i => (hv' i).1) hw.1)).mpr
      (h _ ((heig _ hw.1).mp hw))

end Formal

section Dual

variable {S : Scheme.{0}} {k : Type} [Field k] (x : Sp k ⟶ S)

def epsPtZero : Over.mk x ⟶ epsPt x :=
  Over.homMk (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) (by
    change _ ≫ _ ≫ x = x
    rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
    have : (TrivSqZeroExt.fstHom k k k).toRingHom.comp (algebraMap k (DualNumber k)) =
      RingHom.id k := RingHom.ext fun _ => rfl
    rw [this, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp])

def epsPtScale (c : k) : epsPt x ⟶ epsPt x :=
  Over.homMk (spMap (epsScale c)) (by
    change _ ≫ _ ≫ x = _ ≫ x
    rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
    congr 3
    exact RingHom.ext fun r => (TrivSqZeroExt.map (c • (LinearMap.id : k →ₗ[k] k))).commutes r)

theorem epsPtZero_epsPtScale (c : k) : epsPtZero x ≫ epsPtScale x c = epsPtZero x := by
  refine Over.OverMorphism.ext ?_
  change spMap _ ≫ spMap _ = spMap _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact RingHom.ext fun r => TrivSqZeroExt.fst_map _ r

variable {O : Type} [CommRing O] {G : Over S} [GrpObj G] (act : OAct O G) (τ : O →+* k)

theorem isLieEigen_iff (v : epsPt x ⟶ G) :
    IsLieEigen act x τ v ↔ Eig (epsPtZero x) (epsPtScale x) act.act τ v :=
  ⟨fun h => ⟨Over.OverMorphism.ext h.1, fun a => Over.OverMorphism.ext (h.2 a)⟩,
    fun h => ⟨congrArg (·.left) h.1, fun a => congrArg (·.left) (h.2 a)⟩⟩

theorem lieMult_iff (n : ℕ) : LieMult act x τ n ↔
    ∃ v : Fin n → (epsPt x ⟶ G), (∀ i, Eig (epsPtZero x) (epsPtScale x) act.act τ (v i)) ∧
      ∀ w, Eig (epsPtZero x) (epsPtScale x) act.act τ w →
        ∃! c : Fin n → k, w = (List.ofFn fun i => epsPtScale x (c i) ≫ v i).prod := by
  simp only [LieMult, isLieEigen_iff]
  refine exists_congr fun v => and_congr_right fun _ => forall_congr' fun w =>
    imp_congr_right fun _ => existsUnique_congr fun c => ⟨?_, fun h => ⟨_, fun _ => rfl, h⟩⟩
  rintro ⟨u, hu, rfl⟩
  obtain rfl : u = fun i => epsPtScale x (c i) ≫ v i :=
    funext fun i => Over.OverMorphism.ext (hu i)
  rfl

theorem existsUnique_tangent_lift {A B : Over S} [GrpObj A] [GrpObj B] (ψ : A ⟶ B) [IsMonHom ψ]
    [Etale ψ.left] (w : epsPt x ⟶ B) (hw : epsPtZero x ≫ w = 1) :
    ∃! v : epsPt x ⟶ A, epsPtZero x ≫ v = 1 ∧ v ≫ ψ = w := by
  obtain ⟨v, ⟨h₁, h₂⟩, hu⟩ := existsUnique_dual_lift ψ.left w.left (1 : Over.mk x ⟶ A).left
    (congrArg (·.left) ((MonObj.one_comp ψ).trans hw.symm))
  refine ⟨Over.homMk v ?_, ⟨Over.OverMorphism.ext h₁, Over.OverMorphism.ext h₂⟩,
    fun v' hv' => Over.OverMorphism.ext
      (hu _ ⟨congrArg (·.left) hv'.1, congrArg (·.left) hv'.2⟩)⟩
  rw [← Over.w ψ, ← Category.assoc]
  exact (congrArg (· ≫ B.hom) h₂).trans (Over.w w)

end Dual

theorem lieMult_iff_of_etale :
    ∀ (O : Type) [CommRing O] (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (ψ : A ⟶ B) (a : OAct O A) (b : OAct O B), IsMonHom ψ → Etale ψ.left → (∀ c, a.act c ≫ ψ = ψ ≫ b.act c) → ∀ (k : Type) [Field k] (x : Sp k ⟶ S) (τ : O →+* k) (n : ℕ), LieMult a x τ n ↔ LieMult b x τ n := by
  intro O _ S A B _ _ ψ a b _ _ hab k _ x τ n
  rw [lieMult_iff, lieMult_iff]
  exact mult_iff ψ _ _ (epsPtZero_epsPtScale x) a.act b.act a.hom hab τ
    (existsUnique_tangent_lift x ψ) n

end GlobalTheory.LieEtale
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionIsometryPrimitiveRootBijectiveModN
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionIsometryPrimitiveRootBijectiveModN
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.TorsIsometry

theorem _root_.GlobalTheory.TorsIsometry.exists_eq_nsmul_of_dvd {M : Type} [AddCommGroup M] (B : LinearMap.BilinForm ℤ M)
    (hB : Function.Bijective B) (n : ℕ) (d : M) (hd : ∀ b, (n : ℤ) ∣ B d b) : ∃ f : M, d = n • f := by
  let φ : M →ₗ[ℤ] ℤ :=
    { toFun := fun b => B d b / n
      map_add' := fun x y => by
        simp only [map_add (f := _)]
        exact Int.add_ediv_of_dvd_left (hd x)
      map_smul' := fun c x => by
        simp only [map_zsmul, smul_eq_mul, RingHom.id_apply]
        exact Int.mul_ediv_assoc c (hd x) }
  obtain ⟨f, hf⟩ := hB.2 φ
  refine ⟨f, hB.1 ?_⟩
  ext b
  simp only [map_nsmul, LinearMap.smul_apply, hf, nsmul_eq_mul]
  exact (Int.mul_ediv_cancel' (hd b)).symm

theorem _root_.GlobalTheory.TorsIsometry.ker_and_onto : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (K : Type) [Field K] (Q : Type) [Group Q] (e : Q → Q → Kˣ → Prop) (n : ℕ) (ζ : Kˣ) (ev : D.La → Q), 0 < n → Nat.card {y : Q // y ^ n = 1} = n ^ Module.finrank ℤ D.La → (∀ y c, y ^ n = 1 → e 1 y c → c = 1) → IsPrimitiveRoot ζ n → (∀ a c, ev (a + c) = ev a * ev c) → (∀ a, ev a ^ n = 1) → (∀ a c, e (ev a) (ev c) (ζ ^ D.EF a c)) → (∀ a, ev a = 1 ↔ ∃ c, a = n • c) ∧ ∀ y, y ^ n = 1 ↔ ∃ a, ev a = y := by
  intro E _ _ _ H D K _ Q _ e n ζ ev hn hcard he1 hζ hev hevn hpair
  have hev0 : ev 0 = 1 := by
    have h := hev 0 0
    rw [add_zero] at h
    exact (mul_eq_left.1 h.symm)
  have hevsmul : ∀ (m : ℕ) (c : D.La), ev (m • c) = ev c ^ m := by
    intro m c
    induction m with
    | zero => simp [hev0]
    | succ m ih => rw [succ_nsmul, hev, ih, pow_succ]
  have hker : ∀ a, ev a = 1 ↔ ∃ c, a = n • c := by
    intro a
    constructor
    · intro ha
      refine _root_.GlobalTheory.TorsIsometry.exists_eq_nsmul_of_dvd D.EF D.unimod n a fun c => ?_
      have h := hpair a c
      rw [ha] at h
      exact (hζ.zpow_eq_one_iff_dvd _).1 (he1 _ _ (hevn c) h)
    · rintro ⟨c, rfl⟩
      rw [hevsmul, hevn]
  refine ⟨hker, fun y => ⟨fun hy => ?_, ?_⟩⟩
  swap
  · rintro ⟨a, rfl⟩
    exact hevn a
  haveI : NeZero n := ⟨hn.ne'⟩
  haveI := D.fin
  haveI : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  haveI : NoZeroSMulDivisors ℤ D.La := ⟨fun {c x} h => by
    by_cases hc : c = 0
    · exact Or.inl hc
    · right
      apply D.unimod.1
      ext b
      have := congrArg (fun x => D.EF x b) h
      simp only [map_zsmul, LinearMap.smul_apply, smul_eq_mul, map_zero,
        LinearMap.zero_apply] at this
      simpa [hc] using this⟩
  haveI : Module.Free ℤ D.La := Module.free_of_finite_type_torsion_free'
  let b := Module.finBasis ℤ D.La
  let g : (Fin (Module.finrank ℤ D.La) → ZMod n) → {y : Q // y ^ n = 1} :=
    fun t => ⟨ev (b.equivFun.symm fun i => ((t i).val : ℤ)), hevn _⟩
  have hinj : Function.Injective g := by
    intro t t' htt
    have h : ev (b.equivFun.symm fun i => ((t i).val : ℤ)) =
        ev (b.equivFun.symm fun i => ((t' i).val : ℤ)) := congrArg Subtype.val htt
    have hdiff : ev ((b.equivFun.symm fun i => ((t i).val : ℤ)) -
        b.equivFun.symm fun i => ((t' i).val : ℤ)) = 1 := by
      have h2 := hev ((b.equivFun.symm fun i => ((t i).val : ℤ)) -
        b.equivFun.symm fun i => ((t' i).val : ℤ)) (b.equivFun.symm fun i => ((t' i).val : ℤ))
      rw [sub_add_cancel, h] at h2
      exact mul_eq_right.1 h2.symm
    obtain ⟨c, hc⟩ := (hker _).1 hdiff
    funext i
    have hi := congrArg (fun z => b.equivFun z i) hc
    simp only [map_sub, LinearEquiv.apply_symm_apply, Pi.sub_apply, map_nsmul,
      Pi.smul_apply, nsmul_eq_mul] at hi
    have hcast := congrArg (Int.cast : ℤ → ZMod n) hi
    push_cast at hcast
    simpa [sub_eq_zero] using hcast
  haveI : Finite {y : Q // y ^ n = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  have hbij : Function.Bijective g := hinj.bijective_of_nat_card_le (by
    rw [hcard, Nat.card_fun, Nat.card_zmod, Nat.card_fin])
  obtain ⟨t, ht⟩ := hbij.2 ⟨y, hy⟩
  exact ⟨_, congrArg Subtype.val ht⟩

end GlobalTheory.TorsIsometry
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionIsometryPrimitiveRootBijectiveModNStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionIsometry_primitiveRoot_bijective_mod_n : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (K : Type) [Field K] (Q : Type) [Group Q] (e : Q → Q → Kˣ → Prop) (n : ℕ) (ζ : Kˣ) (ev : D.La → Q), 0 < n → Nat.card {y : Q // y ^ n = 1} = n ^ Module.finrank ℤ D.La → (∀ y c, y ^ n = 1 → e 1 y c → c = 1) → IsPrimitiveRoot ζ n → (∀ a c, ev (a + c) = ev a * ev c) → (∀ a, ev a ^ n = 1) → (∀ a c, e (ev a) (ev c) (ζ ^ D.EF a c)) → (∀ a, ev a = 1 ↔ ∃ c, a = n • c) ∧ ∀ y, y ^ n = 1 ↔ ∃ a, ev a = y := by
  first | exact @GlobalTheory.TorsIsometry.ker_and_onto | exact GlobalTheory.TorsIsometry.ker_and_onto | (intros; apply GlobalTheory.TorsIsometry.ker_and_onto <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.UnimodularSymplecticCoordinatesAndLatticeRank
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem hermForm_self_im_eq_zero {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (h : Hm.IsHermitian)
    (z : Fin g → ℂ) : (hermForm Hm z z).im = 0 := by
  rw [← Complex.conj_eq_iff_im]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hermForm, dotProduct, Matrix.mulVec, Finset.mul_sum, map_sum, map_mul,
    Pi.star_apply, Complex.star_def, Complex.conj_conj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [← h.apply j k, Complex.star_def]
  ring

theorem free_finite_finrank_of_discrete_span {La : Type} [AddCommGroup La] {g : ℕ}
    (Q : La →+ (Fin g → ℂ)) (hinj : Function.Injective Q) (hd : DiscreteTopology Q.range)
    (hsp : Submodule.span ℝ (Set.range Q) = ⊤) :
    Module.Free ℤ La ∧ Module.Finite ℤ La ∧ Module.finrank ℤ La = 2 * g := by
  set L : Submodule ℤ (Fin g → ℂ) := LinearMap.range Q.toIntLinearMap with hL
  haveI : DiscreteTopology L := hd
  haveI : IsZLattice ℝ L := ⟨by
    rw [hL, LinearMap.coe_range]
    exact hsp⟩
  let e : La ≃ₗ[ℤ] L := LinearEquiv.ofInjective Q.toIntLinearMap hinj
  haveI : Module.Free ℤ L := ZLattice.module_free ℝ L
  haveI : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  refine ⟨Module.Free.of_equiv e.symm, Module.Finite.equiv e.symm, ?_⟩
  rw [e.finrank_eq, ZLattice.rank ℝ L, Module.finrank_pi_fintype]
  simp [Complex.finrank_real_complex, mul_comm]

theorem unimodular_symplectic_coordinates_and_lattice_rank :
    (∀ (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (EF : LinearMap.BilinForm ℤ La) (g : ℕ), Function.Bijective EF → (∀ x, EF x x = 0) → Module.finrank ℤ La = 2 * g → ∃ bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] La, ∀ a b, EF (bas a) (bas b) = omegaStd a b) ∧ ∀ (La : Type) [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (g : ℕ) (Q : La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm (Q x) (Q y)).im = EF x y) → Module.Free ℤ La ∧ Module.Finite ℤ La ∧ Module.finrank ℤ La = 2 * g ∧ ∀ x, EF x x = 0 := by
  refine ⟨fun La _ _ _ EF g hbij halt hrk => ?_,
    fun La _ EF g Q Hm ⟨hinj, hd, hsp, hH, _, hIm⟩ => ?_⟩
  · obtain ⟨b, hb⟩ := exists_isSymplecticBasis_of_finrank (B := EF) halt hbij hrk
    have hf : IsSymplecticFamily EF (fun i => b (Sum.inl i)) (fun i => b (Sum.inr i))
        (fun _ => 1) := hb
    classical
    refine ⟨b.equivFun.symm, fun x y => ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Module.Basis.equivFun_symm_apply, Fintype.sum_sum_type, map_add (f := _), LinearMap.add_apply,
      map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    simp only [hf.left_left, hf.right_right, hf.left_right, hf.right_left halt, mul_zero,
      Finset.sum_const_zero, add_zero, zero_add, mul_ite, _root_.mul_one, mul_neg,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_neg_distrib, omegaStd]
    rw [neg_add_eq_sub, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  · obtain ⟨h1, h2, h3⟩ := free_finite_finrank_of_discrete_span Q hinj hd hsp
    exact ⟨h1, h2, h3, fun x => by
      have e : ((EF x x : ℤ) : ℝ) = 0 := by rw [← hIm x x]; exact hermForm_self_im_eq_zero hH _
      exact_mod_cast e⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HermFormSwapOfIsHermitian
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.LatticeHom

theorem exists_le_mul_of_homogeneous {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    (q q' : E → ℝ) (hq : Continuous q) (hq' : Continuous q') (hpos : ∀ z, z ≠ 0 → 0 < q z)
    (hs : ∀ (t : ℝ) z, q (t • z) = t ^ 2 * q z) (hs' : ∀ (t : ℝ) z, q' (t • z) = t ^ 2 * q' z) :
    ∃ C : ℝ, ∀ z, q' z ≤ C * q z := by
  have hS : IsCompact (Metric.sphere (0 : E) 1) := isCompact_sphere 0 1
  have hcont : ContinuousOn (fun z => q' z / q z) (Metric.sphere (0 : E) 1) := by
    refine hq'.continuousOn.div hq.continuousOn ?_
    intro z hz
    have hz0 : z ≠ 0 := by
      rintro rfl
      simp at hz
    exact (hpos z hz0).ne'
  obtain ⟨C, hC⟩ := hS.bddAbove_image hcont
  refine ⟨C, fun z => ?_⟩
  have h0 : ∀ f : E → ℝ, (∀ (t : ℝ) z, f (t • z) = t ^ 2 * f z) → f 0 = 0 := by
    intro f hf
    simpa using hf 0 0
  by_cases hz : z = 0
  · rw [hz, h0 q hs, h0 q' hs', mul_zero]
  · have hr0 : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hwS : ‖z‖⁻¹ • z ∈ Metric.sphere (0 : E) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hr0.ne']
    have hzw : z = ‖z‖ • (‖z‖⁻¹ • z) := by rw [smul_smul, mul_inv_cancel₀ hr0.ne', one_smul]
    have hw0 : ‖z‖⁻¹ • z ≠ 0 := by
      intro h
      rw [h] at hwS
      simp at hwS
    have hwpos := hpos _ hw0
    have hCw : q' (‖z‖⁻¹ • z) / q (‖z‖⁻¹ • z) ≤ C := hC (Set.mem_image_of_mem _ hwS)
    rw [div_le_iff₀ hwpos] at hCw
    rw [hzw, hs, hs']
    calc ‖z‖ ^ 2 * q' (‖z‖⁻¹ • z) ≤ ‖z‖ ^ 2 * (C * q (‖z‖⁻¹ • z)) :=
          mul_le_mul_of_nonneg_left hCw (sq_nonneg _)
      _ = C * (‖z‖ ^ 2 * q (‖z‖⁻¹ • z)) := by ring

theorem hermForm_swap_of_isHermitian {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (h : Hm.IsHermitian)
    (z w : Fin g → ℂ) : hermForm Hm w z = (starRingEnd ℂ) (hermForm Hm z w) := by
  unfold hermForm
  change _ = star _
  simp only [dotProduct, mulVec, star_sum, star_mul', Pi.star_apply, star_star, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [h.apply j i]
  ring

theorem hermForm_add_add {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    hermForm Hm (z + w) (z + w) = hermForm Hm z z + hermForm Hm z w + hermForm Hm w z + hermForm Hm w w := by
  unfold hermForm
  simp only [star_add, mulVec_add, add_dotProduct, dotProduct_add]
  ring

theorem re_hermForm_real_smul {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (t : ℝ) (z : Fin g → ℂ) :
    (hermForm Hm (t • z) (t • z)).re = t ^ 2 * (hermForm Hm z z).re := by
  unfold hermForm
  have hst : star (t • z) = t • star z := by rw [star_smul, star_trivial]
  rw [hst, mulVec_smul, smul_dotProduct, dotProduct_smul, smul_smul, Complex.smul_re]
  ring

theorem continuous_re_hermForm {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) :
    Continuous fun z : Fin g → ℂ => (hermForm Hm z z).re := by
  unfold hermForm
  simp only [dotProduct, mulVec, Pi.star_apply]
  fun_prop

theorem exists_hermForm_pull {g g' : ℕ} {Hm : Matrix (Fin g') (Fin g') ℂ} (h : Hm.IsHermitian)
    (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) :
    ∃ K : Matrix (Fin g) (Fin g) ℂ, K.IsHermitian ∧ ∀ z w, hermForm K z w = hermForm Hm (F z) (F w) := by
  set M := LinearMap.toMatrix' F
  have hF : ∀ z, F z = M *ᵥ z := fun z => by rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  refine ⟨Mᵀ * Hm * Mᵀᴴ, isHermitian_mul_mul_conjTranspose _ h, fun z w => ?_⟩
  unfold hermForm
  rw [hF, hF, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec z Mᵀ, vecMul_transpose, ← star_vecMul,
    vecMul_transpose]

variable {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A'] {L : LB A.left} {L' : LB A'.left} {g g' : ℕ}

theorem semicharacter_add (u : HolUnif A L g) (hL : L.IsLB) {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ}
    (h : u.IsAH Hm χ) (l m : u.Λ) :
    χ (l + m) = χ l * χ m * cexp (Real.pi * I * (hermForm Hm l m).im) := by
  obtain ⟨i, hi⟩ := GlobalTheory.SymmetricSemicharacter.exists_chart u GlobalTheory.SymmetricSemicharacter.valueRules hL 0
  have hfr := h.2.2.2
  have hl : ⊤ ≤ (u.ex (0 + (l : Fin g → ℂ))).left ⁻¹ᵁ L.U i := by
    rw [GlobalTheory.SectionTheta.ex_add_lattice]; exact hi
  have hex : u.ex ((l : Fin g → ℂ) + m) = u.ex 0 := by
    simpa using GlobalTheory.SectionTheta.ex_add_lattice u 0 (l + m)
  have hX : u.fr i ((l : Fin g → ℂ) + m) ≠ 0 := u.fr_ne i _ (by rw [hex]; exact hi)
  have hz : ∀ x, hermForm Hm 0 x = 0 := fun x => by simp [hermForm]
  have e1 : u.fr i 0 = χ (l + m) * cexp (Real.pi * hermForm Hm 0 ((l + m : u.Λ) : Fin g → ℂ) +
      Real.pi / 2 * hermForm Hm ((l + m : u.Λ) : Fin g → ℂ) ((l + m : u.Λ) : Fin g → ℂ)) *
      u.fr i (0 + ((l + m : u.Λ) : Fin g → ℂ)) := hfr (l + m) i 0 hi
  have e2 : u.fr i 0 = χ l * cexp (Real.pi * hermForm Hm 0 l + Real.pi / 2 * hermForm Hm l l) *
      u.fr i (0 + (l : Fin g → ℂ)) := hfr l i 0 hi
  have e3 : u.fr i (0 + (l : Fin g → ℂ)) = χ m * cexp (Real.pi * hermForm Hm (0 + (l : Fin g → ℂ)) m +
      Real.pi / 2 * hermForm Hm m m) * u.fr i (0 + (l : Fin g → ℂ) + m) := hfr m i (0 + l) hl
  simp only [hz, zero_add, mul_zero, Submodule.coe_add] at e1 e2 e3
  rw [e3] at e2
  rw [e2] at e1
  have hb : hermForm Hm (m : Fin g → ℂ) l = (starRingEnd ℂ) (hermForm Hm l m) :=
    hermForm_swap_of_isHermitian h.1 l m
  have hsc := Complex.sub_conj (hermForm Hm l m)
  have hexp : cexp (Real.pi / 2 * hermForm Hm l l) * cexp (Real.pi * hermForm Hm l m + Real.pi / 2 * hermForm Hm m m) =
      cexp (Real.pi / 2 * hermForm Hm ((l : Fin g → ℂ) + m) ((l : Fin g → ℂ) + m)) *
        cexp (Real.pi * I * (hermForm Hm l m).im) := by
    rw [← Complex.exp_add, ← Complex.exp_add, hermForm_add_add, hb]
    congr 1
    push_cast at hsc ⊢
    linear_combination (Real.pi / 2 : ℂ) * hsc
  have hC := Complex.exp_ne_zero (Real.pi / 2 * hermForm Hm ((l : Fin g → ℂ) + m) ((l : Fin g → ℂ) + m))
  have key : (χ (l + m) - χ l * χ m * cexp (Real.pi * I * (hermForm Hm l m).im)) *
      (cexp (Real.pi / 2 * hermForm Hm ((l : Fin g → ℂ) + m) ((l : Fin g → ℂ) + m)) *
        u.fr i ((l : Fin g → ℂ) + m)) = 0 := by
    linear_combination -e1 + (χ l * χ m * u.fr i ((l : Fin g → ℂ) + m)) * hexp
  rcases mul_eq_zero.1 key with h1 | h1
  · exact sub_eq_zero.1 h1
  · exact absurd h1 (mul_ne_zero hC hX)

private theorem conj_cexp_pi_mul_I_mul_real (t : ℝ) :
    (starRingEnd ℂ) (cexp (Real.pi * I * t)) = cexp (-(Real.pi * I * t)) := by
  rw [← Complex.exp_conj, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  ring

theorem exists_complementary_theta
    (hth : ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → ∀ H₀ : Matrix (Fin g) (Fin g) ℂ, (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₀.mulVec (star z)).re) → ∃ ρ : ℝ, ∀ (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : Λ → ℂ), Hm.IsHermitian → (∀ z : Fin g → ℂ, ρ * (z ⬝ᵥ H₀.mulVec (star z)).re ≤ (z ⬝ᵥ Hm.mulVec (star z)).re) → (∀ l, ‖χ l‖ = 1) → (∀ l m : Λ, χ (l + m) = χ l * χ m * cexp (Real.pi * I * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ))).im)) → ∀ z₀, ∃ θ : (Fin g → ℂ) → ℂ, Differentiable ℂ θ ∧ θ z₀ ≠ 0 ∧ ∀ (l : Λ) z, θ (z + l) = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) + Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))))) * θ z)
    (u : HolUnif A L g) (u' : HolUnif A' L' g') (hL : L.IsLB) (hL' : L'.IsLB)
    {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ} {Hm' : Matrix (Fin g') (Fin g') ℂ} {χ' : u'.Λ → ℂ}
    (h : u.IsAH Hm χ) (h' : u'.IsAH Hm' χ') (F : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (hF : ∀ l ∈ u.Λ, F l ∈ u'.Λ) (N : ℕ) :
    ∃ d : ℕ, ∀ z₀, ∃ G : (Fin g → ℂ) → ℂ, G z₀ ≠ 0 ∧
      ∀ θ, u'.IsThetaFn Hm' χ' N θ → u.IsThetaFn Hm χ d (fun z => θ (F z) * G z) := by
  obtain ⟨K, hK, hKF⟩ := exists_hermForm_pull h'.1 F
  obtain ⟨Fl, hFl⟩ : ∃ Fl : u.Λ → u'.Λ, ∀ l, ((Fl l : u'.Λ) : Fin g' → ℂ) = F l :=
    ⟨fun l => ⟨F l, hF l l.2⟩, fun _ => rfl⟩
  have hFl_add : ∀ l m, Fl (l + m) = Fl l + Fl m := fun l m => by
    apply Subtype.ext
    rw [Submodule.coe_add, hFl, hFl, hFl, Submodule.coe_add, map_add (f := _)]
  obtain ⟨ρ, hρ⟩ := hth g u.Λ u.discrete u.full Hm h.2.1
  obtain ⟨C, hC⟩ := exists_le_mul_of_homogeneous (fun z => (hermForm Hm z z).re) (fun z => (hermForm K z z).re)
    (continuous_re_hermForm Hm) (continuous_re_hermForm K) h.2.1 (re_hermForm_real_smul Hm)
    (re_hermForm_real_smul K)
  obtain ⟨d, hd⟩ := exists_nat_ge (ρ + N * C)
  refine ⟨d, fun z₀ => ?_⟩
  obtain ⟨Hg, hHg⟩ : ∃ Hg : Matrix (Fin g) (Fin g) ℂ, Hg = (d : ℂ) • Hm - (N : ℂ) • K := ⟨_, rfl⟩
  obtain ⟨χg, hχg⟩ : ∃ f : u.Λ → ℂ, ∀ l, f l = χ l ^ d * (starRingEnd ℂ) (χ' (Fl l)) ^ N := ⟨_, fun _ => rfl⟩
  have hHg_form : ∀ z w, hermForm Hg z w = d * hermForm Hm z w - N * hermForm K z w := by
    intro z w
    simp [hHg, hermForm, sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul]
  have hHgH : Hg.IsHermitian := by
    rw [hHg, IsHermitian, conjTranspose_sub, conjTranspose_smul, conjTranspose_smul, h.1.eq, hK.eq]
    simp
  have hbound : ∀ z : Fin g → ℂ, ρ * (hermForm Hm z z).re ≤ (hermForm Hg z z).re := by
    intro z
    have hre : (hermForm Hg z z).re = d * (hermForm Hm z z).re - N * (hermForm K z z).re := by
      rw [hHg_form]; simp
    rw [hre]
    have h1 := hC z
    have h2 : 0 ≤ (hermForm Hm z z).re := by
      by_cases hz : z = 0
      · simp [hz, hermForm]
      · exact (h.2.1 z hz).le
    nlinarith [mul_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N) (sub_nonneg.2 h1), mul_nonneg (sub_nonneg.2 hd) h2]
  have hnorm : ∀ l, ‖χg l‖ = 1 := by
    intro l
    rw [hχg, norm_mul, norm_pow, norm_pow, h.2.2.1, Complex.norm_conj, h'.2.2.1, one_pow, one_pow, _root_.one_mul]
  have hsemi : ∀ l m : u.Λ, χg (l + m) = χg l * χg m *
      cexp (Real.pi * I * ((l : Fin g → ℂ) ⬝ᵥ Hg.mulVec (star (m : Fin g → ℂ))).im) := by
    intro l m
    change χg (l + m) = χg l * χg m * cexp (Real.pi * I * (hermForm Hg l m).im)
    have s1 := semicharacter_add u hL h l m
    have s2 := semicharacter_add u' hL' h' (Fl l) (Fl m)
    rw [hFl, hFl, ← hKF] at s2
    rw [hχg, hχg, hχg, hFl_add, s1, s2, hHg_form, map_mul, map_mul, conj_cexp_pi_mul_I_mul_real]
    have him : ((d : ℂ) * hermForm Hm l m - N * hermForm K l m).im =
        d * (hermForm Hm l m).im - N * (hermForm K l m).im := by simp
    rw [him]
    have he : cexp (Real.pi * I * (hermForm Hm l m).im) ^ d * cexp (-(Real.pi * I * (hermForm K l m).im)) ^ N =
        cexp (Real.pi * I * ((d * (hermForm Hm l m).im - N * (hermForm K l m).im : ℝ) : ℂ)) := by
      rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    linear_combination (χ l ^ d * χ m ^ d * (starRingEnd ℂ) (χ' (Fl l)) ^ N * (starRingEnd ℂ) (χ' (Fl m)) ^ N) * he
  obtain ⟨G, hGd, hG0, hGt⟩ := hρ Hg χg hHgH hbound hnorm hsemi z₀
  refine ⟨G, hG0, fun θ hθ => ⟨?_, fun l z => ?_⟩⟩
  · exact (hθ.1.comp (LinearMap.toContinuousLinearMap F).differentiable).mul hGd
  · have t1 := hθ.2 (Fl l) (F z)
    rw [hFl, ← hKF, ← hKF] at t1
    have t2 : G (z + l) = χg l * cexp (Real.pi * hermForm Hg z l + Real.pi / 2 * hermForm Hg l l) * G z := hGt l z
    have hψ : χ' (Fl l) * (starRingEnd ℂ) (χ' (Fl l)) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, h'.2.2.1]; simp
    have hψN : (χ' (Fl l) * (starRingEnd ℂ) (χ' (Fl l))) ^ N = 1 := by rw [hψ, one_pow]
    have hexp : cexp (Real.pi * (d * hermForm Hm z l - N * hermForm K z l) +
        Real.pi / 2 * (d * hermForm Hm l l - N * hermForm K l l)) *
        cexp (Real.pi * hermForm K z l + Real.pi / 2 * hermForm K l l) ^ N =
        cexp (Real.pi * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l) ^ d := by
      rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
      congr 1
      ring
    show θ (F (z + l)) * G (z + l) = _ * (θ (F z) * G z)
    rw [map_add (f := _), t1, t2, hHg_form, hHg_form, hχg]
    linear_combination (χ l ^ d * θ (F z) * G z * (cexp (Real.pi * (d * hermForm Hm z l - N * hermForm K z l) +
        Real.pi / 2 * (d * hermForm Hm l l - N * hermForm K l l)) *
        cexp (Real.pi * hermForm K z l + Real.pi / 2 * hermForm K l l) ^ N)) * hψN +
      (χ l ^ d * θ (F z) * G z) * hexp

end GlobalTheory.LatticeHom
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.AppTopSurjective
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.BaseChangeFns

private theorem surjective_appTop_of_iso {X Y : Scheme.{0}} (e : X ≅ Y) : Function.Surjective e.hom.appTop.hom := by
  first
  | exact (ConcreteCategory.bijective_of_isIso e.hom.appTop).2
  | exact (ConcreteCategory.bijective_of_isIso (e.hom.app ⊤)).2
  | exact fun a => ⟨e.inv.appTop.hom a, by
      rw [← CommRingCat.comp_apply, ← Scheme.comp_appTop, e.inv_hom_id, Scheme.id_appTop]; rfl⟩

private theorem surjective_appTop_comp {X Y Z : Scheme.{0}} (p : X ⟶ Y) (q : Y ⟶ Z)
    (hp : Function.Surjective p.appTop.hom) (hq : Function.Surjective q.appTop.hom) :
    Function.Surjective (p ≫ q).appTop.hom := by
  first
  | exact hp.comp hq
  | (rw [Scheme.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp]; exact hp.comp hq)
  | exact surj_comp hp hq

private theorem surjective_of_comp_surjective_of_injective {A B C : CommRingCat} (g : A ⟶ B) (m : B ⟶ C)
    (hm : Function.Injective m.hom) (h : Function.Surjective (g ≫ m).hom) : Function.Surjective g.hom := by
  intro y
  obtain ⟨x, hx⟩ := h (m.hom y)
  exact ⟨x, hm hx⟩

private theorem injective_presheaf_map_eqToHom {X : Scheme.{0}} {V W : X.Opens} (p : V = W) :
    Function.Injective (X.presheaf.map (eqToHom p).op).hom := by
  subst p
  first
  | (intro a b hab; simpa using hab)
  | (simp only [eqToHom_refl, op_id, Functor.map_id, CommRingCat.hom_id]; exact Function.injective_id)

private theorem isAbelianScheme_pullback' {S₀ S : Scheme.{0}} {B : Over S₀} [GrpObj B] (t : S ⟶ S₀)
    (hB : IsAbelianScheme B) : IsAbelianScheme ((Over.pullback t).obj B) := by
  have h1 := hB.smooth
  have h2 := hB.proper
  have h3 := hB.geomConnected
  have h4 := hB.comm
  constructor
  case comm =>
    first
    | infer_instance
    | exact Functor.obj.instIsCommMonObj _
  case smooth =>
    show Smooth (pullback.snd B.hom t)
    first
    | infer_instance
    | exact MorphismProperty.pullback_snd _ _ h1
  case proper =>
    show IsProper (pullback.snd B.hom t)
    first
    | infer_instance
    | exact MorphismProperty.pullback_snd _ _ h2
  case geomConnected =>
    show GeometricallyConnected (pullback.snd B.hom t)
    first
    | infer_instance
    | exact MorphismProperty.pullback_snd _ _ h3

theorem appTop_surjective (hG : Out.GlobalFnsSt) {S₀ : Scheme.{0}} {B : Over S₀} [GrpObj B]
    (hB : IsAbelianScheme B) {S X : Scheme.{0}} {t : S ⟶ S₀} {π : X ⟶ B.left} {f : X ⟶ S}
    (h : IsPullback π f B.hom t) : Function.Surjective f.appTop.hom := by
  have key : Function.Surjective (pullback.snd B.hom t).appTop.hom :=
    (hG S ((Over.pullback t).obj B) (isAbelianScheme_pullback' t hB)).2
  rw [← h.isoPullback_hom_snd]
  exact surjective_appTop_comp _ _ (surjective_appTop_of_iso _) key

theorem app_surjective : Out.GlobalFnsSt → ∀ (S₀ : Scheme.{0}) (B : Over S₀) [GrpObj B], IsAbelianScheme B → ∀ (S X : Scheme.{0}) (t : S ⟶ S₀) (π : X ⟶ B.left) (f : X ⟶ S), IsPullback π f B.hom t → ∀ U : S.Opens, Function.Surjective (f.app U).hom := by
  intro hG S₀ B _ hB S X t π f h U
  have hP : IsPullback ((f ⁻¹ᵁ U).ι ≫ π) (f ∣_ U) B.hom (U.ι ≫ t) :=
    (isPullback_morphismRestrict f U).flip.paste_horiz h
  have hres := appTop_surjective hG hB hP
  rw [morphismRestrict_appTop] at hres
  have hV := surjective_of_comp_surjective_of_injective _ _ (injective_presheaf_map_eqToHom _) hres
  change Function.Surjective (f.app (U.ι ''ᵁ ⊤)).hom at hV
  rwa [Scheme.Opens.ι_image_top] at hV

end GlobalTheory.BaseChangeFns
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericFlatnessScheme
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

namespace GenericFlatScheme

theorem affine (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (A : CommRingCat.{0})
    (s : Spec A ⟶ Sp R) [LocallyOfFiniteType s] :
    ∃ f : R, f ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (φ : R →+* R'), IsUnit (φ f) →
      Flat (pullback.snd s (spMap φ)) := by
  obtain ⟨g, rfl⟩ : ∃ g : CommRingCat.of R ⟶ A, Spec.map g = s :=
    ⟨Spec.preimage s, Spec.map_preimage s⟩
  have hg : g.hom.FiniteType :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp inferInstance
  let : Algebra R A := g.hom.toAlgebra
  have : Algebra.FiniteType R A := hg
  obtain ⟨a, ha, hfree⟩ := (GlobalTheory.generic_freeness R).2.1 A A
  refine ⟨a, ha, fun R' _ φ hφ => ?_⟩
  let : Algebra R R' := φ.toAlgebra

  let : Algebra (Localization.Away a) R' := (IsLocalization.Away.lift a hφ).toAlgebra
  have : IsScalarTower R (Localization.Away a) R' :=
    IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.Away.lift_eq a hφ x).symm
  have := hfree
  have hbc : IsBaseChange (Localization.Away a)
      (LocalizedModule.mkLinearMap (Submonoid.powers a) A) :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers a) (Localization.Away a) _).mp
      inferInstance
  have : Module.Free (Localization.Away a) (Localization.Away a ⊗[R] A) :=
    Module.Free.of_equiv hbc.equiv.symm
  have hflat : Module.Flat R' (R' ⊗[R] A) :=
    Module.Flat.of_linearEquiv
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R (Localization.Away a) R' R' A).symm

  have hA : g = CommRingCat.ofHom (algebraMap R A) := rfl
  have hF : Flat (Spec.map (CommRingCat.ofHom (algebraMap R' (R' ⊗[R] A)))) :=
    (HasRingHomProperty.Spec_iff (P := @Flat)).mpr (RingHom.flat_algebraMap_iff.mpr hflat)
  rw [hA]
  change Flat (pullback.snd _ (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
  rw [← pullbackSymmetry_hom_comp_fst, ← pullbackSpecIso_hom_fst' R R' A]
  infer_instance

end GenericFlatScheme

theorem generic_flatness_scheme :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R),
      LocallyOfFiniteType s → QuasiCompact s → ∃ f : R, f ≠ 0 ∧
        ∀ (R' : Type) [CommRing R'] (φ : R →+* R'), IsUnit (φ f) →
          Flat (pullback.snd s (spMap φ)) := by
  intro R _ _ _ Z s hs hq
  have := hs
  have := hq
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace s
  let 𝒰 := Z.affineCover.finiteSubcover
  have key : ∀ i, ∃ f : R, f ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (φ : R →+* R'), IsUnit (φ f) →
      Flat (pullback.snd (𝒰.f i ≫ s) (spMap φ)) :=
    fun i => by
      have : LocallyOfFiniteType (𝒰.f i ≫ s) := MorphismProperty.comp_mem _ _ _
        (inferInstance : LocallyOfFiniteType (𝒰.f i)) hs
      exact @GenericFlatScheme.affine R _ _ _ _ (𝒰.f i ≫ s) this
  choose e he0 heF using key
  refine ⟨∏ i, e i, Finset.prod_ne_zero_iff.mpr fun i _ => he0 i, fun R' _ φ hφ => ?_⟩

  have hloc : IsZariskiLocalAtSource @AlgebraicGeometry.Flat :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @AlgebraicGeometry.Flat)
  refine (IsZariskiLocalAtSource.iff_of_openCover (P := @AlgebraicGeometry.Flat)
    (𝒰.pullback₁ (pullback.fst s (spMap φ)))).mpr fun i => ?_
  change Flat (pullback.fst (pullback.fst s (spMap φ)) (𝒰.f i) ≫ pullback.snd s (spMap φ))
  have := heF i R' φ
    (isUnit_of_dvd_unit (map_dvd φ (Finset.dvd_prod_of_mem e (Finset.mem_univ _))) hφ)
  have h : pullback.fst (pullback.fst s (spMap φ)) (𝒰.f i) ≫ pullback.snd s (spMap φ) =
      ((pullbackSymmetry _ _).hom ≫ (pullbackRightPullbackFstIso s (spMap φ) (𝒰.f i)).hom) ≫
        pullback.snd (𝒰.f i ≫ s) (spMap φ) := by
    rw [Category.assoc, pullbackRightPullbackFstIso_hom_snd, pullbackSymmetry_hom_comp_snd_assoc]
  rw [h]
  infer_instance

end GlobalTheory
end
