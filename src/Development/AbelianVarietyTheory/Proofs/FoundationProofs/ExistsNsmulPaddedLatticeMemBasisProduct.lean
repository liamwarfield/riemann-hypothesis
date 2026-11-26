module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RationalPointsIntegralPointsMembership
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IotaOQContinuousInjective
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralLeOfDisjointTranslates
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DerivationDenominatorsAndHostFieldSizes
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemISupInfWeightSubmoduleOfDiagonalStable
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalCoefficientChangeCompare

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNsmulPaddedLatticeMemBasisProduct
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNsmulPaddedLatticeMemBasisProduct
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.GalTheta
open scoped BigOperators

noncomputable section

namespace GlobalTheory.PadCommensurable

def sat {V V' : Type*} [AddCommGroup V] [AddCommGroup V'] (f : V →+ V') (B : AddSubgroup V') : AddSubgroup V where
  carrier := {y | ∃ n : ℕ, 0 < n ∧ n • f y ∈ B}
  zero_mem' := ⟨1, one_pos, by simp⟩
  add_mem' := by
    rintro x y ⟨n, hn, hx⟩ ⟨k, hk, hy⟩
    refine ⟨n * k, Nat.mul_pos hn hk, ?_⟩
    rw [map_add (f := _), smul_add]
    refine B.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact B.nsmul_mem hx _
    · rw [mul_smul]; exact B.nsmul_mem hy _
  neg_mem' := by
    rintro x ⟨n, hn, hx⟩
    exact ⟨n, hn, by rw [map_neg, smul_neg]; exact B.neg_mem hx⟩

theorem uniform_of_fg {V V' : Type*} [AddCommGroup V] [AddCommGroup V'] (f : V →+ V') (A : AddSubgroup V)
    (B : AddSubgroup V') (hA : A.FG) (h : A ≤ sat f B) : ∃ R : ℕ, 0 < R ∧ ∀ y ∈ A, R • f y ∈ B := by
  obtain ⟨S, hS⟩ := hA
  have h' : ∀ y : S, ∃ n : ℕ, 0 < n ∧ n • f y.1.1 ∈ B :=
    fun y => h y.1.2
  choose n hn hy using h'
  refine ⟨∏ y, n y, Finset.prod_pos fun y _ => hn y, fun y hy' => ?_⟩
  have hall : ∀ x : A, x ∈ AddSubsemigroup.closure (S : Set A) →
      (∏ y, n y) • f x.1 ∈ B := by
    intro x hx
    induction hx using AddSubsemigroup.closure_induction with
    | mem x hx =>
      obtain ⟨c, hc⟩ : n ⟨x, hx⟩ ∣ ∏ y, n y := Finset.dvd_prod_of_mem _ (Finset.mem_univ _)
      rw [hc, mul_comm, mul_smul]
      exact B.nsmul_mem (hy ⟨x, hx⟩) _
    | add x y _ _ hx hy =>
      change (∏ y, n y) • f (x.1 + y.1) ∈ B
      rw [map_add, smul_add]
      exact B.add_mem hx hy
  apply hall ⟨y, hy'⟩
  rw [hS]
  trivial

theorem exists_nat_mul_int {K : Type*} [Field K] [NumberField K] (κ : K) :
    ∃ (n : ℕ) (a : 𝓞 K), 0 < n ∧ (a : K) = n * κ := by
  have halg : IsAlgebraic ℤ κ := (IsFractionRing.isAlgebraic_iff ℤ ℚ K).2 (Algebra.IsAlgebraic.isAlgebraic κ)
  obtain ⟨d, hd, hi⟩ := halg.exists_integral_multiple
  rcases Int.natAbs_eq d with h | h
  · refine ⟨d.natAbs, ⟨d • κ, hi⟩, Int.natAbs_pos.2 hd, ?_⟩
    change d • κ = _
    rw [zsmul_eq_mul]
    conv_lhs => rw [h]
    rw [Int.cast_natCast]
  · refine ⟨d.natAbs, -⟨d • κ, hi⟩, Int.natAbs_pos.2 hd, ?_⟩
    change -(d • κ) = _
    rw [zsmul_eq_mul]
    conv_lhs => rw [h]
    rw [Int.cast_neg, Int.cast_natCast]
    ring

theorem exists_nsmul_mem (D : D7) (hD : admG1 D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (hc : Crv D cc δ) {N N' r : ℕ}
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (hb : OnB D b) (w : ℂ) (hw : w ∈ lamOf D cc δ)
    (A : Matrix (Fin N') (Fin N) D.host.E) :
    w • embV D (tor0 D cc δ) A ∈ sat (AddMonoidHom.id _) (LaB D (tor0 D cc δ) b) := by
  obtain ⟨-, -, -, -, hst⟩ := GlobalTheory.CurveLattice.lattice_of_curve D hD cc δ hc
  have hA : A ∈ Submodule.span D.host.K (Set.range b) := by rw [hb.2]; trivial
  obtain ⟨κ, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hA
  have e : w • embV D (tor0 D cc δ) (∑ i, κ i • b i) =
      ∑ i, (D.host.φ₀ (κ i : D.host.E) * w) • embV D (tor0 D cc δ) (b i) := by
    funext τ s t
    have h1 : ∀ i, (κ i • b i) s t = (κ i : D.host.E) * b i s t := fun i => rfl
    have h2 := hD.1 τ
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [embV, tor0, Pi.smul_apply, Finset.sum_apply, Matrix.sum_apply, h1, map_sum, map_mul, h2,
      smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e]
  refine AddSubgroup.sum_mem _ fun i _ => ?_
  obtain ⟨n, a, hn, ha⟩ := exists_nat_mul_int (κ i)
  refine ⟨n, hn, AddSubgroup.subset_closure ⟨_, hst a w hw, i, ?_⟩⟩
  rw [AddMonoidHom.id_apply, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, ha]
  congr 1
  push_cast
  rw [map_mul, map_natCast]
  ring

theorem nsmul_pad_mem : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' m r : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (b : Fin r → Matrix (Fin N') (Fin (N + m)) D.host.E), OnB D b → (La D (tor0 D cc δ) L L').FG → ∃ R : ℕ, 0 < R ∧ ∀ y ∈ La D (tor0 D cc δ) L L', R • pad D m y ∈ LaB D (tor0 D cc δ) b := by
  intro D hD cc δ hc N N' m r L L' b hb hfg
  refine uniform_of_fg (padL D m).toAddMonoidHom _ _ hfg ?_
  rw [La, AddSubgroup.closure_le]
  rintro _ ⟨w, hw, A, -, rfl⟩
  obtain ⟨n, hn, h⟩ := exists_nsmul_mem D hD cc δ hc b hb w hw (padM D m A)
  refine ⟨n, hn, ?_⟩
  change n • pad D m _ ∈ _
  rw [pad_smul, pad_embV D _ (fun τ => map_zero (embT D τ))]
  exact h

end GlobalTheory.PadCommensurable
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNsmulPaddedLatticeMemBasisProductStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.GalTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nsmul_padded_lattice_mem_basis_product : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' m r : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (b : Fin r → Matrix (Fin N') (Fin (N + m)) D.host.E), OnB D b → (La D (tor0 D cc δ) L L').FG → ∃ R : ℕ, 0 < R ∧ ∀ y ∈ La D (tor0 D cc δ) L L', R • pad D m y ∈ LaB D (tor0 D cc δ) b := by
  first | exact @GlobalTheory.PadCommensurable.nsmul_pad_mem | exact GlobalTheory.PadCommensurable.nsmul_pad_mem | (intros; apply GlobalTheory.PadCommensurable.nsmul_pad_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsConjOfTraceEqResiduallyAbsIrreducibleDVR
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanEqTopOfSpanResidueEqTop
namespace GlobalTheory.ResidueSpanLift

open IsLocalRing

theorem mem_smul_top_of_entries {O : Type} [CommRing O] {a : ℕ} (I : Ideal O)
    (X : Matrix (Fin a) (Fin a) O) (h : ∀ i j, X i j ∈ I) :
    X ∈ I • (⊤ : Submodule O (Matrix (Fin a) (Fin a) O)) := by
  rw [Matrix.matrix_eq_sum_single X]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
  have : Matrix.single i j (X i j) = X i j • Matrix.single i j (1 : O) := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [this]
  exact Submodule.smul_mem_smul (h i j) Submodule.mem_top

theorem exists_lift {O ι : Type} [CommRing O] [IsLocalRing O] {a : ℕ}
    (M : ι → Matrix (Fin a) (Fin a) O) (Y : Matrix (Fin a) (Fin a) (ResidueField O))
    (hY : Y ∈ Submodule.span (ResidueField O)
      (Set.range fun g : ι => (M g).map (residue O))) :
    ∃ Z ∈ Submodule.span O (Set.range M), Z.map (residue O) = Y := by
  induction hY using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    exact ⟨M g, Submodule.subset_span ⟨g, rfl⟩, rfl⟩
  | zero => exact ⟨0, Submodule.zero_mem _, by ext i j; simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨Z, hZ, rfl⟩ := hx
    obtain ⟨W, hW, rfl⟩ := hy
    exact ⟨Z + W, Submodule.add_mem _ hZ hW, by ext i j; simp⟩
  | smul c x _ hx =>
    obtain ⟨Z, hZ, rfl⟩ := hx
    obtain ⟨d, rfl⟩ := residue_surjective c
    refine ⟨d • Z, Submodule.smul_mem _ _ hZ, ?_⟩
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]

theorem span_eq_top_of_span_residue_eq_top {O ι : Type} [CommRing O] [IsLocalRing O] {a : ℕ}
    (M : ι → Matrix (Fin a) (Fin a) O)
    (h : Submodule.span (ResidueField O)
      (Set.range fun g : ι => (M g).map (residue O)) = ⊤) :
    Submodule.span O (Set.range M) = ⊤ := by
  refine top_le_iff.mp ?_
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal O)
    Module.Finite.fg_top (maximalIdeal_le_jacobson _) ?_
  intro X _
  obtain ⟨Z, hZ, hZX⟩ := exists_lift M (X.map (residue O)) (h ▸ Submodule.mem_top)
  have hX : X = Z + (X - Z) := by abel
  rw [hX]
  refine Submodule.add_mem_sup hZ (mem_smul_top_of_entries _ _ fun i j => ?_)
  have := congrFun (congrFun hZX i) j
  simp only [Matrix.map_apply] at this
  rw [← residue_eq_zero_iff, Matrix.sub_apply, map_sub, this, sub_self]

end GlobalTheory.ResidueSpanLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsConjOfTraceEqResiduallyAbsIrreducibleDVR
namespace GlobalTheory.TraceConjugacy

open Matrix

theorem exists_conj_of_surjective {O A : Type} [CommRing O] [IsLocalRing O] [Ring A] [Algebra O A]
    {a : ℕ} (φ φ' : A →ₐ[O] Matrix (Fin a) (Fin a) O) (hφ : Function.Surjective φ)
    (htr : ∀ x, (φ x).trace = (φ' x).trace) :
    ∃ U : GL (Fin a) O, ∀ x, φ' x * (U : Matrix (Fin a) (Fin a) O) = U * φ x := by
  classical
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exact ⟨1, fun x => Subsingleton.elim _ _⟩
  obtain ⟨s, hs⟩ := φ.toLinearMap.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.2 hφ)
  have hs' : ∀ X, φ (s X) = X := fun X => LinearMap.congr_fun hs X
  let θ : Matrix (Fin a) (Fin a) O →ₗ[O] Matrix (Fin a) (Fin a) O := φ'.toLinearMap ∘ₗ s
  have hθ : ∀ X, θ X = φ' (s X) := fun X => rfl
  let T : Matrix (Fin a) (Fin a) O →ₗ[O] Matrix (Fin a) (Fin a) O :=
    { toFun := fun X => Matrix.of fun i j => (X * θ (Matrix.single j i 1)).trace
      map_add' := fun X Y => by ext i j; simp [add_mul]
      map_smul' := fun c X => by ext i j; simp }
  have hT : ∀ x, T (φ' x) = φ x := by
    intro x
    ext i j
    change (φ' x * θ (Matrix.single j i 1)).trace = _
    rw [hθ, ← map_mul, ← htr, map_mul, hs', Matrix.trace_mul_single]
    simp
  have hTinj : Function.Injective T :=
    OrzechProperty.injective_of_surjective_endomorphism T fun X =>
      ⟨φ' (s X), by rw [hT, hs']⟩
  have hfac : ∀ x, θ (φ x) = φ' x := fun x => hTinj (by rw [hθ, hT, hT, hs'])
  have hmul : ∀ X Y, θ X * θ Y = θ (X * Y) := by
    intro X Y
    rw [hθ, hθ, ← map_mul, ← hfac, map_mul, hs', hs']
  let o : Fin a := ⟨0, ha⟩
  have h1 : ∑ y, θ (Matrix.single o o 1) y y = 1 := by
    have := htr (s (Matrix.single o o 1))
    rw [hs', Matrix.trace_single_eq_same] at this
    exact this.symm
  obtain ⟨y, -, hy⟩ := IsLocalRing.exists_of_isUnit_sum (show IsUnit (∑ y, θ (Matrix.single o o 1) y y) by
    rw [h1]; exact isUnit_one)
  let U : Matrix (Fin a) (Fin a) O := Matrix.of fun x i => θ (Matrix.single i o 1) x y
  let V : Matrix (Fin a) (Fin a) O := Matrix.of fun j x => θ (Matrix.single o j 1) y x
  have hVU : V * U = θ (Matrix.single o o 1) y y • (1 : Matrix (Fin a) (Fin a) O) := by
    ext j i
    have : (V * U) j i = (θ (Matrix.single o j 1) * θ (Matrix.single i o 1)) y y := by
      simp [Matrix.mul_apply, U, V]
    rw [this, hmul]
    by_cases hij : j = i
    · subst hij
      simp
    · rw [Matrix.single_mul_single_of_ne _ _ _ _ hij]
      simp [hij]
  have hU : IsUnit U := by
    rw [Matrix.isUnit_iff_isUnit_det]
    have := congrArg Matrix.det hVU
    rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one] at this
    exact isUnit_of_mul_isUnit_right (this ▸ hy.pow _)
  refine ⟨hU.unit, fun z => ?_⟩
  rw [IsUnit.unit_spec, ← hfac]
  ext x i
  have h2 : (θ (φ z) * U) x i = (θ (φ z) * θ (Matrix.single i o 1)) x y := by
    simp [Matrix.mul_apply, U]
  have h3 : φ z * Matrix.single i o (1 : O) = ∑ k, φ z k i • Matrix.single k o (1 : O) := by
    ext p q
    by_cases hq : q = o
    · subst hq
      simp [Matrix.sum_apply, Matrix.single_apply]
    · rw [Matrix.mul_single_apply_of_ne _ _ _ _ _ hq]
      simp [Matrix.sum_apply, Matrix.single_apply, Ne.symm hq]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h2, hmul, h3, map_sum, Matrix.sum_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, Matrix.smul_apply, smul_eq_mul, mul_comm]
  rfl

theorem span_eq_top_of_residue {O ι : Type} [CommRing O] [IsLocalRing O] {a : ℕ}
    (M : ι → Matrix (Fin a) (Fin a) O)
    (h : Submodule.span (IsLocalRing.ResidueField O)
      (Set.range fun g => (M g).map (IsLocalRing.residue O)) = ⊤) :
    Submodule.span O (Set.range M) = ⊤ := by
  first
  | exact @_root_.GlobalTheory.ResidueSpanLift.span_eq_top_of_span_residue_eq_top
  | exact _root_.GlobalTheory.ResidueSpanLift.span_eq_top_of_span_residue_eq_top
  | (apply _root_.GlobalTheory.ResidueSpanLift.span_eq_top_of_span_residue_eq_top <;> assumption)
  | (intros; apply _root_.GlobalTheory.ResidueSpanLift.span_eq_top_of_span_residue_eq_top <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ResidueSpanLift.span_eq_top_of_span_residue_eq_top <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ResidueSpanLift.span_eq_top_of_span_residue_eq_top ..)

theorem exists_conj_of_trace_eq_local {O : Type} [CommRing O] [IsLocalRing O] {Γ : Type} [Group Γ]
    {a : ℕ} (ρ ρ' : Γ →* GL (Fin a) O)
    (h : Formalism.MainNotions.N.AbsIrrSub (Formalism.MainNotions.N.mapRep (IsLocalRing.residue O) ρ) ⊤)
    (htr : ∀ g, ((ρ g : GL (Fin a) O) : Matrix (Fin a) (Fin a) O).trace =
      ((ρ' g : GL (Fin a) O) : Matrix (Fin a) (Fin a) O).trace) :
    ∃ U : GL (Fin a) O, ∀ g, ρ' g * U = U * ρ g := by
  classical
  have hspan : Submodule.span O
      (Set.range fun g => ((ρ g : GL (Fin a) O) : Matrix (Fin a) (Fin a) O)) = ⊤ :=
    by
    refine span_eq_top_of_residue _ ?_
    have h0 := GlobalTheory.BurnsideField.span_mat_eq_top_of_absIrrSub _ h
    have h1 : GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat (Formalism.MainNotions.N.mapRep (IsLocalRing.residue O) ρ) = fun g =>
        ((ρ g : GL (Fin a) O) : Matrix (Fin a) (Fin a) O).map (IsLocalRing.residue O) := by
      funext g
      rfl
    rwa [h1] at h0
  let φ : MonoidAlgebra O Γ →ₐ[O] Matrix (Fin a) (Fin a) O :=
    MonoidAlgebra.lift O (Matrix (Fin a) (Fin a) O) Γ ((Units.coeHom (Matrix (Fin a) (Fin a) O)).comp ρ)
  let φ' : MonoidAlgebra O Γ →ₐ[O] Matrix (Fin a) (Fin a) O :=
    MonoidAlgebra.lift O (Matrix (Fin a) (Fin a) O) Γ ((Units.coeHom (Matrix (Fin a) (Fin a) O)).comp ρ')
  have hφ : ∀ g c, φ (MonoidAlgebra.single g c) = c • (ρ g : Matrix (Fin a) (Fin a) O) :=
    fun g c => by simp [φ]
  have hφ' : ∀ g c, φ' (MonoidAlgebra.single g c) = c • (ρ' g : Matrix (Fin a) (Fin a) O) :=
    fun g c => by simp [φ']
  have hsurj : Function.Surjective φ := by
    have : LinearMap.range φ.toLinearMap = ⊤ := by
      rw [eq_top_iff, ← hspan, Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      exact ⟨MonoidAlgebra.single g 1, by simpa using hφ g 1⟩
    exact LinearMap.range_eq_top.1 this
  have htr' : ∀ x, (φ x).trace = (φ' x).trace := by
    intro x
    induction x using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), Matrix.trace_add, Matrix.trace_add, hx, hy]
    | single g c => rw [hφ, hφ', Matrix.trace_smul, Matrix.trace_smul, htr]
  obtain ⟨U, hU⟩ := exists_conj_of_surjective φ φ' hsurj htr'
  refine ⟨U, fun g => Units.ext ?_⟩
  have := hU (MonoidAlgebra.single g 1)
  rwa [hφ, hφ', one_smul, one_smul] at this

theorem exists_conj_of_trace_eq :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Γ : Type) [Group Γ] (a : ℕ) (ρ ρ' : Γ →* GL (Fin a) O), Formalism.MainNotions.N.AbsIrrSub (Formalism.MainNotions.N.mapRep (IsLocalRing.residue O) ρ) ⊤ → (∀ g, ((ρ g : GL (Fin a) O) : Matrix (Fin a) (Fin a) O).trace = ((ρ' g : GL (Fin a) O) : Matrix (Fin a) (Fin a) O).trace) → ∃ U : GL (Fin a) O, ∀ g, ρ' g * U = U * ρ g :=
  fun _ _ _ _ _ _ _ ρ ρ' h htr => exists_conj_of_trace_eq_local ρ ρ' h htr

end GlobalTheory.TraceConjugacy
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsConjOfTraceEqResiduallyAbsIrreducibleDVRStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conj_of_trace_eq_residually_absIrreducible_DVR : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Γ : Type) [Group Γ] (a : ℕ) (ρ ρ' : Γ →* GL (Fin a) O), Formalism.MainNotions.N.AbsIrrSub (Formalism.MainNotions.N.mapRep (IsLocalRing.residue O) ρ) ⊤ → (∀ g, ((ρ g : GL (Fin a) O) : Matrix (Fin a) (Fin a) O).trace = ((ρ' g : GL (Fin a) O) : Matrix (Fin a) (Fin a) O).trace) → ∃ U : GL (Fin a) O, ∀ g, ρ' g * U = U * ρ g := by
  first | exact @GlobalTheory.TraceConjugacy.exists_conj_of_trace_eq | exact GlobalTheory.TraceConjugacy.exists_conj_of_trace_eq | (intros; apply GlobalTheory.TraceConjugacy.exists_conj_of_trace_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarValueLeMeanSquareGenusOne
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarValueLeMeanSquareGenusOne
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
open MeasureTheory

noncomputable section

namespace GlobalTheory.GenusOneSup

theorem area_le (Λ : AddSubgroup ℂ) {w₁ w₂ : ℂ} (h₁ : w₁ ∈ Λ) (h₂ : w₂ ∈ Λ)
    (h : 0 < |((starRingEnd ℂ) w₁ * w₂).im|) : area Λ ≤ |((starRingEnd ℂ) w₁ * w₂).im| :=
  csInf_le ⟨0, fun _ ha => ha.1.le⟩ ⟨h, w₁, h₁, w₂, h₂, rfl⟩

theorem area_closure {w₁ w₂ : ℂ} (h : 0 < |((starRingEnd ℂ) w₁ * w₂).im|) :
    area (AddSubgroup.closure {w₁, w₂}) = |((starRingEnd ℂ) w₁ * w₂).im| := by
  have h₁ : w₁ ∈ AddSubgroup.closure ({w₁, w₂} : Set ℂ) := AddSubgroup.subset_closure (by simp)
  have h₂ : w₂ ∈ AddSubgroup.closure ({w₁, w₂} : Set ℂ) := AddSubgroup.subset_closure (by simp)
  refine le_antisymm (area_le _ h₁ h₂ h) (le_csInf ⟨_, h, w₁, h₁, w₂, h₂, rfl⟩ ?_)
  rintro a ⟨ha, x, hx, y, hy, rfl⟩
  obtain ⟨m, n, rfl⟩ := AddSubgroup.mem_closure_pair.1 hx
  obtain ⟨m', n', rfl⟩ := AddSubgroup.mem_closure_pair.1 hy
  have e : ((starRingEnd ℂ) (m • w₁ + n • w₂) * (m' • w₁ + n' • w₂)).im =
      ((m * n' - n * m' : ℤ) : ℝ) * ((starRingEnd ℂ) w₁ * w₂).im := by
    simp [Complex.mul_im]
    ring
  rw [e, abs_mul] at ha ⊢
  have hk : (m * n' - n * m' : ℤ) ≠ 0 := by
    intro h0
    rw [h0] at ha
    simp at ha
  have : (1 : ℝ) ≤ |((m * n' - n * m' : ℤ) : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs hk
  nlinarith

theorem exists_domain {w₁ w₂ : ℂ} (hli : LinearIndependent ℝ ![w₁, w₂]) :
    ∃ F : Set ℂ, IsAddFundamentalDomain (AddSubgroup.closure ({w₁, w₂} : Set ℂ)) F volume ∧
      Bornology.IsBounded F ∧ 0 < |((starRingEnd ℂ) w₁ * w₂).im| ∧
      volume F = ENNReal.ofReal |((starRingEnd ℂ) w₁ * w₂).im| := by
  let b : Module.Basis (Fin 2) ℝ ℂ := basisOfLinearIndependentOfCardEqFinrank hli (by simp)
  have hb : ⇑b = ![w₁, w₂] := coe_basisOfLinearIndependentOfCardEqFinrank _ _
  have hdet : Complex.basisOneI.det b = ((starRingEnd ℂ) w₁ * w₂).im := by
    rw [Module.Basis.det_apply, Matrix.det_fin_two]
    simp [Module.Basis.toMatrix_apply, hb, Complex.mul_im]
    ring
  have hspan : (Submodule.span ℤ (Set.range b)).toAddSubgroup = AddSubgroup.closure ({w₁, w₂} : Set ℂ) := by
    rw [Submodule.span_int_eq_addSubgroupClosure, hb]
    congr 1
    simp [Set.pair_comm]
  refine ⟨ZSpan.fundamentalDomain b, ?_, ZSpan.fundamentalDomain_isBounded b, ?_, ?_⟩
  · rw [← hspan]; exact ZSpan.isAddFundamentalDomain' b volume
  · rw [← hdet]; exact abs_pos.2 (Complex.basisOneI.isUnit_det b).ne_zero
  · rw [ZSpan.measure_fundamentalDomain b volume Complex.basisOneI, hdet,
      measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped _ _), ← Complex.toBasis_orthonormalBasisOneI]
    have := Complex.orthonormalBasisOneI.volume_parallelepiped
    simp only [OrthonormalBasis.coe_toBasis, this, mul_one]

def lineIso : EuclideanSpace ℂ Unit ≃ₗᵢ[ℝ] ℂ where
  toFun x := x ()
  invFun z := WithLp.toLp 2 (fun _ => z)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl
  norm_map' x := by
    show ‖x ()‖ = ‖x‖
    simp [EuclideanSpace.norm_eq]

theorem sup_le_mean (Λ : AddSubgroup ℂ) (a v : ℝ) (F : Set ℂ) (g : ℂ → ℂ) (ha : 0 < a) (hv : 1 ≤ v)
    (hmin : ∀ x ∈ Λ, x ≠ 0 → a / v ≤ ‖x‖ ^ 2) (hF : IsAddFundamentalDomain Λ F volume)
    (hvol : volume F = ENNReal.ofReal a) (hg : Differentiable ℂ g)
    (hper : ∀ x ∈ Λ, ∀ z, ‖g (z + x)‖ ^ 2 * Real.exp (-Real.pi * ‖z + x‖ ^ 2 / a) =
      ‖g z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2 / a))
    (hint : IntegrableOn (fun z => ‖g z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2 / a)) F) (z : ℂ) :
    ‖g z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2 / a) ≤
      3 * (2 * v + 1) * (a⁻¹ * ∫ z in F, ‖g z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2 / a)) := by
  set s : ℝ := Real.sqrt a with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 ha
  have hs2 : s ^ 2 = a := Real.sq_sqrt ha.le
  let φ : EuclideanSpace ℂ Unit ≃L[ℝ] ℂ :=
    lineIso.toContinuousLinearEquiv.trans (ContinuousLinearEquiv.smulLeft (Units.mk0 s hs0.ne'))
  have hφ : ∀ x, φ x = s • lineIso x := fun _ => rfl
  have hn : ∀ x, ‖φ x‖ ^ 2 = a * ‖x‖ ^ 2 := fun x => by
    rw [hφ, norm_smul, lineIso.norm_map, mul_pow, Real.norm_eq_abs, sq_abs, hs2]
  have hw : ∀ x, -Real.pi * ‖x‖ ^ 2 = -Real.pi * ‖φ x‖ ^ 2 / a := fun x => by
    rw [hn]; field_simp
  have hmp : MeasurePreserving φ volume (ENNReal.ofReal a⁻¹ • (volume : Measure ℂ)) := by
    have h1 : MeasurePreserving (fun z : ℂ => s • z) volume (ENNReal.ofReal a⁻¹ • (volume : Measure ℂ)) := by
      refine ⟨measurable_const_smul s, ?_⟩
      rw [Measure.map_addHaar_smul volume hs0.ne', Complex.finrank_real_complex, hs2,
        abs_of_pos (inv_pos.2 ha)]
    exact h1.comp lineIso.measurePreserving
  have hemb : MeasurableEmbedding φ := φ.toHomeomorph.measurableEmbedding
  let A : AddSubgroup (EuclideanSpace ℂ Unit) := Λ.comap (φ : EuclideanSpace ℂ Unit →+ ℂ)
  have hA : ∀ x, x ∈ A ↔ φ x ∈ Λ := fun _ => Iff.rfl
  have hF' : IsAddFundamentalDomain A (φ ⁻¹' F) volume := by
    refine hF.preimage_of_equiv (f := φ) (e := fun y : Λ => (⟨φ.symm y, (hA _).2 (by simp)⟩ : A))
      ⟨hmp.measurable.aemeasurable, ?_⟩ ⟨?_, ?_⟩ ?_
    · rw [hmp.map_eq]; exact Measure.smul_absolutelyContinuous
    · intro x y h
      exact Subtype.ext (φ.symm.injective (congrArg Subtype.val h))
    · intro x
      exact ⟨⟨φ x, x.2⟩, Subtype.ext (by simp)⟩
    · intro y x
      show φ (φ.symm y + x) = (y : ℂ) + φ x
      simp
  have hvol' : volume (φ ⁻¹' F) = 1 := by
    rw [hmp.measure_preimage_emb hemb, Measure.smul_apply, hvol, smul_eq_mul,
      ← ENNReal.ofReal_mul (inv_pos.2 ha).le, inv_mul_cancel₀ ha.ne', ENNReal.ofReal_one]
  have hd : Differentiable ℂ (fun x : EuclideanSpace ℂ Unit => g (φ x)) := by
    have : Differentiable ℂ (fun x : EuclideanSpace ℂ Unit => (s : ℂ) * x ()) := by fun_prop
    exact hg.comp this
  have key := GlobalTheory.ThetaSupBall.sup_le_mean_square Unit A v (φ ⁻¹' F) (fun x => g (φ x)) hv ?_ hF' hvol' hd ?_ ?_ (φ.symm z)
  · simp only [hw, Fintype.card_unit, Nat.cast_one, mul_one, pow_one, ContinuousLinearEquiv.apply_symm_apply] at key
    rw [hmp.setIntegral_preimage_emb hemb (fun z => ‖g z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2 / a)),
      Measure.restrict_smul, integral_smul_measure, ENNReal.toReal_ofReal (inv_pos.2 ha).le, smul_eq_mul] at key
    exact key
  · intro x hx hx0
    have := hmin (φ x) hx (by simpa using hx0)
    rw [hn, div_eq_mul_one_div] at this
    exact le_of_mul_le_mul_left this ha
  · intro x hx y
    simp only [hw, map_add (f := _)]
    exact hper _ hx _
  · simp only [hw]
    refine (hmp.integrableOn_comp_preimage hemb
      (f := fun z => ‖g z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2 / a))).2 ?_
    unfold IntegrableOn
    rw [Measure.restrict_smul]
    exact Integrable.smul_measure hint ENNReal.ofReal_ne_top

theorem thetaTranslation_weighted_normSq (Λ : AddSubgroup ℂ) (t z : ℂ) (g : ℂ → ℂ) :
    ‖U1 Λ t g z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2 / area Λ) =
      ‖g (z + t)‖ ^ 2 * Real.exp (-Real.pi * ‖z + t‖ ^ 2 / area Λ) := by
  unfold U1
  rw [norm_mul, mul_pow, Complex.norm_exp, mul_assoc, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 2
  have e : (2 * (area Λ : ℂ)) = ((2 * area Λ : ℝ) : ℂ) := by push_cast; ring
  rw [e, Complex.sub_re, Complex.div_ofReal_re, Complex.div_ofReal_re, ← Complex.normSq_eq_norm_sq,
    ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.normSq_apply]
  simp
  ring

theorem lattice_sup (Λ : AddSubgroup ℂ)
    (hΛ : ∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂})
    (v : ℝ) (hv : 1 ≤ v) (hmin : ∀ x ∈ Λ, x ≠ 0 → area Λ / v ≤ ‖x‖ ^ 2) (t : ℂ) :
    ‖U1 Λ t (sgStar Λ) 0‖ ^ 2 ≤ 3 * (2 * v + 1) * nrm1Sq Λ (sgStar Λ) := by
  obtain ⟨⟨hd, -, -, hU⟩, -⟩ := GlobalTheory.OddTheta.sgStar_laws Λ hΛ
  obtain ⟨w₁, w₂, hli, rfl⟩ := hΛ
  obtain ⟨F, hF, hb, hpos, hvol⟩ := exists_domain hli
  have har := area_closure hpos
  rw [← har] at hpos hvol
  set Λ : AddSubgroup ℂ := AddSubgroup.closure {w₁, w₂} with hΛ
  have hper : ∀ x ∈ Λ, ∀ z, ‖sgStar Λ (z + x)‖ ^ 2 * Real.exp (-Real.pi * ‖z + x‖ ^ 2 / area Λ) =
      ‖sgStar Λ z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2 / area Λ) := by
    intro x hx z
    rw [← thetaTranslation_weighted_normSq, hU x hx, norm_mul]
    split_ifs <;> simp
  have hc : Continuous fun z => ‖sgStar Λ z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2 / area Λ) := by
    have := hd.continuous
    fun_prop
  have hint : IntegrableOn (fun z => ‖sgStar Λ z‖ ^ 2 * Real.exp (-Real.pi * ‖z‖ ^ 2 / area Λ)) F :=
    (hc.continuousOn.integrableOn_compact hb.isCompact_closure).mono_set subset_closure
  have key := sup_le_mean Λ (area Λ) v F (sgStar Λ) hpos hv hmin hF hvol hd hper hint t
  have h0 := thetaTranslation_weighted_normSq Λ t 0 (sgStar Λ)
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_div,
    Real.exp_zero, mul_one, zero_add] at h0
  rw [h0]
  refine key.trans (le_of_eq ?_)
  congr 1
  have hF' := Classical.epsilon_spec (p := fun Fd : Set ℂ => IsAddFundamentalDomain Λ Fd volume) ⟨F, hF⟩
  have : Countable Λ := by
    have : (Λ : Set ℂ) ⊆ Set.range (fun p : ℤ × ℤ => p.1 • w₁ + p.2 • w₂) := by
      intro x hx
      obtain ⟨m, n, rfl⟩ := AddSubgroup.mem_closure_pair.1 hx
      exact ⟨(m, n), rfl⟩
    exact ((Set.countable_range _).mono this).to_subtype
  have : VAddInvariantMeasure Λ ℂ volume := ⟨fun γ s _ => measure_preimage_add volume (γ : ℂ) s⟩
  unfold nrm1Sq
  simp only
  rw [setAverage_eq, measureReal_def, hF'.measure_eq hF, hF'.setIntegral_eq hF, hvol,
    ENNReal.toReal_ofReal hpos.le, smul_eq_mul]
  intro γ z
  have := hper γ γ.2 z
  rw [add_comm] at this
  exact this

theorem value_le_mean_square : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ t, ‖U1 (lamOf D cc δ) t (sgStar (lamOf D cc δ)) 0‖ ^ 2 ≤ 3 * (2 * D.host.rdE + 1) * nrm1Sq (lamOf D cc δ) (sgStar (lamOf D cc δ)) := by
  intro D hD cc δ hc t
  obtain ⟨hΛ, -, -, -, hst⟩ := GlobalTheory.CurveLattice.lattice_of_curve D hD cc δ hc
  obtain ⟨-, hlog, hrd, -⟩ := GlobalTheory.NormSum.letters_and_sizes D hD
  refine lattice_sup _ hΛ _ hrd ?_ t
  intro x hx hx0
  have hd : (0 : ℝ) < D.host.d := by exact_mod_cast D.host.hyp.2.1.pos
  have hsq := D.host.sqd_sq
  let β : D.host.K := ⟨D.host.sqd, IntermediateField.mem_adjoin_simple_self ℚ _⟩
  have hβ : β ^ 2 = -(D.host.d : D.host.K) := Subtype.ext (by simpa [β] using hsq)
  have hi : IsIntegral ℤ β := by
    refine IsIntegral.of_pow (n := 2) two_pos ?_
    rw [hβ]
    exact (isIntegral_natCast _).neg
  have hm := hst ⟨β, hi⟩ x hx
  set c : ℂ := D.host.φ₀ (D.host.sqd) with hcdef
  have hm' : c * x ∈ lamOf D cc δ := hm
  have hc2 : c ^ 2 = -(D.host.d : ℂ) := by
    rw [hcdef, ← map_pow, hsq]; simp
  have hre : c.re * c.re - c.im * c.im = -(D.host.d : ℝ) := by
    have := congrArg Complex.re hc2
    simpa [pow_two] using this
  have him : c.re * c.im = 0 := by
    have := congrArg Complex.im hc2
    simp [pow_two] at this
    linarith
  have hre0 : c.re = 0 := by
    rcases mul_eq_zero.1 him with h | h
    · exact h
    · rw [h] at hre; nlinarith [mul_self_nonneg c.re]
  have him2 : c.im ^ 2 = D.host.d := by rw [hre0] at hre; linarith
  have e : |((starRingEnd ℂ) x * (c * x)).im| = |c.im| * ‖x‖ ^ 2 := by
    have : ((starRingEnd ℂ) x * (c * x)).im = c.im * ‖x‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp
      ring
    rw [this, abs_mul, abs_of_nonneg (sq_nonneg ‖x‖)]
  have hx2 : 0 < ‖x‖ ^ 2 := by positivity
  have hci : 0 < |c.im| := abs_pos.2 (by intro h; rw [h] at him2; linarith)
  have hle := area_le _ hx hm' (by rw [e]; positivity)
  have hrd0 : 0 < D.host.rdE := by linarith
  have hdle : (D.host.d : ℝ) ≤ D.host.rdE ^ 2 := by
    rw [← Real.log_le_log_iff hd (by positivity), Real.log_pow]
    exact_mod_cast hlog
  have hcle : |c.im| ≤ D.host.rdE := abs_le_of_sq_le_sq' (by rw [him2]; exact hdle) hrd0.le |> abs_le.2
  rw [div_le_iff₀ hrd0]
  rw [e] at hle
  nlinarith

end GlobalTheory.GenusOneSup
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarValueLeMeanSquareGenusOneStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sigmaStar_value_le_meanSquare_genusOne : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ t, ‖U1 (lamOf D cc δ) t (sgStar (lamOf D cc δ)) 0‖ ^ 2 ≤ 3 * (2 * D.host.rdE + 1) * nrm1Sq (lamOf D cc δ) (sgStar (lamOf D cc δ)) := by
  first | exact @GlobalTheory.GenusOneSup.value_le_mean_square | exact GlobalTheory.GenusOneSup.value_le_mean_square | (intros; apply GlobalTheory.GenusOneSup.value_le_mean_square <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSubmodule
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSubmodule
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.GKSubmodule

noncomputable def resAct {p q : ℕ} (M : GKMod p q) (N : Submodule ℂ M.V)
    (h : ∀ Z, ∀ x ∈ N, M.act Z x ∈ N) : Mat p q →ₗ[ℂ] Module.End ℂ N where
  toFun Z := (M.act Z).restrict (h Z)
  map_add' X Y := by
    ext x
    simp [LinearMap.restrict_apply]
  map_smul' c X := by
    ext x
    simp [LinearMap.restrict_apply]

theorem resAct_coe {p q : ℕ} (M : GKMod p q) (N : Submodule ℂ M.V)
    (h : ∀ Z, ∀ x ∈ N, M.act Z x ∈ N) (Z : Mat p q) (x : N) :
    ((resAct M N h Z x : N) : M.V) = M.act Z x := rfl

theorem exists_submodule : ∀ (p q : ℕ) (M : GKMod p q) (N : Submodule ℂ M.V), (∀ Z, ∀ x ∈ N, M.act Z x ∈ N) → ∃ (M' : GKMod p q) (i : M'.V →ₗ[ℂ] M.V), Function.Injective i ∧ LinearMap.range i = N ∧ ∀ Z x, i (M'.act Z x) = M.act Z (i x) := by
  intro p q M N h
  have hlie : IsLieAct (resAct M N h) := by
    intro X Y
    ext x
    have := congrArg (fun f : Module.End ℂ M.V => f x) (M.lie X Y)
    simpa [resAct_coe] using this
  have hk : ∀ v : N, ∃ W : Submodule ℂ N, FiniteDimensional ℂ W ∧ v ∈ W ∧
      KStable (resAct M N h) W := by
    intro v
    obtain ⟨W, hW, hv, hs⟩ := M.kfin v
    refine ⟨W.comap N.subtype, ?_, hv, ?_⟩
    · exact Module.Finite.of_injective
        (N.subtype.restrict (p := W.comap N.subtype) (q := W) (fun x hx => hx))
        (fun a b hab => Subtype.ext (Subtype.ext (congrArg (fun z : W => (z : M.V)) hab)))
    · intro X hX w hw
      exact hs X hX w hw
  have hw : ∀ v : N, v ∈ ⨆ μ : Ix p q → ℚ, wtSub (resAct M N h) μ := by
    intro v
    have h1 := GlobalTheory.T.mem_iSup_inf_weightSubmodule_of_diagonal_stable p q M.V M.act N (fun a => h _) v v.2 (M.wts v)
    have h2 : (⨆ μ : Ix p q → ℚ, N ⊓ wtSub M.act μ) ≤
        (⨆ μ : Ix p q → ℚ, wtSub (resAct M N h) μ).map N.subtype := by
      refine iSup_le fun μ x hx => ?_
      refine ⟨⟨x, hx.1⟩, ?_, rfl⟩
      refine Submodule.mem_iSup_of_mem μ ?_
      have hx2 := hx.2
      simp only [wtSub, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker] at hx2 ⊢
      intro a
      apply Subtype.ext
      simpa [resAct_coe] using hx2 a
    obtain ⟨y, hy, hyv⟩ := h2 h1
    have : y = v := Subtype.ext hyv
    exact this ▸ hy
  exact ⟨{ V := N, act := resAct M N h, lie := hlie, kfin := hk, wts := hw }, N.subtype,
    N.injective_subtype, N.range_subtype, fun _ _ => rfl⟩

end GlobalTheory.GKSubmodule
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSubmoduleStatement
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_gkMod_injective_range_eq_of_act_stable : ∀ (p q : ℕ) (M : GKMod p q) (N : Submodule ℂ M.V), (∀ Z, ∀ x ∈ N, M.act Z x ∈ N) → ∃ (M' : GKMod p q) (i : M'.V →ₗ[ℂ] M.V), Function.Injective i ∧ LinearMap.range i = N ∧ ∀ Z x, i (M'.act Z x) = M.act Z (i x) := by
  first | exact @GlobalTheory.GKSubmodule.exists_submodule | exact GlobalTheory.GKSubmodule.exists_submodule | (intros; apply GlobalTheory.GKSubmodule.exists_submodule <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IrreducibleOfWeightLine
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IrreducibleOfWeightLine
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory.FockIrr

theorem act_diag_of_mem_wtSub {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {act : Mat p q →ₗ[ℂ] Module.End ℂ V} {μ : Ix p q → ℚ} {v : V} (h : v ∈ wtSub act μ)
    (a : Ix p q) : act (Eab a a) v = ((μ a : ℚ) : ℂ) • v := by
  have h1 := (Submodule.mem_iInf _).1 h a
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at h1
  exact sub_eq_zero.1 h1

theorem irreducible_of_weight_line : ∀ (p q : ℕ) (M : GKMod p q) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (E : M.V →ₗ[ℂ] H), Function.Injective E → (∀ Z x y, inner ℂ (E (M.act Z x)) (E y) = inner ℂ (E x) (E (M.act (adjZ Z) y))) → ∀ (S : Ix p q → Ix p q → Prop), Equivalence S → ∀ (μ : Ix p q → ℚ) (v : M.V) (U : Submodule ℂ M.V), v ∈ wtSub M.act μ → (∀ U' : Submodule ℂ M.V, v ∈ U' → (∀ a b, S a b → ∀ x ∈ U', M.act (Eab a b) x ∈ U') → U ≤ U') → (∀ x ∈ U, x ∈ wtSub M.act μ → ∃ c : ℂ, x = c • v) → ∀ N : Submodule ℂ M.V, N ≤ U → (∀ a b, S a b → ∀ x ∈ N, M.act (Eab a b) x ∈ N) → N = ⊥ ∨ N = U := by
  intro p q M H _ _ E hE hadj S hS μ v U hv hU hline N hNU hN
  by_cases hvN : v ∈ N
  · exact Or.inr (le_antisymm hNU (hU N hvN hN))
  left
  have horth : ∀ x ∈ N, inner ℂ (E x) (E v) = 0 := by
    intro x hx
    have hx' := GlobalTheory.T.mem_iSup_inf_weightSubmodule_of_diagonal_stable p q M.V M.act N (fun a => hN a a (hS.refl a)) x hx (M.wts x)
    clear hx
    induction hx' using Submodule.iSup_induction' with
    | mem ν y hy =>
      obtain ⟨hyN, hyν⟩ := hy
      by_cases hν : ν = μ
      · subst hν
        obtain ⟨c, hc⟩ := hline y (hNU hyN) hyν
        by_cases hc0 : c = 0
        · simp [hc, hc0]
        · exfalso
          apply hvN
          have : v = c⁻¹ • y := by rw [hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
          rw [this]
          exact N.smul_mem _ hyN
      · obtain ⟨a, ha⟩ := Function.ne_iff.1 hν
        have h1 := hadj (Eab a a) y v
        rw [GlobalTheory.FockTensor.adjZ_Eab, GlobalTheory.FockTensor.sgnIx_mul_self, one_smul,
          act_diag_of_mem_wtSub hyν, act_diag_of_mem_wtSub hv, map_smul, map_smul,
          inner_smul_left, inner_smul_right, map_ratCast] at h1
        have hne : ((ν a : ℚ) : ℂ) - ((μ a : ℚ) : ℂ) ≠ 0 := by
          rw [sub_ne_zero]; exact_mod_cast ha
        have h2 : (((ν a : ℚ) : ℂ) - ((μ a : ℚ) : ℂ)) * inner ℂ (E y) (E v) = 0 := by
          rw [sub_mul, h1, sub_self]
        exact (mul_eq_zero.1 h2).resolve_left hne
    | zero => simp
    | add y z _ _ hy hz => rw [map_add (f := _), inner_add_left, hy, hz, add_zero]
  let U' : Submodule ℂ M.V :=
    { carrier := {y | ∀ x ∈ N, inner ℂ (E x) (E y) = 0}
      add_mem' := fun {y z} hy hz x hx => by
        rw [map_add (f := _), inner_add_right, hy x hx, hz x hx, add_zero]
      zero_mem' := fun x _ => by simp
      smul_mem' := fun c y hy x hx => by
        rw [map_smul, inner_smul_right, hy x hx, mul_zero] }
  have hUU' : U ≤ U' := by
    refine hU U' horth ?_
    intro a b hab y hy x hx
    have h1 := hadj (adjZ (Eab a b)) x y
    rw [GlobalTheory.FockTensor.adjZ_adjZ] at h1
    rw [← h1]
    apply hy
    rw [GlobalTheory.FockTensor.adjZ_Eab, map_smul, LinearMap.smul_apply]
    exact N.smul_mem _ (hN b a (hS.symm hab) x hx)
  rw [eq_bot_iff]
  intro x hx
  have h0 : inner ℂ (E x) (E x) = 0 := hUU' (hNU hx) x hx
  rw [inner_self_eq_zero] at h0
  exact (Submodule.mem_bot ℂ).2 (hE (by rw [h0, map_zero]))

end GlobalTheory.FockIrr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IrreducibleOfWeightLineStatement
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_bot_or_eq_of_weight_line_generates : ∀ (p q : ℕ) (M : GKMod p q) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (E : M.V →ₗ[ℂ] H), Function.Injective E → (∀ Z x y, inner ℂ (E (M.act Z x)) (E y) = inner ℂ (E x) (E (M.act (adjZ Z) y))) → ∀ (S : Ix p q → Ix p q → Prop), Equivalence S → ∀ (μ : Ix p q → ℚ) (v : M.V) (U : Submodule ℂ M.V), v ∈ wtSub M.act μ → (∀ U' : Submodule ℂ M.V, v ∈ U' → (∀ a b, S a b → ∀ x ∈ U', M.act (Eab a b) x ∈ U') → U ≤ U') → (∀ x ∈ U, x ∈ wtSub M.act μ → ∃ c : ℂ, x = c • v) → ∀ N : Submodule ℂ M.V, N ≤ U → (∀ a b, S a b → ∀ x ∈ N, M.act (Eab a b) x ∈ N) → N = ⊥ ∨ N = U := by
  first | exact @GlobalTheory.FockIrr.irreducible_of_weight_line | exact GlobalTheory.FockIrr.irreducible_of_weight_line | (intros; apply GlobalTheory.FockIrr.irreducible_of_weight_line <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExtremalRowWeight
open GlobalTheory.DualWeyl MvPolynomial NumberField
open Formalism.GradedWeylDivisibility (rowAct rowW rowNu)
open Formalism.REAL (fockF)
open scoped Matrix ComplexConjugate InnerProductSpace

noncomputable section

namespace GlobalTheory.DualWeylFock

variable {N : ℕ} {la : Fin N → ℕ}

theorem fock_smul_left {σ : Type} (c : ℂ) (f g : MvPolynomial σ ℂ) : fockF (c • f) g = c * fockF f g := by
  rw [Formalism.REAL.fischerInner_eq_sum_of_subset _ _ f.support support_smul, fockF, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_smul, smul_eq_mul]
  ring

def fockLeft {σ : Type} (g : MvPolynomial σ ℂ) : MvPolynomial σ ℂ →ₗ[ℂ] ℂ where
  toFun f := fockF f g
  map_add' f f' := Formalism.REAL.fischerInner_add_left f f' g
  map_smul' c f := fock_smul_left c f g

theorem extremal_rowWeight (hla : Antitone la) : IsWeightedHomogeneous (rowW N N) (extremal la ℂ) la := by
  have hnu : rowNu (r := N) la = la := by
    funext b
    simp [rowNu]
  have := Formalism.GradedWeylDivisibility.hwRowWeight ℂ N N le_rfl la hla
  rwa [hnu] at this

theorem evalAt_one_of_ne {μ : Fin N → ℕ} (hμ : μ ≠ la) {q : Pol N ℂ} (hq : q ∈ nabla la ℂ)
    (hw : IsWeightedHomogeneous (rowW N N) q μ) : evalAt 1 q = 0 := by
  obtain ⟨a, ha⟩ := Function.ne_iff.mp hμ
  let t : Fin N → ℂ := fun b => if b = a then 2 else 1
  have hprod : ∀ e : Fin N → ℕ, ∏ b, t b ^ e b = 2 ^ e a := by
    intro e
    rw [Finset.prod_eq_single a]
    · simp [t]
    · intro b _ hb; simp [t, hb]
    · simp
  have h1 := evalAt_rowAct 1 (Matrix.diagonal t) q
  have h2 := evalAt_colAct 1 (Matrix.diagonal t) q
  rw [Formalism.GradedWeylDivisibility.rowActDiagWeight ℂ N N t μ _ hw, hprod, Matrix.mul_one, map_smul, smul_eq_mul] at h1
  rw [colAct_of_mem hq _ (Matrix.blockTriangular_diagonal t), Matrix.one_mul, map_smul, smul_eq_mul] at h2
  simp only [diagChar, Matrix.diagonal_apply_eq] at h2
  rw [hprod] at h2
  have hne : (2 : ℂ) ^ μ a - 2 ^ la a ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    have h' : (2 : ℕ) ^ μ a = 2 ^ la a := by exact_mod_cast h
    exact ha (Nat.pow_right_injective le_rfl h')
  have : ((2 : ℂ) ^ μ a - 2 ^ la a) * evalAt 1 q = 0 := by rw [sub_mul, h1, h2, sub_self]
  exact (mul_eq_zero.mp this).resolve_left hne

theorem fock_extremal (hla : Antitone la) {f : Pol N ℂ} (hf : f ∈ nabla la ℂ) :
    fockF f (extremal la ℂ) = evalAt 1 f * fockF (extremal la ℂ) (extremal la ℂ) := by
  have hfin := weightedHomogeneousComponent_finsupp (w := rowW N N) f
  have hsum := sum_weightedHomogeneousComponent (rowW N N) f
  rw [finsum_eq_sum _ hfin] at hsum
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← hsum, Formalism.REAL.fischerInner_sum_left, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have hmem := Formalism.GradedWeylDivisibility.dualWeylRowGraded ℂ N N la μ f hf
  have hw' := weightedHomogeneousComponent_isWeightedHomogeneous (w := rowW N N) μ f
  by_cases hμ : μ = la
  · subst hμ
    conv_lhs => rw [GlobalTheory.T.dualWeyl_eq_evalAt_one_smul_extremal_of_rowWeight ℂ N μ hla _ hmem hw']
    rw [fock_smul_left]
  · rw [evalAt_one_of_ne hμ hmem hw', zero_mul]
    exact Formalism.GradedWeylDivisibility.fockWeightOrth _ _ _ μ la _ _ hμ hw' (extremal_rowWeight hla)

theorem exists_form_eq (ψ : Pol N ℂ →ₗ[ℂ] ℂ) : ∃ h ∈ nabla la ℂ, ∀ f ∈ nabla la ℂ, form la f h = ψ f := by
  have : CompleteSpace (Space la) := FiniteDimensional.complete ℂ _
  let φ : Space la →ₗ[ℂ] ℂ := ψ ∘ₗ (nabla la ℂ).subtype ∘ₗ (toSpace la).symm.toLinearMap
  let v : Space la := (InnerProductSpace.toDual ℂ (Space la)).symm (LinearMap.toContinuousLinearMap φ)
  refine ⟨((toSpace la).symm v).1, ((toSpace la).symm v).2, fun f hf => ?_⟩
  have h1 : ⟪v, toSpace la ⟨f, hf⟩⟫_ℂ = φ (toSpace la ⟨f, hf⟩) := InnerProductSpace.toDual_symm_apply
  exact h1

theorem form_eq_fock_div (N : ℕ) (la : Fin N → ℕ) (hla : Antitone la) :
    ∀ f ∈ nabla la ℂ, ∀ f' ∈ nabla la ℂ,
      form la f f' = fockF f f' / fockF (extremal la ℂ) (extremal la ℂ) := by
  intro f hf f' hf'
  obtain ⟨hre, him⟩ := Formalism.GradedWeylDivisibility.fockPos _ (extremal la ℂ) extremal_ne_zero
  set c := fockF (extremal la ℂ) (extremal la ℂ) with hc
  have hc0 : c ≠ 0 := fun h => by rw [h] at hre; simp at hre
  have hcc : conj c = c := Complex.conj_eq_iff_im.mpr him
  obtain ⟨h, hh, H⟩ := exists_form_eq (la := la) (c⁻¹ • fockLeft f')
  have H' : ∀ g ∈ nabla la ℂ, form la g h = fockF g f' / c := fun g hg => by
    rw [H g hg, div_eq_inv_mul]; rfl
  have hE := extremal_mem (R := ℂ) hla
  have key : h = f' := by
    rw [← sub_eq_zero]
    refine eq_zero_of_evalAt_unitary (Submodule.sub_mem _ hh hf') fun u => ?_
    have hst : ∀ (g : Matrix (Fin N) (Fin N) ℂ), ∀ p ∈ nabla la ℂ, rowAct ℂ g p ∈ nabla la ℂ :=
      fun g p hp => Formalism.GradedWeylDivisibility.dualWeylRowStable ℂ N N la g p hp
    have h1 := H' _ (hst (u.1)ᴴ _ hE)
    have h2 : rowAct ℂ u.1 (rowAct ℂ (u.1)ᴴ (extremal la ℂ)) = extremal la ℂ := by
      have h3 : (u.1)ᴴ * u.1 = 1 := Matrix.mem_unitaryGroup_iff'.mp u.2
      rw [← AlgHom.comp_apply, Formalism.GradedWeylDivisibility.rowActMul ℂ N N, h3, Formalism.GradedWeylDivisibility.ldlat_rowAct_one]
      rfl
    rw [← form_rowAct u, h2, Formalism.GradedWeylDivisibility.fockRowAdj, Matrix.conjTranspose_conjTranspose, ← conj_form,
      (GlobalTheory.T.dualWeyl_extremal_reproducing_normSq_one N la hla).1 _ (hst _ _ hh), Formalism.GradedWeylDivisibility.fockHerm, fock_extremal hla (hst _ _ hf'),
      evalAt_rowAct, evalAt_rowAct, Matrix.mul_one, ← hc, ← starRingEnd_apply, map_mul, hcc,
      mul_div_cancel_right₀ _ hc0] at h1
    rw [map_sub, sub_eq_zero]
    exact (starRingEnd ℂ).injective h1
  rw [← H' f hf, key]

end GlobalTheory.DualWeylFock
end
end
