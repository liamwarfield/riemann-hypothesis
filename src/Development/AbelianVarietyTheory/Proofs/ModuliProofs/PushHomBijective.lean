module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FiniteFlatSurjectiveMulByNAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAlgHomLocalizationAugmentation
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CardAlgHomReducedTraceSum
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsClosedSubschemeTranslationKernel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.KTrivOfGeometricPointsAndTangents
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.KTrivOfGeometricPointsAndTangents
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.KCriterion

theorem mono_of_unramified_of_geometric_points {X Y : Scheme.{0}} (f : X ⟶ Y) [FormallyUnramified f]
    [LocallyOfFiniteType f]
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] (y y' : Sp k ⟶ X), y ≫ f = y' ≫ f → y = y') : Mono f := by
  have hs : Surjective (pullback.diagonal f) := ⟨fun z => by
    let κ : Type := (pullback f f).residueField z
    let y : Sp (AlgebraicClosure κ) ⟶ pullback f f :=
      spMap (algebraMap κ (AlgebraicClosure κ)) ≫ (pullback f f).fromSpecResidueField z
    have e := h _ (y ≫ pullback.fst f f) (y ≫ pullback.snd f f)
      ((Category.assoc _ _ _).trans ((congrArg _ pullback.condition).trans (Category.assoc _ _ _).symm))
    have e' : (y ≫ pullback.fst f f) ≫ pullback.diagonal f = y := by
      refine pullback.hom_ext ?_ ?_
      · simp
      · simp [e]
    exact ⟨(y ≫ pullback.fst f f) (IsLocalRing.closedPoint _),
      (congrArg (fun q => q (IsLocalRing.closedPoint _)) e').trans (Scheme.fromSpecResidueField_apply z _)⟩⟩
  have : IsIso (pullback.diagonal f) := (isIso_iff_isOpenImmersion_and_surjective _).2 ⟨inferInstance, hs⟩
  exact (pullback.isIso_diagonal_iff f).1 this

theorem triv_of_inK_local {S : Scheme.{0}} {A : Over S} [GrpObj A] {M : LB A.left} {K : Type} [CommRing K]
    [IsLocalRing K] {t : Sp K ⟶ S} {x : Over.mk t ⟶ A} (hx : InK A M x) : Triv (Out.translDiff A M x) := by
  obtain ⟨V, hp, c, hc⟩ := hx (IsLocalRing.closedPoint K)
  have hV : V = ⊤ := (IsLocalRing.closedPoint_mem_iff V).1 hp
  have := exists_isGen_translDiff_comp A M x (𝟙 _) V (fun q => hV.ge trivial) c hc
  rwa [Category.id_comp] at this

theorem kTriv_of_points_of_tangents : Out.Laws → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → IsProjBy A.hom → ∀ M : LB A.left, M.IsLB → (∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra R K], (∀ x : specO R K ⟶ A, Triv (Out.translDiff A M x) → x = 1) ∧ ∀ x : specO R (DualNumber K) ⟶ A, ptMap (TrivSqZeroExt.fstHom R K K) ≫ x = 1 → Triv (Out.translDiff A M x) → x = 1) → Out.KTriv A M := by
  intro hL R _ A _ _ hA hP M hM hK
  obtain ⟨hO, -, hT⟩ := TrivTwist.inK_iff_trivial_twist _ A M hM
  obtain ⟨H, j, hj, hH⟩ := GlobalTheory.UU.TwistKer.exists_closed_twist_kernel hL.globalFns R A hA hP M (pw M 0) hM hO
  have hrep : ∀ (T : Over (Sp R)) (x : T ⟶ A), InK A M x ↔ ∃ y : T ⟶ H, y ≫ j = x :=
    fun T x => (hT _ rfl T x).trans (hH T x)
  have := hA.proper
  have hft : LocallyOfFiniteType H.hom := by rw [← Over.w j]; infer_instance
  have hpt : ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (y : Over.mk t ⟶ H), y ≫ j = 1 := by
    intro k _ _ t
    obtain ⟨φ, rfl⟩ := Spec.map_surjective t
    let _ : Algebra R k := φ.hom.toAlgebra
    exact fun y => (hK k).1 (y ≫ j) (triv_of_inK_local ((hrep _ _).2 ⟨y, rfl⟩))
  have htan : ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R)
      (y : Over.mk (TangentCrit.dualBase k ≫ t) ⟶ H), y ≫ j = 1 := by
    intro k _ _ t
    obtain ⟨φ, rfl⟩ := Spec.map_surjective t
    let _ : Algebra R k := φ.hom.toAlgebra
    have e : TangentCrit.dualBase k ≫ Spec.map φ = spMap (algebraMap R (DualNumber k)) :=
      (Spec.map_comp _ _).symm
    rw [e]
    intro y
    refine (hK k).2 (y ≫ j) ?_ (triv_of_inK_local ((hrep _ _).2 ⟨y, rfl⟩))
    rw [← Category.assoc]
    exact hpt k _ _
  have hext : ∀ {T : Scheme.{0}} {t : T ⟶ Sp R}, (∀ y : Over.mk t ⟶ H, y ≫ j = 1) →
      ∀ w w' : T ⟶ H.left, w ≫ H.hom = t → w' ≫ H.hom = t → w = w' := fun h w w' e e' =>
    (cancel_mono j.left).1 (congrArg (fun q => q.left)
      ((h (Over.homMk w e)).trans (h (Over.homMk w' e')).symm))
  have hu : FormallyUnramified H.hom :=
    TangentCrit.formallyUnramified_of_tangent H.hom fun k _ _ w hw =>
      hext (htan k (TangentCrit.dualPt k ≫ w ≫ H.hom)) _ _ hw (by simp only [Category.assoc])
  have hm : Mono H.hom := mono_of_unramified_of_geometric_points H.hom fun k _ _ y y' e =>
    hext (hpt k (y' ≫ H.hom)) _ _ e rfl
  refine kTriv_iff_forall.2 fun T x hx => ?_
  obtain ⟨y, rfl⟩ := (hrep T x).1 hx
  obtain ⟨y', hy'⟩ := (hrep T 1).1 (inK_one hM T)
  have : y = y' := Over.OverMorphism.ext ((cancel_mono H.hom).1 ((Over.w y).trans (Over.w y').symm))
  rw [this, hy']

end GlobalTheory.KCriterion
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.KTrivOfGeometricPointsAndTangentsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kTriv_of_geometric_points_and_tangents : Out.Laws → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → IsProjBy A.hom → ∀ M : LB A.left, M.IsLB → (∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra R K], (∀ x : specO R K ⟶ A, Triv (Out.translDiff A M x) → x = 1) ∧ ∀ x : specO R (DualNumber K) ⟶ A, ptMap (TrivSqZeroExt.fstHom R K K) ≫ x = 1 → Triv (Out.translDiff A M x) → x = 1) → Out.KTriv A M := by
  first | exact @GlobalTheory.KCriterion.kTriv_of_points_of_tangents | exact GlobalTheory.KCriterion.kTriv_of_points_of_tangents | (intros; apply GlobalTheory.KCriterion.kTriv_of_points_of_tangents <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FiniteSections
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct

noncomputable section
namespace GlobalTheory.AmpleStabTorsion

theorem finite_sections {k : Type} [Field k] [IsAlgClosed k] (H : Over (Sp k)) [IsFinite H.hom] :
    Finite (Out.baseOver (Sp k) ⟶ H) := by
  have hfin : (Set.univ : Set H.left).Finite :=
    (H.hom.finite_preimage_singleton (IsLocalRing.closedPoint k)).subset fun t _ => Subsingleton.elim _ _
  have : Finite H.left := Set.finite_univ_iff.1 hfin
  refine Finite.of_injective
    (fun y : Out.baseOver (Sp k) ⟶ H => (y.left : Sp k ⟶ H.left) (IsLocalRing.closedPoint k)) fun y y' h => ?_
  exact Over.OverMorphism.ext (ext_of_apply_closedPoint_eq H.hom (Over.w y) (Over.w y') h)


theorem exists_pow_eq_one : Out.Laws → ∀ (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ M : LB A.left, M.IsLB → Out.RelAmple A M → ∀ x : Out.baseOver (Sp k) ⟶ A, Triv (Out.translDiff A M x) → ∃ m : ℕ, 1 ≤ m ∧ x ^ m = 1 := by
  intro hL k _ _ A _ _ hA M hM hamp x hx
  set_option backward.isDefEq.respectTransparency false in
  have isLB_pw {X : Scheme.{0}} {H : LB X} (hH : H.IsLB) (t : ℤ) : (AbLaw.pw H t).IsLB := by
    refine { cover := hH.cover, g_self := ?_, cocycle := ?_ }
    · intro i
      have h := congrArg (· ^ t) (hH.g_self i)
      simpa only [AbLaw.pw, one_zpow, ← map_zpow] using h
    · intro i j k
      have h := congrArg (· ^ t) (hH.cocycle i j k)
      simpa only [AbLaw.pw, mul_zpow, ← map_zpow] using h
  obtain ⟨d, -, n, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy k A M hM).1 hamp
  obtain ⟨h0, -, htw⟩ := GlobalTheory.UU.TrivTwist.inK_iff_trivial_twist _ A M hM
  obtain ⟨H, j, hj, hH⟩ := GlobalTheory.T.exists_closed_subscheme_translation_kernel hL.globalFns k A hA ⟨_, isLB_pw hM d, n, s, hs⟩ M _ hM h0
  have := GlobalTheory.AmpleStabFinite.isFinite_of_relAmple hL.globalFns k A hA M _ hM h0 hamp H j hj hH
  have := finite_sections H
  have hxK : x ∈ GlobalTheory.UU.kSubgroup A hM (Out.baseOver (Sp k)) := by
    obtain ⟨c, hc⟩ := hx
    exact fun p => ⟨⊤, trivial, _, LB.isGen_genPull _ c hc _⟩
  have hfin : ((GlobalTheory.UU.kSubgroup A hM (Out.baseOver (Sp k)) : Set (Out.baseOver (Sp k) ⟶ A))).Finite :=
    (Set.finite_range fun y : Out.baseOver (Sp k) ⟶ H => y ≫ j).subset fun z hz =>
      (hH _ z).1 ((htw _ rfl _ z).1 hz)
  have : Finite (GlobalTheory.UU.kSubgroup A hM (Out.baseOver (Sp k))) := hfin
  obtain ⟨m, hm, e⟩ := (isOfFinOrder_of_finite (⟨x, hxK⟩ : GlobalTheory.UU.kSubgroup A hM (Out.baseOver (Sp k)))).exists_pow_eq_one
  exact ⟨m, hm, congrArg Subtype.val e⟩

end GlobalTheory.AmpleStabTorsion
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubWeilPerfectOfGeneric
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsUnitDetPairingOfBicharacterOfDvdTrace
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.DetBicharacterPowFour
open scoped TensorProduct

namespace GlobalTheory

private theorem sum_pairing_eq_card_ite_one {Γ K : Type} [CommGroup Γ] [Fintype Γ] [DecidableEq Γ] [Field K]
    (X : Γ → Γ → K) (h0 : ∀ a b, X a b ≠ 0) (hl : ∀ a a' b, X (a * a') b = X a b * X a' b)
    (hr : ∀ a b b', X a (b * b') = X a b * X a b')
    (hnd : ∀ a, (∀ b, X a b = 1) → a = 1) (c : Γ) :
    (∑ b, X c b) = if c = 1 then (Fintype.card Γ : K) else 0 := by
  split_ifs with hc
  · subst hc
    have h1 : ∀ b, X 1 b = 1 := by
      intro b
      have h := hl 1 1 b
      rw [one_mul] at h
      have hb := h0 1 b
      have : X 1 b * (X 1 b - 1) = 0 := by rw [mul_sub, mul_one, ← h, sub_self]
      rcases mul_eq_zero.mp this with h' | h'
      · exact absurd h' hb
      · exact sub_eq_zero.mp h'
    simp [h1]
  · obtain ⟨b₀, hb₀⟩ : ∃ b₀, X c b₀ ≠ 1 := by
      by_contra hne
      simp only [not_exists, ne_eq, not_not] at hne
      exact hc (hnd c hne)
    have hshift : (∑ b, X c b) = X c b₀ * ∑ b, X c b := by
      rw [Finset.mul_sum]
      simp_rw [← hr]
      exact (Equiv.sum_comp (Equiv.mulLeft b₀) (fun b => X c b)).symm
    have : (X c b₀ - 1) * ∑ b, X c b = 0 := by
      rw [sub_mul, one_mul, ← hshift, sub_self]
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd (sub_eq_zero.mp h') hb₀
    · exact h'

theorem det_bicharacter_pow_four :
    ∀ (Γ K : Type) [CommGroup Γ] [Fintype Γ] [DecidableEq Γ] [Field K] (X : Γ → Γ → K), (∀ a b, X a b ≠ 0) → (∀ a a' b, X (a * a') b = X a b * X a' b) → (∀ a b b', X a (b * b') = X a b * X a b') → (∀ a, (∀ b, X a b = 1) → a = 1) → (Matrix.of X).det ^ 4 = (Fintype.card Γ : K) ^ (2 * Fintype.card Γ) := by
  intro Γ K _ _ _ _ X h0 hl hr hnd
  set M : Matrix Γ Γ K := Matrix.of X with hM
  have hMP : M * Matrix.transpose (M.submatrix (Equiv.inv Γ) id) = (Fintype.card Γ : K) • (1 : Matrix Γ Γ K) := by
    ext a a'
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, id_eq, hM,
      Matrix.of_apply, Equiv.inv_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    simp_rw [← hl]
    rw [sum_pairing_eq_card_ite_one X h0 hl hr hnd]
    by_cases h : a = a'
    · subst h; simp
    · have : a * a'⁻¹ ≠ 1 := fun e => h (mul_inv_eq_one.mp e)
      simp [h, this]
  have hdet := congrArg Matrix.det hMP
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_permute, Matrix.det_smul, Matrix.det_one,
    mul_one] at hdet
  have hs : ((Equiv.Perm.sign (Equiv.inv Γ) : ℤ) : K) ^ 2 = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.inv Γ)) with e | e <;> simp [e]
  calc M.det ^ 4 = (M.det * (((Equiv.Perm.sign (Equiv.inv Γ) : ℤ) : K) * M.det)) ^ 2 := by
        rw [mul_pow, mul_pow, hs]; ring
    _ = (Fintype.card Γ : K) ^ (2 * Fintype.card Γ) := by rw [hdet, ← pow_mul, mul_comm]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsUnitDetPairingOfBicharacterOfDvdTrace
open scoped TensorProduct

namespace GlobalTheory

private theorem submatrix_eq_pt_mul_map_mul_transpose {O H K Γ : Type} [CommRing O] [CommRing H] [Algebra O H] [Field K]
    [Algebra O K] {r : ℕ} (b : Module.Basis (Fin r) O H) (D : Matrix (Fin r) (Fin r) O)
    (pt : Γ → (H →ₐ[O] K)) (X : Γ → Γ → K)
    (hX : ∀ a a', X a a' = ∑ i, ∑ j, algebraMap O K (D i j) * pt a (b i) * pt a' (b j))
    (e : Fin r ≃ Γ) :
    (Matrix.of X).submatrix e e = Matrix.of (fun i j => pt (e i) (b j)) * D.map (algebraMap O K) *
      Matrix.transpose (Matrix.of (fun i j => pt (e i) (b j))) := by
  ext i k
  simp only [Matrix.submatrix_apply, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul, hX]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem isUnit_det_of_bicharacter_of_dvd_trace :
    ∀ (O H K Γ : Type) [CommRing O] [IsDomain O] [CommRing H] [Algebra O H] [Field K] [IsAlgClosed K] [Algebra O K] [CommGroup Γ] (r : ℕ) (b : Module.Basis (Fin r) O H) (D : Matrix (Fin r) (Fin r) O) (pt : Γ → (H →ₐ[O] K)) (X : Γ → Γ → K) (c : O), Function.Injective (algebraMap O K) → IsReduced (K ⊗[O] H) → Function.Bijective pt → (∀ a a', X a a' = ∑ i, ∑ j, algebraMap O K (D i j) * pt a (b i) * pt a' (b j)) → (∀ a b, X a b ≠ 0) → (∀ a a' b, X (a * a') b = X a b * X a' b) → (∀ a b b', X a (b * b') = X a b * X a b') → (∀ a, (∀ b, X a b = 1) → a = 1) → c ≠ 0 → (r : O) = c ^ 2 → (∀ h : H, c ∣ Algebra.trace O H h) → IsUnit D.det := by
  intro O H K Γ _ _ _ _ _ _ _ _ r b D pt X c hinj hred hpt hX hne hm₁ hm₂ hnd hc hr hdvd
  classical
  haveI : Module.Free O H := Module.Free.of_basis b
  haveI : Module.Finite O H := Module.Finite.of_basis b
  obtain ⟨hfin, hcard, htrace⟩ :=
    finite_card_trace_algHom_of_isReduced_baseChange O H K hred
  let E : Γ ≃ (H →ₐ[O] K) := Equiv.ofBijective pt hpt
  haveI : Finite Γ := Finite.of_equiv _ E.symm
  letI : Fintype Γ := Fintype.ofFinite Γ
  letI : Fintype (H →ₐ[O] K) := Fintype.ofFinite _
  have hcardΓ : Fintype.card Γ = r := by
    rw [← Nat.card_eq_fintype_card, Nat.card_congr E, hcard, Module.finrank_eq_card_basis b,
      Fintype.card_fin]

  let e : Fin r ≃ Γ := (Fintype.equivFinOfCardEq hcardΓ).symm
  let P : Matrix (Fin r) (Fin r) K := Matrix.of fun i j => pt (e i) (b j)
  let D' : Matrix (Fin r) (Fin r) K := D.map (algebraMap O K)

  have hXP : (Matrix.of X).submatrix e e = P * D' * Matrix.transpose P := submatrix_eq_pt_mul_map_mul_transpose b D pt X hX e

  have hsum : ∀ h : H, algebraMap O K (Algebra.trace O H h) = ∑ i, pt (e i) h := by
    intro h
    rw [htrace h, finsum_eq_sum_of_fintype]
    exact (Fintype.sum_equiv (e.trans E) (fun i => pt (e i) h) (fun ga => ga h)
      fun _ => rfl).symm
  have hdvd' : ∀ h : H, ∃ d, Algebra.trace O H h = c * d := fun h => hdvd h
  choose T hT using hdvd'
  let Tm : Matrix (Fin r) (Fin r) O := Matrix.of fun j k => T (b j * b k)

  have hPP : Matrix.transpose P * P = (algebraMap O K c) • Tm.map (algebraMap O K) := by
    ext j k
    simp only [Matrix.mul_apply, Matrix.transpose_apply, P, Matrix.of_apply, Matrix.smul_apply,
      Matrix.map_apply, Tm, smul_eq_mul]
    have hjk : algebraMap O K c * algebraMap O K (T (b j * b k)) =
        algebraMap O K (Algebra.trace O H (b j * b k)) := by
      rw [hT, map_mul]
    rw [hjk, hsum]
    exact Finset.sum_congr rfl fun i _ => (map_mul (pt (e i)) (b j) (b k)).symm
  have hTm : (Tm.map (algebraMap O K)).det = algebraMap O K Tm.det :=
    ((algebraMap O K).map_det Tm).symm
  have hD' : D'.det = algebraMap O K D.det := ((algebraMap O K).map_det D).symm
  have hdetP : P.det ^ 2 = algebraMap O K c ^ r * algebraMap O K Tm.det := by
    have h := congrArg Matrix.det hPP
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul, Fintype.card_fin, hTm] at h
    rw [sq, h]
  have h4 := det_bicharacter_pow_four Γ K X hne hm₁ hm₂ hnd
  rw [← Matrix.det_submatrix_equiv_self e (Matrix.of X), hXP, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose, hcardΓ] at h4
  have hrK : (r : K) = algebraMap O K c ^ 2 := by
    rw [← map_natCast (algebraMap O K) r, hr, map_pow]

  have key : algebraMap O K c ^ (4 * r) * algebraMap O K (Tm.det ^ 4 * D.det ^ 4) =
      algebraMap O K c ^ (4 * r) * 1 := by
    rw [map_mul, map_pow, map_pow, ← hD', mul_one]
    calc algebraMap O K c ^ (4 * r) * (algebraMap O K Tm.det ^ 4 * D'.det ^ 4)
        = (algebraMap O K c ^ r * algebraMap O K Tm.det) ^ 4 * D'.det ^ 4 := by ring
      _ = (P.det ^ 2) ^ 4 * D'.det ^ 4 := by rw [hdetP]
      _ = (P.det * D'.det * P.det) ^ 4 := by ring
      _ = (r : K) ^ (2 * r) := h4
      _ = algebraMap O K c ^ (4 * r) := by
        rw [hrK, ← pow_mul]
        congr 1
        ring
  have hu : algebraMap O K c ^ (4 * r) ≠ 0 :=
    pow_ne_zero _ (by rwa [ne_eq, map_eq_zero_iff _ hinj])
  have h1 := mul_left_cancel₀ hu key
  rw [← map_one (algebraMap O K)] at h1
  have h2 := hinj h1
  exact isUnit_iff_exists_inv.mpr ⟨Tm.det ^ 4 * D.det ^ 3, by linear_combination h2⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsUnitDetPairingOfBicharacterOfDvdTraceStatement
open scoped TensorProduct
theorem _root_.GlobalTheory.T.isUnit_det_pairing_of_bicharacter_of_dvd_trace : ∀ (O H K Γ : Type) [CommRing O] [IsDomain O] [CommRing H] [Algebra O H] [Field K] [IsAlgClosed K] [Algebra O K] [CommGroup Γ] (r : ℕ) (b : Module.Basis (Fin r) O H) (D : Matrix (Fin r) (Fin r) O) (pt : Γ → (H →ₐ[O] K)) (X : Γ → Γ → K) (c : O), Function.Injective (algebraMap O K) → IsReduced (K ⊗[O] H) → Function.Bijective pt → (∀ a a', X a a' = ∑ i, ∑ j, algebraMap O K (D i j) * pt a (b i) * pt a' (b j)) → (∀ a b, X a b ≠ 0) → (∀ a a' b, X (a * a') b = X a b * X a' b) → (∀ a b b', X a (b * b') = X a b * X a b') → (∀ a, (∀ b, X a b = 1) → a = 1) → c ≠ 0 → (r : O) = c ^ 2 → (∀ h : H, c ∣ Algebra.trace O H h) → IsUnit D.det := by
  first | exact @GlobalTheory.isUnit_det_of_bicharacter_of_dvd_trace | exact GlobalTheory.isUnit_det_of_bicharacter_of_dvd_trace | (intros; apply GlobalTheory.isUnit_det_of_bicharacter_of_dvd_trace <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubWeilPerfectOfGeneric
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.PerfectPairing
variable {O : Type} [CommRing O]

theorem exists_rep [IsLocalRing O] (A : Over (Sp O)) [GrpObj A] [IsCommMonObj A] (n : ℕ)
    (hfin : IsFinite ((𝟙 A) ^ n : A ⟶ A).left) (hflat : Flat ((𝟙 A) ^ n : A ⟶ A).left) :
    ∃ (H : Type) (_ : CommRing H) (_ : Algebra O H), Module.Free O H ∧ Module.Finite O H ∧
      ∃ y : specO O H ⟶ A, y ^ n = 1 ∧ ∀ (S : Type) [CommRing S] [Algebra O S] (z : specO O S ⟶ A), z ^ n = 1 →
        ∃! φ : H →ₐ[O] S, ptMap φ ≫ y = z := by
  obtain ⟨H, φ, y, hφf, hφl, hpb⟩ := finRep_exists_isPullback_spec ((𝟙 A) ^ n : A ⟶ A).left
    (CommRingCat.of O) (eSec A)
  letI : Algebra O H := φ.hom.toAlgebra
  haveI : Module.Finite O H := hφf
  haveI : Module.Flat O H := hφl
  have hpow : ∀ {T : Over (Sp O)} (z : T ⟶ A),
      z.left ≫ ((𝟙 A) ^ n : A ⟶ A).left = (z ^ n).left := by
    intro T z
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  have he : eSec A ≫ A.hom = 𝟙 _ := Over.w (η[A])
  have hy : y ≫ A.hom = (specO O H).hom := by
    rw [← Over.w ((𝟙 A) ^ n : A ⟶ A), ← Category.assoc, hpb.w, Category.assoc, he]
    exact Category.comp_id _
  let y' : specO O H ⟶ A := Over.homMk y hy
  refine ⟨H, inferInstance, inferInstance, Module.free_of_flat_of_isLocalRing, inferInstance, y', ?_, ?_⟩
  · apply Over.OverMorphism.ext
    rw [← hpow, GlobalTheory.UU.one_left]
    exact hpb.w
  · intro S _ _ z hz
    have hw : z.left ≫ ((𝟙 A) ^ n : A ⟶ A).left =
        Spec.map (CommRingCat.ofHom (algebraMap O S)) ≫ eSec A := by
      rw [hpow, hz, GlobalTheory.UU.one_left]
      rfl
    let l : Spec (CommRingCat.of S) ⟶ Spec H := hpb.lift _ _ hw
    have hl : Spec.map (Spec.preimage l) = l := Spec.map_preimage l
    have h1 : φ ≫ Spec.preimage l = CommRingCat.ofHom (algebraMap O S) := by
      apply Spec.map_injective
      rw [Spec.map_comp, hl]
      exact hpb.lift_snd _ _ hw
    refine ⟨⟨(Spec.preimage l).hom, fun r => congrArg (fun f => f.hom r) h1⟩, ?_, ?_⟩
    · apply Over.OverMorphism.ext
      change Spec.map (Spec.preimage l) ≫ y = z.left
      rw [hl]
      exact hpb.lift_fst _ _ hw
    · intro ψ hψ
      have h2 : Spec.map (CommRingCat.ofHom ψ.toRingHom : H ⟶ CommRingCat.of S) = l := by
        apply hpb.hom_ext
        · rw [hpb.lift_fst _ _ hw, ← hψ]
          rfl
        · rw [hpb.lift_snd _ _ hw, ← Spec.map_comp]
          congr 1
          ext r
          exact ψ.commutes r
      have h3 := Spec.map_injective (h2.trans hl.symm)
      ext a
      exact congrArg (fun f => f.hom a) h3

theorem isReduced_rep {A : Over (Sp O)} [GrpObj A] [IsCommMonObj A] {n : ℕ} {H : Type} [CommRing H] [Algebra O H]
    [Module.Finite O H] {y : specO O H ⟶ A} (hy : y ^ n = 1)
    (hu : ∀ (S : Type) [CommRing S] [Algebra O S] (z : specO O S ⟶ A), z ^ n = 1 →
      ∃! φ : H →ₐ[O] S, ptMap φ ≫ y = z)
    (F : Type) [Field F] [IsAlgClosed F] [Algebra O F] (hn : (n : F) ≠ 0) : _root_.IsReduced (F ⊗[O] H) := by
  refine TorsionReduced.isReduced_of_forall_dualNumber F _ fun φ b => ?_
  let χ : H →ₐ[O] DualNumber F := (φ.restrictScalars O).comp Algebra.TensorProduct.includeRight
  have hz : (ptMap χ ≫ y) ^ n = 1 := by rw [← MonObj.comp_pow, hy, MonObj.comp_one]
  have h2 := TorsionReduced.eq_const_of_pow_eq_one hn.isUnit _ hz
  simp only [← Category.assoc] at h2
  rw [TangentPow.ptMap_comp_ptMap, TangentPow.ptMap_comp_ptMap] at h2
  have h4 := (hu _ _ hz).unique rfl h2.symm
  have h5 : ∀ a, (χ a).snd = 0 := fun a => by
    have := congrArg TrivSqZeroExt.snd (congrArg (fun f => f a) h4)
    simpa using this
  induction b with
  | add x y hx hy => simp [hx, hy]
  | tmul f a =>
    have : f ⊗ₜ[O] a = f • ((1 : F) ⊗ₜ[O] a) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    rw [this, map_smul, TrivSqZeroExt.snd_smul]
    exact smul_eq_zero_of_right f (h5 a)

theorem eq_one_of_affine {A : Over (Sp O)} [GrpObj A] {T : Over (Sp O)} (x : T ⟶ A)
    (h : ∀ (S : Type) [CommRing S] [Algebra O S] (ρ : specO O S ⟶ T), ρ ≫ x = 1) : x = 1 := by
  apply Over.OverMorphism.ext
  refine T.left.affineOpenCover.openCover.hom_ext _ _ fun i => ?_
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (T.left.affineOpenCover.f i ≫ T.hom)
  letI : Algebra O (T.left.affineOpenCover.X i) := ψ.hom.toAlgebra
  let ρ : specO O (T.left.affineOpenCover.X i) ⟶ T := Over.homMk (T.left.affineOpenCover.f i) hψ.symm
  have := (h _ ρ).trans (MonObj.comp_one ρ).symm
  exact congrArg (fun q => q.left) this

section Val
variable {A : Over (Sp O)} [GrpObj A] [IsCommMonObj A] {L : RigLB A} (c : CubicalStr A L) (n : ℕ)
  {S S' : Type} [CommRing S] [Algebra O S] [CommRing S'] [Algebra O S']

def Val (x y : specO O S ⟶ A) (s : S) : Prop :=
  ∃ ζ, GlobalTheory.UU.CubWeil c n x y ζ ∧ (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom ζ.val = s

variable {c n} {x x' y y' : specO O S ⟶ A} {s s' : S}

theorem Val.exists (hx : x ^ n = 1) (hy : y ^ n = 1) : ∃ s, Val c n x y s := by
  obtain ⟨ζ, h, -⟩ := GlobalTheory.UU.existsUnique_cubWeil c hx hy
  exact ⟨_, ζ, h, rfl⟩

theorem Val.unique (h : Val c n x y s) (h' : Val c n x y s') : s = s' := by
  obtain ⟨ζ, h, rfl⟩ := h
  obtain ⟨ζ', h', rfl⟩ := h'
  rw [h.unique h']

theorem Val.isUnit (h : Val c n x y s) : IsUnit s := by
  obtain ⟨ζ, h, rfl⟩ := h
  exact ζ.isUnit.map _

theorem val_one_iff : Val c n x y 1 ↔ GlobalTheory.UU.CubWeil c n x y 1 := by
  refine ⟨fun ⟨ζ, h, e⟩ => ?_, fun h => ⟨1, h, map_one _⟩⟩
  have : ζ = 1 := Units.ext ((ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of S)).hom).1 (e.trans (map_one _).symm))
  exact this ▸ h

theorem Val.mul_left (h : Val c n x y s) (h' : Val c n x' y s') : Val c n (x * x') y (s * s') := by
  obtain ⟨ζ, h, rfl⟩ := h
  obtain ⟨ζ', h', rfl⟩ := h'
  exact ⟨_, h.mul_left h', map_mul _ _ _⟩

theorem Val.mul_right (h : Val c n x y s) (h' : Val c n x y' s') : Val c n x (y * y') (s * s') := by
  obtain ⟨ζ, h, rfl⟩ := h
  obtain ⟨ζ', h', rfl⟩ := h'
  have := (h.symm.mul_left h'.symm).symm
  rw [mul_inv, inv_inv, inv_inv] at this
  exact ⟨_, this, map_mul _ _ _⟩

theorem Val.comp (h : Val c n x y s) (f : S →ₐ[O] S') : Val c n (ptMap f ≫ x) (ptMap f ≫ y) (f s) := by
  obtain ⟨ζ, h, rfl⟩ := h
  refine ⟨_, h.comp (ptMap f), ?_⟩
  exact congrArg (fun q => q.hom ζ.val) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f.toRingHom))

theorem exists_matrix (c : CubicalStr A L) {H : Type} [CommRing H] [Algebra O H] {r : ℕ} (b : Module.Basis (Fin r) O H)
    {y : specO O H ⟶ A} (hy : y ^ n = 1) :
    ∃ D : Matrix (Fin r) (Fin r) O, ∀ (S : Type) [CommRing S] [Algebra O S] (φ ψ : H →ₐ[O] S),
      Val c n (ptMap φ ≫ y) (ptMap ψ ≫ y) (∑ i, ∑ j, algebraMap O S (D i j) * φ (b i) * ψ (b j)) := by
  have hz : ∀ χ : H →ₐ[O] H ⊗[O] H, (ptMap χ ≫ y) ^ n = 1 := fun χ => by
    rw [← MonObj.comp_pow, hy, MonObj.comp_one]
  obtain ⟨e, he⟩ := Val.exists (c := c) (hz Algebra.TensorProduct.includeLeft) (hz Algebra.TensorProduct.includeRight)
  refine ⟨fun i j => (b.tensorProduct b).repr e (i, j), fun S _ _ φ ψ => ?_⟩
  have h := he.comp (Algebra.TensorProduct.productMap φ ψ)
  rw [← Category.assoc, ← Category.assoc, TangentPow.ptMap_comp_ptMap, TangentPow.ptMap_comp_ptMap,
    Algebra.TensorProduct.productMap_left, Algebra.TensorProduct.productMap_right] at h
  convert h using 1
  conv_rhs => rw [← (b.tensorProduct b).sum_repr e]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, Module.Basis.tensorProduct_apply, Algebra.TensorProduct.productMap_apply_tmul, Algebra.smul_def,
    _root_.mul_assoc]

end Val

theorem algHom_eq_of_isUnit_det {H S : Type} [CommRing H] [Algebra O H] [CommRing S] [Algebra O S] {r : ℕ}
    (b : Module.Basis (Fin r) O H) (D : Matrix (Fin r) (Fin r) O) (hD : IsUnit D.det) (φ φ' : H →ₐ[O] S)
    (h : ∑ i, ∑ j, algebraMap O (S ⊗[O] H) (D i j) * (φ (b i) ⊗ₜ[O] (1 : H)) * ((1 : S) ⊗ₜ[O] b j) =
      ∑ i, ∑ j, algebraMap O (S ⊗[O] H) (D i j) * (φ' (b i) ⊗ₜ[O] (1 : H)) * ((1 : S) ⊗ₜ[O] b j)) : φ = φ' := by
  have key : ∀ ψ : H →ₐ[O] S,
      ∑ i, ∑ j, algebraMap O (S ⊗[O] H) (D i j) * (ψ (b i) ⊗ₜ[O] (1 : H)) * ((1 : S) ⊗ₜ[O] b j) =
        ∑ j, (Matrix.vecMul (fun i => ψ (b i)) (D.map (algebraMap O S)) j) • Algebra.TensorProduct.basis S b j := by
    intro ψ
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.vecMul, dotProduct, Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Algebra.TensorProduct.algebraMap_apply, TensorProduct.smul_tmul', mul_comm]
  rw [key, key] at h
  have h1 := (Algebra.TensorProduct.basis S b).equivFun.symm.injective
    (((Algebra.TensorProduct.basis S b).equivFun_symm_apply _).trans
      (h.trans ((Algebra.TensorProduct.basis S b).equivFun_symm_apply _).symm))
  have hD' : IsUnit (D.map (algebraMap O S)) := by
    rw [Matrix.isUnit_iff_isUnit_det]
    have := hD.map (algebraMap O S)
    rwa [RingHom.map_det] at this
  have h2 := (Matrix.vecMul_injective_of_isUnit hD') h1
  exact AlgHom.toLinearMap_injective (b.ext fun i => congrFun h2 i)

end GlobalTheory.PerfectPairing

namespace GlobalTheory

open PerfectPairing in
theorem cubWeil_perfect_of_generic : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [Field K] [IsAlgClosed K] [CharZero K] [Algebra O K], Function.Injective (algebraMap O K) → ∀ (A : Over (Sp O)) [GrpObj A] [IsCommMonObj A] (g : ℕ), SmoothOfRelativeDimension g A.hom → ∀ (L : RigLB A) (c : CubicalStr A L) (n : ℕ), 1 ≤ n → IsFinite ((𝟙 A) ^ n : A ⟶ A).left → Flat ((𝟙 A) ^ n : A ⟶ A).left → Nat.card {x : specO O K ⟶ A // x ^ n = 1} = n ^ (2 * g) → (∀ x : specO O K ⟶ A, x ^ n = 1 → (∀ y : specO O K ⟶ A, y ^ n = 1 → GlobalTheory.UU.CubWeil c n x y 1) → x = 1) → ∀ (T : Over (Sp O)) (x : T ⟶ A), x ^ n = 1 → (∀ (T' : Over (Sp O)) (ρ : T' ⟶ T) (y : T' ⟶ A), y ^ n = 1 → GlobalTheory.UU.CubWeil c n (ρ ≫ x) y 1) → x = 1 := by
  intro O K _ _ _ _ _ _ _ hinj A _ _ g hsm L c n hn hfin hflat hcard hK T x hx hT
  obtain ⟨H, _, _, _, _, y, hy, hu⟩ := exists_rep A n hfin hflat
  have hnK : (n : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hred := isReduced_rep hy hu K hnK
  let b := Module.finBasis O H
  obtain ⟨D, hD⟩ := exists_matrix c b hy
  have hz : ∀ {S : Type} [CommRing S] [Algebra O S] (χ : H →ₐ[O] S), (ptMap χ ≫ y) ^ n = 1 := fun χ => by
    rw [← MonObj.comp_pow, hy, MonObj.comp_one]
  let Γ : Subgroup (specO O K ⟶ A) := (powMonoidHom n).ker
  choose pt hpt using fun a : Γ => (hu K a.1 a.2).exists
  have hbij : Function.Bijective pt := by
    refine ⟨fun a a' e => Subtype.ext (by rw [← hpt, ← hpt, e]), fun χ => ⟨⟨ptMap χ ≫ y, hz χ⟩, ?_⟩⟩
    exact (hu K _ (hz χ)).unique (hpt _) rfl
  let X : Γ → Γ → K := fun a a' => ∑ i, ∑ j, algebraMap O K (D i j) * pt a (b i) * pt a' (b j)
  have hX : ∀ a a' : Γ, Val c n a.1 a'.1 (X a a') := fun a a' => by
    have := hD K (pt a) (pt a')
    rwa [hpt, hpt] at this
  have hr : Module.finrank O H = n ^ (2 * g) := by
    rw [← (GlobalTheory.finite_card_trace_algHom_of_isReduced_baseChange O H K hred).2.1, ← Nat.card_eq_of_bijective pt hbij]
    exact hcard
  have hdet : IsUnit D.det := by
    refine GlobalTheory.T.isUnit_det_pairing_of_bicharacter_of_dvd_trace O H K Γ _ b D pt X ((n : O) ^ g) hinj hred hbij (fun _ _ => rfl)
      (fun a a' => (hX a a').isUnit.ne_zero) (fun a a' d => (hX _ _).unique ((hX a d).mul_left (hX a' d)))
      (fun a d d' => (hX _ _).unique ((hX a d).mul_right (hX a d'))) (fun a ha => Subtype.ext ?_) (fun h0 => ?_) ?_
      (GlobalTheory.pow_dvd_trace_torsion O A n H y g hsm hy hu)
    · refine hK a.1 a.2 fun z hz => val_one_iff.1 ?_
      have := hX a ⟨z, hz⟩
      rwa [ha] at this
    · have := congrArg (algebraMap O K) h0
      rw [map_pow, map_natCast, map_zero] at this
      exact pow_ne_zero g hnK this
    · rw [hr, Nat.cast_pow, mul_comm, pow_mul]
  refine eq_one_of_affine x fun S _ _ ρ => ?_
  obtain ⟨φ, hφ, -⟩ := hu S (ρ ≫ x) (by rw [← MonObj.comp_pow, hx, MonObj.comp_one])
  obtain ⟨φ', hφ', -⟩ := hu S 1 (one_pow n)
  let l : S →ₐ[O] S ⊗[O] H := Algebra.TensorProduct.includeLeft
  let m : H →ₐ[O] S ⊗[O] H := Algebra.TensorProduct.includeRight
  have h1 := hD _ (l.comp φ) m
  have h2 := hD _ (l.comp φ') m
  rw [← TangentPow.ptMap_comp_ptMap, Category.assoc] at h1 h2
  rw [hφ, ← Category.assoc] at h1
  rw [hφ', MonObj.comp_one] at h2
  have e1 := h1.unique (val_one_iff.2 (hT _ _ _ (hz m)))
  have e2 := h2.unique (val_one_iff.2 (GlobalTheory.UU.cubWeil_one_left c (hz m)))
  rw [← hφ, ← hφ', algHom_eq_of_isUnit_det b D hdet φ φ' (e1.trans e2.symm)]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubWeilPerfectOfGenericStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_one_of_cubWeil_trivial_of_generic : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [Field K] [IsAlgClosed K] [CharZero K] [Algebra O K], Function.Injective (algebraMap O K) → ∀ (A : Over (Sp O)) [GrpObj A] [IsCommMonObj A] (g : ℕ), SmoothOfRelativeDimension g A.hom → ∀ (L : RigLB A) (c : CubicalStr A L) (n : ℕ), 1 ≤ n → IsFinite ((𝟙 A) ^ n : A ⟶ A).left → Flat ((𝟙 A) ^ n : A ⟶ A).left → Nat.card {x : specO O K ⟶ A // x ^ n = 1} = n ^ (2 * g) → (∀ x : specO O K ⟶ A, x ^ n = 1 → (∀ y : specO O K ⟶ A, y ^ n = 1 → GlobalTheory.UU.CubWeil c n x y 1) → x = 1) → ∀ (T : Over (Sp O)) (x : T ⟶ A), x ^ n = 1 → (∀ (T' : Over (Sp O)) (ρ : T' ⟶ T) (y : T' ⟶ A), y ^ n = 1 → GlobalTheory.UU.CubWeil c n (ρ ≫ x) y 1) → x = 1 := by
  first | exact @GlobalTheory.cubWeil_perfect_of_generic | exact GlobalTheory.cubWeil_perfect_of_generic | (intros; apply GlobalTheory.cubWeil_perfect_of_generic <;> assumption)
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct

noncomputable section
namespace GlobalTheory.GenericKTriv

section Pull

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A']
  {φ : A'.left ⟶ A.left} {L : LB A.left} {L' : LB A'.left}

theorem pushHom_bijective (h : IsGrpPullback A' A f φ) (T : Over S') : Function.Bijective (pushHom h T) := by
  refine ⟨fun x y e => Over.OverMorphism.ext
    (h.1.hom_ext (congrArg (fun q => q.left) e) (by rw [Over.w, Over.w])), fun x => ?_⟩
  exact ⟨Over.homMk (h.1.lift x.left T.hom (Over.w x)) (h.1.lift_snd _ _ _),
    Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩

theorem triv_pull (h : IsGrpPullback A' A f φ) (hL : L.IsLB) (hL' : L'.IsLB) (e : LBIso L' (L.pull φ))
    {T : Over S'} (x : T ⟶ A') (hx : Triv (Out.translDiff A L (pushHom h T x))) :
    Triv (Out.translDiff A' L' x) := by
  obtain ⟨w, hw⟩ := e
  obtain ⟨c, hc⟩ := hx
  let T₀ : Over S := Over.mk (T.hom ≫ f)
  let a : Over.mk ((T ⊗ A').hom ≫ f) ⟶ T₀ := Over.homMk (fst T A').left (by
    show (fst T A').left ≫ T.hom ≫ f = (T ⊗ A').hom ≫ f
    rw [← Category.assoc, Over.w])
  let j : Over.mk ((T ⊗ A').hom ≫ f) ⟶ T₀ ⊗ A := lift a (pushPt h.1.w (snd T A'))
  have k₂ : j.left ≫ (snd T₀ A).left = (snd T A').left ≫ φ := congrArg (fun q => q.left) (lift_snd a (pushPt h.1.w (snd T A')))
  have k₁ : j.left ≫ ((fst T₀ A ≫ pushHom h T x) * snd T₀ A).left = ((fst T A' ≫ x) * snd T A').left ≫ φ := by
    have e : j ≫ ((fst T₀ A ≫ pushHom h T x) * snd T₀ A) = (a ≫ pushHom h T x) * pushPt h.1.w (snd T A') := by
      rw [MonObj.comp_mul, lift_fst_assoc, lift_snd]
    have e₁ := h.2 (T ⊗ A') (fst T A' ≫ x) (snd T A') (a ≫ pushHom h T x) (pushPt h.1.w (snd T A'))
      (Category.assoc (fst T A').left x.left φ).symm rfl
    rw [← e] at e₁
    exact e₁
  have h4 : Triv (LB.LinComb L (K := Fin 2) (fun i => j.left ≫
      ![(lift (fst T₀ A ≫ pushHom h T x) (snd T₀ A) ≫ μ[A]).left, (snd T₀ A).left] i) ![1, -1]) :=
    ⟨_, DVR.pullGen_isGen _ _ _ c hc _⟩
  have h3 : (fun i => j.left ≫
      ![(lift (fst T₀ A ≫ pushHom h T x) (snd T₀ A) ≫ μ[A]).left, (snd T₀ A).left] i) =
      fun i => ![(lift (fst T A' ≫ x) (snd T A') ≫ μ[A']).left, (snd T A').left] i ≫ φ := by
    funext i
    fin_cases i
    exacts [k₁, k₂]
  rw [h3] at h4
  obtain ⟨c', hc'⟩ := h4
  exact exists_down ((isGen_iff w).1 hw) hL hL' c' hc'

theorem eq_one_of_factor (h : IsGrpPullback A' A f φ) (hL : L.IsLB) (hL' : L'.IsLB) (e : LBIso L' (L.pull φ))
    (hK : Out.KTriv A' L') {R : Type} [CommRing R] (t : Sp R ⟶ S') {s : Sp R ⟶ S} (hs : s = t ≫ f)
    (x : Over.mk s ⟶ A) (hx : Triv (Out.translDiff A L x)) : x = 1 := by
  subst hs
  obtain ⟨y, rfl⟩ := (pushHom_bijective h (Over.mk t)).2 x
  obtain ⟨c, hc⟩ := triv_pull h hL hL' e y hx
  have : y = 1 := hK R t y fun p => ⟨⊤, trivial, _, LB.isGen_genPull _ c hc _⟩
  rw [this]
  exact map_one (pushHom h (Over.mk t))

theorem card_torsion (h : IsGrpPullback A' A f φ) {Y : Scheme.{0}} (t : Y ⟶ S') {s : Y ⟶ S} (hs : s = t ≫ f)
    (n : ℕ) : Nat.card {x : Over.mk s ⟶ A // x ^ n = 1} = Nat.card {x : Over.mk t ⟶ A' // x ^ n = 1} := by
  subst hs
  let E := MulEquiv.ofBijective _ (pushHom_bijective h (Over.mk t))
  refine (Nat.card_congr (E.toEquiv.subtypeEquiv fun x => ?_)).symm
  show x ^ n = 1 ↔ E x ^ n = 1
  rw [← map_pow, MulEquiv.map_eq_one_iff]

end Pull

theorem field_torsion (hL : Out.Laws) {O : Type} [CommRing O] (A : Over (Sp O)) [GrpObj A] [IsCommMonObj A]
    (hA : IsAbelianScheme A) {M : LB A.left} (hM : M.IsLB) (hamp : Out.RelAmple A M) {k : Type} [Field k]
    [IsAlgClosed k] (f : Sp k ⟶ Sp O) {s : Sp k ⟶ Sp O} (hs : s = 𝟙 _ ≫ f) (x : Over.mk s ⟶ A)
    (hx : Triv (Out.translDiff A M x)) : ∃ m : ℕ, 1 ≤ m ∧ x ^ m = 1 := by
  subst hs
  have h := PullbackComparison.isGrpPullback f A
  have hM' := pull_isLB hM (PullbackComparison.pφ f A)
  have e : LBIso (M.pull (PullbackComparison.pφ f A)) (M.pull (PullbackComparison.pφ f A)) := PolBaseChange.lbIso_refl hM'
  have hA' := PolPull.isAbelianScheme_of_isGrpPullback hA h
  have := hA'.comm
  obtain ⟨y, rfl⟩ := (pushHom_bijective h (Out.baseOver (Sp k))).2 x
  have hy := triv_pull h hM hM' e y hx
  obtain ⟨w, hw⟩ := e
  obtain ⟨m, hm, hy⟩ := AmpleStabTorsion.exists_pow_eq_one hL k _ hA' _ hM'
    (relAmple_pull h.1 hM hM' ((isGen_iff w).1 hw) ⊤ (isAffineOpen_top _) (fun _ => trivial) hamp) y hy
  refine ⟨m, hm, ?_⟩
  exact (map_pow (pushHom h _) y m).symm.trans ((congrArg (pushHom h _) hy).trans (map_one _))

theorem exists_cover {O K R : Type} [CommRing O] [IsDomain O] [Field K] [CommRing R] (i : O →+* K)
    (hi : Function.Injective i) (j : O →+* R) (hj : ∀ a : O, a ≠ 0 → IsUnit (j a)) :
    ∃ (R' : Type) (_ : CommRing R') (a : R →+* R') (b : K →+* R'), a.FaithfullyFlat ∧ a.comp j = b.comp i := by
  let F := FractionRing O
  let iF : F →+* K := IsFractionRing.lift hi
  let jF : F →+* R := IsLocalization.lift (M := nonZeroDivisors O) (g := j)
    fun y => hj y (nonZeroDivisors.ne_zero y.2)
  letI : Algebra F K := iF.toAlgebra
  letI : Algebra F R := jF.toAlgebra
  refine ⟨R ⊗[F] K, inferInstance, algebraMap R (R ⊗[F] K),
    (Algebra.TensorProduct.includeRight : K →ₐ[F] R ⊗[F] K).toRingHom, ?_, ?_⟩
  · rw [RingHom.faithfullyFlat_algebraMap_iff]
    infer_instance
  · ext o
    have h₁ : j o = algebraMap F R (algebraMap O F o) := (IsLocalization.lift_eq _ o).symm
    have h₂ : i o = algebraMap F K (algebraMap O F o) := (IsFractionRing.lift_algebraMap hi o).symm
    show algebraMap R (R ⊗[F] K) (j o) = (Algebra.TensorProduct.includeRight : K →ₐ[F] R ⊗[F] K) (i o)
    rw [h₁, h₂, AlgHom.commutes, ← IsScalarTower.algebraMap_apply]

theorem eq_one_of_generic {O K R : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K] [CommRing R]
    [Algebra O R] (hi : Function.Injective (algebraMap O K)) (hj : ∀ a : O, a ≠ 0 → IsUnit (algebraMap O R a))
    {A : Over (Sp O)} [GrpObj A] {M : LB A.left} (hM : M.IsLB) (P : Out.PolAV (Sp K)) {φ : P.A.left ⟶ A.left}
    (h : IsGrpPullback P.A A (spMap (algebraMap O K)) φ) (e : LBIso P.L (M.pull φ)) (x : specO O R ⟶ A)
    (hx : Triv (Out.translDiff A M x)) : x = 1 := by
  obtain ⟨R', _, a, b, ha, hab⟩ := exists_cover _ hi _ hj
  let q : Over.mk (spMap a ≫ (specO O R).hom) ⟶ specO O R := Over.homMk (spMap a) rfl
  have hs : spMap a ≫ (specO O R).hom = spMap b ≫ spMap (algebraMap O K) := by
    show spMap a ≫ spMap (algebraMap O R) = _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hab]
  have h₁ : q ≫ x = 1 := eq_one_of_factor h hM P.isLB e P.ktriv (spMap b) hs _
    (ArtinReduction.exists_isGen_translDiff_comp A M q x hx)
  obtain ⟨_, _⟩ := (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom a)).2 ha
  have : Epi (spMap a) := Flat.epi_of_flat_of_surjective _
  have h₂ : q ≫ x = q ≫ 1 := by rw [h₁, MonObj.comp_one]
  exact Over.OverMorphism.ext ((cancel_epi (spMap a)).1 (congrArg (fun z => z.left) h₂))

theorem tangent_pow {O k : Type} [CommRing O] [CommRing k] [Algebra O k] (A : Over (Sp O)) [GrpObj A] {p : ℕ}
    (hp : (p : k) = 0) (x : specO O (DualNumber k) ⟶ A) (hx : ptMap (TrivSqZeroExt.fstHom O k k) ≫ x = 1) :
    x ^ p = 1 := by
  obtain ⟨w, hw, -⟩ := (TangentPow.pow_eq_scale_and_existsUnique_torsion O A k p x hx).2 hp
  have hm : ∀ n : ℕ, mulN A n = 𝟙 A ^ n := fun n => by
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ, ← ih]; rfl
  have hι : torsion.ι A p ≫ mulN A p = 1 := by
    refine pullback.condition.trans ?_
    rw [toUnit_unique (pullback.snd _ _) (toUnit _)]
    rfl
  rw [hm, MonObj.comp_pow, Category.comp_id] at hι
  rw [← hw, ← MonObj.comp_pow, hι, MonObj.comp_one]

theorem kTriv_of_generic : Out.Laws → ∀ (O K : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [Field K] [IsAlgClosed K] [CharZero K] [Algebra O K], Function.Injective (algebraMap O K) → (∀ q : Ideal O, q.IsPrime → q ≠ ⊥ → ∃ p : ℕ, p.Prime ∧ (p : O) ∈ q) → ∀ (A : Over (Sp O)) [GrpObj A], IsAbelianScheme A → ∀ (g : ℕ), SmoothOfRelativeDimension g A.hom → ∀ M : LB A.left, M.IsLB → Out.Rigidified A M → Out.RelAmple A M → ∀ (P : Out.PolAV (Sp K)) (φ : P.A.left ⟶ A.left), IsGrpPullback P.A A (spMap (algebraMap O K)) φ → LBIso P.L (M.pull φ) → Out.KTriv A M := by
  intro hL O K _ _ _ _ _ _ _ hi hq A _ hA g hg M hM hrig hamp P φ h e
  have := hA.comm
  obtain ⟨d, -, m, s, hs⟩ := (Unif.relAmple_iff_veryAmpleBy O A M hM).1 hamp
  have hproj : IsProjBy A.hom := ⟨_, isLB_pw hM d, m, s, hs⟩
  obtain ⟨L, rfl, ⟨c⟩⟩ := Moduli.cubicalStr_of_triv_theta hL _ A hA M hM hrig (GlobalTheory.T.theorem_of_cube_projective_abelianScheme_affineBase hL O A hA hproj M hM)
  have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} g
  have hgP : P.g = g := H1.dim_unique P.A.hom P.smoothDim
    (MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension g) h.1 hg)
    ((η[P.A]).left (Nonempty.some (inferInstanceAs (Nonempty (Sp K)))))
  have tors : ∀ (n : ℕ), 1 ≤ n → ∀ (T : Over (Sp O)) (x : T ⟶ A), x ^ n = 1 → Triv (Out.translDiff A L.L x) →
      x = 1 := by
    intro n hn T x hxn hx
    have hnK : (n : K) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    obtain ⟨f₁, f₂, f₃⟩ := GlobalTheory.T.finite_flat_surjective_mul_by_n_abelianScheme hL O A hA L.L hM hamp n hn
    refine GlobalTheory.T.eq_one_of_cubWeil_trivial_of_generic O K hi A g hg L c n hn f₁ f₂ ?_ ?_ T x hxn fun T' ρ y hy => ?_
    · rw [← hgP, ← (hL.mulN _ P n hn).2.2.2.2 K (𝟙 _) hnK]
      exact card_torsion h (𝟙 _) (Category.id_comp _).symm n
    · intro y hy hp
      exact eq_one_of_factor h hM P.isLB e P.ktriv (𝟙 _) (Category.id_comp _).symm y
        (CubNondeg.main hL _ A hA L c K _ n hnK f₁ f₂ f₃ y hy hp)
    · refine UU.KerPair.cubWeil_of_gen hL.globalFns _ A hA L c n T' _ y ?_ hy
        (ArtinReduction.exists_isGen_translDiff_comp A L.L ρ x hx)
      rw [← MonObj.comp_pow, hxn, MonObj.comp_one]
  refine GlobalTheory.T.kTriv_of_geometric_points_and_tangents hL O A hA hproj L.L hM fun k _ _ _ => ⟨fun x hx => ?_, fun x hx₀ hx => ?_⟩
  · obtain ⟨n, hn, hxn⟩ := field_torsion hL A hA hM hamp _ (Category.id_comp _).symm x hx
    exact tors n hn _ x hxn hx
  · by_cases hk : RingHom.ker (algebraMap O k) = ⊥
    · refine eq_one_of_generic hi (fun a ha => ?_) hM P h e x hx
      have ha' : algebraMap O k a ≠ 0 := fun h0 => ha (by
        have : a ∈ RingHom.ker (algebraMap O k) := h0
        rwa [hk] at this)
      rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
      exact (congrArg IsUnit ((TrivSqZeroExt.fstHom O k k).commutes a)).mpr ha'.isUnit
    · obtain ⟨p, hp, hpq⟩ := hq _ (RingHom.ker_isPrime _) hk
      have hp0 : (p : k) = 0 := by rw [← map_natCast (algebraMap O k)]; exact hpq
      exact tors p hp.one_le _ x (tangent_pow A hp0 x hx₀) hx

end GlobalTheory.GenericKTriv
