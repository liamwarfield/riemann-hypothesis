module

public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsObjOfUniformisedTripleComplex
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionOfGenerization
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RatioSqEqDetJAut

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AllClassesStOfLandherrOfHasseNorm
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AllClassesOccur
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DatumCommensurablePeriod
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix nonZeroDivisors
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi

namespace GlobalTheory.TwoLattices

open Module

theorem natAbs_det_gram {M κ : Type} [AddCommGroup M] [Fintype κ] [DecidableEq κ] (b : Basis κ ℤ M)
    (B : LinearMap.BilinForm ℤ M) (hB : Function.Bijective B) :
    (Matrix.of fun i k => B (b i) (b k)).det.natAbs = 1 := by
  have h := LinearEquiv.isUnit_det (LinearEquiv.ofBijective B hB) b b.dualBasis
  have e : LinearMap.toMatrix b b.dualBasis (LinearEquiv.ofBijective B hB : M →ₗ[ℤ] _) =
      (Matrix.of fun i k => B (b i) (b k))ᵀ := by
    ext i k
    simp [LinearMap.toMatrix_apply]
  rw [e, Matrix.det_transpose] at h
  exact Int.isUnit_iff_natAbs_eq.mp h

theorem index_similitude {M M' : Type} [AddCommGroup M] [AddCommGroup M'] [Module.Free ℤ M] [Module.Finite ℤ M]
    [Module.Free ℤ M'] [Module.Finite ℤ M'] (B : LinearMap.BilinForm ℤ M) (B' : LinearMap.BilinForm ℤ M')
    (hB : Function.Bijective B) (hB' : Function.Bijective B') (j : M →+ M') (hj : Function.Injective j)
    (n N : ℕ) (hn : finrank ℤ M = n) (hn' : finrank ℤ M' = n)
    (h : ∀ a b, B' (j a) (j b) = (N : ℤ) ^ 2 * B a b) : j.range.index = N ^ n := by
  let b : Basis (Fin n) ℤ M := Module.finBasisOfFinrankEq ℤ M hn
  let b' : Basis (Fin n) ℤ M' := Module.finBasisOfFinrankEq ℤ M' hn'
  let bN : Basis (Fin n) ℤ j.range := b.map (AddMonoidHom.ofInjective hj).toIntLinearEquiv
  have hbN : ∀ i, (bN i : M') = j (b i) := fun i => rfl
  rw [AddSubgroup.index_eq_natAbs_det b' j.range bN, Basis.det_apply]
  set J := b'.toMatrix (fun i => (bN i : M')) with hJ
  have key : Jᵀ * (Matrix.of fun i k => B' (b' i) (b' k)) * J =
      ((N : ℤ) ^ 2) • Matrix.of fun i k => B (b i) (b k) := by
    ext i k
    have e1 : ∀ i, j (b i) = ∑ l, J l i • b' l := fun i => by
      rw [← hbN]
      exact (b'.sum_repr _).symm
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, ← h, e1, Matrix.mul_apply,
      Matrix.transpose_apply, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
      Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have k2 := congrArg (fun X => X.det.natAbs) key
  simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul, Int.natAbs_mul, natAbs_det_gram b B hB,
    natAbs_det_gram b' B' hB', _root_.mul_one, Int.natAbs_pow, Int.natAbs_natCast, Fintype.card_fin] at k2
  have : J.det.natAbs ^ 2 = (N ^ n) ^ 2 := by
    rw [sq, k2]; ring
  exact Nat.pow_left_injective (by norm_num) this

variable {E : Type} [Field E] [NumberField E]

theorem exists_mul_mem {M' V : Type} [AddCommGroup M'] [Module (𝓞 E) M'] [AddCommGroup V] [Module E V]
    [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] (φ' : M' →ₗ[𝓞 E] V)
    (hs : Submodule.span E (Set.range φ') = ⊤) (v : V) : ∃ N : ℕ, 0 < N ∧ ∃ b, φ' b = N • v := by
  have hv : v ∈ Submodule.span E (Set.range φ') := hs ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => obtain ⟨b, rfl⟩ := hx; exact ⟨1, one_pos, b, by simp⟩
  | zero => exact ⟨1, one_pos, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨N, hN, b, hb⟩ := hx
    obtain ⟨K, hK, c, hc⟩ := hy
    refine ⟨N * K, Nat.mul_pos hN hK, K • b + N • c, ?_⟩
    rw [map_add (f := _), map_nsmul, map_nsmul, hb, hc, smul_add, smul_smul, smul_smul, mul_comm K N]
  | smul e x _ hx =>
    obtain ⟨N, hN, b, hb⟩ := hx
    have halg : IsAlgebraic ℤ e :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic e)
    obtain ⟨m, s, hm, hs⟩ := halg.exists_nsmul_eq (S := 𝓞 E)
    refine ⟨m * N, Nat.mul_pos (Nat.pos_of_ne_zero hm) hN, s • b, ?_⟩
    rw [map_smul, hb, ← IsScalarTower.algebraMap_smul E s, ← hs, smul_assoc, smul_comm e N x, mul_smul]

theorem exists_mul_le {M M' V : Type} [AddCommGroup M] [Module (𝓞 E) M] [Module.Finite (𝓞 E) M]
    [AddCommGroup M'] [Module (𝓞 E) M'] [AddCommGroup V] [Module E V]
    [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] (φ : M →ₗ[𝓞 E] V) (φ' : M' →ₗ[𝓞 E] V)
    (hs : Submodule.span E (Set.range φ') = ⊤) : ∃ N : ℕ, 0 < N ∧ ∀ a, ∃ b, φ' b = N • φ a := by
  obtain ⟨s, hS⟩ := Module.Finite.fg_top (R := 𝓞 E) (M := M)
  choose n hn c hc using exists_mul_mem φ' hs
  refine ⟨∏ x ∈ s, n (φ x), Finset.prod_pos fun x _ => hn _, fun a => ?_⟩
  have ha : a ∈ Submodule.span (𝓞 E) (s : Set M) := hS ▸ Submodule.mem_top
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun x => n (φ x)) (Finset.mem_coe.mp hx)
    exact ⟨k • c (φ x), by rw [map_nsmul, hc, smul_smul, hk, mul_comm]⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨b, hb⟩ := hx
    obtain ⟨d, hd⟩ := hy
    exact ⟨b + d, by rw [map_add (f := _), map_add (f := _), hb, hd, smul_add]⟩
  | smul e x _ hx =>
    obtain ⟨b, hb⟩ := hx
    exact ⟨e • b, by rw [map_smul, map_smul, hb, smul_comm]⟩

theorem exists_lift {R M M' V : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] [AddCommGroup V] [Module R V] (φ : M →ₗ[R] V) (φ' : M' →ₗ[R] V)
    (hi : Function.Injective φ') (N : ℕ) (h : ∀ a, ∃ b, φ' b = N • φ a) :
    ∃ j : M →ₗ[R] M', ∀ a, φ' (j a) = N • φ a := by
  choose f hf using h
  refine ⟨⟨⟨f, fun x y => hi ?_⟩, fun c x => hi ?_⟩, hf⟩
  · rw [map_add (f := _), hf, hf, hf, map_add (f := _), smul_add]
  · simp only [RingHom.id_apply]
    rw [map_smul, hf, hf, map_smul, smul_comm]

theorem rank_of_lattice {M : Type} [AddCommGroup M] {g : ℕ} (P : M →+ (Fin g → ℂ)) (hi : Function.Injective P)
    (hd : DiscreteTopology P.range) (hs : Submodule.span ℝ (Set.range P) = ⊤) :
    finrank ℤ M = 2 * g := by
  let L : Submodule ℤ (Fin g → ℂ) := P.range.toIntSubmodule
  haveI : DiscreteTopology L := hd
  haveI : IsZLattice ℝ L := ⟨hs⟩
  have h := ZLattice.rank ℝ L
  have e : M ≃ₗ[ℤ] L := (AddMonoidHom.ofInjective hi).toIntLinearEquiv
  rw [e.finrank_eq, h, Module.finrank_pi_fintype]
  simp [mul_comm]

variable [IsCMField E]

theorem herm_nsmul {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (N : ℕ) (x y : Fin r → E) :
    FD.herm G (N • x) (N • y) = (N : E) ^ 2 * FD.herm G x y := by
  simp only [FD.herm, FD.cc, Pi.smul_apply, nsmul_eq_mul, map_mul, map_natCast, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem form_lift {H : Host E} (D D' : Datum H) {r : ℕ} (ξ : E) (Gm : Matrix (Fin r) (Fin r) E)
    (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (φ' : D'.La →ₗ[𝓞 E] (Fin r → E))
    (h : ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * FD.herm Gm (φ x) (φ y)))
    (h' : ∀ x y, ((D'.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * FD.herm Gm (φ' x) (φ' y)))
    (N : ℕ) (j : D.La → D'.La) (hj : ∀ a, φ' (j a) = N • φ a) (a b : D.La) :
    D'.EF (j a) (j b) = (N : ℤ) ^ 2 * D.EF a b := by
  apply Int.cast_injective (α := ℚ)
  rw [h', hj, hj, herm_nsmul]
  push_cast
  rw [h, ← smul_eq_mul ((N : ℚ) ^ 2), ← map_smul]
  congr 1
  rw [Algebra.smul_def]
  simp only [map_pow, map_natCast]
  ring

theorem hermForm_real_smul {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (t : ℝ) (z w : Fin g → ℂ) :
    hermForm Hm ((t : ℂ) • z) ((t : ℂ) • w) = ((t ^ 2 : ℝ) : ℂ) * hermForm Hm z w := by
  simp only [hermForm, star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    Complex.star_def, Complex.conj_ofReal]
  push_cast
  ring

end GlobalTheory.TwoLattices


open GlobalTheory.TwoLattices in
theorem GlobalTheory.datum_commensurable_period :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D D' : Datum H) (r : ℕ) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (φ' : D'.La →ₗ[𝓞 E] (Fin r → E)) (g : ℕ) (ty : Fin g → (E →+* ℂ)), FD.cc ξ = -ξ → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, FD.cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * FD.herm Gm (φ x) (φ y))) → (Function.Injective φ' ∧ Submodule.span E (Set.range φ') = ⊤ ∧ (∀ a b, FD.cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((D'.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * FD.herm Gm (φ' x) (φ' y))) → ∀ P, IsPeriod D ty P → ∃ (N : ℕ) (j : D.La →ₗ[𝓞 E] D'.La) (j' : D'.La →ₗ[𝓞 E] D.La) (P' : D'.La →+ (Fin g → ℂ)), (0 < N ∧ (∀ a, j' (j a) = (N ^ 2) • a) ∧ (∀ a, j (j' a) = (N ^ 2) • a) ∧ (∀ a b, D'.EF (j a) (j b) = (N : ℤ) ^ 2 * D.EF a b) ∧ (∀ a b, D.EF (j' a) (j' b) = (N : ℤ) ^ 2 * D'.EF a b) ∧ Nat.card (D'.La ⧸ LinearMap.range j) = N ^ (2 * g)) ∧ IsPeriod D' ty P' ∧ (∀ a, P' (j a) = (N : ℂ) • P a) ∧ ∀ a, P (j' a) = (N : ℂ) • P' a := by
  intro E _ _ _ H D D' r ξ Gm φ φ' g ty _ ⟨hi, hs, _, _, hE⟩ ⟨hi', hs', _, _, hE'⟩ P ⟨hPl, hPi, hPd, hPs, Hm, hH, hpos, hIm⟩
  haveI := D.fin
  haveI := D'.fin
  obtain ⟨N₁, hN₁, h₁⟩ := exists_mul_le φ φ' hs'
  obtain ⟨N₂, hN₂, h₂⟩ := exists_mul_le φ' φ hs
  set N := N₁ * N₂ with hNdef
  have hN : 0 < N := Nat.mul_pos hN₁ hN₂
  obtain ⟨j, hj⟩ := exists_lift φ φ' hi' N fun a => by
    obtain ⟨b, hb⟩ := h₁ a
    exact ⟨N₂ • b, by rw [map_nsmul, hb, smul_smul, mul_comm]⟩
  obtain ⟨j', hj'⟩ := exists_lift φ' φ hi N fun a => by
    obtain ⟨b, hb⟩ := h₂ a
    exact ⟨N₁ • b, by rw [map_nsmul, hb, smul_smul]⟩
  clear_value N
  have hNE : (N : E) ≠ 0 := by exact_mod_cast hN.ne'
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have c₁ : ∀ a, j' (j a) = (N ^ 2) • a := fun a => hi (by rw [hj', hj, map_nsmul, smul_smul, sq])
  have c₂ : ∀ a, j (j' a) = (N ^ 2) • a := fun a => hi' (by rw [hj, hj', map_nsmul, smul_smul, sq])
  have f₁ := form_lift D D' ξ Gm φ φ' hE hE' N j hj
  have f₂ := form_lift D' D ξ Gm φ' φ hE' hE N j' hj'
  have cancel : ∀ v w : Fin r → E, N • v = N • w → v = w := fun v w h => by
    rw [← Nat.cast_smul_eq_nsmul E, ← Nat.cast_smul_eq_nsmul E] at h
    exact smul_right_injective _ hNE h
  have ji : Function.Injective j := fun a b h => hi (cancel _ _ (by rw [← hj, ← hj, h]))
  have ji' : Function.Injective j' := fun a b h => hi' (cancel _ _ (by rw [← hj', ← hj', h]))
  let P' : D'.La →+ (Fin g → ℂ) :=
    { toFun := fun a => (N : ℂ)⁻¹ • P (j' a)
      map_zero' := by simp
      map_add' := fun a b => by simp only [map_add (f := _), smul_add] }
  have hP' : ∀ a, P' a = (N : ℂ)⁻¹ • P (j' a) := fun _ => rfl
  have p₂ : ∀ a, P (j' a) = (N : ℂ) • P' a := fun a => by
    rw [hP', smul_smul, mul_inv_cancel₀ hNC, one_smul]
  have p₁ : ∀ a, P' (j a) = (N : ℂ) • P a := fun a => by
    rw [hP', c₁, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    congr 1
    push_cast
    field_simp
  have P'i : Function.Injective P' := fun a b h => ji' (hPi (by rw [p₂, p₂, h]))
  have P'd : DiscreteTopology P'.range := by
    let f : P'.range → P.range := fun x => ⟨(N : ℂ) • (x : Fin g → ℂ), by
      obtain ⟨a, ha⟩ := x.2
      exact ⟨j' a, by rw [p₂, ha]⟩⟩
    refine DiscreteTopology.of_continuous_injective (f := f) ?_ ?_
    · exact Continuous.subtype_mk (continuous_subtype_val.const_smul (N : ℂ)) _
    · intro x y h
      exact Subtype.ext (smul_right_injective _ hNC (congrArg Subtype.val h))
  have P's : Submodule.span ℝ (Set.range P') = ⊤ := by
    rw [eq_top_iff, ← hPs, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    have : P a = (N : ℝ)⁻¹ • P' (j a) := by
      rw [p₁]
      ext i
      simp only [Pi.smul_apply, Complex.real_smul, smul_eq_mul]
      push_cast
      field_simp
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  have hper : IsPeriod D' ty P' := by
    refine ⟨fun a x i => ?_, P'i, P'd, P's, Hm, hH, hpos, fun x y => ?_⟩
    · simp only [hP', map_smul, Pi.smul_apply, hPl, smul_eq_mul]
      ring
    · have e : ((N : ℂ))⁻¹ = (((N : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
      rw [hP', hP', e, hermForm_real_smul, Complex.im_ofReal_mul, hIm, f₂]
      push_cast
      field_simp
  haveI : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) _
  haveI : Module.Finite ℤ D'.La := Module.Finite.trans (𝓞 E) _
  haveI : Module.IsTorsionFree ℤ D.La := hPi.moduleIsTorsionFree P (fun c x => map_zsmul P c x)
  haveI : Module.IsTorsionFree ℤ D'.La := P'i.moduleIsTorsionFree P' (fun c x => map_zsmul P' c x)
  refine ⟨N, j, j', P', ⟨hN, c₁, c₂, f₁, f₂, ?_⟩, hper, p₁, p₂⟩
  exact index_similitude D.EF D'.EF D.unimod D'.unimod j.toAddMonoidHom ji (2 * g) N
    (rank_of_lattice P hPi hPd hPs) (rank_of_lattice P' P'i P'd P's) f₁
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniformisedQuotientOfCommensurable
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix nonZeroDivisors
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi

namespace GlobalTheory.CommensurableQuotient

theorem card_range_eq {R M Q : Type} [Ring R] [AddCommGroup M] [Module R M] [Group Q]
    (φ : Multiplicative M →* Q) (p : Submodule R M) (h : ∀ a, φ (Multiplicative.ofAdd a) = 1 ↔ a ∈ p) :
    Nat.card φ.range = Nat.card (M ⧸ p) := by
  have e : φ.ker = AddSubgroup.toSubgroup p.toAddSubgroup := Subgroup.ext fun a => h a.toAdd
  rw [← Subgroup.index_ker, e, AddSubgroup.index_toSubgroup]
  rfl

theorem exists_point_lift {k : Type} [Field k] [IsAlgClosed k] {A B : Over (Sp k)} (ψ : A ⟶ B) [IsFinite ψ.left]
    [Surjective ψ.left] (c : 𝟙_ (Over (Sp k)) ⟶ B) : ∃ d : 𝟙_ (Over (Sp k)) ⟶ A, d ≫ ψ = c := by
  obtain ⟨u, hu⟩ := H1.SectionDivision.exists_section (k := k) (pullback.snd ψ.left c.left)
  have hb : (u ≫ pullback.fst ψ.left c.left) ≫ ψ.left = c.left := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hu]; exact Category.id_comp _
  have hw : (u ≫ pullback.fst ψ.left c.left) ≫ A.hom = (𝟙_ (Over (Sp k))).hom := by
    rw [← Over.w ψ, ← Category.assoc, hb]; exact Over.w c
  exact ⟨Over.homMk _ hw, Over.OverMorphism.ext hb⟩

theorem smoothDim_of_etale {k : Type} [Field k] {A B : Over (Sp k)} (ψ : A ⟶ B) [Etale ψ.left] [Smooth B.hom]
    [GeometricallyConnected B.hom] (x : A.left) {g : ℕ} (hA : SmoothOfRelativeDimension g A.hom) :
    SmoothOfRelativeDimension g B.hom := by
  have : ConnectedSpace (Sp k) := inferInstanceAs (ConnectedSpace (PrimeSpectrum k))
  have : ConnectedSpace B.left := GeometricallyConnected.connectedSpace B.hom B.hom.isOpenMap
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected B.hom (ψ.left x)
  have h : SmoothOfRelativeDimension (0 + d) (ψ.left ≫ B.hom) := inferInstance
  rw [Over.w ψ, zero_add] at h
  rwa [H1.dim_unique _ hA h x]

theorem isHolTo_smul_comp {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X Y : Scheme.{0}}
    {y : V → (Sp ℂ ⟶ X)} (h : IsHolTo Set.univ y) (c : ℂ) (φ : X ⟶ Y) :
    IsHolTo Set.univ (fun z => y (c • z) ≫ φ) := by
  intro U f
  obtain ⟨h₁, h₂⟩ := h (φ ⁻¹ᵁ U) ((φ.app U).hom f)
  have hc : Differentiable ℂ (fun z : V => c • z) := differentiable_id.const_smul c
  refine ⟨h₁.preimage hc.continuous, ?_⟩
  simp only [← valAt'_comp]
  exact h₂.comp hc.differentiableOn fun z hz => hz

theorem exists_weilIs (hL : Out.Laws) {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {k : Type}
    [Field k] (t : SAB H (Sp k)) [IsProper t.G.hom] {g : ℕ} (hd : SmoothOfRelativeDimension g t.G.hom)
    (ha : Out.RelAmple t.G t.PP.L) (hk : Out.KTriv t.G t.PP.L) (n : ℕ) {T : Over (Sp k)} (x y : T ⟶ t.G)
    (hx : x ^ n = 1) (hy : y ^ n = 1) : ∃ c, Out.WeilIs t.G t.PP.L n x y c := by
  obtain ⟨-, ws, gs', -⟩ := t.sym
  let P : Out.PolAV (Sp k) :=
    { A := t.G, g := g, smoothDim := hd, L := t.PP.L, isLB := t.PP.isLB, ample := ha, ktriv := hk
      isAb := AbelianSchemeGerms.isAbelianScheme_of_proper t.G t.semi
      rigid := ⟨t.PP.rig, t.PP.rigGen⟩
      sym := fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff ws).1 gs') _⟩ }
  exact ((hL.weil _ P n T).1 x y hx hy).exists

end GlobalTheory.CommensurableQuotient

namespace GlobalTheory

open CommensurableQuotient

theorem exists_uniformised_quotient_of_commensurable : Out.Laws → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (t : SAB H (Sp k)) (g p : ℕ) (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ t.G)), 0 < p → IsProper t.G.hom → SmoothOfRelativeDimension g t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → (∀ x ∈ C, ∀ a, x ≫ t.act.act a ∈ C) → (∀ x ∈ C, x ^ p ^ 2 = 1) → (∀ x ∈ C, ∀ y ∈ C, Out.WeilIs t.G t.PP.L ((p ^ 2 : ℕ) : ℤ) x y 1) → Nat.card C = p ^ (2 * g) → ∃ (t' : SAB H (Sp k)) (ψ : t.G ⟶ t'.G), IsProper t'.G.hom ∧ Out.RelAmple t'.G t'.PP.L ∧ Out.KTriv t'.G t'.PP.L ∧ IsMonHom ψ ∧ IsFinite ψ.left ∧ Etale ψ.left ∧ Surjective ψ.left ∧ (∀ x : 𝟙_ (Over (Sp k)) ⟶ t.G, x ≫ ψ = 1 ↔ x ∈ C) ∧ (∀ a, t.act.act a ≫ ψ = ψ ≫ t'.act.act a) ∧ LBIso (lbPow t.PP.L (p ^ 2)) (t'.PP.L.pull ψ.left)) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D D' : Datum H) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)) (P' : D'.La →+ (Fin g → ℂ)) (N : ℕ) (j : D.La →ₗ[𝓞 E] D'.La) (j' : D'.La →ₗ[𝓞 E] D.La) (t : SAB H (Sp ℂ)) (e : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ t.G)), D'.p = D.p → D'.q = D.q → (0 < N ∧ (∀ a, j' (j a) = (N ^ 2) • a) ∧ (∀ a, j (j' a) = (N ^ 2) • a) ∧ (∀ a b, D'.EF (j a) (j b) = (N : ℤ) ^ 2 * D.EF a b) ∧ (∀ a b, D.EF (j' a) (j' b) = (N : ℤ) ^ 2 * D'.EF a b) ∧ Nat.card (D'.La ⧸ LinearMap.range j) = N ^ (2 * g)) → IsPeriod D ty P → IsPeriod D' ty P' → (∀ a, P' (j a) = (N : ℂ) • P a) → (∀ a, P (j' a) = (N : ℂ) • P' a) → (IsProper t.G.hom ∧ SmoothOfRelativeDimension g t.G.hom ∧ Out.RelAmple t.G t.PP.L ∧ Out.KTriv t.G t.PP.L ∧ DetCond D t.act (𝟙 (Sp ℂ)) H.rt0 ∧ (∀ z w, e (z + w) = e z * e w) ∧ Function.Surjective e ∧ (∀ z, e z = 1 ↔ z ∈ P.range) ∧ (∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ t.act.act a) ∧ IsHolTo Set.univ (fun z => (e z).left) ∧ ∀ (k : ℕ) (a b : D.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D.EF a b : ℂ) / k) → Out.WeilIs t.G t.PP.L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P b)) (unitOn c)) → ∃ (t' : SAB H (Sp ℂ)) (e' : (Fin g → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ t'.G)), (IsProper t'.G.hom ∧ SmoothOfRelativeDimension g t'.G.hom ∧ Out.RelAmple t'.G t'.PP.L ∧ Out.KTriv t'.G t'.PP.L ∧ DetCond D' t'.act (𝟙 (Sp ℂ)) H.rt0 ∧ (∀ z w, e' (z + w) = e' z * e' w) ∧ Function.Surjective e' ∧ (∀ z, e' z = 1 ↔ z ∈ P'.range) ∧ (∀ (a : 𝓞 E) z, e' (fun k => ty k (a : E) * z k) = e' z ≫ t'.act.act a) ∧ IsHolTo Set.univ (fun z => (e' z).left) ∧ ∀ (k : ℕ) (a b : D'.La) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a b : ℂ) / k) → Out.WeilIs t'.G t'.PP.L k (e' ((k : ℂ)⁻¹ • P' a)) (e' ((k : ℂ)⁻¹ • P' b)) (unitOn c)) := by
  intro hL hQ E _ _ _ H D D' g ty P P' N j j' t e hp hq ⟨hN, _, _, _, hE, hcard⟩ _ hP' hj hj'
    ⟨hpr, hsm, ham, hkt, hdet, hadd, hsurj, hker, hlin, hhol, hweil⟩
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have e0 : e 0 = 1 := (hker 0).2 (zero_mem _)
  let eh : Multiplicative (Fin g → ℂ) →* (𝟙_ (Over (Sp ℂ)) ⟶ t.G) :=
    { toFun := fun z => e z.toAdd, map_one' := e0, map_mul' := fun z w => hadd _ _ }
  have epow : ∀ (n : ℕ) z, e z ^ n = e ((n : ℂ) • z) := fun n z => by
    rw [Nat.cast_smul_eq_nsmul]
    exact (map_pow eh (Multiplicative.ofAdd z) n).symm
  have esub : ∀ z w, e z = e w ↔ z - w ∈ P.range := fun z w => by
    rw [← hker, ← mul_inv_eq_one, ← div_eq_mul_inv]
    exact Eq.congr_left (map_div eh (Multiplicative.ofAdd z) (Multiplicative.ofAdd w)).symm
  let φ : Multiplicative D'.La →* (𝟙_ (Over (Sp ℂ)) ⟶ t.G) :=
    { toFun := fun a => e ((N : ℂ)⁻¹ • P' a.toAdd)
      map_one' := by rw [toAdd_one, map_zero, smul_zero, e0]
      map_mul' := fun a b => by rw [toAdd_mul, map_add (f := _), smul_add, hadd] }
  have hmem : ∀ x, x ∈ φ.range ↔ ∃ a, e ((N : ℂ)⁻¹ • P' a) = x := fun x => Iff.rfl
  have hrw : ∀ (k : ℕ) a, ((k * N ^ 2 : ℕ) : ℂ)⁻¹ • P (j' a) = (N : ℂ)⁻¹ • (k : ℂ)⁻¹ • P' a := fun k a => by
    rw [hj', smul_smul, smul_smul]
    congr 1
    push_cast
    field_simp
  have hw : ∀ (k : ℕ) (a b : D'.La) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D'.EF a b : ℂ) / k) →
      Out.WeilIs t.G t.PP.L ((k * N ^ 2 : ℕ) : ℤ) (e ((N : ℂ)⁻¹ • (k : ℂ)⁻¹ • P' a))
        (e ((N : ℂ)⁻¹ • (k : ℂ)⁻¹ • P' b)) (unitOn c) := fun k a b c hk hc => by
    rw [← hrw, ← hrw]
    refine hweil (k * N ^ 2) (j' a) (j' b) c (by positivity) (hc.trans ?_)
    rw [hE]
    congr 1
    push_cast
    field_simp
  obtain ⟨t', ψ, hpr', ham', hkt', hψ, hfin, het, hsj, hkψ, hact, hiso⟩ :=
    hQ E H ℂ t g N φ.range hN hpr hsm ham hkt
      (by
        intro x hx c
        obtain ⟨a, rfl⟩ := (hmem x).1 hx
        refine (hmem _).2 ⟨c • a, ?_⟩
        rw [← hlin]
        congr 1
        ext i
        simp only [Pi.smul_apply, smul_eq_mul, hP'.1]
        ring)
      (by
        intro x hx
        obtain ⟨a, rfl⟩ := (hmem x).1 hx
        rw [epow, hker]
        refine ⟨j' a, ?_⟩
        rw [hj', smul_smul]
        congr 1
        push_cast
        field_simp)
      (by
        intro x hx y hy
        obtain ⟨a, rfl⟩ := (hmem x).1 hx
        obtain ⟨b, rfl⟩ := (hmem y).1 hy
        have h := hw 1 a b 1 one_pos (by
          rw [Units.val_one, Nat.cast_one, div_one, ← Complex.exp_int_mul_two_pi_mul_I (-(D'.EF a b))]
          congr 1
          push_cast
          ring)
        rw [_root_.one_mul, Nat.cast_one, inv_one, one_smul, one_smul, show unitOn (1 : ℂˣ) = 1 from map_one _] at h
        exact h)
      (by
        rw [← hcard]
        refine card_range_eq φ _ fun a => (hker _).trans ⟨?_, ?_⟩
        · rintro ⟨b, hb⟩
          refine ⟨b, hP'.2.1 ?_⟩
          rw [hj, hb, smul_inv_smul₀ hN']
          rfl
        · rintro ⟨b, rfl⟩
          exact ⟨b, by rw [toAdd_ofAdd, hj, inv_smul_smul₀ hN']⟩)
  have hA := AbelianSchemeGerms.isAbelianScheme_of_proper t.G t.semi
  have hB := AbelianSchemeGerms.isAbelianScheme_of_proper t'.G t'.semi
  have := hB.smooth
  have := hB.geomConnected
  have hsm' : SmoothOfRelativeDimension g t'.G.hom :=
    smoothDim_of_etale ψ ((e 0).left (default : PrimeSpectrum ℂ)) hsm
  have hker' : ∀ z, e ((N : ℂ)⁻¹ • z) ≫ ψ = 1 ↔ z ∈ P'.range := fun z => by
    rw [hkψ, hmem]
    constructor
    · rintro ⟨a, ha⟩
      obtain ⟨b, hb⟩ := (esub _ _).1 ha
      refine ⟨a - j b, ?_⟩
      rw [map_sub, hj, hb, ← smul_sub, smul_inv_smul₀ hN', sub_sub_cancel]
    · rintro ⟨a, rfl⟩
      exact ⟨a, rfl⟩
  refine ⟨t', fun z => e ((N : ℂ)⁻¹ • z) ≫ ψ, hpr', hsm', ham', hkt', fun τ => ?_, fun z w => ?_, fun y => ?_, hker',
    fun a z => ?_, isHolTo_smul_comp hhol _ ψ.left, fun k a b c hk hc => ?_⟩
  · rw [hp, hq, ← LieEtale.lieMult_iff_of_etale _ _ _ _ ψ t.act t'.act hψ het hact,
      ← LieEtale.lieMult_iff_of_etale _ _ _ _ ψ t.act t'.act hψ het hact]
    exact hdet τ
  · simp only [smul_add, hadd, MonObj.mul_comp]
  · obtain ⟨x, rfl⟩ := exists_point_lift ψ y
    obtain ⟨z, rfl⟩ := hsurj x
    exact ⟨(N : ℂ) • z, by simp only [inv_smul_smul₀ hN']⟩
  · beta_reduce
    rw [Category.assoc, ← hact, ← Category.assoc, ← hlin]
    congr 2
    ext i
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  · have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
    have htor : ∀ a, (e ((N : ℂ)⁻¹ • (k : ℂ)⁻¹ • P' a) ≫ ψ) ^ k = 1 := fun a => by
      rw [← MonObj.pow_comp, epow, smul_comm (k : ℂ), smul_inv_smul₀ hk', hker']
      exact ⟨a, rfl⟩
    obtain ⟨c', hc'⟩ := exists_weilIs hL t' hsm' ham' hkt' k _ _ (htor a) (htor b)
    have h₁ := (weilIs_along_hom hL.globalFns _ _ _ ψ _ _ _ _ _ _ _ c' c' hA hB t.PP.isLB t'.PP.isLB hψ hiso hc').1
    have h₂ := hw k a b c hk hc
    rw [Nat.cast_mul] at h₂
    exact CommutatorPairing.weilIs_unique hL.globalFns hA t.PP.isLB h₁ h₂ ▸ hc'

end GlobalTheory
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix nonZeroDivisors
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi

theorem GlobalTheory.all_classes_occur :
    (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G G' : Matrix (Fin r) (Fin r) E), (∀ a b, FD.cc (G a b) = G b a) → (∀ a b, FD.cc (G' a b) = G' b a) → G.det ≠ 0 → G'.det ≠ 0 → (∀ τ : E →+* ℂ, ∃ p0 : ℕ, (∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ FD.gram τ G Q = Matrix.diagonal fun a : Fin r => ((FD.sgn p0 (a : ℕ) : ℝ) : ℂ)) ∧ (∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧ FD.gram τ G' Q = Matrix.diagonal fun a : Fin r => ((FD.sgn p0 (a : ℕ) : ℝ) : ℂ))) → (∃ z : E, G'.det = z * FD.cc z * G.det) → ∃ ga : GL (Fin r) E, ∀ x y, FD.herm G ((ga : Matrix (Fin r) (Fin r) E) *ᵥ x) ((ga : Matrix (Fin r) (Fin r) E) *ᵥ y) = FD.herm G' x y) → (∀ (F : Type) [Field F] [NumberField F] (δ x : F), δ ≠ 0 → x ≠ 0 → (∀ σ : F →+* ℝ, ∃ a b : ℝ, σ x = a ^ 2 - σ δ * b ^ 2) → (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F), ∃ a b : v.adicCompletion F, algebraMap F (v.adicCompletion F) x = a ^ 2 - algebraMap F (v.adicCompletion F) δ * b ^ 2) → ∃ a b : F, x = a ^ 2 - δ * b ^ 2) → Out.Laws → (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (t : SAB H (Sp k)) (g p : ℕ) (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ t.G)), 0 < p → IsProper t.G.hom → SmoothOfRelativeDimension g t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → (∀ x ∈ C, ∀ a, x ≫ t.act.act a ∈ C) → (∀ x ∈ C, x ^ p ^ 2 = 1) → (∀ x ∈ C, ∀ y ∈ C, Out.WeilIs t.G t.PP.L ((p ^ 2 : ℕ) : ℤ) x y 1) → Nat.card C = p ^ (2 * g) → ∃ (t' : SAB H (Sp k)) (ψ : t.G ⟶ t'.G), IsProper t'.G.hom ∧ Out.RelAmple t'.G t'.PP.L ∧ Out.KTriv t'.G t'.PP.L ∧ IsMonHom ψ ∧ IsFinite ψ.left ∧ Etale ψ.left ∧ Surjective ψ.left ∧ (∀ x : 𝟙_ (Over (Sp k)) ⟶ t.G, x ≫ ψ = 1 ↔ x ∈ C) ∧ (∀ a, t.act.act a ≫ ψ = ψ ≫ t'.act.act a) ∧ LBIso (lbPow t.PP.L (p ^ 2)) (t'.PP.L.pull ψ.left)) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (U : FamilyUnif Xo σ ty), l.A = 1 → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → ∀ (D' : Datum H) (f : ℕ → D.La →ₗ[𝓞 E] D'.La), D'.p = D.p → D'.q = D.q → (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n * m) a = f n a + n • e) ∧ (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e) → (∀ n : ℕ, 0 < n → ∀ a a', (n : ℤ) ∣ D'.EF (f n a) (f n a') - D.EF a a') → ∃ (i : Fin U.n) (gam : D'.La ≃ₗ[𝓞 E] (U.Di i).La), (∀ a a', (U.Di i).EF (gam a) (gam a') = D'.EF a a') ∧ ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ∃ e, gam (f l.M a) = U.t i a + l.M • e := by
  intro hL hN hLaw hQ E _ _ _ H D l Xo σ g ty U hA hσ hty D' f hp hq hf hE
  let i₀ : Fin U.n := ⟨0, U.n_pos⟩
  obtain ⟨hp₀, hq₀⟩ := U.sig i₀
  have hξ : FD.cc (H.rt : E) = -(H.rt : E) := by
    have h2 : (H.rt : E) ^ 2 = -(H.d : E) := by
      have := congrArg (fun a : 𝓞 E => (a : E)) H.rt_sq
      simpa using this
    have h3 : (FD.cc (H.rt : E)) ^ 2 = (H.rt : E) ^ 2 := by
      unfold FD.cc
      rw [← map_pow, h2, map_neg, map_natCast]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h3 with h | h
    · exfalso
      obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
      have h4 : starRingEnd ℂ (τ (H.rt : E)) = τ (H.rt : E) := by
        rw [← IsCMField.complexEmbedding_complexConj]
        exact congrArg τ h
      obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 h4
      have h5 := congrArg τ h2
      rw [map_pow, hr, map_neg, map_natCast] at h5
      have h6 : r ^ 2 = -(H.d : ℝ) := by exact_mod_cast h5
      have h7 : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
      nlinarith [sq_nonneg r]
    · exact h
  have hξ0 : (H.rt : E) ≠ 0 := by
    intro h
    have := congrArg (fun a : 𝓞 E => (a : E)) H.rt_sq
    simp only [h, RingOfIntegers.coe_eq_algebraMap, map_pow, map_neg, map_natCast] at this
    have h2 : (H.d : E) = 0 := by
      simpa using this
    exact H.d_prime.ne_zero (by exact_mod_cast h2)
  obtain ⟨Gm, φ, hφ⟩ := GlobalTheory.exists_herm_coord_of_datum E H (U.Di i₀) (H.rt : E) hξ hξ0 _ rfl
  obtain ⟨φ', hφ'⟩ := GlobalTheory.T.hermitian_forms_same_signature_same_space hL hN E H (U.Di i₀) D' _ _ Gm φ (hp.trans hp₀.symm) (hq.trans hq₀.symm) hξ hφ
  obtain ⟨hg, P₀, hP₀⟩ := (GlobalTheory.T.typeFn_period_exist_moduli_nonempty E H (U.Di i₀)).2.1 g ty (by rw [hp₀, hq₀]; exact hty)
  rw [hp₀, hq₀] at hg
  obtain ⟨N, j, j', P', hj, hP', h₁, h₂⟩ :=
    GlobalTheory.datum_commensurable_period E H (U.Di i₀) D' _ _ Gm φ φ' g ty hξ hφ hφ' P₀ hP₀
  obtain ⟨t₀, e₀, -, -, ht₀⟩ := GlobalTheory.T.exists_universal_fibre_uniformised_triple E H D l Xo σ g ty U i₀ P₀ hσ hg hP₀
  obtain ⟨t, e, ht⟩ := GlobalTheory.exists_uniformised_quotient_of_commensurable hLaw hQ E H (U.Di i₀) D' g ty P₀ P' N j j' t₀ e₀
    (hp.trans hp₀.symm) (hq.trans hq₀.symm) hj hP₀ hP' h₁ h₂ ht₀
  obtain ⟨o, m, hm⟩ := GlobalTheory.T.exists_obj_of_uniformised_triple_complex hLaw E H D D' l σ g ty P' t e f hA hσ hp hq hP' ht hf hE
  obtain ⟨y, ⟨hy, ⟨om⟩⟩, -⟩ := Xo.rep (Sp ℂ) (spMap σ) inferInstance o
  obtain ⟨i, P, hP, rfl⟩ := U.onto y hy
  obtain ⟨n, hn⟩ : ∃ n : SABMap t Xo.univ.t (U.u i P), n.φ = m.φ ≫ om.toSABMap.φ := by
    have := sabComp pullCubComp E H _ _ _ _ _ _ _ _ om.toSABMap m
    rwa [Category.id_comp] at this
  obtain ⟨h, gam, hh, hgam, hiso⟩ := GlobalTheory.T.familyUnif_fibre_lattice_eq_of_pullback E H D l Xo σ g ty U i P D' P' t e n hP hP' ht
  refine ⟨i, gam, hiso, fun a ha => ?_⟩
  have hM : (l.M : ℂ) ≠ 0 := by
    have := l.three_le
    exact_mod_cast (by omega : l.M ≠ 0)
  have k₁ : U.ex i P ((l.M : ℂ)⁻¹ • P (gam (f l.M a))) = U.ex i P ((l.M : ℂ)⁻¹ • P (U.t i a)) := by
    apply Over.OverMorphism.ext
    rw [← U.ex_eta i P hP a ha, hgam, ← map_smul, ← hh, hn, ← Category.assoc, hm a ha, om.eta, Over.comp_left]
    congr 1
  have k₂ : U.ex i P ((l.M : ℂ)⁻¹ • P (gam (f l.M a)) - (l.M : ℂ)⁻¹ • P (U.t i a)) = 1 := by
    have := U.ex_add i P hP ((l.M : ℂ)⁻¹ • P (gam (f l.M a)) - (l.M : ℂ)⁻¹ • P (U.t i a))
      ((l.M : ℂ)⁻¹ • P (U.t i a))
    rw [sub_add_cancel, k₁] at this
    exact (right_eq_mul.1 this)
  obtain ⟨b, hb⟩ := (U.ex_ker i P hP _).1 k₂
  refine ⟨b, hP.2.1 ?_⟩
  rw [map_add (f := _), map_nsmul, hb, ← Nat.cast_smul_eq_nsmul ℂ, ← smul_sub, smul_smul, mul_inv_cancel₀ hM, one_smul]
  abel
end

theorem GlobalTheory.allClassesSt_of_landherr_of_hasseNorm :
    GlobalTheory.Published.LandherrSt → GlobalTheory.Published.HasseNormSt → GlobalTheory.AllClassesSt :=
  fun hL hN => GlobalTheory.all_classes_occur hL hN GlobalTheory.abelianSchemeLaws_all.1 (GlobalTheory.T.exists_heckeQuotient_principal_triple GlobalTheory.abelianSchemeLaws_all.1)

theorem GlobalTheory.allClassesSt_of_hasseNorm : GlobalTheory.Published.HasseNormSt → GlobalTheory.AllClassesSt :=
  fun hN => GlobalTheory.allClassesSt_of_landherr_of_hasseNorm
    (GlobalTheory.Published.landherrSt_of_landherr (GlobalTheory.LocalQuad.landherr_of_hasseNormSt hN)) hN
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeDatumOfSelfDualLatticeStatement
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_latticeDatum_of_selfDual_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (r : ℕ) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (Λ' : Submodule (𝓞 E) (Fin r → E)), cc ξ = -ξ → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * herm Gm (φ x) (φ y))) → Λ'.FG → Submodule.span E (Λ' : Set (Fin r → E)) = ⊤ → (∀ v : Fin r → E, (∀ y ∈ Λ', ∃ n : ℤ, Algebra.trace ℚ E (ξ * herm Gm v y) = n) ↔ v ∈ Λ') → ∃ (D' : Datum H) (φ' : D'.La →ₗ[𝓞 E] (Fin r → E)), D'.p = D.p ∧ D'.q = D.q ∧ LinearMap.range φ' = Λ' ∧ (Function.Injective φ' ∧ Submodule.span E (Set.range φ') = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((D'.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * herm Gm (φ' x) (φ' y))) := by
  first | exact @GlobalTheory.LatticeDatum.exists_datum_of_selfDual | exact GlobalTheory.LatticeDatum.exists_datum_of_selfDual | (intros; apply GlobalTheory.LatticeDatum.exists_datum_of_selfDual <;> assumption)
end

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

theorem GlobalTheory.selfDual_lattice_occurs : GlobalTheory.Published.HasseNormSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (σ' : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ' ty) (r : ℕ) (M : ModelsOf F r) (ξ₀ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : Dw.La →ₗ[𝓞 E] (Fin r → E)) (Λ' : Submodule (𝓞 E) (Fin r → E)) (f : ℕ → Dw.La →ₗ[𝓞 E] Λ'), l.A = 1 → σ' (baseKA l).ρ = H.rt0 → IsTypeFn H Dw.p Dw.q ty → ModelBase M → (∀ k, (M.X k).Gm = Gm ∧ (M.X k).ξ0 = ξ₀) → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((Dw.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (-ξ₀ * herm Gm (φ x) (φ y))) → Λ'.FG → Submodule.span E (Λ' : Set (Fin r → E)) = ⊤ → (∀ v : Fin r → E, (∀ y ∈ Λ', ∃ n : ℤ, Algebra.trace ℚ E (-ξ₀ * herm Gm v y) = n) ↔ v ∈ Λ') → (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ v, f (n * m) a = f n a + n • v) → (∀ n : ℕ, 0 < n → (∀ a, (∃ v, f n a = n • v) ↔ ∃ v, a = n • v) ∧ ∀ a', ∃ a v, a' = f n a + n • v) → (∀ n : ℕ, 0 < n → ∀ a a', ∃ z : ℤ, Algebra.trace ℚ E (-ξ₀ * herm Gm (f n a) (f n a')) - (Dw.EF a a' : ℤ) = n * z) → ∃ (k : Fin F.n) (γ : GL (Fin r) E), (∀ u v, herm Gm ((γ : Matrix (Fin r) (Fin r) E) *ᵥ u) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) = herm Gm u v) ∧ (∀ v, v ∈ Λ' ↔ (γ : Matrix (Fin r) (Fin r) E) *ᵥ v ∈ (M.X k).Λ) ∧ ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La), ∃ w ∈ (M.X k).Λ, (γ : Matrix (Fin r) (Fin r) E) *ᵥ (f l.M a : Fin r → E) = (M.φ k (F.t k a) : Fin r → E) + l.M • w := by
  intro hH E _ _ _ H Dw l Xo σ' g ty F r M ξ₀ Gm φ Λ' f hA hσ hty hM hk hφ hfg hsp hsd hc hb hi
  have hξ : cc (-ξ₀) = -(-ξ₀) := by
    have h := (M.X ⟨0, F.n_pos⟩).ξ0_im
    rw [(hk _).2] at h
    unfold cc at h ⊢
    rw [map_neg, h]
  obtain ⟨D', φ', hp, hq, hr, hφ'⟩ := GlobalTheory.T.exists_latticeDatum_of_selfDual_lattice E H Dw r (-ξ₀) Gm φ Λ' hξ hφ hfg hsp hsd
  let e : D'.La ≃ₗ[𝓞 E] Λ' := (LinearEquiv.ofInjective φ' hφ'.1).trans (LinearEquiv.ofEq _ _ hr)
  have he : ∀ x, φ' (e.symm x) = (x : Fin r → E) := fun x => by
    have : ∀ y, ((e y : Λ') : Fin r → E) = φ' y := fun y => rfl
    rw [← this, e.apply_symm_apply]
  obtain ⟨k, gam, hg1, hg2⟩ := GlobalTheory.allClassesSt_of_hasseNorm hH E H Dw l Xo σ' g ty F hA hσ hty D'
    (fun n => e.symm.toLinearMap ∘ₗ f n) hp hq
    ⟨fun n m hn hm a => by
      obtain ⟨v, hv⟩ := hc n m hn hm a
      exact ⟨e.symm v, by simp [hv]⟩,
     fun n hn => ⟨fun a => by
      rw [← (hb n hn).1 a]
      constructor
      · rintro ⟨v, hv⟩
        refine ⟨e v, ?_⟩
        rw [← map_nsmul, ← hv]
        simp
      · rintro ⟨v, hv⟩
        exact ⟨e.symm v, by simp [hv]⟩,
      fun a' => by
        obtain ⟨a, v, hv⟩ := (hb n hn).2 (e a')
        refine ⟨a, e.symm v, ?_⟩
        apply e.injective
        simp [hv]⟩⟩
    (fun n hn a a' => by
      obtain ⟨z, hz⟩ := hi n hn a a'
      refine ⟨z, ?_⟩
      have h := hφ'.2.2.2.2 (e.symm (f n a)) (e.symm (f n a'))
      rw [he, he] at h
      rw [← h] at hz
      exact_mod_cast hz)
  let ψ : (F.Di k).La →ₗ[𝓞 E] (Fin r → E) := (M.X k).Λ.subtype ∘ₗ (M.φ k).toLinearMap
  have hψ : ∀ a, ψ a = (M.φ k a : Fin r → E) := fun a => rfl
  have hrange : Set.range ψ = ((M.X k).Λ : Set (Fin r → E)) := by
    ext v
    constructor
    · rintro ⟨a, rfl⟩
      exact (M.φ k a).2
    · intro hv
      exact ⟨(M.φ k).symm ⟨v, hv⟩, by rw [hψ, LinearEquiv.apply_symm_apply]⟩
  obtain ⟨γ, hγ1, hγ2⟩ := GlobalTheory.T.exists_unitary_matrix_of_lattice_isometry E H D' (F.Di k) r (-ξ₀) Gm φ' ψ gam hξ hφ'
    ⟨Subtype.val_injective.comp (M.φ k).injective, by rw [hrange]; exact (M.X k).Λ_span, hφ.2.2.1, hφ.2.2.2.1,
      fun x y => by
        have h := hM.ef k x y
        rw [(hk k).1, (hk k).2] at h
        exact h⟩ hg1
  refine ⟨k, γ, hγ1, fun v => ⟨fun hv => ?_, fun hv => ?_⟩, fun a ha => ?_⟩
  · have h := hγ2 (e.symm ⟨v, hv⟩)
    rw [he] at h
    rw [← h]
    exact (M.φ k _).2
  · have h := hγ2 (gam.symm ((M.φ k).symm ⟨_, hv⟩))
    rw [LinearEquiv.apply_symm_apply, hψ, LinearEquiv.apply_symm_apply] at h
    have h2 := congrArg (fun w => ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ w) h
    simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at h2
    rw [h2, ← hr]
    exact LinearMap.mem_range_self _ _
  · obtain ⟨w, hw⟩ := hg2 a ha
    refine ⟨M.φ k w, (M.φ k w).2, ?_⟩
    have h := hγ2 (e.symm (f l.M a))
    rw [he] at h
    rw [← h]
    change ψ (gam ((e.symm.toLinearMap ∘ₗ f l.M) a)) = ψ (F.t k a) + l.M • ψ w
    rw [hw, map_add (f := _), map_nsmul]
