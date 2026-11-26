module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermLevelZeroAndBoundedRepresentatives
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesComplementUnitaryActsOnTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthonormalBasisAndOneOrbit
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsEquivOfRetractions
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTerms
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBound
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGluingHomomorphismDefectGroup
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitEntries
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralOfMulVec
public import Formalism.LocalRingCardinality.DataSpaces

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFlagDualBasis
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.UnitriangularCoeff

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem sigR_inclR (e : E) : sigR R σ (inclR R e) = inclR R (σ e) := by
  simp [sigR, inclR]

def hRight (x : Fin n → R ⊗[F] E) : (Fin n → R ⊗[F] E) →ₗ[R ⊗[F] E] R ⊗[F] E where
  toFun y := hR R σ J x y
  map_add' y z := by
    simp only [hR, Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c y := by
    simp only [hR, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem hRight_apply (x y : Fin n → R ⊗[F] E) : hRight R σ J x y = hR R σ J x y := rfl

theorem hR_add_right (x y z : Fin n → R ⊗[F] E) :
    hR R σ J x (y + z) = hR R σ J x y + hR R σ J x z := (hRight R σ J x).map_add y z

theorem hR_sub_right (x y z : Fin n → R ⊗[F] E) :
    hR R σ J x (y - z) = hR R σ J x y - hR R σ J x z := (hRight R σ J x).map_sub y z

theorem hR_smul_right (x y : Fin n → R ⊗[F] E) (c : R ⊗[F] E) :
    hR R σ J x (c • y) = c * hR R σ J x y := (hRight R σ J x).map_smul c y

theorem hR_zero_right (x : Fin n → R ⊗[F] E) : hR R σ J x 0 = 0 := (hRight R σ J x).map_zero

theorem hR_ratV (x y : Fin n → E) :
    hR R σ J (ratV (F := F) R x) (ratV (F := F) R y) = inclR R (hE σ J x y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hR, hE, Formalism.UG.hform, ratV, JR, Matrix.map_apply, map_sum, map_mul, sigR_inclR,
    AlgHom.coe_toRingHom, RingHom.coe_coe]

theorem hE_symm (hσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) (x y : Fin n → E) :
    hE σ J y x = σ (hE σ J x y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hE, Formalism.UG.hform, map_sum, map_mul, AlgHom.coe_toRingHom, RingHom.coe_coe, hσ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hJ.1 b a]
  ring

variable {R σ J}

theorem hermitian_flag_dual_basis (hσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) {r : ℕ} {P : Frame E n r} {T : F}
    (hP : P.IsStd σ J T) (a : Fin r) (c : Fin (r + 1)) :
    hE σ J (P.f a) (F0 P c) = if c = a.castSucc then 1 else 0 := by
  induction c using Fin.lastCases with
  | last =>
    rw [F0, Fin.snoc_last, hP.2.2.2.2.1 a, if_neg (Fin.castSucc_lt_last a).ne']
  | cast c =>
    rw [F0, Fin.snoc_castSucc, hE_symm σ J hσ hJ, hP.2.2.1 c a]
    by_cases h : c = a
    · subst h; simp
    · rw [if_neg h, if_neg (fun e => h (Fin.castSucc_injective _ e)), map_zero]

theorem pairR (hσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) {r : ℕ} {P : Frame E n r} {T : F}
    (hP : P.IsStd σ J T) (a : Fin r) (c : Fin (r + 1)) :
    hR R σ J (ratV (F := F) R (P.f a)) (ratV (F := F) R (F0 P c)) = if c = a.castSucc then 1 else 0 := by
  rw [hR_ratV, hermitian_flag_dual_basis hσ hJ hP a c]
  split_ifs <;> simp only [map_one, map_zero]

theorem pair_sum (hσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) {r : ℕ} {P : Frame E n r} {T : F}
    (hP : P.IsStd σ J T) (a : Fin r) (c : Fin (r + 1) → R ⊗[F] E) :
    hR R σ J (ratV (F := F) R (P.f a)) (∑ b, c b • ratV (F := F) R (F0 P b)) = c a.castSucc := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← hRight_apply, map_sum]
  simp only [map_smul, hRight_apply, pairR hσ hJ hP, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem expand (hσ : ∀ x, σ (σ x) = x) (hJ : IsHermND σ J) {r : ℕ} {P : Frame E n r} {T : F}
    (hP : P.IsStd σ J T) (b : Fin (r + 1)) (w : Fin n → R ⊗[F] E)
    (hw : w ∈ spanR (F := F) R (F0 P) {a | a < b}) :
    w = ∑ a, (if h : a < b then hR R σ J (ratV (F := F) R
      (P.f (a.castLT (lt_of_lt_of_le h (Fin.le_last b))))) w else 0) • ratV (F := F) R (F0 P a) := by
  unfold spanR at hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c, hc, rfl⟩ := hx
    have hc' : c < b := hc
    symm
    rw [Finset.sum_eq_single c]
    · rw [dite_eq_left hc', pairR hσ hJ hP, Fin.castSucc_castLT, if_pos rfl, one_smul]
    · intro a _ hac
      split_ifs with h
      · rw [pairR hσ hJ hP, Fin.castSucc_castLT, if_neg (fun e => hac e.symm), zero_smul]
      · rw [zero_smul]
    · intro h; exact absurd (Finset.mem_univ c) h
  | zero =>
    symm
    refine Finset.sum_eq_zero fun a _ => ?_
    split_ifs <;> simp [hR_zero_right]
  | add x y _ _ hx hy =>
    conv_lhs => rw [hx, hy]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs <;> simp [hR_add_right, add_smul]
  | smul c x _ hx =>
    conv_lhs => rw [hx]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs <;> simp [hR_smul_right, smul_smul]

end Alg

theorem combine {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] {r : ℕ} (b : Fin (r + 1))
    (G : Fin (r + 1) → M) (y : ∀ a : Fin (r + 1), a < b → A) :
    (∑ a, (if h : a < b then y a h else 0) • G a) + G b =
      ∑ a, (if a = b then 1 else if h : a < b then y a h else 0) • G a := by
  have key : ∀ a, (if a = b then (1 : A) else if h : a < b then y a h else 0) • G a =
      (if h : a < b then y a h else 0) • G a + (if a = b then G a else 0) := by
    intro a
    by_cases hab : a = b
    · subst hab; simp
    · simp [hab]
  simp only [key, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem sigma_sigma {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  let τ : E →+* ℂ := (IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := E)).toRingHom
  apply τ.injective
  rw [hσ.2.2.2 τ, hσ.2.2.2 τ, star_star]

theorem exists_coeff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (r : ℕ) (P : Frame E n r) (T : F), P.IsStd σ J T → ∃ ν : Ssub (Fv F v) σ J P → ({p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → Fv F v ⊗[F] E), Continuous ν ∧ ∀ (s : Ssub (Fv F v) σ J P) (x : {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2} → Fv F v ⊗[F] E), x = ν s ↔ ∀ b, lin (Fv F v) σ J (s : HA (Fv F v) σ J) (ratV (F := F) (Fv F v) (F0 P b)) = ∑ a : Fin (r + 1), (if a = b then 1 else if h : a < b then x ⟨(a, b), h⟩ else 0 : Fv F v ⊗[F] E) • ratV (F := F) (Fv F v) (F0 P a) := by
  intro F E _ _ _ _ _ σ hσ n J hJ v r P T hP
  have hss : ∀ x, σ (σ x) = x := sigma_sigma σ hσ
  haveI : IsTopologicalRing (Fv F v ⊗[F] E) := IsModuleTopology.isTopologicalRing (Fv F v) _
  have ha : ∀ p : {p : Fin (r + 1) × Fin (r + 1) // p.1 < p.2}, (p.1.1 : ℕ) < r :=
    fun p => lt_of_lt_of_le p.2 (Fin.le_last _)
  refine ⟨fun s p => hR (Fv F v) σ J (ratV (F := F) (Fv F v) (P.f (p.1.1.castLT (ha p))))
      (lin (Fv F v) σ J (s : HA (Fv F v) σ J) (ratV (F := F) (Fv F v) (F0 P p.1.2))), ?_, ?_⟩
  · refine continuous_pi fun p => ?_
    have hM : Continuous fun s : Ssub (Fv F v) σ J P =>
        ((HA.mat (Fv F v) σ J (s : HA (Fv F v) σ J) : GL (Fin n) (Fv F v ⊗[F] E)) :
          Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) :=
      Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
    have hMij : ∀ i j, Continuous fun s : Ssub (Fv F v) σ J P =>
        ((HA.mat (Fv F v) σ J (s : HA (Fv F v) σ J) : GL (Fin n) (Fv F v ⊗[F] E)) :
          Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) i j :=
      fun i j => (continuous_apply j).comp ((continuous_apply i).comp hM)
    simp only [hR, Formalism.UG.hform, lin, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
    exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      continuous_const.mul (continuous_finsetSum _ fun k _ => (hMij j k).mul continuous_const)
  · intro s x
    constructor
    · rintro rfl b
      have hU : lin (Fv F v) σ J (s : HA (Fv F v) σ J) (ratV (F := F) (Fv F v) (F0 P b)) -
          ratV (F := F) (Fv F v) (F0 P b) ∈ spanR (F := F) (Fv F v) (F0 P) {a | a < b} := s.2 b
      have e1 := sub_eq_iff_eq_add.mp (expand hss hJ hP b _ hU)
      refine e1.trans ((combine b _ _).trans ?_)
      refine Finset.sum_congr rfl fun a _ => ?_
      congr 1
      split_ifs with h1 h2
      · rfl
      · rw [hR_sub_right, pairR hss hJ hP, Fin.castSucc_castLT, if_neg h2.ne', sub_zero]
      · rfl
    · intro H
      funext p
      obtain ⟨⟨a, b⟩, h⟩ := p
      symm
      show hR (Fv F v) σ J (ratV (F := F) (Fv F v) (P.f (a.castLT (lt_of_lt_of_le h (Fin.le_last b)))))
        (lin (Fv F v) σ J (s : HA (Fv F v) σ J) (ratV (F := F) (Fv F v) (F0 P b))) = x ⟨(a, b), h⟩
      rw [H b, pair_sum hss hJ hP, Fin.castSucc_castLT, if_neg h.ne, dite_eq_left h]

end GlobalTheory.UnitriangularCoeff
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PairingSecondTypeTestOnRepresentatives
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PairingSecondTypeTestOnRepresentatives
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.TypeRep

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem h_add_left (a b y : S.V) : S.h (a + b) y = S.h a y + S.h b y := by
  simp only [Frames.h, hf, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem h_add_right (a y z : S.V) : S.h a (y + z) = S.h a y + S.h a z := by
  simp only [Frames.h, hf, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]

theorem h_smul_left (c : E) (a y : S.V) : S.h (c • a) y = c * S.h a y := by
  simp only [Frames.h, hf, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem h_smul_right (c : E) (a y : S.V) : S.h a (c • y) = L.cj c * S.h a y := by
  simp only [Frames.h, hf, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

private theorem h_zero_left' (y : S.V) : S.h 0 y = 0 := by
  simp [Frames.h, hf]

private theorem h_zero_right_flag_measures (a : S.V) : S.h a 0 = 0 := by
  simp [Frames.h, hf]

private theorem h_eq_zero_of_span_orth {s t : Set S.V} (hst : ∀ a ∈ s, ∀ b ∈ t, S.h a b = 0) {x y : S.V}
    (hx : x ∈ Submodule.span E s) (hy : y ∈ Submodule.span E t) : S.h x y = 0 := by
  induction hx using Submodule.span_induction with
  | mem a ha =>
    induction hy using Submodule.span_induction with
    | mem b hb => exact hst a ha b hb
    | zero => exact h_zero_right_flag_measures S a
    | add u v _ _ hu hv => rw [h_add_right, hu, hv, add_zero]
    | smul c u _ hu => rw [h_smul_right, hu, mul_zero]
  | zero => exact h_zero_left' S y
  | add u v _ _ hu hv => rw [h_add_left, hu, hv, add_zero]
  | smul c u _ hu => rw [h_smul_left, hu, mul_zero]

theorem iso_of (g : Fin (r + 1) → S.V) (t : E)
    (hg : ∀ a b, hf L S.Hm (g a) (g b) = if a = Fin.last r ∧ b = Fin.last r then t else 0)
    {x y : S.V} (hx : x ∈ S.spanTo g r) (hy : y ∈ S.spanTo g r) : S.h x y = 0 := by
  unfold Frames.spanTo at hx hy
  refine h_eq_zero_of_span_orth S ?_ hx hy
  rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
  change hf L S.Hm (g i) (g j) = 0
  rw [hg, if_neg]
  rintro ⟨rfl, -⟩
  simp at hi

theorem spanTo_mono (g : Fin (r + 1) → S.V) : S.spanTo g r ≤ S.spanTo g (r + 1) := by
  unfold Frames.spanTo
  exact Submodule.span_mono (Set.image_mono fun i (hi : (i : ℕ) < r) => Nat.lt_succ_of_lt hi)

theorem disj (hli : LinearIndependent E (Sum.elim S.f S.f')) :
    Disjoint (S.spanTo S.f (r + 1)) (S.spanTo S.f' (r + 1)) := by
  have h := (linearIndependent_sum.1 hli).2.2
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr] at h
  unfold Frames.spanTo
  exact h.mono (Submodule.span_mono (Set.image_subset_range _ _))
    (Submodule.span_mono (Set.image_subset_range _ _))

theorem frame_split (Λ : Submodule L.O S.V) (g g' : Fin (r + 1) → S.V) (h0 : S.th ≠ 0)
    (hg : ∀ b, g b ∈ S.spanTo S.f (r + 1))
    (hg' : ∀ b, g' b ∈ Λ ∧ g' b ∈ S.spanTo S.f' (r + 1)) {m : S.V} (hm : m ∈ S.Mof g g') :
    ∃ a ∈ S.spanTo S.f (r + 1), ∃ a' ∈ S.spanTo S.f' (r + 1), a' ∈ Λ ∧
      algebraMap F E S.th • m = a + a' := by
  have hinv : ∀ v : S.V, algebraMap F E S.th • algebraMap F E S.th⁻¹ • v = v := by
    intro v
    rw [smul_smul, ← map_mul, mul_inv_cancel₀ h0, map_one, one_smul]
  unfold Frames.Mof at hm
  induction hm using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨b, rfl⟩ | ⟨b, rfl⟩
    · exact ⟨algebraMap F E S.th • g b, Submodule.smul_mem _ _ (hg b), 0, Submodule.zero_mem _,
        Submodule.zero_mem _, by rw [add_zero]⟩
    · refine ⟨-g b, Submodule.neg_mem _ (hg b), g' b, (hg' b).2, (hg' b).1, ?_⟩
      dsimp only
      rw [hinv]
      abel
  | zero => exact ⟨0, Submodule.zero_mem _, 0, Submodule.zero_mem _, Submodule.zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, a', ha', hΛ, he⟩ := hx
    obtain ⟨b, hb, b', hb', hΛ', he'⟩ := hy
    exact ⟨a + b, Submodule.add_mem _ ha hb, a' + b', Submodule.add_mem _ ha' hb',
      Submodule.add_mem _ hΛ hΛ', by rw [smul_add, he, he']; abel⟩
  | smul c x _ hx =>
    obtain ⟨a, ha, a', ha', hΛ, he⟩ := hx
    refine ⟨(c : E) • a, Submodule.smul_mem _ _ ha, (c : E) • a', Submodule.smul_mem _ _ ha',
      Λ.smul_mem c hΛ, ?_⟩
    rw [Subring.smul_def, smul_comm, he, smul_add]

private theorem algebraMap_mem_O_of_mem_valuationInteger (L : LocE F E) {x : F} (hx : x ∈ 𝒪[F]) : algebraMap F E x ∈ L.O := by
  rw [L.O_def]
  have := isIntegral_algebraMap (R := 𝒪[F]) (A := E) (x := ⟨x, hx⟩)
  convert this using 1
  rw [IsScalarTower.algebraMap_apply 𝒪[F] F E]
  rfl

theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → ¬ S.BBzero d Λ → ∀ B₀ : Set S.V, (∀ y ∈ B₀, y ∈ Λ ∧ y ∈ S.X ⊔ S.X') → (∀ y ∈ S.sat Λ, ∃ y₀ ∈ B₀, y - y₀ ∈ S.M d Λ) → (∀ x₁ ∈ S.X, ∀ x₁' ∈ S.X', ∀ x₂ ∈ S.X, ∀ x₂' ∈ S.X', algebraMap F E S.th⁻¹ • (x₁ + x₁') ∈ B₀ → algebraMap F E S.th⁻¹ • (x₂ + x₂') ∈ B₀ → ∃ c ∈ L.O, S.h x₁ x₂' = algebraMap F E S.th * c) → S.TypeBe d Λ := by
  intro F _ _ _ _ _ E _ _ _ L r k S d Λ hT hB B₀ hB₀ hrep hpair
  obtain ⟨hli, -, -, -, -, h0, hthF, -⟩ := GlobalTheory.FrameBasic.main L r k S
  obtain ⟨hSD, -, hMsat, hfr, hfr', -, -, -⟩ := GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT
  have hlev := (GlobalTheory.T.termLevel_zero_and_bounded_representatives L r k S d Λ hT).2.1
  have hthO : algebraMap F E S.th ∈ L.O := algebraMap_mem_O_of_mem_valuationInteger L hthF
  have hcj : L.cj (algebraMap F E S.th) = algebraMap F E S.th := L.cj.commutes S.th
  have hinv : ∀ v : S.V, algebraMap F E S.th⁻¹ • algebraMap F E S.th • v = v := by
    intro v
    rw [smul_smul, ← map_mul, inv_mul_cancel₀ h0, map_one, one_smul]
  have hint : ∀ v ∈ Λ, ∀ w ∈ Λ, S.h v w ∈ L.O := fun v hv w hw => (hSD.2 w).2 hw v hv
  have hXX : ∀ v ∈ S.X, ∀ w ∈ S.X, S.h v w = 0 := fun v hv w hw =>
    iso_of S S.f (-algebraMap F E S.T) S.gram hv hw
  have hXX' : ∀ v ∈ S.X', ∀ w ∈ S.X', S.h v w = 0 := fun v hv w hw =>
    iso_of S S.f' (-algebraMap F E S.T') S.gram' hv hw
  have hXME : S.X ≤ S.ME := (spanTo_mono S S.f).trans le_sup_left
  have hX'ME : S.X' ≤ S.ME := (spanTo_mono S S.f').trans le_sup_right
  have hsatΛ : S.sat Λ ≤ Λ := inf_le_left
  have hg : ∀ b, S.fr d Λ b ∈ S.spanTo S.f (r + 1) := fun b =>
    ((hfr (r + 1) le_rfl _).2 (Submodule.subset_span (Set.mem_image_of_mem _ b.2))).2
  have hg' : ∀ b, S.fr' d Λ b ∈ Λ ∧ S.fr' d Λ b ∈ S.spanTo S.f' (r + 1) := fun b =>
    (hfr' (r + 1) le_rfl _).2 (Submodule.subset_span (Set.mem_image_of_mem _ b.2))
  have hdisj := Submodule.disjoint_def.1 (disj S hli)
  have key : ∀ x ∈ S.X, ∀ x' ∈ S.X', S.InTh Λ (x + x') → ∃ u ∈ S.X, ∃ u' ∈ S.X',
      u + u' ∈ B₀ ∧ u + u' ∈ Λ ∧ x' - algebraMap F E S.th • u' ∈ Λ ∧
      ∃ m ∈ Λ, (x - algebraMap F E S.th • u) + (x' - algebraMap F E S.th • u') =
        algebraMap F E S.th • m := by
    rintro x hx x' hx' ⟨y, hyΛ, hxy⟩
    have hyME : y ∈ S.ME := by
      rw [← hinv y, ← hxy]
      exact Submodule.smul_mem _ _ (Submodule.add_mem _ (hXME hx) (hX'ME hx'))
    have hysat : y ∈ S.sat Λ := Submodule.mem_inf.2 ⟨hyΛ, hyME⟩
    obtain ⟨y₀, hy₀, hmM⟩ := hrep y hysat
    obtain ⟨hy₀Λ, hy₀X⟩ := hB₀ y₀ hy₀
    obtain ⟨u, hu, u', hu', rfl⟩ := Submodule.mem_sup.1 hy₀X
    have hmΛ : y - (u + u') ∈ Λ := hsatΛ (hMsat hmM)
    obtain ⟨b, hb, b', hb', hb'Λ, hbb⟩ := frame_split S Λ _ _ h0 hg hg' hmM
    have hsum : (x - algebraMap F E S.th • u) + (x' - algebraMap F E S.th • u') =
        algebraMap F E S.th • (y - (u + u')) := by
      rw [smul_sub, ← hxy, smul_add]
      abel
    have hdiff : b' - (x' - algebraMap F E S.th • u') = 0 := by
      apply hdisj
      · have he : b' - (x' - algebraMap F E S.th • u') = (x - algebraMap F E S.th • u) - b := by
          have h2 := hsum.trans hbb
          linear_combination -h2
        rw [he]
        exact Submodule.sub_mem _
          (spanTo_mono S S.f (Submodule.sub_mem _ hx (Submodule.smul_mem _ _ hu))) hb
      · exact Submodule.sub_mem _ hb'
          (spanTo_mono S S.f' (Submodule.sub_mem _ hx' (Submodule.smul_mem _ _ hu')))
    have ha' : x' - algebraMap F E S.th • u' = b' := (sub_eq_zero.1 hdiff).symm
    exact ⟨u, hu, u', hu', hy₀, hy₀Λ, by rw [ha']; exact hb'Λ, y - (u + u'), hmΛ, hsum⟩
  refine ⟨hB, ?_, ?_⟩
  · intro y hy
    obtain ⟨y₀, hy₀, hm⟩ := hrep y hy
    exact (hlev y hy r).2 ⟨y₀, (hB₀ y₀ hy₀).2, hm⟩
  · intro x₁ hx₁ x₁' hx₁' x₂ hx₂ x₂' hx₂' h1 h2
    obtain ⟨u₁, hu₁, u₁', hu₁', hB1, hy1, ha1', m₁, hm₁, he1⟩ := key x₁ hx₁ x₁' hx₁' h1
    obtain ⟨u₂, hu₂, u₂', hu₂', hB2, hy2, ha2', m₂, hm₂, he2⟩ := key x₂ hx₂ x₂' hx₂' h2
    generalize ht : algebraMap F E S.th = t at *
    set a₁ := x₁ - t • u₁ with ha₁
    set a₁' := x₁' - t • u₁' with ha₁d
    set a₂' := x₂' - t • u₂' with ha₂d
    have ha₁X : a₁ ∈ S.X := Submodule.sub_mem _ hx₁ (Submodule.smul_mem _ _ hu₁)
    have ha₁'X : a₁' ∈ S.X' := Submodule.sub_mem _ hx₁' (Submodule.smul_mem _ _ hu₁')
    have ha₂'X : a₂' ∈ S.X' := Submodule.sub_mem _ hx₂' (Submodule.smul_mem _ _ hu₂')
    have hB1' : algebraMap F E S.th⁻¹ • (t • u₁ + t • u₁') ∈ B₀ := by rw [← smul_add, hinv]; exact hB1
    have hB2' : algebraMap F E S.th⁻¹ • (t • u₂ + t • u₂') ∈ B₀ := by rw [← smul_add, hinv]; exact hB2
    obtain ⟨c₀, hc₀, hc₀e⟩ := hpair (t • u₁) (Submodule.smul_mem _ _ hu₁) (t • u₁')
      (Submodule.smul_mem _ _ hu₁') (t • u₂) (Submodule.smul_mem _ _ hu₂) (t • u₂')
      (Submodule.smul_mem _ _ hu₂') hB1' hB2'
    have ex₁ : x₁ = t • u₁ + a₁ := by rw [ha₁]; abel
    have ex₂' : x₂' = t • u₂' + a₂' := by rw [ha₂d]; abel
    have eA : S.h x₁ x₂' = S.h (t • u₁) (t • u₂') + S.h (t • u₁) a₂' + S.h a₁ (t • u₂') +
        S.h a₁ a₂' := by
      rw [ex₁, ex₂', h_add_left, h_add_right, h_add_right]
      ring
    have eB : S.h (t • u₁) a₂' = t * S.h u₁ a₂' := h_smul_left S _ _ _
    have eC : S.h (u₁ + u₁') a₂' = S.h u₁ a₂' + S.h u₁' a₂' := h_add_left S _ _ _
    have eD : S.h u₁' a₂' = 0 := hXX' _ hu₁' _ ha₂'X
    have eE : S.h a₁ (t • u₂') = t * S.h a₁ u₂' := by rw [h_smul_right, hcj]
    have eF : S.h a₁ (u₂ + u₂') = S.h a₁ u₂ + S.h a₁ u₂' := h_add_right S _ _ _
    have eG : S.h a₁ u₂ = 0 := hXX _ ha₁X _ hu₂
    have eH : S.h (a₁ + a₁') a₂' = S.h a₁ a₂' + S.h a₁' a₂' := h_add_left S _ _ _
    have eI : S.h (t • m₁) a₂' = t * S.h m₁ a₂' := h_smul_left S _ _ _
    have eJ : S.h a₁' a₂' = 0 := hXX' _ ha₁'X _ ha₂'X
    have eK : S.h (t • m₁) (u₂ + u₂') = t * S.h m₁ (u₂ + u₂') := h_smul_left S _ _ _
    have eL : S.h (a₁ + a₁') (u₂ + u₂') = S.h a₁ (u₂ + u₂') + S.h a₁' (u₂ + u₂') :=
      h_add_left S _ _ _
    rw [he1] at eH eL
    have hO1 : S.h (u₁ + u₁') a₂' ∈ L.O := hint _ hy1 _ ha2'
    have hO2 : S.h m₁ (u₂ + u₂') ∈ L.O := hint _ hm₁ _ hy2
    have hO3 : S.h a₁' (u₂ + u₂') ∈ L.O := hint _ ha1' _ hy2
    have hO4 : S.h m₁ a₂' ∈ L.O := hint _ hm₁ _ ha2'
    refine ⟨c₀ + S.h (u₁ + u₁') a₂' + (t * S.h m₁ (u₂ + u₂') - S.h a₁' (u₂ + u₂')) + S.h m₁ a₂',
      ?_, ?_⟩
    · exact L.O.add_mem (L.O.add_mem (L.O.add_mem hc₀ hO1)
        (L.O.sub_mem (L.O.mul_mem hthO hO2) hO3)) hO4
    · rw [eA, hc₀e]
      linear_combination eB - t * eC - t * eD + eE - t * eF - t * eG - eH + eI - eJ + t * eK - t * eL

end GlobalTheory.HL.TypeRep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PairingSecondTypeTestOnRepresentativesStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairing_second_type_test_on_representatives : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → ¬ S.BBzero d Λ → ∀ B₀ : Set S.V, (∀ y ∈ B₀, y ∈ Λ ∧ y ∈ S.X ⊔ S.X') → (∀ y ∈ S.sat Λ, ∃ y₀ ∈ B₀, y - y₀ ∈ S.M d Λ) → (∀ x₁ ∈ S.X, ∀ x₁' ∈ S.X', ∀ x₂ ∈ S.X, ∀ x₂' ∈ S.X', algebraMap F E S.th⁻¹ • (x₁ + x₁') ∈ B₀ → algebraMap F E S.th⁻¹ • (x₂ + x₂') ∈ B₀ → ∃ c ∈ L.O, S.h x₁ x₂' = algebraMap F E S.th * c) → S.TypeBe d Λ := by
  first | exact @GlobalTheory.HL.TypeRep.main | exact GlobalTheory.HL.TypeRep.main | (intros; apply GlobalTheory.HL.TypeRep.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianEichlerProductParamsIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianEichlerProductParamsIntegral
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

noncomputable section
namespace GlobalTheory.HL.SAN.IntParam

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem eich_int (L : LocE F E) {N : ℕ} {Hm : Matrix (Fin N) (Fin N) E}
    (hI : ∀ i j, Hm i j ∈ L.O) {x u v : Fin N → E} {s : E} (hx : ∀ j, x j ∈ L.O)
    (hu : ∀ j, u j ∈ L.O) (hs : s ∈ L.O) (hv : ∀ j, v j ∈ L.O) (j : Fin N) :
    eich L Hm x u s v j ∈ L.O := by
  simp only [eich, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  exact L.O.sub_mem (L.O.add_mem (hv j) (L.O.mul_mem (hf_int L hI hv hu) (hx j)))
    (L.O.mul_mem (hf_int L hI hv hx) (L.O.add_mem (hu j) (L.O.mul_mem hs (hx j))))

theorem prod_fix {N : ℕ} (y : Fin N → E) :
    ∀ l : List ((Fin N → E) ≃ₗ[E] (Fin N → E)), (∀ g ∈ l, g y = y) → l.prod y = y := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons g l ih =>
    intro h
    rw [List.prod_cons, LinearEquiv.mul_apply, ih (fun g' hg' => h g' (List.mem_cons_of_mem _ hg')),
      h g List.mem_cons_self]

theorem finiteRing_sq_sub_mul_sq_eq_of_card (L : LocE F E) (N : ℕ) (Hm : Matrix (Fin N) (Fin N) E) (hH : IsHerm L Hm)
    (hI : ∀ i j, Hm i j ∈ L.O) : ∀ (r : ℕ) (X Y u : Fin r → Fin N → E) (s : Fin r → E)
    (e : Fin r → (Fin N → E) ≃ₗ[E] (Fin N → E)), (∀ i j, X i j ∈ L.O) → (∀ i j, Y i j ∈ L.O) →
    (∀ a b, hf L Hm (X a) (Y b) = if a = b then 1 else 0) → (∀ a b, hf L Hm (X a) (X b) = 0) →
    (∀ i, ∀ j, j ≤ i → hf L Hm (u i) (X j) = 0 ∧ hf L Hm (u i) (Y j) = 0) →
    (∀ i, s i + L.cj (s i) = hf L Hm (u i) (u i)) →
    (∀ i v, e i v = eich L Hm (X i) (u i) (s i) v) →
    (∀ x : Fin N → E, (∀ j, (List.ofFn e).prod x j ∈ L.O) ↔ ∀ j, x j ∈ L.O) →
    (∀ i j, u i j ∈ L.O) ∧ ∀ i, s i ∈ L.O := by
  intro r
  induction r with
  | zero => intro X Y u s e _ _ _ _ _ _ _ _; exact ⟨fun i => i.elim0, fun i => i.elim0⟩
  | succ r ih =>
    intro X Y u s e hX hY hXY hXX hu hs he hn
    set n' := (List.ofFn fun i : Fin r => e i.succ).prod with hn'def
    have hprod : ∀ x, (List.ofFn e).prod x = e 0 (n' x) := by
      intro x; rw [List.ofFn_succ, List.prod_cons, LinearEquiv.mul_apply]

    have hfix : n' (Y 0) = Y 0 := by
      refine prod_fix (Y 0) _ fun g hg => ?_
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hg
      have h1 : hf L Hm (Y 0) (u i.succ) = 0 := by
        rw [← GlobalTheory.HL.Eichler.hf_cj L hH, (hu i.succ 0 (Fin.zero_le _)).2, map_zero]
      have h2 : hf L Hm (Y 0) (X i.succ) = 0 := by
        rw [← GlobalTheory.HL.Eichler.hf_cj L hH, hXY, if_neg (Fin.succ_ne_zero i), map_zero]
      rw [he, eich, h1, h2]; simp
    have h0 : e 0 (Y 0) = Y 0 - (u 0 + s 0 • X 0) := by
      have h1 : hf L Hm (Y 0) (u 0) = 0 := by
        rw [← GlobalTheory.HL.Eichler.hf_cj L hH, (hu 0 0 le_rfl).2, map_zero]
      have h2 : hf L Hm (Y 0) (X 0) = 1 := by
        rw [← GlobalTheory.HL.Eichler.hf_cj L hH, hXY, if_pos rfl, map_one]
      rw [he, eich, h1, h2]; simp
    have hnY : ∀ j, (List.ofFn e).prod (Y 0) j ∈ L.O := (hn (Y 0)).2 (hY 0)
    rw [hprod, hfix, h0] at hnY
    have hw : ∀ j, (u 0 + s 0 • X 0) j ∈ L.O := by
      intro j
      have := L.O.sub_mem (hY 0 j) (hnY j)
      simpa using this
    have hs0 : s 0 ∈ L.O := by
      have h := hf_int L hI hw (hY 0)
      rwa [GlobalTheory.HL.Eichler.hf_add_l, GlobalTheory.HL.Eichler.hf_smul_l, (hu 0 0 le_rfl).2, hXY, if_pos rfl,
        mul_one, zero_add] at h
    have hu0 : ∀ j, u 0 j ∈ L.O := by
      intro j
      have h := L.O.sub_mem (hw j) (L.O.mul_mem hs0 (hX 0 j))
      simpa using h

    have he0 : ∀ x, (∀ j, e 0 x j ∈ L.O) ↔ ∀ j, x j ∈ L.O := by
      intro x
      constructor
      · intro h j
        have hinv := GlobalTheory.HL.Eichler.eich_inv L hH (X 0) (u 0) (s 0) (hXX 0 0) (hu 0 0 le_rfl).1 (hs 0) x
        rw [← hinv, ← he]
        exact eich_int L hI (hX 0) (fun k => L.O.neg_mem (hu0 k)) (GlobalTheory.UnramOrder.cj_mem L hs0) h j
      · intro h j
        rw [he]
        exact eich_int L hI (hX 0) hu0 hs0 h j
    have hn2 : ∀ x : Fin N → E, (∀ j, (List.ofFn fun i : Fin r => e i.succ).prod x j ∈ L.O) ↔
        ∀ j, x j ∈ L.O := by
      intro x
      rw [← hn x, hprod, ← hn'def]
      exact (he0 (n' x)).symm
    obtain ⟨hU, hS⟩ := ih (fun i => X i.succ) (fun i => Y i.succ) (fun i => u i.succ)
      (fun i => s i.succ) (fun i => e i.succ) (fun i => hX i.succ) (fun i => hY i.succ)
      (fun a b => by rw [hXY]; simp only [Fin.succ_inj]) (fun a b => hXX a.succ b.succ)
      (fun i j hj => hu i.succ j.succ (Fin.succ_le_succ_iff.mpr hj)) (fun i => hs i.succ)
      (fun i v => he i.succ v) hn2
    refine ⟨fun i => Fin.cases hu0 (fun i => hU i) i, fun i => Fin.cases hs0 (fun i => hS i) i⟩

theorem eich_prod_params_int : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) (N r : ℕ) (Hm : Matrix (Fin N) (Fin N) E) (hH : IsHerm L Hm) (hI : ∀ i j, Hm i j ∈ L.O) (X Y u : Fin r → Fin N → E) (s : Fin r → E) (e : Fin r → (Fin N → E) ≃ₗ[E] (Fin N → E)) (hX : ∀ i j, X i j ∈ L.O) (hY : ∀ i j, Y i j ∈ L.O) (hXY : ∀ a b, hf L Hm (X a) (Y b) = if a = b then 1 else 0) (hXX : ∀ a b, hf L Hm (X a) (X b) = 0) (hu : ∀ i, ∀ j, j ≤ i → hf L Hm (u i) (X j) = 0 ∧ hf L Hm (u i) (Y j) = 0) (hs : ∀ i, s i + L.cj (s i) = hf L Hm (u i) (u i)) (he : ∀ i v, e i v = eich L Hm (X i) (u i) (s i) v) (hn : ∀ x : Fin N → E, (∀ j, (List.ofFn e).prod x j ∈ L.O) ↔ ∀ j, x j ∈ L.O), (∀ i j, u i j ∈ L.O) ∧ ∀ i, s i ∈ L.O := by
  intro F _ _ _ _ _ E _ _ _ L N r Hm hH hI X Y u s e hX hY hXY hXX hu hs he hn
  exact finiteRing_sq_sub_mul_sq_eq_of_card L N Hm hH hI r X Y u s e hX hY hXY hXX hu hs he hn

end GlobalTheory.HL.SAN.IntParam
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianEichlerProductParamsIntegralStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianEichlerProduct_params_integral : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E) (N r : ℕ) (Hm : Matrix (Fin N) (Fin N) E) (hH : IsHerm L Hm) (hI : ∀ i j, Hm i j ∈ L.O) (X Y u : Fin r → Fin N → E) (s : Fin r → E) (e : Fin r → (Fin N → E) ≃ₗ[E] (Fin N → E)) (hX : ∀ i j, X i j ∈ L.O) (hY : ∀ i j, Y i j ∈ L.O) (hXY : ∀ a b, hf L Hm (X a) (Y b) = if a = b then 1 else 0) (hXX : ∀ a b, hf L Hm (X a) (X b) = 0) (hu : ∀ i, ∀ j, j ≤ i → hf L Hm (u i) (X j) = 0 ∧ hf L Hm (u i) (Y j) = 0) (hs : ∀ i, s i + L.cj (s i) = hf L Hm (u i) (u i)) (he : ∀ i v, e i v = eich L Hm (X i) (u i) (s i) v) (hn : ∀ x : Fin N → E, (∀ j, (List.ofFn e).prod x j ∈ L.O) ↔ ∀ j, x j ∈ L.O), (∀ i j, u i j ∈ L.O) ∧ ∀ i, s i ∈ L.O := by
  first | exact @GlobalTheory.HL.SAN.IntParam.eich_prod_params_int | exact GlobalTheory.HL.SAN.IntParam.eich_prod_params_int | (intros; apply GlobalTheory.HL.SAN.IntParam.eich_prod_params_int <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameLatticeUnimodularGeneratorsExponentZero
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameLatticeUnimodularGeneratorsExponentZero
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.HL.StdPlace NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.FrameUnimod
open GlobalTheory.HL.Defect GlobalTheory.HL.Eichler GlobalTheory.HL.StdLat GlobalTheory.UnramOrder Matrix

theorem frame_unimodular : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.a = 0 → ∃ u : Fin (2 * (r + 1)) → S.V, S.M d Λ = Submodule.span L.O (Set.range u) ∧ Submodule.span E (Set.range u) = S.ME ∧ (∀ i j, hf L S.Hm (u i) (u j) ∈ L.O) ∧ ∃ P : Matrix (Fin (2 * (r + 1))) (Fin (2 * (r + 1))) E, IsIntM L P ∧ (Matrix.of fun i j => hf L S.Hm (u i) (u j)) * P = 1 := by
  intro F _ _ _ _ _ E _ _ _ L r k S d Λ hT ha0
  obtain ⟨hSD, hW, hM, -, -, -⟩ := GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT
  obtain ⟨-, -, ⟨c, hc0, hc⟩, -, -, hth0, -⟩ := GlobalTheory.FrameBasic.main L r k S
  obtain ⟨-, -, hv, hvu⟩ := GlobalTheory.UnramVal.vE_valuation L S.ϖ S.ϖ_irr
  have hn : (S.wit d Λ).1 ∈ S.N := hW.2.2.1
  have hn' : (S.wit d Λ).2 ∈ S.N' := hW.2.2.2.1
  have hint : ∀ x ∈ Λ, ∀ y ∈ Λ, hf L S.Hm x y ∈ L.O := fun x hx y hy => (hSD.2 y).2 hy x hx
  have hMe : S.M d Λ = Submodule.span L.O (Set.range (gens S (S.fr d Λ) (S.fr' d Λ))) := Mof_eq S _ _
  have hg : ∀ i, gens S (S.fr d Λ) (S.fr' d Λ) i ∈ Λ := fun i =>
    (hM (hMe ▸ Submodule.subset_span ⟨i, rfl⟩)).1
  have hsp : ∀ j, S.spanTo (S.fr d Λ) j = S.spanTo S.f j := by
    obtain ⟨s, hs, h⟩ := FrameOnto.exists_matrix S S.f S.T S.gram _ hn
    exact spanTo_eq S _ _ s hs h
  have hsp' : ∀ j, S.spanTo (S.fr' d Λ) j = S.spanTo S.f' j := by
    obtain ⟨s, hs, h⟩ := FrameOnto.exists_matrix S S.f' S.T' S.gram' _ hn'
    exact spanTo_eq S _ _ s hs h
  have hdet : (Matrix.of fun i j => hf L S.Hm (gens S (S.fr d Λ) (S.fr' d Λ) i)
      (gens S (S.fr d Λ) (S.fr' d Λ) j)).det =
      algebraMap F E ((-1) ^ (r + 1) * S.th⁻¹ ^ (2 * (r + 1)) * c) := by
    refine (det_gens S hn hn').trans ?_
    rw [hc]; simp only [map_mul, map_pow, map_neg, map_one]
  have hc' : ((-1) ^ (r + 1) * S.th⁻¹ ^ (2 * (r + 1)) * c : F) ≠ 0 := by
    simp [hc0, hth0]
  have hmem : ((-1) ^ (r + 1) * S.th⁻¹ ^ (2 * (r + 1)) * c : F) ∈ 𝒪[F] := by
    rw [← algebraMap_mem_iff L, ← hdet]
    exact det_mem _ fun i j => hint _ (hg i) _ (hg j)
  obtain ⟨w0, hw0⟩ := hvu _ hc'
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le ((hv _ hc').2 hmem)
  rw [hm, zpow_natCast] at hw0
  have ha : S.a = m := by
    have e1 : c = S.th ^ (2 * (r + 1)) * ((S.ϖ : F) ^ m *
        ((((-1) ^ (r + 1) * w0 : (𝒪[F])ˣ) : 𝒪[F]) : F)) := by
      have e2 : ((((-1) ^ (r + 1) * w0 : (𝒪[F])ˣ) : 𝒪[F]) : F) = (-1) ^ (r + 1) * ((w0 : 𝒪[F]) : F) := by
        simp
      rw [e2, mul_left_comm ((S.ϖ : F) ^ m), ← hw0, ← mul_assoc ((-1 : F) ^ _), ← mul_assoc ((-1 : F) ^ _),
        ← mul_pow, inv_pow]
      field_simp
      simp
    unfold Frames.a Frames.vth
    unfold Frames.th at e1
    rw [hc, e1]
    split_ifs
    · rw [← mul_assoc, ← pow_add, vE_pow_mul _ S.ϖ_irr]; push_cast; ring
    · rw [one_pow, one_mul, vE_pow_mul _ S.ϖ_irr]; ring
  have hm0 : m = 0 := by omega
  rw [hm0, pow_zero, one_mul] at hw0
  let e : Fin (2 * (r + 1)) ≃ Fin (r + 1) ⊕ Fin (r + 1) :=
    (finCongr (two_mul (r + 1))).trans finSumFinEquiv.symm
  have hrange : Set.range (fun i => gens S (S.fr d Λ) (S.fr' d Λ) (e i)) =
      Set.range (gens S (S.fr d Λ) (S.fr' d Λ)) :=
    EquivLike.range_comp (gens S (S.fr d Λ) (S.fr' d Λ)) e
  refine ⟨fun i => gens S (S.fr d Λ) (S.fr' d Λ) (e i), ?_, ?_, fun i j => hint _ (hg _) _ (hg _), ?_⟩
  · rw [hrange, hMe]
  · rw [hrange]
    unfold Frames.ME
    rw [← hsp, ← hsp']
    apply le_antisymm
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨b | b, rfl⟩
      · exact Submodule.mem_sup_left (Submodule.subset_span ⟨b, b.2, rfl⟩)
      · simp only [gens, Sum.elim_inr]
        refine Submodule.smul_mem _ _ (Submodule.sub_mem _ ?_ ?_)
        · exact Submodule.mem_sup_right (Submodule.subset_span ⟨b, b.2, rfl⟩)
        · exact Submodule.mem_sup_left (Submodule.subset_span ⟨b, b.2, rfl⟩)
    · have h1 : ∀ b, S.fr d Λ b ∈ Submodule.span E (Set.range (gens S (S.fr d Λ) (S.fr' d Λ))) :=
        fun b => Submodule.subset_span ⟨Sum.inl b, rfl⟩
      refine sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
      · rintro _ ⟨b, -, rfl⟩
        exact h1 b
      · rintro _ ⟨b, -, rfl⟩
        have h2 : S.fr' d Λ b = S.fr d Λ b +
            algebraMap F E S.th • gens S (S.fr d Λ) (S.fr' d Λ) (Sum.inr b) := by
          simp only [gens, Sum.elim_inr, smul_smul, ← map_mul, mul_inv_cancel₀ hth0, map_one, one_smul]
          abel
        rw [h2]
        exact Submodule.add_mem _ (h1 b)
          (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr b, rfl⟩))
  · set Gm : Matrix (Fin (2 * (r + 1))) (Fin (2 * (r + 1))) E :=
      Matrix.of fun i j => hf L S.Hm (gens S (S.fr d Λ) (S.fr' d Λ) (e i))
        (gens S (S.fr d Λ) (S.fr' d Λ) (e j)) with hGm
    have hGdet : Gm.det = algebraMap F E ((w0 : 𝒪[F]) : F) := by
      have : Gm = (Matrix.of fun i j => hf L S.Hm (gens S (S.fr d Λ) (S.fr' d Λ) i)
          (gens S (S.fr d Λ) (S.fr' d Λ) j)).submatrix e e := rfl
      rw [this, Matrix.det_submatrix_equiv_self, hdet, ← hw0]
    have hA : ∀ i j, Gm i j ∈ L.O := fun i j => hint _ (hg _) _ (hg _)
    let A : Matrix (Fin (2 * (r + 1))) (Fin (2 * (r + 1))) L.O := Matrix.of fun i j => ⟨Gm i j, hA i j⟩
    have hAG : A.map L.O.subtype = Gm := rfl
    have hadj : ∀ i j, Gm.adjugate i j ∈ L.O := fun i j => by
      have h4 : A.adjugate.map L.O.subtype = Gm.adjugate := by
        rw [← hAG]; exact RingHom.map_adjugate L.O.subtype A
      rw [← h4]
      exact Subtype.property _
    refine ⟨algebraMap F E (((w0⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) : F) • Gm.adjugate, fun i j => ?_, ?_⟩
    · rw [Matrix.smul_apply, smul_eq_mul]
      exact L.O.mul_mem ((algebraMap_mem_iff L _).2 (w0⁻¹ : (𝒪[F])ˣ).1.2) (hadj i j)
    · rw [Matrix.mul_smul, Matrix.mul_adjugate, hGdet, smul_smul, ← map_mul]
      have h8 : (((w0⁻¹ : (𝒪[F])ˣ) : 𝒪[F]) : F) * ((w0 : 𝒪[F]) : F) = 1 := by
        rw [← Subring.coe_mul, Units.inv_mul]; simp
      rw [h8, map_one, one_smul]

end GlobalTheory.HL.FrameUnimod
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameLatticeUnimodularGeneratorsExponentZeroStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.HL.StdPlace NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameLattice_unimodular_generators_exponent_zero : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.a = 0 → ∃ u : Fin (2 * (r + 1)) → S.V, S.M d Λ = Submodule.span L.O (Set.range u) ∧ Submodule.span E (Set.range u) = S.ME ∧ (∀ i j, hf L S.Hm (u i) (u j) ∈ L.O) ∧ ∃ P : Matrix (Fin (2 * (r + 1))) (Fin (2 * (r + 1))) E, IsIntM L P ∧ (Matrix.of fun i j => hf L S.Hm (u i) (u j)) * P = 1 := by
  first | exact @GlobalTheory.HL.FrameUnimod.frame_unimodular | exact GlobalTheory.HL.FrameUnimod.frame_unimodular | (intros; apply GlobalTheory.HL.FrameUnimod.frame_unimodular <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MinorSmulEqRowSpaceOfCofVecOrth
open NumberField Module Matrix Formalism.BasicNotions
open scoped ENNReal

namespace GlobalTheory

theorem minor_smul_eq_rowSpace_of_cofVec_orth (K V : Type) [Field K] [NumberField K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (r : ℕ)
    (Y : Matrix (Fin r) (Fin (r + 1)) (𝓞 K)) (b₀ : Fin (r + 1)) (u : Fin (r + 1) → V)
    (hu : ∑ b, Formalism.HermitianLatticeCounting.LatticeSumBounds.cofVec Y b • u b = 0) (b : Fin (r + 1)) :
    (Y.submatrix id b₀.succAbove).det • u b =
      ∑ a, Y a b • ∑ c, (Y.submatrix id b₀.succAbove).adjugate c a • u (b₀.succAbove c) := by
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff K]
  intro φ
  have hφ : ∀ (x : 𝓞 K) (v : V), φ (x • v) = algebraMap (𝓞 K) K x * φ v := by
    intro x v
    rw [← algebraMap_smul K x v, map_smul, smul_eq_mul]
  have hsub : ∀ b' : Fin (r + 1), (Y.map (algebraMap (𝓞 K) K)).submatrix id b'.succAbove
      = (algebraMap (𝓞 K) K).mapMatrix (Y.submatrix id b'.succAbove) := by
    intro b'; ext i j; simp
  have h0 : ∑ b, φ (u b) * Formalism.HermitianLatticeCounting.LatticeSumBounds.cofVec (Y.map (algebraMap (𝓞 K) K)) b = 0 := by
    have := congrArg φ hu
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_zero] at this
    rw [← this]
    refine Finset.sum_congr rfl fun b' _ => ?_
    rw [hφ, mul_comm]
    congr 1
    unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.cofVec
    rw [hsub, ← RingHom.map_det, map_mul, map_pow, map_neg, map_one]
  have h := congrFun ((Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.kernelRowSpace K r (Y.map (algebraMap (𝓞 K) K))).2
    (fun b => φ (u b)) h0 b₀) b
  rw [hsub, ← RingHom.map_det, ← RingHom.map_adjugate] at h
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sub, sub_eq_zero, hφ, map_sum]
  simp only [Pi.smul_apply, smul_eq_mul] at h
  rw [h]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.vecMul, dotProduct, hφ, map_sum, RingHom.mapMatrix_apply, Matrix.map_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [mul_comm]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [mul_comm]

theorem exists_reps_ideal_inv_lattice (K V : Type) [Field K] [NumberField K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (S0 : Submodule (𝓞 K) V) (J : Ideal (𝓞 K)) (hS : S0.FG)
    (hJ : J ≠ ⊥) :
    ∃ R : Finset V, R.card ≤ Ideal.absNorm J ^ finrank K (Submodule.span K (S0 : Set V)) ∧
      ∀ x : V, (∀ j ∈ J, j • x ∈ S0) → ∃ y ∈ R, x - y ∈ S0 := by
  classical
  let P : Submodule (𝓞 K) V :=
    { carrier := {x | ∀ j ∈ J, j • x ∈ S0}
      add_mem' := fun {a b} ha hb j hj => by
        rw [smul_add]; exact S0.add_mem (ha j hj) (hb j hj)
      zero_mem' := fun j hj => by simp
      smul_mem' := fun c x hx j hj => by
        rw [smul_comm]; exact S0.smul_mem c (hx j hj) }
  obtain ⟨j₀, hj₀, hj₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
  have hinj : Function.Injective (algebraMap (𝓞 K) K) := IsFractionRing.injective _ _
  have hj₀K : algebraMap (𝓞 K) K j₀ ≠ 0 := fun h => hj₀0 (hinj (by simpa using h))
  have : Module.IsTorsionFree (𝓞 K) V := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun c x h => ?_
    rw [← algebraMap_smul K c x, smul_eq_zero] at h
    rcases h with h | h
    · exact Or.inl (hinj (by simpa using h))
    · exact Or.inr h
  have : Module.Finite (𝓞 K) S0 := Module.Finite.iff_fg.mpr hS
  let f : P →ₗ[𝓞 K] S0 := (j₀ • P.subtype).codRestrict S0 (fun x => x.2 j₀ hj₀)
  have hf : Function.Injective f := by
    intro x y h
    have h' : j₀ • (x : V) = j₀ • (y : V) := congrArg Subtype.val h
    exact Subtype.ext (smul_right_injective V hj₀0 h')
  have : Module.Finite (𝓞 K) P := Module.Finite.of_injective f hf
  have : Module.FinitePresentation (𝓞 K) P := Module.finitePresentation_of_finite _ _
  have : Module.Flat (𝓞 K) P := inferInstance
  have : Module.Projective (𝓞 K) P := Module.Flat.projective_of_finitePresentation
  have hcard := Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.projQuotCard K P J hJ
  have hN : Ideal.absNorm J ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
  have hrk : finrank (𝓞 K) P ≤ finrank K (Submodule.span K (S0 : Set V)) := by
    obtain ⟨g, hg⟩ := exists_linearIndependent_of_le_finrank (R := 𝓞 K) (M := P) le_rfl
    have hmem : ∀ i, (g i : V) ∈ Submodule.span K (S0 : Set V) := by
      intro i
      have h1 : j₀ • (g i : V) ∈ Submodule.span K (S0 : Set V) :=
        Submodule.subset_span ((g i).2 j₀ hj₀)
      rw [← algebraMap_smul K j₀] at h1
      exact (Submodule.smul_mem_iff _ hj₀K).mp h1
    have hg1 : LinearIndependent (𝓞 K) (fun i => (g i : V)) :=
      hg.map' P.subtype (Submodule.ker_subtype P)
    have hg2 : LinearIndependent K (fun i => (g i : V)) :=
      (LinearIndependent.iff_fractionRing (𝓞 K) K).mp hg1
    have hg3 : LinearIndependent K
        (fun i => (⟨g i, hmem i⟩ : Submodule.span K (S0 : Set V))) :=
      LinearIndependent.of_comp (Submodule.span K (S0 : Set V)).subtype hg2
    simpa using hg3.fintype_card_le_finrank
  have : Finite (P ⧸ (J • ⊤ : Submodule (𝓞 K) P)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hN)
  have : Fintype (P ⧸ (J • ⊤ : Submodule (𝓞 K) P)) := Fintype.ofFinite _
  refine ⟨Finset.univ.image (fun q : P ⧸ (J • ⊤ : Submodule (𝓞 K) P) => ((Quotient.out q : P) : V)),
    ?_, ?_⟩
  · refine Finset.card_image_le.trans ?_
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hcard]
    exact Nat.pow_le_pow_right (Nat.pos_of_ne_zero hN) hrk
  · intro x hx
    let x' : P := ⟨x, hx⟩
    let q : P ⧸ (J • ⊤ : Submodule (𝓞 K) P) := Submodule.Quotient.mk x'
    refine ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ q), ?_⟩
    have h1 : x' - Quotient.out q ∈ (J • ⊤ : Submodule (𝓞 K) P) :=
      (Submodule.Quotient.eq _).mp (Quotient.out_eq q).symm
    have h2 : ∀ z ∈ (J • ⊤ : Submodule (𝓞 K) P), (z : V) ∈ S0 := by
      intro z hz
      refine Submodule.smul_induction_on hz (fun j hj n _ => n.2 j hj) (fun a b ha hb => ?_)
      exact S0.add_mem ha hb
    exact h2 _ h1

theorem exists_reps_cofVec_orth_mod_rowSpace :
    ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (S0 B : Submodule (𝓞 K) V) (I : Ideal (𝓞 K)) (r s : ℕ) (Y : Matrix (Fin r) (Fin (r + 1)) (𝓞 K)) (b₀ : Fin (r + 1)), S0.FG → finrank K (Submodule.span K (S0 : Set V)) = s → I ≠ ⊥ → I • B ≤ S0 → (Y.submatrix id b₀.succAbove).det ≠ 0 → ∃ reps : Finset (Fin (r + 1) → V), reps.card ≤ Ideal.absNorm (Ideal.span {(Y.submatrix id b₀.succAbove).det} * I) ^ (s * r) ∧ ∀ u : Fin (r + 1) → V, (∀ b, u b ∈ B) → ∑ b, Formalism.HermitianLatticeCounting.LatticeSumBounds.cofVec Y b • u b = 0 → ∃ u₀ ∈ reps, ∃ v : Fin r → V, (∀ a, v a ∈ S0) ∧ ∀ b, u b = u₀ b + ∑ a, Y a b • v a := by
  intro K V _ _ _ _ _ _ _ _ S0 B I r s Y b₀ hS hs hI hIB hd
  classical
  set d := (Y.submatrix id b₀.succAbove).det with hd_def
  have hJ : Ideal.span {d} * I ≠ ⊥ := by
    refine mul_ne_zero ?_ hI
    simpa using hd
  obtain ⟨R, hR, hrep⟩ := exists_reps_ideal_inv_lattice K V S0 _ hS hJ
  rw [hs] at hR
  have hdK : algebraMap (𝓞 K) K d ≠ 0 := fun h =>
    hd (IsFractionRing.injective (𝓞 K) K (by simpa using h))
  refine ⟨(Fintype.piFinset fun _ : Fin r => R).image (fun w b => ∑ a, Y a b • w a), ?_, ?_⟩
  · refine Finset.card_image_le.trans ?_
    rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_mul]
    exact Nat.pow_le_pow_left hR r
  · intro u huB hu
    let w : Fin r → V := fun a =>
      ∑ c, (Y.submatrix id b₀.succAbove).adjugate c a • u (b₀.succAbove c)
    have hwB : ∀ a, w a ∈ B := fun a =>
      B.sum_mem fun c _ => B.smul_mem _ (huB _)
    let v' : Fin r → V := fun a => (algebraMap (𝓞 K) K d)⁻¹ • w a
    have hdv : ∀ a, d • v' a = w a := fun a => by
      rw [← algebraMap_smul K d, smul_inv_smul₀ hdK]
    have huv : ∀ b, u b = ∑ a, Y a b • v' a := by
      intro b
      have h := minor_smul_eq_rowSpace_of_cofVec_orth K V r Y b₀ u hu b
      apply smul_right_injective V hdK
      simp only [algebraMap_smul]
      rw [h, Finset.smul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [smul_comm d, hdv]
    have hv' : ∀ a, ∀ j ∈ Ideal.span {d} * I, j • v' a ∈ S0 := by
      intro a j hj
      obtain ⟨i, hi, rfl⟩ := Ideal.mem_span_singleton_mul.mp hj
      rw [mul_comm, mul_smul, hdv]
      exact hIB (Submodule.smul_mem_smul hi (hwB a))
    choose y hyR hy using fun a => hrep (v' a) (hv' a)
    refine ⟨_, Finset.mem_image_of_mem _ (Fintype.mem_piFinset.mpr hyR), fun a => v' a - y a, hy, ?_⟩
    intro b
    rw [huv b, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← smul_add, add_sub_cancel]

end GlobalTheory
end
