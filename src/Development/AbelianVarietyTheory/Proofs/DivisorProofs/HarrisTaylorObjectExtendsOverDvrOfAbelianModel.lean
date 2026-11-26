module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleDiagonalExtendedBundleOfGeneric
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateSimilitudeGeometricPointsOfGenericDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisationKernelKilledOverDvrOfGeneric

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoPullbackExtendDVR
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoPullbackExtendDVR
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PullIsoExt

theorem isPullback_sq {S S' : Scheme.{0}} {G : Over S} {A : Over S'} {f : S' ⟶ S}
    {a : A.left ⟶ G.left} (hA : IsPullback a A.hom G.hom f)
    {φ₂ : (A ⊗ A).left ⟶ (G ⊗ G).left} (h : Geo.Tor.IsSquare a φ₂) :
    IsPullback φ₂ (A ⊗ A).hom (G ⊗ G).hom f := by
  have w₁ : (fst G G).left ≫ G.hom = (G ⊗ G).hom := Over.w _
  have w₂ : (snd G G).left ≫ G.hom = (G ⊗ G).hom := Over.w _
  have v₁ : (fst A A).left ≫ A.hom = (A ⊗ A).hom := Over.w _
  have v₂ : (snd A A).left ≫ A.hom = (A ⊗ A).hom := Over.w _
  have h₁ := h.1
  have h₂ := h.2
  refine ⟨⟨by rw [← w₁, reassoc_of% h₁, hA.w, reassoc_of% v₁]⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => pullback.lift
      (hA.lift (s.fst ≫ (fst G G).left) s.snd (by rw [Category.assoc, w₁, s.condition]))
      (hA.lift (s.fst ≫ (snd G G).left) s.snd (by rw [Category.assoc, w₂, s.condition]))
      (by rw [IsPullback.lift_snd, IsPullback.lift_snd])) (fun s => ?_) (fun s => ?_)
    (fun s m h1 h2 => ?_)⟩⟩
  · apply pullback.hom_ext
    · change _ ≫ (fst G G).left = _ ≫ (fst G G).left
      rw [Category.assoc, h₁, ← Category.assoc]
      exact (congrArg (· ≫ a) (pullback.lift_fst _ _ _)).trans (IsPullback.lift_fst _ _ _ _)
    · change _ ≫ (snd G G).left = _ ≫ (snd G G).left
      rw [Category.assoc, h₂, ← Category.assoc]
      exact (congrArg (· ≫ a) (pullback.lift_snd _ _ _)).trans (IsPullback.lift_fst _ _ _ _)
  · rw [← v₁, ← Category.assoc]
    exact (congrArg (· ≫ A.hom) (pullback.lift_fst _ _ _)).trans (IsPullback.lift_snd _ _ _ _)
  · apply pullback.hom_ext
    · refine Eq.trans ?_ (pullback.lift_fst _ _ _).symm
      change _ ≫ (fst A A).left = _
      apply hA.hom_ext
      · rw [IsPullback.lift_fst, ← h1, Category.assoc, Category.assoc, h₁]
      · rw [IsPullback.lift_snd, ← h2, ← v₁, Category.assoc]
    · refine Eq.trans ?_ (pullback.lift_snd _ _ _).symm
      change _ ≫ (snd A A).left = _
      apply hA.hom_ext
      · rw [IsPullback.lift_fst, ← h1, Category.assoc, Category.assoc, h₂]
      · rw [IsPullback.lift_snd, ← h2, ← v₂, Category.assoc]

theorem lbIso_pull_ext : ∀ (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (G : Over (Sp W)) [GrpObj G] (A : Over (Sp L)) [GrpObj A] (φ : A.left ⟶ G.left) (φ₂ : (G2 A).left ⟶ (G2 G).left), IsAbelianScheme G → IsGrpPullback A G (spMap (algebraMap W L)) φ → IsSquare φ φ₂ → ∀ (P : LB (G2 A).left) (P' : LB (G2 G).left), P.IsLB → P'.IsLB → LBIso P (P'.pull φ₂) → ∀ (a b : G2 A ⟶ G2 A) (a' b' : G2 G ⟶ G2 G), a.left ≫ φ₂ = φ₂ ≫ a'.left → b.left ≫ φ₂ = φ₂ ≫ b'.left → LBIso (P.pull a.left) (P.pull b.left) → LBIso (P'.pull a'.left) (P'.pull b'.left) := by
  intro W L _ _ _ _ _ _ G _ A _ φ φ₂ hG hφ hsq P P' hP hP' hPP' a b a' b' ha hb h
  have hpb : IsPullback φ₂ (G2 A).hom (G2 G).hom (spMap (algebraMap W L)) := isPullback_sq hφ.1 hsq
  have hG2 : IsAbelianScheme (G2 G) := ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.isAbelianScheme_tensor G G hG hG
  have side : ∀ (c : G2 A ⟶ G2 A) (c' : G2 G ⟶ G2 G), c.left ≫ φ₂ = φ₂ ≫ c'.left →
      LBIso ((P'.pull c'.left).pull φ₂) (P.pull c.left) := fun c c' hc =>
    LBIso.trans (pull_isLB (pull_isLB hP' _) _) (pull_isLB hP' _) (pull_isLB hP _)
      (GlobalTheory.GenSpread.lbIso_pull_pull hP' φ₂ hc).symm
      (GlobalTheory.GenSpread.lbIso_pull_of_lbIso hPP' c.left rfl).symm
  have key : LBIso ((P'.pull a'.left).pull φ₂) ((P'.pull b'.left).pull φ₂) :=
    LBIso.trans (pull_isLB (pull_isLB hP' _) _) (pull_isLB hP _) (pull_isLB (pull_isLB hP' _) _)
      (side a a' ha)
      (LBIso.trans (pull_isLB hP _) (pull_isLB hP _) (pull_isLB (pull_isLB hP' _) _) h (side b b' hb).symm)
  exact GlobalTheory.GenericIsoAb.lbIso_of_generic_pullback W L (G2 G) (G2 A).left (G2 A).hom φ₂ hG2 hpb
    (P'.pull a'.left) (P'.pull b'.left) (pull_isLB hP' _) (pull_isLB hP' _) key

end GlobalTheory.PullIsoExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoPullbackExtendDVRStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleIso_pullback_extend_DVR : ∀ (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (G : Over (Sp W)) [GrpObj G] (A : Over (Sp L)) [GrpObj A] (φ : A.left ⟶ G.left) (φ₂ : (G2 A).left ⟶ (G2 G).left), IsAbelianScheme G → IsGrpPullback A G (spMap (algebraMap W L)) φ → IsSquare φ φ₂ → ∀ (P : LB (G2 A).left) (P' : LB (G2 G).left), P.IsLB → P'.IsLB → LBIso P (P'.pull φ₂) → ∀ (a b : G2 A ⟶ G2 A) (a' b' : G2 G ⟶ G2 G), a.left ≫ φ₂ = φ₂ ≫ a'.left → b.left ≫ φ₂ = φ₂ ≫ b'.left → LBIso (P.pull a.left) (P.pull b.left) → LBIso (P'.pull a'.left) (P'.pull b'.left) := by
  first | exact @GlobalTheory.PullIsoExt.lbIso_pull_ext | exact GlobalTheory.PullIsoExt.lbIso_pull_ext | (intros; apply GlobalTheory.PullIsoExt.lbIso_pull_ext <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieConditionExtendsAbelianSchemeDvr
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenPartSplitsByIdempotentMatricesDomain
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenPartSplitsByIdempotentMatricesDomain
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT

namespace GlobalTheory.LieExtProj

open Matrix

variable {W : Type} [CommRing W] {n : ℕ} {R' : Type} [CommRing R'] (β : W →+* R') (v : Fin n → R')

theorem act_one : ((1 : Matrix (Fin n) (Fin n) W).map β) *ᵥ v = (1 : R') • v := by
  rw [Matrix.map_one _ (map_zero β) (map_one β), one_mulVec, one_smul]

theorem act_add {M N : Matrix (Fin n) (Fin n) W} {s s' : R'} (hM : (M.map β) *ᵥ v = s • v)
    (hN : (N.map β) *ᵥ v = s' • v) : ((M + N).map β) *ᵥ v = (s + s') • v := by
  rw [Matrix.map_add _ (map_add β), add_mulVec, hM, hN, add_smul]

theorem act_sub {M N : Matrix (Fin n) (Fin n) W} {s s' : R'} (hM : (M.map β) *ᵥ v = s • v)
    (hN : (N.map β) *ᵥ v = s' • v) : ((M - N).map β) *ᵥ v = (s - s') • v := by
  rw [Matrix.map_sub _ (map_sub β), sub_mulVec, hM, hN, sub_smul]

theorem act_smul {M : Matrix (Fin n) (Fin n) W} {s : R'} (r : W) (hM : (M.map β) *ᵥ v = s • v) :
    ((r • M).map β) *ᵥ v = (β r * s) • v := by
  have : (r • M).map β = β r • M.map β := by ext; simp
  rw [this, Matrix.smul_mulVec, hM, smul_smul]

theorem act_mul {M N : Matrix (Fin n) (Fin n) W} {s s' : R'} (hM : (M.map β) *ᵥ v = s • v)
    (hN : (N.map β) *ᵥ v = s' • v) : ((M * N).map β) *ᵥ v = (s * s') • v := by
  rw [Matrix.map_mul, ← mulVec_mulVec, hN, mulVec_smul, hM, smul_smul, mul_comm]

theorem act_list {κ : Type} (F : κ → Matrix (Fin n) (Fin n) W) (S : κ → R')
    (h : ∀ j, ((F j).map β) *ᵥ v = S j • v) (l : List κ) :
    (((l.map F).prod).map β) *ᵥ v = (l.map S).prod • v := by
  induction l with
  | nil => simpa using act_one β v
  | cons j l ih => simpa using act_mul β v (h j) ih

theorem act_finset {κ : Type} (F : κ → Matrix (Fin n) (Fin n) W) (S : κ → R')
    (h : ∀ j, ((F j).map β) *ᵥ v = S j • v) (s : Finset κ) :
    ((∑ j ∈ s, F j).map β) *ᵥ v = (∑ j ∈ s, S j) • v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj]; exact act_add β v (h j) ih

theorem act_finsupp {O : Type} (F : O → Matrix (Fin n) (Fin n) W) (S : O → R')
    (h : ∀ x, ((F x).map β) *ᵥ v = S x • v) (f : O →₀ W) :
    ((f.sum fun x r => r • F x).map β) *ᵥ v = (f.sum fun x r => β r * S x) • v :=
  act_finset β v _ _ (fun x => act_smul β v (f x) (h x)) f.support

theorem ext_mulVec {L : Type} [Field L] {M N : Matrix (Fin n) (Fin n) L} (h : ∀ x, M *ᵥ x = N *ᵥ x) : M = N :=
  Matrix.toLin'.injective (LinearMap.ext fun x => by simpa [Matrix.toLin'_apply] using h x)

end GlobalTheory.LieExtProj

namespace GlobalTheory.LieExtProj
open Matrix

theorem rhoPart_splits_by_idempotents : ∀ (W L : Type) [CommRing W] [IsDomain W] [Field L] [Algebra W L] [IsFractionRing W L] (O : Type) [CommRing O] (n a : ℕ) (A : O →+* Matrix (Fin n) (Fin n) W) (ω : O) (tr nm : ℤ) (ρ : W) (t : Fin a → (O →+* W)), ω ^ 2 - tr * ω + nm = 0 → ρ ^ 2 - tr * ρ + nm = 0 → (∀ i, t i ω = ρ) → (∀ i j, i ≠ j → Ideal.span (Set.range fun x => t i x - t j x) = ⊤) → IsUnit ((tr ^ 2 - 4 * nm : ℤ) : W) → (∀ v : Fin n → L, ((A ω).map (algebraMap W L)).mulVec v = algebraMap W L ρ • v → ∃ w : Fin a → Fin n → L, (∀ i c, ((A c).map (algebraMap W L)).mulVec (w i) = algebraMap W L (t i c) • w i) ∧ v = ∑ i, w i) → ∃ Q : Fin a → Matrix (Fin n) (Fin n) W, (∀ i, Q i * Q i = Q i) ∧ (∀ i c, A c * Q i = t i c • Q i) ∧ (∀ (R' : Type) [CommRing R'] (β : W →+* R') (v : Fin n → R'), ((A ω).map β).mulVec v = β ρ • v → v = ∑ i, ((Q i).map β).mulVec v) ∧ ∀ (R' : Type) [CommRing R'] (β : W →+* R') (i : Fin a) (v : Fin n → R'), (∀ c, ((A c).map β).mulVec v = β (t i c) • v) → ((Q i).map β).mulVec v = v := by
  intro W L _ _ _ _ _ O _ n a A ω tr nm ρ t hω hρ htω hcop hdisc hsplit
  classical
  have hu2 : (2 * ρ - tr) * (2 * ρ - tr) = ((tr ^ 2 - 4 * nm : ℤ) : W) := by
    push_cast; linear_combination 4 * hρ
  have hu : IsUnit (2 * ρ - (tr : W)) := isUnit_of_mul_isUnit_left (hu2 ▸ hdisc)
  obtain ⟨ui, hui⟩ := hu.exists_left_inv
  set P : Matrix (Fin n) (Fin n) W := ui • (A ω + (ρ - tr) • 1) with hPdef

  have hf : ∀ i j, ∃ f : O →₀ W, i ≠ j →
      (f.sum fun x r => r * t i x) - (f.sum fun x r => r * t j x) = 1 := by
    intro i j
    by_cases hij : i = j
    · exact ⟨0, fun h => (h hij).elim⟩
    · have h1 : (1 : W) ∈ Ideal.span (Set.range fun x => t i x - t j x) := by
        rw [hcop i j hij]; trivial
      obtain ⟨f, hf⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 h1
      refine ⟨f, fun _ => ?_⟩
      rw [← hf, ← Finsupp.sum_sub]
      simp [Finsupp.sum, smul_eq_mul, mul_sub]
  choose f hf using hf
  let Z : Fin a → Fin a → Matrix (Fin n) (Fin n) W := fun i j =>
    ((f i j).sum fun x r => r • A x) - ((f i j).sum fun x r => r * t j x) • (1 : Matrix (Fin n) (Fin n) W)
  let E : Fin a → Matrix (Fin n) (Fin n) W := fun i =>
    ((List.finRange a).map fun j => if j = i then 1 else Z i j).prod
  let Q : Fin a → Matrix (Fin n) (Fin n) W := fun i => E i * P

  have hP : ∀ (R' : Type) [CommRing R'] (β : W →+* R') (v : Fin n → R'),
      ((A ω).map β) *ᵥ v = β ρ • v → (P.map β) *ᵥ v = v := by
    intro R' _ β v hv
    have h := act_smul β v ui (act_add β v hv (act_smul β v (ρ - tr) (act_one β v)))
    rw [h]
    have : β ui * (β ρ + β (ρ - tr) * 1) = β (ui * (2 * ρ - tr)) := by
      simp only [map_mul, map_sub, map_ofNat, _root_.mul_one]; ring
    rw [this, hui, map_one, one_smul]

  have hE : ∀ (R' : Type) [CommRing R'] (β : W →+* R') (k i : Fin a) (v : Fin n → R'),
      (∀ c, ((A c).map β) *ᵥ v = β (t k c) • v) → ((E i).map β) *ᵥ v = (if k = i then (1 : R') else 0) • v := by
    intro R' _ β k i v hv
    have hZ : ∀ j, ((if j = i then 1 else Z i j).map β) *ᵥ v =
        (if j = i then 1 else β ((f i j).sum fun x r => r * t k x) - β ((f i j).sum fun x r => r * t j x)) • v := by
      intro j
      split_ifs
      · exact act_one β v
      · have h1 := act_finsupp β v (fun x => A x) (fun x => β (t k x)) hv (f i j)
        have h2 := act_sub β v h1 (act_smul β v ((f i j).sum fun x r => r * t j x) (act_one β v))
        refine h2.trans ?_
        congr 1
        set_option synthInstance.maxHeartbeats 100000 in
          simp [Finsupp.sum, map_sum, map_mul]
    rw [act_list β v _ _ hZ]
    by_cases hki : k = i
    · rw [if_pos hki]
      subst hki
      refine congrArg (· • v) ?_
      apply List.prod_eq_one
      intro x hx
      obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
      split_ifs with hj
      · rfl
      · rw [← map_sub, hf k j (Ne.symm hj), map_one]
    · rw [if_neg hki]
      refine congrArg (· • v) ?_
      apply List.prod_eq_zero
      refine List.mem_map.2 ⟨k, List.mem_finRange k, ?_⟩
      rw [if_neg hki, sub_self]
  have hQ : ∀ (R' : Type) [CommRing R'] (β : W →+* R') (k i : Fin a) (v : Fin n → R'),
      (∀ c, ((A c).map β) *ᵥ v = β (t k c) • v) → ((Q i).map β) *ᵥ v = (if k = i then (1 : R') else 0) • v := by
    intro R' _ β k i v hv
    have h1 : (P.map β) *ᵥ v = (1 : R') • v := by
      rw [one_smul]; exact hP R' β v (by rw [hv, htω])
    have h2 := hE R' β k i v hv
    have h3 := act_mul β v h2 h1
    rw [_root_.mul_one] at h3
    exact h3

  have hAP : A ω * P = ρ • P := by
    have hω' : ω * ω = (tr : O) * ω - (nm : O) := by linear_combination hω
    have hA2 : A ω * A ω = (tr : W) • A ω - (nm : W) • (1 : Matrix (Fin n) (Fin n) W) := by
      rw [← map_mul, hω', map_sub, map_mul, map_intCast, map_intCast]
      rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul, zsmul_one, ← zsmul_eq_mul]
    have hnm : (nm : W) = tr * ρ - ρ ^ 2 := by linear_combination hρ
    rw [hPdef, mul_smul_comm, mul_add, mul_smul_comm, _root_.mul_one, hA2, hnm]
    module

  set βL := algebraMap W L
  have hinj : Function.Injective fun M : Matrix (Fin n) (Fin n) W => M.map βL :=
    Matrix.map_injective (IsFractionRing.injective W L)
  have hdec : ∀ x : Fin n → L, ∃ w : Fin a → Fin n → L,
      (∀ i, ((Q i).map βL) *ᵥ x = w i) ∧ (∀ i c, ((A c).map βL) *ᵥ w i = βL (t i c) • w i) ∧
      (P.map βL) *ᵥ x = ∑ i, w i := by
    intro x
    have hy : ((A ω).map βL) *ᵥ ((P.map βL) *ᵥ x) = βL ρ • ((P.map βL) *ᵥ x) := by
      rw [mulVec_mulVec, ← Matrix.map_mul, hAP]
      have : (ρ • P).map βL = βL ρ • P.map βL := by ext; simp
      rw [this, Matrix.smul_mulVec]
    obtain ⟨w, hw, hsum⟩ := hsplit _ hy
    refine ⟨w, fun i => ?_, hw, hsum⟩
    show ((E i * P).map βL) *ᵥ x = w i
    rw [Matrix.map_mul, ← mulVec_mulVec, hsum, mulVec_sum]
    rw [Finset.sum_eq_single i]
    · rw [hE L βL i i (w i) (hw i), if_pos rfl, one_smul]
    · intro k _ hk; rw [hE L βL k i (w k) (hw k), if_neg hk, zero_smul]
    · intro h; exact absurd (Finset.mem_univ i) h
  choose w hwQ hwA hwP using hdec
  have hsumQ : ∑ i, Q i = P := by
    apply hinj
    apply ext_mulVec
    intro x
    simp only
    rw [hwP x]
    have : (∑ i, Q i).map βL = ∑ i, (Q i).map βL := by ext; simp [Matrix.sum_apply]
    rw [this, Matrix.sum_mulVec]
    exact Finset.sum_congr rfl fun i _ => hwQ x i
  refine ⟨Q, fun i => ?_, fun i c => ?_, ?_, ?_⟩
  · apply hinj
    apply ext_mulVec
    intro x
    simp only
    rw [Matrix.map_mul, ← mulVec_mulVec, hwQ x i, hQ L βL i i _ (hwA x i), if_pos rfl, one_smul]
  · apply hinj
    apply ext_mulVec
    intro x
    simp only
    have : (t i c • Q i).map βL = βL (t i c) • (Q i).map βL := by ext; simp
    rw [Matrix.map_mul, ← mulVec_mulVec, hwQ x i, hwA x i c, this, Matrix.smul_mulVec, hwQ x i]
  · intro R' _ β v hv
    have : (∑ i, Q i).map β = ∑ i, (Q i).map β := by ext; simp [Matrix.sum_apply]
    rw [← Matrix.sum_mulVec, ← this, hsumQ, hP R' β v hv]
  · intro R' _ β i v hv
    rw [hQ R' β i i v hv, if_pos rfl, one_smul]

end GlobalTheory.LieExtProj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenPartSplitsByIdempotentMatricesDomainStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenPart_splits_by_idempotent_matrices_domain : ∀ (W L : Type) [CommRing W] [IsDomain W] [Field L] [Algebra W L] [IsFractionRing W L] (O : Type) [CommRing O] (n a : ℕ) (A : O →+* Matrix (Fin n) (Fin n) W) (ω : O) (tr nm : ℤ) (ρ : W) (t : Fin a → (O →+* W)), ω ^ 2 - tr * ω + nm = 0 → ρ ^ 2 - tr * ρ + nm = 0 → (∀ i, t i ω = ρ) → (∀ i j, i ≠ j → Ideal.span (Set.range fun x => t i x - t j x) = ⊤) → IsUnit ((tr ^ 2 - 4 * nm : ℤ) : W) → (∀ v : Fin n → L, ((A ω).map (algebraMap W L)).mulVec v = algebraMap W L ρ • v → ∃ w : Fin a → Fin n → L, (∀ i c, ((A c).map (algebraMap W L)).mulVec (w i) = algebraMap W L (t i c) • w i) ∧ v = ∑ i, w i) → ∃ Q : Fin a → Matrix (Fin n) (Fin n) W, (∀ i, Q i * Q i = Q i) ∧ (∀ i c, A c * Q i = t i c • Q i) ∧ (∀ (R' : Type) [CommRing R'] (β : W →+* R') (v : Fin n → R'), ((A ω).map β).mulVec v = β ρ • v → v = ∑ i, ((Q i).map β).mulVec v) ∧ ∀ (R' : Type) [CommRing R'] (β : W →+* R') (i : Fin a) (v : Fin n → R'), (∀ c, ((A c).map β).mulVec v = β (t i c) • v) → ((Q i).map β).mulVec v = v := by
  first | (exact @GlobalTheory.LieExtProj.rhoPart_splits_by_idempotents) | (exact GlobalTheory.LieExtProj.rhoPart_splits_by_idempotents) | (intros; apply GlobalTheory.LieExtProj.rhoPart_splits_by_idempotents  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRankIdempotentMatrixLocalRingMapField
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRankIdempotentMatrixLocalRingMapField
open Matrix

namespace GlobalTheory.IdemRankLocal

theorem exists_conj_diag (W : Type) [CommRing W] [IsLocalRing W] (n : ℕ)
    (p : Matrix (Fin n) (Fin n) W) (hp : p * p = p) :
    ∃ (r : ℕ) (P P' : Matrix (Fin n) (Fin n) W), P * P' = 1 ∧
    p = P * Matrix.diagonal (fun i : Fin n => if i.val < r then (1 : W) else 0) * P' := by
  classical
  set f : (Fin n → W) →ₗ[W] (Fin n → W) := Matrix.toLin' p with hfdef
  have hf : IsIdempotentElem f := by
    show f * f = f
    rw [Module.End.mul_eq_comp, hfdef, ← Matrix.toLin'_mul, hp]
  have hc := LinearMap.IsIdempotentElem.isCompl hf
  haveI : Module.Projective W (LinearMap.range f) :=
    Module.Projective.of_split (LinearMap.range f).subtype
      (Submodule.linearProjOfIsCompl _ _ hc)
      (LinearMap.ext fun x => Submodule.linearProjOfIsCompl_apply_left hc x)
  haveI : Module.Projective W (LinearMap.ker f) :=
    Module.Projective.of_split (LinearMap.ker f).subtype
      (Submodule.linearProjOfIsCompl _ _ hc.symm)
      (LinearMap.ext fun x => Submodule.linearProjOfIsCompl_apply_left hc.symm x)
  haveI : Module.Finite W (LinearMap.range f) :=
    Module.Finite.of_surjective (Submodule.linearProjOfIsCompl _ _ hc)
      (Submodule.linearProjOfIsCompl_surjective hc)
  haveI : Module.Finite W (LinearMap.ker f) :=
    Module.Finite.of_surjective (Submodule.linearProjOfIsCompl _ _ hc.symm)
      (Submodule.linearProjOfIsCompl_surjective hc.symm)
  haveI : Module.Free W (LinearMap.range f) := Module.free_of_flat_of_isLocalRing
  haveI : Module.Free W (LinearMap.ker f) := Module.free_of_flat_of_isLocalRing
  set r := Module.finrank W (LinearMap.range f)
  set s := Module.finrank W (LinearMap.ker f)
  let b1 := Module.finBasis W (LinearMap.range f)
  let b2 := Module.finBasis W (LinearMap.ker f)
  let bs : Module.Basis (Fin r ⊕ Fin s) W (Fin n → W) :=
    (b1.prod b2).map (Submodule.prodEquivOfIsCompl _ _ hc)
  have hrs : r + s = n := by
    have := Module.finrank_eq_card_basis bs
    simpa [Fintype.card_sum] using this.symm
  have hbs1 : ∀ i, f (bs (Sum.inl i)) = bs (Sum.inl i) := by
    intro i
    simp only [bs, Module.Basis.map_apply, Module.Basis.prod_apply]
    simp
    obtain ⟨y, hy⟩ := (b1 i).2
    rw [← hy]
    exact LinearMap.congr_fun hf y
  have hbs2 : ∀ i, f (bs (Sum.inr i)) = 0 := by
    intro i
    simp only [bs, Module.Basis.map_apply, Module.Basis.prod_apply]
    simp
  let b : Module.Basis (Fin n) W (Fin n → W) := bs.reindex (finSumFinEquiv.trans (finCongr hrs))
  have hb : ∀ j : Fin n, f (b j) = (if j.val < r then (1 : W) else 0) • b j := by
    intro j
    have hj : b j = bs ((finSumFinEquiv.trans (finCongr hrs)).symm j) := Module.Basis.reindex_apply _ _ _
    rw [hj]
    by_cases h : j.val < r
    · have : (finSumFinEquiv.trans (finCongr hrs)).symm j = Sum.inl ⟨j, h⟩ := by
        apply (finSumFinEquiv.trans (finCongr hrs)).injective
        ext; simp
      rw [this, if_pos h, one_smul, hbs1]
    · have : (finSumFinEquiv.trans (finCongr hrs)).symm j = Sum.inr ⟨j.val - r, by omega⟩ := by
        apply (finSumFinEquiv.trans (finCongr hrs)).injective
        ext; simp; omega
      rw [this, if_neg h, zero_smul, hbs2]
  have hdiag : LinearMap.toMatrix b b f = Matrix.diagonal (fun i : Fin n => if i.val < r then (1 : W) else 0) := by
    ext i j
    rw [LinearMap.toMatrix_apply, hb j, map_smul, b.repr_self]
    by_cases hij : i = j
    · subst hij; simp; split_ifs <;> simp
    · simp [Matrix.diagonal_apply_ne _ hij, Finsupp.single_apply, Ne.symm hij]
      split_ifs <;> simp [Finsupp.single_apply, Ne.symm hij]
  let e := Pi.basisFun W (Fin n)
  refine ⟨r, e.toMatrix b, b.toMatrix e, ?_, ?_⟩
  · exact Module.Basis.toMatrix_mul_toMatrix_flip e b
  · have := basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix e b e b f
    rw [← hdiag, this, LinearMap.toMatrix_eq_toMatrix', hfdef, LinearMap.toMatrix'_toLin']

theorem rank_map_const : ∀ (W : Type) [CommRing W] [IsLocalRing W] (n : ℕ) (Q : Matrix (Fin n) (Fin n) W),
    Q * Q = Q → ∃ r : ℕ, ∀ (k : Type) [Field k] (β : W →+* k), (Q.map β).rank = r := by
  intro W _ _ n Q hQ
  classical
  obtain ⟨r, P, P', hPP', hQeq⟩ := exists_conj_diag W n Q hQ
  refine ⟨Fintype.card {i : Fin n // i.val < r}, fun k _ β => ?_⟩
  have hm : P.map β * P'.map β = 1 := by
    rw [← Matrix.map_mul, hPP', Matrix.map_one _ β.map_zero β.map_one]
  have hP : IsUnit (P.map β).det := Matrix.isUnit_det_of_right_inverse hm
  have hP' : IsUnit (P'.map β).det := Matrix.isUnit_det_of_left_inverse hm
  rw [hQeq, Matrix.map_mul, Matrix.map_mul, Matrix.rank_mul_eq_left_of_isUnit_det _ _ hP',
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ hP, Matrix.diagonal_map β.map_zero,
    Matrix.rank_diagonal]
  exact Fintype.card_congr (Equiv.subtypeEquivRight (fun i => by split_ifs with h <;> simp [h]))

end GlobalTheory.IdemRankLocal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRankIdempotentMatrixLocalRingMapFieldStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rank_idempotent_matrix_local_ring_map_field : ∀ (W : Type) [CommRing W] [IsLocalRing W] (n : ℕ) (Q : Matrix (Fin n) (Fin n) W), Q * Q = Q → ∃ r : ℕ, ∀ (k : Type) [Field k] (β : W →+* k), (Q.map β).rank = r := by
  first | exact @GlobalTheory.IdemRankLocal.rank_map_const | exact GlobalTheory.IdemRankLocal.rank_map_const | (intros; apply GlobalTheory.IdemRankLocal.rank_map_const <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieConditionExtendsAbelianSchemeDvr
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT

namespace GlobalTheory.LieExt

theorem prod_ofFn_eq {X : Type*} [Monoid X] {V : Type*} [AddCommMonoid V] (T : V → X)
    (h0 : T 0 = 1) (hadd : ∀ c c', T (c + c') = T c * T c') :
    ∀ {a : ℕ} (w : Fin a → V), (List.ofFn (fun i => T (w i))).prod = T (∑ i, w i)
  | 0, w => by simp [h0]
  | a + 1, w => by
    rw [List.ofFn_succ, List.prod_cons, prod_ofFn_eq T h0 hadd (fun i => w i.succ), Fin.sum_univ_succ, hadd]

theorem lie_ext : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G], IsAbelianScheme G → ∀ (act : OActN D.O G) (ρ : W) (t : Fin D.a → (𝓞 D.F →+* W)), (∀ i, t i D.ω = ρ) → ρ ^ 2 - D.tr * ρ + D.nm = 0 → (∀ i j, i ≠ j → Ideal.span (Set.range fun x => t i x - t j x) = ⊤) → IsUnit ((D.tr ^ 2 - 4 * D.nm : ℤ) : W) → (∀ (R' : Type) [CommRing R'] (β : L →+* R'), ∀ v : epsPtR (spMap (β.comp (algebraMap W L))) ⟶ G, IsTanScal act (spMap (β.comp (algebraMap W L))) (algebraMap (𝓞 D.F) D.O D.ω) (β (algebraMap W L ρ)) v → ∃ w : Fin D.a → (epsPtR (spMap (β.comp (algebraMap W L))) ⟶ G), (∀ i, ∀ c : 𝓞 D.F, IsTanScal act (spMap (β.comp (algebraMap W L))) (algebraMap (𝓞 D.F) D.O c) (β (algebraMap W L (t i c))) (w i)) ∧ v = (List.ofFn w).prod) → (∀ (k : Type) [Field k] [IsAlgClosed k] (β : L →+* k) i, LieMult (act.toF D) (spMap (β.comp (algebraMap W L))) ((β.comp (algebraMap W L)).comp (t i)) D.m) → (∀ (R' : Type) [CommRing R'] (β : W →+* R'), ∀ v : epsPtR (spMap β) ⟶ G, IsTanScal act (spMap β) (algebraMap (𝓞 D.F) D.O D.ω) (β ρ) v → ∃ w : Fin D.a → (epsPtR (spMap β) ⟶ G), (∀ i, ∀ c : 𝓞 D.F, IsTanScal act (spMap β) (algebraMap (𝓞 D.F) D.O c) (β (t i c)) (w i)) ∧ v = (List.ofFn w).prod) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (β : W →+* k) i, LieMult (act.toF D) (spMap β) (β.comp (t i)) D.m := by
  intro p _ D W L _ _ _ _ _ _ G _ _ hab act ρ t htω hρ hcomax hdisc hgen hrank
  have hsm : Smooth G.hom := hab.smooth
  obtain ⟨n, M, hM⟩ := GlobalTheory.T.exists_tangent_coords_base_change_smooth_comm_group W G hsm

  have hT0 : ∀ {X : Type} [Group X] {V : Type} [AddCommMonoid V] (T : V → X),
      (∀ c c', T (c + c') = T c * T c') → T 0 = 1 := fun T h => by
    have := h 0 0
    rw [add_zero] at this
    exact mul_eq_left.mp this.symm
  obtain ⟨T₀, hinj₀, -, hadd₀, -, heq₀⟩ := hM W (RingHom.id W)
  have hmap : ∀ X : Matrix (Fin n) (Fin n) W, X.map (RingHom.id W) = X := fun X => by ext; simp
  have hext : ∀ X Y : Matrix (Fin n) (Fin n) W, (∀ c, T₀ (X.mulVec c) = T₀ (Y.mulVec c)) → X = Y := by
    intro X Y h
    ext i j
    have := congrFun (hinj₀ (h (Pi.single j 1))) i
    simpa [Matrix.mulVec_single_one] using this
  let Am : 𝓞 D.F → Matrix (Fin n) (Fin n) W := fun c => M (act.act (algebraMap (𝓞 D.F) D.O c))
  have hAm : ∀ c x, T₀ x ≫ act.act (algebraMap (𝓞 D.F) D.O c) = T₀ ((Am c).mulVec x) := fun c x => by
    simpa [hmap] using heq₀ _ (act.hom _) x
  let A : 𝓞 D.F →+* Matrix (Fin n) (Fin n) W := RingHom.mk'
    { toFun := Am
      map_one' := hext _ _ fun x => by
        rw [Matrix.one_mulVec, ← hAm, map_one, act.one, Category.comp_id]
      map_mul' := fun c d => hext _ _ fun x => by
        rw [← hAm, map_mul, act.mul, ← Category.assoc, hAm, hAm, Matrix.mulVec_mulVec] }
    (fun c d => hext _ _ fun x => by
      show T₀ ((Am (c + d)).mulVec x) = T₀ ((Am c + Am d).mulVec x)
      rw [← hAm, map_add (f := _), act.add, MonObj.comp_mul, hAm, hAm, ← hadd₀, Matrix.add_mulVec])
  have hA : ∀ c, A c = M (act.act (algebraMap (𝓞 D.F) D.O c)) := fun c => rfl

  have tanT : ∀ (R' : Type) [CommRing R'] (β : W →+* R') (T : (Fin n → R') → (epsPtR (spMap β) ⟶ G)),
      Function.Injective T →
      (∀ (s : R') c, (T (s • c)).left = spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsScaleR s) ≫ (T c).left) →
      (∀ u : G ⟶ G, IsMonHom u → ∀ c, T c ≫ u = T (((M u).map β).mulVec c)) →
      (∀ v : epsPtR (spMap β) ⟶ G, spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ v.left =
        (1 : Over.mk (spMap β) ⟶ G).left ↔ v ∈ Set.range T) →
      ∀ (c : 𝓞 D.F) (s : R') (x : Fin n → R'),
        IsTanScal act (spMap β) (algebraMap (𝓞 D.F) D.O c) s (T x) ↔ ((A c).map β).mulVec x = s • x := by
    intro R' _ β T hinj hscale heq hrange c s x
    have hact : T x ≫ act.act (algebraMap (𝓞 D.F) D.O c) = T (((A c).map β).mulVec x) :=
      heq _ (act.hom _) x
    constructor
    · rintro ⟨-, h2⟩
      refine hinj (Over.OverMorphism.ext ?_)
      rw [← hact, h2, hscale]
    · intro hx
      refine ⟨(hrange _).2 ⟨x, rfl⟩, ?_⟩
      rw [hact, hx, hscale]
  have hωroot : D.ω ^ 2 - (D.tr : 𝓞 D.F) * D.ω + (D.nm : 𝓞 D.F) = 0 := by
    rw [← D.tr_eq, ← D.nm_eq]; ring
  have hβL : (RingHom.id L).comp (algebraMap W L) = algebraMap W L := RingHom.id_comp _
  obtain ⟨Q, hQ1, hQ2, hQ3, hQ4⟩ := GlobalTheory.T.eigenPart_splits_by_idempotent_matrices_domain W L (𝓞 D.F) n D.a A D.ω D.tr D.nm ρ t hωroot hρ htω hcomax hdisc
    (by
      intro v hv
      obtain ⟨T, hinj, hrange, hadd, hscale, heq⟩ := hM L ((RingHom.id L).comp (algebraMap W L))
      have tv := (tanT L _ T hinj hscale heq hrange D.ω ((RingHom.id L) (algebraMap W L ρ)) v).2
        (by rw [hβL, RingHom.id_apply]; exact hv)
      obtain ⟨w, hw, hvw⟩ := hgen L (RingHom.id L) (T v) tv
      have hy : ∀ i, ∃ y, w i = T y := fun i => by obtain ⟨y, h⟩ := (hrange _).1 (hw i 0).1; exact ⟨y, h.symm⟩
      choose y hy using hy
      refine ⟨y, fun i c => ?_, ?_⟩
      · have := (tanT L _ T hinj hscale heq hrange c _ (y i)).1 (by rw [← hy]; exact hw i c)
        rwa [hβL, RingHom.id_apply] at this
      · apply hinj
        rw [hvw, ← prod_ofFn_eq T (hT0 T hadd) hadd]
        exact congrArg List.prod (congrArg List.ofFn (funext hy)))
  have hmapsmul : ∀ (R' : Type) [CommRing R'] (β : W →+* R') (s : W) (X : Matrix (Fin n) (Fin n) W),
      (s • X).map β = β s • X.map β := fun R' _ β s X => by ext; simp
  have heig : ∀ (R' : Type) [CommRing R'] (β : W →+* R') i c (x : Fin n → R'),
      ((A c).map β).mulVec (((Q i).map β).mulVec x) = β (t i c) • (((Q i).map β).mulVec x) := by
    intro R' _ β i c x
    rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, hQ2, hmapsmul, Matrix.smul_mulVec]

  have rk : ∀ (k : Type) [Field k] (β : W →+* k) i,
      LieMult (act.toF D) (spMap β) (β.comp (t i)) D.m ↔ ((Q i).map β).rank = D.m := by
    intro k _ β i
    obtain ⟨T, hinj, hrange, hadd, hscale, heq⟩ := hM k β
    rw [GlobalTheory.T.lieMult_iff_finrank_common_eigenspace_coords W G (𝓞 D.F) (act.toF D) n k β T (fun c => (A c).map β) hinj hrange hadd hscale
      (fun c x => heq _ (act.hom _) x)]
    have hsub : (⨅ c, LinearMap.ker (Matrix.mulVecLin ((A c).map β) - (β.comp (t i)) c • LinearMap.id) :
        Submodule k (Fin n → k)) = LinearMap.range ((Q i).map β).mulVecLin := by
      ext y
      simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, Matrix.mulVecLin_apply,
        LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero, LinearMap.mem_range, RingHom.comp_apply]
      constructor
      · intro h
        exact ⟨y, hQ4 k β i y h⟩
      · rintro ⟨z, rfl⟩ c
        exact heig k β i c z
    rw [hsub]
    rfl
  refine ⟨fun R' _ β v hv => ?_, fun k _ _ β i => ?_⟩
  · obtain ⟨T, hinj, hrange, hadd, hscale, heq⟩ := hM R' β
    obtain ⟨x, rfl⟩ := (hrange v).1 hv.1
    have hx := (tanT R' β T hinj hscale heq hrange D.ω (β ρ) x).1 hv
    refine ⟨fun i => T (((Q i).map β).mulVec x), fun i c =>
      (tanT R' β T hinj hscale heq hrange c _ _).2 (heig R' β i c x), ?_⟩
    rw [prod_ofFn_eq T (hT0 T hadd) hadd, ← hQ3 R' β x hx]
  · obtain ⟨r, hr⟩ := GlobalTheory.T.exists_rank_idempotent_matrix_local_ring_map_field W n (Q i) (hQ1 i)
    refine (rk k β i).2 ?_
    rw [hr, ← hr (AlgebraicClosure L) ((algebraMap L (AlgebraicClosure L)).comp (algebraMap W L))]
    exact (rk _ _ i).1 (hrank (AlgebraicClosure L) (algebraMap L (AlgebraicClosure L)) i)

end GlobalTheory.LieExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieConditionExtendsAbelianSchemeDvrStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_lie_condition_extends_abelianScheme_dvr : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G], IsAbelianScheme G → ∀ (act : OActN D.O G) (ρ : W) (t : Fin D.a → (𝓞 D.F →+* W)), (∀ i, t i D.ω = ρ) → ρ ^ 2 - D.tr * ρ + D.nm = 0 → (∀ i j, i ≠ j → Ideal.span (Set.range fun x => t i x - t j x) = ⊤) → IsUnit ((D.tr ^ 2 - 4 * D.nm : ℤ) : W) → (∀ (R' : Type) [CommRing R'] (β : L →+* R'), ∀ v : epsPtR (spMap (β.comp (algebraMap W L))) ⟶ G, IsTanScal act (spMap (β.comp (algebraMap W L))) (algebraMap (𝓞 D.F) D.O D.ω) (β (algebraMap W L ρ)) v → ∃ w : Fin D.a → (epsPtR (spMap (β.comp (algebraMap W L))) ⟶ G), (∀ i, ∀ c : 𝓞 D.F, IsTanScal act (spMap (β.comp (algebraMap W L))) (algebraMap (𝓞 D.F) D.O c) (β (algebraMap W L (t i c))) (w i)) ∧ v = (List.ofFn w).prod) → (∀ (k : Type) [Field k] [IsAlgClosed k] (β : L →+* k) i, LieMult (act.toF D) (spMap (β.comp (algebraMap W L))) ((β.comp (algebraMap W L)).comp (t i)) D.m) → (∀ (R' : Type) [CommRing R'] (β : W →+* R'), ∀ v : epsPtR (spMap β) ⟶ G, IsTanScal act (spMap β) (algebraMap (𝓞 D.F) D.O D.ω) (β ρ) v → ∃ w : Fin D.a → (epsPtR (spMap β) ⟶ G), (∀ i, ∀ c : 𝓞 D.F, IsTanScal act (spMap β) (algebraMap (𝓞 D.F) D.O c) (β (t i c)) (w i)) ∧ v = (List.ofFn w).prod) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (β : W →+* k) i, LieMult (act.toF D) (spMap β) (β.comp (t i)) D.m := by
  first | exact @GlobalTheory.LieExt.lie_ext | exact GlobalTheory.LieExt.lie_ext | (intros; apply GlobalTheory.LieExt.lie_ext <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperGroupSchemeDvrSectionsMulEquivGeneric
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperGroupSchemeDvrSectionsMulEquivGeneric
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
namespace GlobalTheory.LevExt

noncomputable def pullPtsEquiv {S S' : Scheme.{0}} (A : Over S') [GrpObj A] (G : Over S) [GrpObj G] (f : S' ⟶ S)
    (φ : A.left ⟶ G.left) (h : IsGrpPullback A G f φ) (T : Over S') :
    (T ⟶ A) ≃* (Over.mk (T.hom ≫ f) ⟶ G) :=
  MulEquiv.mk' (Equiv.ofBijective
    (fun x => Over.homMk (x.left ≫ φ) (by
      simp only [Over.mk_hom, Category.assoc]
      rw [h.1.w, ← Category.assoc, Over.w]))
    (by
      constructor
      · intro x x' hx
        have hx' : x.left ≫ φ = x'.left ≫ φ := congrArg CommaMorphism.left hx
        ext1
        exact h.1.hom_ext hx' (by rw [Over.w, Over.w])
      · intro z
        refine ⟨Over.homMk (h.1.lift z.left T.hom (by simpa using z.w)) (by simp), ?_⟩
        ext1
        exact h.1.lift_fst _ _ _))
    (by
      intro x y
      ext1
      exact (h.2 T x y (Over.homMk (x.left ≫ φ) (by
          simp only [Over.mk_hom, Category.assoc]
          rw [h.1.w, ← Category.assoc, Over.w])) (Over.homMk (y.left ≫ φ) (by
          simp only [Over.mk_hom, Category.assoc]
          rw [h.1.w, ← Category.assoc, Over.w])) rfl rfl).symm)

noncomputable def precompEquiv {C : Type*} [Category C] [CartesianMonoidalCategory C] {T₁ T₂ M : C} [GrpObj M]
    (i : T₁ ≅ T₂) : (T₂ ⟶ M) ≃* (T₁ ⟶ M) where
  toFun x := i.hom ≫ x
  invFun x := i.inv ≫ x
  left_inv x := by simp
  right_inv x := by simp
  map_mul' x y := MonObj.comp_mul _ _ _

end GlobalTheory.LevExt

namespace GlobalTheory.LevExt

theorem sections_generic_mulEquiv : ∀ (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (G : Over (Sp W)) [GrpObj G] (A : Over (Sp L)) [GrpObj A] (φ : A.left ⟶ G.left), IsProper G.hom → IsGrpPullback A G (spMap (algebraMap W L)) φ → ∃ e : (𝟙_ (Over (Sp L)) ⟶ A) ≃* (𝟙_ (Over (Sp W)) ⟶ G), ∀ y, y.left ≫ φ = spMap (algebraMap W L) ≫ (e y).left := by
  intro W L _ _ _ _ _ _ G _ A _ φ hP hφ
  obtain ⟨e1, he1⟩ := GlobalTheory.T.proper_group_scheme_points_valuationRing_mulEquiv W L (Sp W) G hP (𝟙 (Sp W))
  let i : Over.mk (spMap (algebraMap W L) ≫ 𝟙 (Sp W)) ≅ Over.mk ((𝟙_ (Over (Sp L))).hom ≫ spMap (algebraMap W L)) :=
    Over.isoMk (Iso.refl _) (by simp)
  let e : (𝟙_ (Over (Sp L)) ⟶ A) ≃* (𝟙_ (Over (Sp W)) ⟶ G) :=
    ((pullPtsEquiv A G (spMap (algebraMap W L)) φ hφ _).trans (precompEquiv i)).trans e1.symm
  refine ⟨e, fun y => ?_⟩
  have h1 := he1 (e y)
  have h2 : e1 (e y) = i.hom ≫ pullPtsEquiv A G (spMap (algebraMap W L)) φ hφ _ y := e1.apply_symm_apply _
  rw [h2] at h1
  simp only [i] at h1
  simp only [Over.isoMk_hom_left, Iso.refl_hom, Over.comp_left] at h1
  rw [← h1]
  simp only [Category.id_comp]
  rfl

end GlobalTheory.LevExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperGroupSchemeDvrSectionsMulEquivGenericStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.properGroupScheme_dvr_sections_mulEquiv_generic : ∀ (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (G : Over (Sp W)) [GrpObj G] (A : Over (Sp L)) [GrpObj A] (φ : A.left ⟶ G.left), IsProper G.hom → IsGrpPullback A G (spMap (algebraMap W L)) φ → ∃ e : (𝟙_ (Over (Sp L)) ⟶ A) ≃* (𝟙_ (Over (Sp W)) ⟶ G), ∀ y, y.left ≫ φ = spMap (algebraMap W L) ≫ (e y).left := by
  first | exact @GlobalTheory.LevExt.sections_generic_mulEquiv | exact GlobalTheory.LevExt.sections_generic_mulEquiv | (intros; apply GlobalTheory.LevExt.sections_generic_mulEquiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectExtendsOverDvrOfAbelianModel
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.HTObjExt

variable {p : ℕ} [Fact p.Prime]

theorem sp_point {R W R' : Type} [CommRing R] [CommRing W] [CommRing R'] (gm : R →+* W) (β : R →+* R')
    (x : Sp R' ⟶ Sp W) (hx : x ≫ spMap gm = spMap β) : ∃ β₀ : W →+* R', spMap β₀ = x ∧ β₀.comp gm = β := by
  refine ⟨(Spec.preimage x).hom, by simp [spMap], ?_⟩
  have e : spMap ((Spec.preimage x).hom.comp gm) = spMap β := by
    rw [spMap_comp, ← hx]; congr 1; simp [spMap]
  have e2 := Spec.map_injective e
  exact congrArg CommRingCat.Hom.hom e2

theorem lift_match₂ {S S' : Scheme.{0}} {A : Over S'} {G : Over S} {φ : A.left ⟶ G.left}
    {φ₂ : (A ⊗ A).left ⟶ (G ⊗ G).left} (hsq : IsSquare φ φ₂) (u v : A ⊗ A ⟶ A) (U V : G ⊗ G ⟶ G)
    (hu : u.left ≫ φ = φ₂ ≫ U.left) (hv : v.left ≫ φ = φ₂ ≫ V.left) :
    (lift u v).left ≫ φ₂ = φ₂ ≫ (lift U V).left := by
  have pG : IsPullback (fst G G).left (snd G G).left G.hom G.hom := IsPullback.of_hasPullback _ _
  apply pG.hom_ext
  · rw [Category.assoc, hsq.1, ← Category.assoc, ← Over.comp_left, lift_fst, hu, Category.assoc,
      ← Over.comp_left, lift_fst]
  · rw [Category.assoc, hsq.2, ← Category.assoc, ← Over.comp_left, lift_snd, hv, Category.assoc,
      ← Over.comp_left, lift_snd]

theorem isTanScal_push {O : Type} [Ring O] {S S' : Scheme.{0}} {G : Over S} {A : Over S'} [GrpObj G] [GrpObj A]
    {f : S' ⟶ S} {φ : A.left ⟶ G.left} (h : IsGrpPullback A G f φ) (act : OActN O A) (act' : OActN O G)
    (hact : ∀ c, (act.act c).left ≫ φ = φ ≫ (act'.act c).left) {R' : Type} [CommRing R'] (x : Sp R' ⟶ S') :
    ∃ e : (epsPtR x ⟶ A) ≃* (epsPtR (x ≫ f) ⟶ G), ∀ (b : O) (c : R') (v : epsPtR x ⟶ A),
      IsTanScal act x b c v ↔ IsTanScal act' (x ≫ f) b c (e v) := by
  obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv h (epsPtR x) (spMap (algebraMap R' (DualNumber R')) ≫ x ≫ f)
    (Category.assoc _ _ _).symm
  obtain ⟨e₀, he₀⟩ := GlobalTheory.LiePull.exists_pushEquiv h (Over.mk x) (x ≫ f) rfl
  refine ⟨e, fun b c v => ?_⟩
  have one : (1 : Over.mk (x ≫ f) ⟶ G).left = (1 : Over.mk x ⟶ A).left ≫ φ := by
    rw [← he₀, map_one]
  have sc : spMap (epsScaleR c) ≫ spMap (algebraMap R' (DualNumber R')) =
      spMap (algebraMap R' (DualNumber R')) := by
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  have fs : spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ spMap (algebraMap R' (DualNumber R')) = 𝟙 _ := by
    refine (Spec.map_comp _ _).symm.trans ((congrArg Spec.map ?_).trans (Spec.map_id _))
    ext a
    simp [TrivSqZeroExt.algebraMap_eq_inl]
  have E : e (v ≫ act.act b) = e v ≫ act'.act b := Over.OverMorphism.ext (by
    rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, hact, Category.assoc])
  refine and_congr ?_ ?_
  · rw [one, he]
    refine ⟨fun E => by rw [← E]; exact (Category.assoc _ _ _).symm,
      fun E => h.1.hom_ext ((Category.assoc _ _ _).trans E) ?_⟩
    refine ((Category.assoc _ _ _).trans ?_).trans (Over.w (1 : Over.mk x ⟶ A)).symm
    refine (congrArg (spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ ·) (Over.w v)).trans ?_
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ x) fs).trans (Category.id_comp _))
  · rw [← E, he, he]
    refine ⟨fun E => by rw [E]; exact Category.assoc _ _ _, fun E => h.1.hom_ext (E.trans (Category.assoc _ _ _).symm) ?_⟩
    refine (Over.w (v ≫ act.act b)).trans (Eq.symm ((Category.assoc _ _ _).trans ?_))
    refine (congrArg (spMap (epsScaleR c) ≫ ·) (Over.w v)).trans ?_
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ x) sc)

theorem tate_push {D : Datum p} {S S' : Scheme.{0}} {G : Over S} {A : Over S'} [GrpObj G] [GrpObj A]
    [IsCommMonObj A] {f : S' ⟶ S} {φ : A.left ⟶ G.left} (h : IsGrpPullback A G f φ)
    {φ₂ : (G2 A).left ⟶ (G2 G).left} (hsq : IsSquare φ φ₂) (act : OActN D.O A) (act' : OActN D.O G)
    (hact : ∀ c, (act.act c).left ≫ φ = φ ≫ (act'.act c).left) (P : LB (G2 A).left) (P' : LB (G2 G).left)
    (hP : P.IsLB) (hP' : P'.IsLB) (iP : LBIso P (P'.pull φ₂)) (N : ℕ) (lv : D.La → (𝟙_ (Over S') ⟶ A))
    (lv' : D.La → (𝟙_ (Over S) ⟶ G)) (hlv : ∀ y, (lv y).left ≫ φ = f ≫ (lv' y).left)
    (k : Type) [Field k] (x : Sp k ⟶ S')
    (H : ∃ I : TateIsoO D k (Over.mk x ⟶ A) (fun c g => g ≫ act.act c)
        (fun n g g' z => Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) n g g' (unitOn z)),
      ∀ y, toUnit _ ≫ lv y = I.ev N y) :
    ∃ I : TateIsoO D k (Over.mk (x ≫ f) ⟶ G) (fun c g => g ≫ act'.act c)
        (fun n g g' z => Out.WeilIs G (P'.pull (lift (𝟙 G) (𝟙 G)).left) n g g' (unitOn z)),
      ∀ y, toUnit _ ≫ lv' y = I.ev N y := by
  obtain ⟨I, hI⟩ := H
  obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv h (Over.mk x) (x ≫ f) rfl
  have hd : (lift (𝟙 A) (𝟙 A)).left ≫ φ₂ = φ ≫ (lift (𝟙 G) (𝟙 G)).left :=
    GlobalTheory.AxisTrivExt.lift_match hsq.1 hsq.2 (𝟙 A) (𝟙 A) (𝟙 G) (𝟙 G) (by simp) (by simp)
  have a3 : LBIso (P.pull (lift (𝟙 A) (𝟙 A)).left) ((P'.pull φ₂).pull (lift (𝟙 A) (𝟙 A)).left) :=
    GenSpread.lbIso_pullback iP _
  have b1 : LBIso (P'.pull (φ ≫ (lift (𝟙 G) (𝟙 G)).left)) ((P'.pull φ₂).pull (lift (𝟙 A) (𝟙 A)).left) :=
    GenSpread.lbIso_pull_pull hP' _ hd.symm
  have b2 : LBIso (P'.pull (φ ≫ (lift (𝟙 G) (𝟙 G)).left)) ((P'.pull (lift (𝟙 G) (𝟙 G)).left).pull φ) :=
    GenSpread.lbIso_pull_pull hP' φ rfl
  have iD : LBIso (P.pull (lift (𝟙 A) (𝟙 A)).left) ((P'.pull (lift (𝟙 G) (𝟙 G)).left).pull φ) :=
    LBIso.trans (pull_isLB hP _) (pull_isLB hP' _) (pull_isLB (pull_isLB hP' _) _)
      (LBIso.trans (pull_isLB hP _) (pull_isLB (pull_isLB hP' _) _) (pull_isLB hP' _) a3 b1.symm) b2
  have W' := fun (n : ℤ) (g g' : Over.mk x ⟶ A) (z : kˣ) =>
    weilIs_baseChange_of_comm S S' G A f φ h (P'.pull (lift (𝟙 G) (𝟙 G)).left) (P.pull (lift (𝟙 A) (𝟙 A)).left)
      (pull_isLB hP' _) (pull_isLB hP _) iD k x n g g' (e g) (e g') z (he g) (he g')
  have lin : ∀ (c : D.O) (g : Over.mk x ⟶ A), e (g ≫ act.act c) = e g ≫ act'.act c := fun c g =>
    Over.OverMorphism.ext (by rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, hact, Category.assoc])
  refine ⟨{ ζ := I.ζ
            ζ_prim := I.ζ_prim
            ζ_pow := I.ζ_pow
            ev := fun n y => e (I.ev n y)
            add := fun n y y' => by simp only [I.add, map_mul]
            lin := fun n c y => by simp only [I.lin, lin]
            ker := fun n hn hp y => by
              rw [← I.ker n hn hp y]
              exact ⟨fun E => e.injective (E.trans (map_one e).symm), fun E => by rw [E, map_one]⟩
            onto := fun n hn hp q => by
              obtain ⟨q, rfl⟩ := e.surjective q
              rw [← map_pow]
              refine Iff.trans ?_ ((I.onto n hn hp q).trans ?_)
              · exact ⟨fun E => e.injective (E.trans (map_one e).symm), fun E => by rw [E, map_one]⟩
              · exact ⟨fun ⟨y, hy⟩ => ⟨y, by rw [hy]⟩, fun ⟨y, hy⟩ => ⟨y, e.injective hy⟩⟩
            tower := fun n m hn hm hp y => by rw [← map_pow, I.tower n m hn hm hp y]
            isom := fun n hn hp y y' => (W' n _ _ _).1 (I.isom n hn hp y y') }, fun y => ?_⟩
  show toUnit _ ≫ lv' y = e (I.ev N y)
  rw [← hI y]
  have e₁ : (toUnit (Over.mk x)).left = x := by simpa using Over.w (toUnit (Over.mk x))
  have e₂ : (toUnit (Over.mk (x ≫ f))).left = x ≫ f := by simpa using Over.w (toUnit (Over.mk (x ≫ f)))
  apply Over.OverMorphism.ext
  rw [he, Over.comp_left, Over.comp_left, Category.assoc, hlv, e₁, e₂, Category.assoc]

theorem extends_obj : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (gm : R →+* W) (o : Obj b N (spMap ((algebraMap W L).comp gm))) (G : Over (Sp W)) [GrpObj G] (φ : o.A.left ⟶ G.left), IsAbelianScheme G → IsGrpPullback o.A G (spMap (algebraMap W L)) φ → ∃ o' : Obj b N (spMap gm), Nonempty (ObjMap o o' (spMap (algebraMap W L))) := by
  intro p _ D R _ b N W L _ _ _ _ _ _ gm o G _ φ hG hA
  haveI : IsCommMonObj G := hG.comm
  have pG : IsPullback (fst G G).left (snd G G).left G.hom G.hom := IsPullback.of_hasPullback _ _
  let φ₂ : (G2 o.A).left ⟶ (G2 G).left := pG.lift ((fst o.A o.A).left ≫ φ) ((snd o.A o.A).left ≫ φ) (by
    rw [Category.assoc, Category.assoc, hA.1.w, ← Category.assoc, ← Category.assoc, Over.w (fst o.A o.A),
      Over.w (snd o.A o.A)])
  have hsq : IsSquare φ φ₂ := ⟨pG.lift_fst _ _ _, pG.lift_snd _ _ _⟩

  obtain ⟨act', ⟨h1, h2, h3, h4⟩, hact⟩ := GlobalTheory.T.exists_ring_action_extension_compatible W L G o.A φ (isSemiAbelian_of_isAbelianScheme G hG) hA
    D.Oᵐᵒᵖ (fun a => o.act.act a.unop) (fun a => o.act.hom _) (by simpa using o.act.one)
    (fun a c => by simp [o.act.mul]) (fun a c => by simp [o.act.add])
  let actG : OActN D.O G :=
    { act := fun c => act' (MulOpposite.op c)
      hom := fun c => h1 _
      one := by simpa using h2
      mul := fun c d => by rw [MulOpposite.op_mul]; exact h3 _ _
      add := fun c d => by rw [MulOpposite.op_add]; exact h4 _ _ }
  have hactG : ∀ c, (o.act.act c).left ≫ φ = φ ≫ (actG.act c).left := fun c => hact (MulOpposite.op c)

  obtain ⟨P', hP', r1, r2, iP⟩ := GlobalTheory.AxisTrivExt.exists_extension_square_of_axes_trivial W L G o.A φ φ₂ hG hA hsq
    o.P o.isLB o.rig₁ o.rig₂
  have hP := o.isLB
  have symm' : LBIso P' (P'.pull (lift (snd G G) (fst G G)).left) := by
    have i0 : LBIso (o.P.pull (𝟙 (G2 o.A).left)) (o.P.pull (lift (snd o.A o.A) (fst o.A o.A)).left) :=
      LBIso.trans (pull_isLB hP _) hP (pull_isLB hP _) (lbIso_pull_id hP) o.symm
    have i1 := GlobalTheory.T.lineBundleIso_pullback_extend_DVR W L G o.A φ φ₂ hG hA hsq o.P P' hP hP' iP (𝟙 _) (lift (snd o.A o.A) (fst o.A o.A))
      (𝟙 _) (lift (snd G G) (fst G G)) (by simp)
      (lift_match₂ hsq _ _ _ _ hsq.2.symm hsq.1.symm) i0
    exact LBIso.trans hP' (pull_isLB hP' _) (pull_isLB hP' _) (lbIso_pull_id hP').symm i1
  have rosati' : ∀ c : D.O, LBIso (P'.pull (lift (fst G G ≫ actG.act c) (snd G G)).left)
      (P'.pull (lift (fst G G) (snd G G ≫ actG.act (D.star c).unop)).left) := fun c =>
    GlobalTheory.T.lineBundleIso_pullback_extend_DVR W L G o.A φ φ₂ hG hA hsq o.P P' hP hP' iP _ _ _ _
      (lift_match₂ hsq _ _ _ _ (by rw [Over.comp_left, Category.assoc, hactG, ← Category.assoc, ← hsq.1,
        Category.assoc, Over.comp_left]) hsq.2.symm)
      (lift_match₂ hsq _ _ _ _ hsq.1.symm (by rw [Over.comp_left, Category.assoc, hactG, ← Category.assoc,
        ← hsq.2, Category.assoc, Over.comp_left])) (o.rosati c)
  have ample' := GlobalTheory.T.relAmple_diagonal_extendedBundle_of_generic W L G o.A φ φ₂ hG hA hsq o.P P' hP hP' iP o.ample
  have kerP' : ∃ e : ℕ, e.Coprime p ∧ ∀ (T : Over (Sp W)) (x : T ⟶ G),
      (∃ t : (P'.pull (lift (snd G T ≫ x) (fst G T)).left).Gen, t.IsGen) → x ^ e = 1 := by
    obtain ⟨e, he, hk⟩ := o.kerP
    exact ⟨e, he, GlobalTheory.T.polarisation_kernel_killed_over_dvr_of_generic W L G o.A φ φ₂ hG hA hsq o.P P' hP hP' iP r1 r2 symm' ample' e hk⟩

  obtain ⟨eL, heL⟩ := GlobalTheory.T.properGroupScheme_dvr_sections_mulEquiv_generic W L G o.A φ hG.proper hA
  have inj : ∀ s₁ s₂ : 𝟙_ (Over (Sp L)) ⟶ o.A, s₁.left ≫ φ = s₂.left ≫ φ → s₁ = s₂ := fun s₁ s₂ e =>
    Over.OverMorphism.ext (hA.1.hom_ext e (by rw [Over.w, Over.w]))
  have key : ∀ s t, s.left ≫ φ = spMap (algebraMap W L) ≫ t.left → eL s = t := fun s t e => by
    have e' := heL (eL.symm t)
    rw [MulEquiv.apply_symm_apply] at e'
    rw [inj s (eL.symm t) (e.trans e'.symm), MulEquiv.apply_symm_apply]
  let eta' : D.La → (𝟙_ (Over (Sp W)) ⟶ G) := fun y => eL (o.eta y)
  have eta_add' : ∀ x y, eta' (x + y) = eta' x * eta' y := fun x y => by
    simp only [eta', o.eta_add, map_mul]
  have hlv : ∀ y, (o.eta y).left ≫ φ = spMap (algebraMap W L) ≫ (eta' y).left := fun y => heL _

  have disc : IsUnit ((D.tr ^ 2 - 4 * D.nm : ℤ) : W) := by
    have hc : (Int.natAbs (D.tr ^ 2 - 4 * D.nm)).Coprime p := by
      refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (Fact.out)).2 fun hd => D.disc_p ?_)
      exact Int.ofNat_dvd_left.2 hd
    have hu := (b.unit _ hc).map gm
    rw [map_natCast] at hu
    rcases Int.natAbs_eq (D.tr ^ 2 - 4 * D.nm) with e | e
    · rw [e, Int.cast_natCast]; exact hu
    · rw [e, Int.cast_neg, Int.cast_natCast]; exact hu.neg
  have comax' : ∀ i j, i ≠ j → Ideal.span (Set.range fun x => (gm.comp (b.t i)) x - (gm.comp (b.t j)) x) = ⊤ :=
    fun i j hij => by
      have e := congrArg (Ideal.map gm) (b.comax i j hij)
      rw [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at e
      simpa [Function.comp_def, map_sub] using e
  have hx : ∀ (R' : Type) [CommRing R'] (β : L →+* R'),
      spMap β ≫ spMap ((algebraMap W L).comp gm) = spMap (β.comp ((algebraMap W L).comp gm)) :=
    fun R' _ β => (spMap_comp _ _).symm
  have lieGen : ∀ (R' : Type) [CommRing R'] (β : L →+* R'), ∀ v : epsPtR (spMap (β.comp (algebraMap W L))) ⟶ G,
      IsTanScal actG (spMap (β.comp (algebraMap W L))) (algebraMap (𝓞 D.F) D.O D.ω) (β (algebraMap W L (gm b.ρ))) v →
      ∃ w : Fin D.a → (epsPtR (spMap (β.comp (algebraMap W L))) ⟶ G),
        (∀ i, ∀ c : 𝓞 D.F, IsTanScal actG (spMap (β.comp (algebraMap W L))) (algebraMap (𝓞 D.F) D.O c)
          (β (algebraMap W L ((gm.comp (b.t i)) c))) (w i)) ∧ v = (List.ofFn w).prod := by
    intro R' _ β
    rw [spMap_comp]
    intro v hv
    obtain ⟨e, he⟩ := isTanScal_push hA o.act actG hactG (spMap β)
    have hu := (he _ _ (e.symm v)).2 (by rw [MulEquiv.apply_symm_apply]; exact hv)
    obtain ⟨w, hw, hwv⟩ := o.lie R' (β.comp ((algebraMap W L).comp gm)) (spMap β) (hx R' β) _ hu
    refine ⟨fun i => e (w i), fun i c => (he _ _ _).1 (hw i c), ?_⟩
    rw [← e.apply_symm_apply v, hwv, map_list_prod, List.map_ofFn]
    rfl
  have rankGen : ∀ (k : Type) [Field k] [IsAlgClosed k] (β : L →+* k) i,
      LieMult (actG.toF D) (spMap (β.comp (algebraMap W L))) ((β.comp (algebraMap W L)).comp (gm.comp (b.t i))) D.m := by
    intro k _ _ β i
    rw [spMap_comp]
    exact (GlobalTheory.LiePull.lieMult_pull (𝓞 D.F) (Sp W) (Sp L) G o.A (spMap (algebraMap W L)) φ (actG.toF D)
      (o.act.toF D) hA (fun c => hactG _) k (spMap β) _ D.m).1 (o.lieRank k (spMap β) _ (hx k β) i)
  obtain ⟨lieG, rankG⟩ := GlobalTheory.T.harrisTaylor_lie_condition_extends_abelianScheme_dvr p D W L G hG actG (gm b.ρ) (fun i => gm.comp (b.t i))
    (fun i => by simp [b.t_ω]) (by simpa using congrArg gm b.ρ_root) comax' disc lieGen rankGen

  have geomGen : ∀ (k : Type) [Field k] [IsAlgClosed k] (β : L →+* k),
      ∃ I : TateIsoO D k (Over.mk (spMap (β.comp (algebraMap W L))) ⟶ G) (fun c g => g ≫ actG.act c)
        (fun n g g' z => Out.WeilIs G (P'.pull (lift (𝟙 G) (𝟙 G)).left) n g g' (unitOn z)),
      ∀ x, toUnit _ ≫ eta' x = I.ev N x := by
    intro k _ _ β
    rw [spMap_comp]
    exact tate_push hA hsq o.act actG hactG o.P P' hP hP' iP N o.eta eta' hlv k (spMap β)
      (o.geom k (spMap β) _ (hx k β))
  have geomG := GlobalTheory.T.tateSimilitude_geometric_points_of_generic_dvr p D R b N W L gm G hG actG P' hP' eta' eta_add' geomGen
  have lie' : ∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ Sp W), x ≫ spMap gm = spMap β →
      ∀ v : epsPtR x ⟶ G, IsTanScal actG x (algebraMap (𝓞 D.F) D.O D.ω) (β b.ρ) v →
        ∃ w : Fin D.a → (epsPtR x ⟶ G),
          (∀ i, ∀ c : 𝓞 D.F, IsTanScal actG x (algebraMap (𝓞 D.F) D.O c) (β (b.t i c)) (w i)) ∧
          v = (List.ofFn w).prod := by
    intro R' _ β x hx' v hv
    obtain ⟨β₀, rfl, rfl⟩ := sp_point gm β x hx'
    exact lieG R' β₀ v hv
  have rank' : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp W) (β : R →+* k), x ≫ spMap gm = spMap β →
      ∀ i, LieMult (actG.toF D) x (β.comp (b.t i)) D.m := by
    intro k _ _ x β hx' i
    obtain ⟨β₀, rfl, rfl⟩ := sp_point gm β x hx'
    exact rankG k β₀ i
  have lin' : ∀ (c : D.O) x, eta' (c • x) = eta' x ≫ actG.act c := by
    intro c x
    show eL (o.eta (c • x)) = eL (o.eta x) ≫ actG.act c
    rw [o.eta_lin]
    refine key _ _ ?_
    rw [Over.comp_left, Category.assoc, hactG, ← Category.assoc, hlv, Category.assoc, Over.comp_left]
  have ker' : ∀ x, eta' (N • x) = 1 := by
    intro x
    show eL (o.eta (N • x)) = 1
    rw [o.eta_ker, map_one]
  have geom' : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp W) (β : R →+* k), x ≫ spMap gm = spMap β →
      ∃ I : TateIsoO D k (Over.mk x ⟶ G) (fun c g => g ≫ actG.act c)
        (fun n g g' z => Out.WeilIs G (P'.pull (lift (𝟙 G) (𝟙 G)).left) n g g' (unitOn z)),
      ∀ y, toUnit _ ≫ eta' y = I.ev N y := by
    intro k _ _ x β hx'
    obtain ⟨β₀, rfl, rfl⟩ := sp_point gm β x hx'
    exact geomG k β₀
  exact ⟨Obj.mk G hG actG P' hP' r1 r2 symm' ample' kerP' rosati' lie' rank' eta' eta_add' lin' ker' geom',
    ⟨ObjMap.mk φ φ₂ hA hsq hactG iP hlv⟩⟩
end GlobalTheory.HTObjExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectExtendsOverDvrOfAbelianModelStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylorObject_extends_over_dvr_of_abelianModel : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (gm : R →+* W) (o : Obj b N (spMap ((algebraMap W L).comp gm))) (G : Over (Sp W)) [GrpObj G] (φ : o.A.left ⟶ G.left), IsAbelianScheme G → IsGrpPullback o.A G (spMap (algebraMap W L)) φ → ∃ o' : Obj b N (spMap gm), Nonempty (ObjMap o o' (spMap (algebraMap W L))) := by
  first | exact @GlobalTheory.HTObjExt.extends_obj | exact GlobalTheory.HTObjExt.extends_obj | (intros; apply GlobalTheory.HTObjExt.extends_obj <;> assumption)
end
