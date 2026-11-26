module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.NoCommonComponentCoordinatesPlane
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapperSubquotFinite
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AssemblyBase
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PSnapperQuotFiltX
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StCutRestrLenExact
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
public import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StSubsetDiffConst
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsMultiProjPrimeMIdealOverGraph
public import GroundTheory.HeightsAndTheta.Heights.ThetaKeyFormula.RigSymFormTauINontrivial

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PFrameJacobianGeneric
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

noncomputable section

open MvPolynomial
open scoped Matrix

theorem frame_matrix_det_ne_zero {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n))) :
    (Matrix.of fun j l : Fin n => b j l).det ≠ 0 := by
  intro h
  obtain ⟨v, hv, hvM⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h
  apply hv
  have hsum : ∑ j, v j • b j = 0 := by
    ext l
    have := congrFun hvM l
    simpa [Matrix.vecMul, dotProduct, mul_comm] using this
  have hli := Fintype.linearIndependent_iff.mp b.toBasis.linearIndependent v (by simpa using hsum)
  funext j
  exact hli j

theorem FrameJacobianGeneric.proof (hR : JacobianRankGeneric.Statement)
    (hC : ConormalGenerationGeneric.Statement) : FrameJacobianGeneric.Statement := by
  classical
  intro n d J hJ hd b
  have := hJ
  set K := FractionRing (MvPolynomial (Fin n) ℂ ⧸ J)
  let π : MvPolynomial (Fin n) ℂ →+* K :=
    (algebraMap (MvPolynomial (Fin n) ℂ ⧸ J) K).comp (Ideal.Quotient.mk J)
  have hπ : ∀ f, π f = 0 ↔ f ∈ J := by
    intro f
    simp only [π, RingHom.comp_apply]
    rw [IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
  have hdn : d ≤ n := by
    have h1 := ringKrullDim_quotient_le J
    rw [hd, MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field, zero_add,
      Nat.card_eq_fintype_card, Fintype.card_fin] at h1
    exact_mod_cast h1
  obtain ⟨t, G, hG⟩ := Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian J)
  set r := Fintype.card (Fin n) - d with hr
  obtain ⟨a, c, hac⟩ := IndefiniteRowSideFullHecke.Inter.exists_jacobian_minor_not_mem_charZero J G hG d hd
  have hrn : r = n - d := by rw [hr, Fintype.card_fin]
  have hGJ : ∀ i, G i ∈ J := fun i => hG ▸ Ideal.subset_span ⟨i, rfl⟩
  let V : Matrix (Fin r) (Fin n) K := Matrix.of fun i l => π (pderiv l (G (a i)))
  let N : Matrix (Fin n) (Fin n) K := Matrix.of fun l j => π (C (b j l))
  let W : Matrix (Fin r) (Fin n) K := Matrix.of fun i j => π (frameDeriv b j (G (a i)))
  have hW : W = V * N := by
    ext i j
    set_option synthInstance.maxHeartbeats 100000 in
      simp [W, V, N, frameDeriv, Matrix.mul_apply, map_sum, mul_comm]
  have hVc : (V.submatrix id c).det ≠ 0 := by
    have : V.submatrix id c = π.mapMatrix (Matrix.of fun i j => pderiv (c j) (G (a i))) := by
      ext i j
      rfl
    rw [this, ← RingHom.map_det]
    exact fun h => hac ((hπ _).mp h)
  have hN : N.det ≠ 0 := by
    have : N = π.mapMatrix ((C : ℂ →+* MvPolynomial (Fin n) ℂ).mapMatrix
        (Matrix.of fun j l : Fin n => b j l)ᵀ) := by
      ext l j
      rfl
    rw [this, ← RingHom.map_det, ← RingHom.map_det, Matrix.det_transpose]
    intro h
    rw [hπ] at h
    have hu : IsUnit (C (Matrix.of fun j l : Fin n => b j l).det : MvPolynomial (Fin n) ℂ) :=
      (isUnit_iff_ne_zero.mpr (frame_matrix_det_ne_zero b)).map C
    exact hJ.ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)
  have hVinj : ∀ x : Fin r → K, x ᵥ* V = 0 → x = 0 := by
    intro x hx
    apply Matrix.eq_zero_of_vecMul_eq_zero hVc
    ext j
    simpa [Matrix.vecMul, dotProduct] using congrFun hx (c j)
  have hWinj : ∀ x : Fin r → K, Wᵀ *ᵥ x = 0 → x = 0 := by
    intro x hx
    rw [Matrix.mulVec_transpose, hW, ← Matrix.vecMul_vecMul] at hx
    exact hVinj x (Matrix.eq_zero_of_vecMul_eq_zero hN hx)
  obtain ⟨col, hcol⟩ := ReciprocityTheory.AnForm.R.gs_exists_rows_det_ne_zero Wᵀ hWinj
  have hcol' : (W.submatrix id col).det ≠ 0 := by
    rwa [← Matrix.det_transpose, Matrix.transpose_submatrix]
  have hinj : Function.Injective col := by
    intro i i' h
    by_contra hne
    apply hcol
    apply Matrix.det_zero_of_row_eq hne
    funext k
    simp [h]
  let I₀ : Finset (Fin n) := (Finset.univ.image col)ᶜ
  have hmem : ∀ j, j ∈ Set.range col ↔ j ∉ I₀ := by
    intro j
    simp [I₀]
  let e : Fin r ≃ {j // j ∉ I₀} :=
    (Equiv.ofInjective col hinj).trans (Equiv.subtypeEquivRight hmem)
  have he : ∀ i, (e i : Fin n) = col i := fun i => rfl
  let f : {j // j ∉ I₀} → MvPolynomial (Fin n) ℂ := fun k => G (a (e.symm k))
  have hli : LinearIndependent K (fun i => genericGradient J (G (a i))) := by
    rw [Fintype.linearIndependent_iff]
    intro x hx
    have : x ᵥ* V = 0 := by
      rw [Matrix.vecMul_eq_sum]
      exact hx
    simpa using congrFun (hVinj x this)
  have hspan : Submodule.span K (Set.range (genericGradient J ∘ f)) =
      Submodule.span K (genericGradient J '' (J : Set _)) := by
    have hrange : Set.range (genericGradient J ∘ f) =
        Set.range (fun i => genericGradient J (G (a i))) := by
      ext v
      constructor
      · rintro ⟨k, rfl⟩
        exact ⟨e.symm k, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨e i, by simp [f]⟩
    rw [hrange]
    apply Submodule.eq_of_le_of_finrank_le
    · apply Submodule.span_mono
      rintro _ ⟨i, rfl⟩
      exact ⟨G (a i), hGJ _, rfl⟩
    · rw [finrank_span_eq_card hli, Fintype.card_fin]
      exact (hR n d J hd).trans (by simp)
  obtain ⟨s, hsJ, hs⟩ := hC n J {j // j ∉ I₀} f (fun k => hGJ _) hspan
  refine ⟨I₀, f, s, ?_, fun k => hGJ _, hsJ, ?_, hs⟩
  · rw [Finset.card_compl, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin,
      Fintype.card_fin]
    omega
  · intro hdet
    rw [← hπ, frameJacobianDet, RingHom.map_det, ← Matrix.det_submatrix_equiv_self e] at hdet
    apply hcol'
    convert hdet using 2
    ext i i'
    simp [f, W, he]

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PSnapperQuotDevissageX
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

theorem SnapperFinite.closed : SnapperFinite.Statement.{u, v, w} :=
  SnapperFinite.proof Extension.proof Extension.proof TwistTilde.proof TwistTilde.proof TildeShift.proof
    (TildeFiniteE.proof SerreFinite.full)

theorem SnapperSubquotFinite.closed : SnapperSubquotFinite.Statement.{u, v, w} :=
  SnapperSubquotFinite.proof SnapperFinite.closed

theorem SnapperQuotAdd.closed : SnapperQuotAdd.Statement.{u, v, w} :=
  SnapperQuotAdd.proof SnapperSubquotFinite.closed

theorem SnapperQuotDevissage.closed : SnapperQuotDevissage.Statement.{u, v, w} :=
  SnapperQuotDevissage.proof SnapperQuotFilt.proof SnapperQuotIso.proof SnapperQuotAdd.closed SubFamilyTwist.proof

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StatementsNefBigCountAlongMultiples
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

def NefBigCountAlongMultiples.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (P0 : Ideal (MRing ι))
    (II : IntersectionSystem),
    1 ≤ D → IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    IsNefBigDatum P0 y D A →
    ∀ ε : ℝ, 0 < ε → ∃ a : ℕ, 1 ≤ a ∧ ∀ᶠ k : ℕ in atTop,
      (II K ι (mCoordIdeal y) (D + 1) (fun _ => A) - ε) *
          (((a * k : ℕ) : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) ≤
        smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) (a * k)

end

end GroundTheory.Heights₂.Heights.Targets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PRestrLenEuler
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

namespace RestrLenEuler

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem length_toNat_eq_finrank (M : Type w) [AddCommGroup M] [Module k M] :
    (Module.length k M).toNat = Module.finrank k M := by
  by_cases h : Module.Finite k M
  · rw [Module.length_eq_finrank]; rfl
  · rw [Module.finrank_of_not_finite h, Module.length_eq_rank]
    have : Cardinal.aleph0 ≤ Module.rank k M := by
      by_contra hlt
      exact h (Module.rank_lt_aleph0_iff.mp (not_le.mp hlt))
    rw [Cardinal.toENat_eq_top.mpr this]
    rfl

theorem vanish_of_fg (F : SubFamily k x Ω) (hF : ∀ I, (F.sub I).FG) :
    ∃ c₀ : ℤ, ∀ i : ℕ, 1 ≤ i → ∀ c : ℤ, c₀ ≤ c → Subsingleton ((F.toSubSystem.twist (twistSys k x c)).H i) := by
  obtain ⟨M, -, hM⟩ := Extension.full k Ω N x Ω F hF
  obtain ⟨c₀, hc₀⟩ := TildeVanish.proof SerreVanish.full k Ω N x Ω M
  have h0 : M.tildeSys 0 = F.toSubSystem := SubSystem.ext_sub fun I => hM I
  refine ⟨c₀, fun i hi c hc => ?_⟩
  rw [← h0, ← SurjectiveClosed.tildeSys_eq_twist]
  exact hc₀ i hi c hc

def incl (F₁ F₂ : SubSystem k x Ω) (h21 : ∀ I, F₂.sub I ≤ F₁.sub I) (I : Chart x) :
    F₂.sub I →ₗ[k] F₁.sub I where
  toFun y := ⟨y, h21 I y.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl


set_option maxHeartbeats 1000000 in
theorem quotH_subsingleton (F₁ F₂ : SubSystem k x Ω) (h21 : ∀ I, F₂.sub I ≤ F₁.sub I) (i : ℕ)
    (h1 : Subsingleton (F₁.H i)) (h2 : Subsingleton (F₂.H (i + 1))) :
    Subsingleton (SubSystem.quotH F₁ F₂ i) := by
  have hdd := CechDSq.full (N + 1) (support x) k (fun I : Chart x => F₁.sub I) F₁.res
    (fun _ _ _ _ _ => LinearMap.ext fun _ => rfl)
  have L := Cech.longExact (R := k) (U := support x)
    (A := fun I : Chart x => F₂.sub I) (B := fun I : Chart x => F₁.sub I)
    (C := fun I : Chart x => F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I)
    (ρA := F₂.res) (ρB := F₁.res) (ρC := SubSystem.quotRes F₁ F₂)
    (dA := fun _ => ⊤) (dB := fun _ => ⊤) (dC := fun _ => ⊤)
    (φ := incl F₁ F₂ h21) (ψ := fun I => (SubSystem.quotSub F₁ F₂ I).mkQ)
    (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ => Submodule.mem_top)
    (fun _ _ _ => Submodule.mem_top)
    (fun I a b hab => Subtype.ext (show (a : Ω) = b from congrArg (fun z : F₁.sub I => (z : Ω)) hab))
    (fun I y => (Submodule.Quotient.mk_eq_zero (SubSystem.quotSub F₁ F₂ I)).mpr y.2)
    (fun I m _ hm => ⟨⟨m, (Submodule.Quotient.mk_eq_zero (SubSystem.quotSub F₁ F₂ I)).mp hm⟩, Submodule.mem_top, rfl⟩)
    (fun I z _ => (Submodule.Quotient.mk_surjective _ z).imp fun y hy => ⟨Submodule.mem_top, hy⟩)
    (fun _ _ _ _ _ => Submodule.mem_top) hdd
  obtain ⟨-, hex⟩ := L
  obtain ⟨hg, δ, hgδ, -⟩ := hex i
  have hB : Subsingleton (Cech.Hdeg (fun I : Chart x => F₁.sub I) (fun _ => (⊤ : Submodule k _)) F₁.res i) :=
    haveI : Subsingleton (Cech.H (fun I : Chart x => F₁.sub I) F₁.res i) := h1
    (SnapperQuotientAdditivity.hdegTopEquiv _ _ i).toEquiv.subsingleton
  have hA : Subsingleton (Cech.Hdeg (fun I : Chart x => F₂.sub I) (fun _ => (⊤ : Submodule k _)) F₂.res (i + 1)) :=
    haveI : Subsingleton (Cech.H (fun I : Chart x => F₂.sub I) F₂.res (i + 1)) := h2
    (SnapperQuotientAdditivity.hdegTopEquiv _ _ (i + 1)).toEquiv.subsingleton
  have hC : Subsingleton (Cech.Hdeg (fun I : Chart x => F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I)
      (fun _ => (⊤ : Submodule k _)) (SubSystem.quotRes F₁ F₂) i) := by
    refine ⟨fun a b => ?_⟩
    have hz : ∀ y : Cech.Hdeg (fun I : Chart x => F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I)
        (fun _ => (⊤ : Submodule k _)) (SubSystem.quotRes F₁ F₂) i, y = 0 := by
      intro y
      obtain ⟨b, hb⟩ := (hgδ y).mp (Subsingleton.elim _ _)
      rw [← hb, Subsingleton.elim b 0, map_zero]
    rw [hz a, hz b]
  exact (SnapperQuotientAdditivity.hdegTopEquiv _ _ i).symm.toEquiv.subsingleton

end RestrLenEuler


open RestrLenEuler in
theorem RestrLenEuler.proof : RestrLenEuler.Statement.{u, w} := by
  intro k _ Ω _ _ N x qq hqq _ t L n
  set Ls : Fin t → SubSystem k x Ω := fun j => (L j).toSubSystem with hLs
  let Q : LineBundle k x := twistPowsBundle (twistBundle k x 0) t L n
  have hQ : Q.toSubSystem = (twistSys k x 0).twistPows t Ls n :=
    twistPowsBundle_toSubSystem (twistBundle k x 0) t L n
  obtain ⟨G, hG, hGfg⟩ := IdealTwistFamily.proof k Ω N x Q qq hqq
  obtain ⟨a₁, ha₁⟩ := vanish_of_fg Q.toSubFamily Q.fg
  obtain ⟨a₂, ha₂⟩ := vanish_of_fg G hGfg
  obtain ⟨a₃, ha₃⟩ := SurjectiveClosed.proof Extension.full IdealTwistFamily.proof
    (TildeVanish.proof SerreVanish.full) k Ω N x Q qq hqq
  refine Filter.eventually_atTop.mpr ⟨max a₁ (max a₂ a₃), fun c hc => ?_⟩
  have hc₁ : a₁ ≤ c := le_of_max_le_left hc
  have hc₂ : a₂ ≤ c := le_of_max_le_left (le_of_max_le_right hc)
  have hc₃ : a₃ ≤ c := le_of_max_le_right (le_of_max_le_right hc)
  set F₁ := ((twistSys k x 0).twistPows t Ls n).twist (twistSys k x c) with hF₁
  have hF₁Q : F₁ = Q.toSubSystem.twist (twistSys k x c) := by rw [hQ]
  have hF₂ : (((twistSys k x 0).twist (idealSys x qq)).twistPows t Ls n).twist (twistSys k x c) =
      F₁.twist (idealSys x qq) := by
    rw [twistPows_twist_comm, SurjectiveClosed.twist_twist_comm]
  have hF₂G : F₁.twist (idealSys x qq) = G.toSubSystem.twist (twistSys k x c) := by
    rw [hG, hF₁Q, SurjectiveClosed.twist_twist_comm]
  have h21 : ∀ I, (F₁.twist (idealSys x qq)).sub I ≤ F₁.sub I :=
    SurjectiveClosed.twist_idealSys_le F₁ qq
  have hvan : ∀ i, 1 ≤ i → Subsingleton (SubSystem.quotH F₁ (F₁.twist (idealSys x qq)) i) := by
    intro i hi
    refine quotH_subsingleton F₁ _ h21 i ?_ ?_
    · rw [hF₁Q]; exact ha₁ i hi c hc₁
    · rw [hF₂G]; exact ha₂ (i + 1) (by omega) c hc₂
  have hlift := ha₃ c hc₃
  rw [← hF₁Q] at hlift
  unfold pieceChar restrLen
  rw [hF₂, QuotientH0Length.length_secs_eq _ _ hlift, length_toNat_eq_finrank, eulerCharQuot,
    Finset.sum_eq_single 0]
  · simp only [pow_zero, one_mul]; rfl
  · intro i _ hi
    have := hvan i (Nat.one_le_iff_ne_zero.mpr hi)
    rw [Module.finrank_zero_of_subsingleton]
    simp
  · intro h; exact absurd (Finset.mem_range.mpr (Nat.succ_pos N)) h

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PInterNumAdditive
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

section Monoid

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

abbrev twistMonoid : CommMonoid (SubSystem S x Ω) where
  mul F Q := F.twist Q
  one := twistSys S x 0
  mul_assoc F P Q := SubSystem.twist_assoc F P Q
  one_mul F := twistSys_zero_twist F
  mul_one F := SubSystem.twist_twistSys_zero F
  mul_comm F Q := SubSystem.twist_comm F Q

attribute [local instance] twistMonoid

theorem foldl_twist_eq_mul {n : ℕ} (L : Fin n → SubSystem S x Ω) (l : List (Fin n)) (F : SubSystem S x Ω) :
    l.foldl (fun F i => F.twist (L i)) F = F * (l.map L).prod := by
  induction l generalizing F with
  | nil => exact (mul_one F).symm
  | cons a l ih =>
    rw [List.foldl_cons, ih, List.map_cons, List.prod_cons, ← mul_assoc]
    rfl

theorem prod_map_filter {α M : Type*} [CommMonoid M] (p : α → Bool) (f : α → M) (l : List α) :
    ((l.filter p).map f).prod = (l.map fun a => if p a then f a else 1).prod := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : p a
    · simp [h, ih]
    · simp [h, ih]

theorem tensorSub_eq_prod {n : ℕ} (L : Fin n → SubSystem S x Ω) (T : Finset (Fin n)) :
    tensorSub L T = ∏ j ∈ T, L j := by
  unfold tensorSub
  rw [foldl_twist_eq_mul]
  change 1 * _ = _
  rw [one_mul, prod_map_filter, ← Fin.prod_univ_def, ← Finset.prod_filter]
  congr 1
  ext j
  simp

end Monoid

section MixDiff

theorem powerset_map_emb {α β : Type*} (e : α ↪ β) (s : Finset α) :
    (s.map e).powerset = s.powerset.map (Finset.mapEmbedding e).toEmbedding := by
  ext T
  simp only [Finset.mem_powerset, Finset.mem_map, Finset.subset_map_iff, RelEmbedding.coe_toEmbedding,
    Finset.mapEmbedding_apply]
  constructor
  · rintro ⟨u, hu, rfl⟩; exact ⟨u, hu, rfl⟩
  · rintro ⟨u, hu, rfl⟩; exact ⟨u, hu, rfl⟩

variable {G : Type*} [CommMonoid G]

def mixDiff (f : G → ℤ) {n : ℕ} (L : Fin n → G) : ℤ :=
  ∑ T : Finset (Fin n), (-1) ^ (n - T.card) * f (∏ j ∈ T, L j)

theorem mixDiff_snoc (f : G → ℤ) {m : ℕ} (L : Fin m → G) (X : G) :
    mixDiff f (Fin.snoc (α := fun _ => G) L X) = mixDiff (fun g => f (X * g)) L - mixDiff f L := by
  classical
  unfold mixDiff
  rw [← Finset.powerset_univ, ← Finset.powerset_univ, Fin.univ_castSuccEmb, Finset.cons_eq_insert,
    Finset.sum_powerset_insert (by simp), powerset_map_emb, Finset.sum_map, Finset.sum_map,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun U _ => ?_
  have hU : U.card ≤ m := by simpa using U.card_le_univ
  have hlast : Fin.last m ∉ U.map Fin.castSuccEmb := by simp [Fin.castSucc_ne_last]
  have hp : ∏ j ∈ U.map Fin.castSuccEmb, Fin.snoc (α := fun _ => G) L X j = ∏ j ∈ U, L j := by
    rw [Finset.prod_map]
    simp
  simp only [RelEmbedding.coe_toEmbedding, Finset.mapEmbedding_apply, Finset.card_insert_of_notMem hlast,
    Finset.card_map, Finset.prod_insert hlast, hp, Fin.snoc_last]
  rw [show m + 1 - U.card = m - U.card + 1 by omega, show m + 1 - (U.card + 1) = m - U.card by omega, pow_succ]
  ring

theorem mixDiff_snoc_mul (f : G → ℤ) {m : ℕ} (L : Fin m → G) (X Y : G) :
    mixDiff f (Fin.snoc (α := fun _ => G) L (X * Y)) =
      mixDiff f (Fin.snoc (α := fun _ => G) L X) + mixDiff f (Fin.snoc (α := fun _ => G) L Y) +
        mixDiff f (Fin.snoc (α := fun _ => G) (Fin.snoc (α := fun _ => G) L X) Y) := by
  simp only [mixDiff_snoc]
  have h : mixDiff (fun g => f (Y * (X * g))) L = mixDiff (fun g => f (X * Y * g)) L := by
    congr 1
    funext g
    rw [mul_left_comm, mul_assoc]
  simp only [h]
  ring

end MixDiff

section Main

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

attribute [local instance] twistMonoid

theorem interSum_eq_mixDiff (pp : Ideal (Poly S N)) {n : ℕ} (L : Fin n → SubSystem S x Ω) (c : ℕ) :
    interSum pp L c = mixDiff (fun F => restrLen pp (F.twist (twistSys S x (c : ℤ)))) L := by
  unfold interSum mixDiff
  simp only [tensorSub_eq_prod]

end Main

attribute [local instance] twistMonoid

theorem InterNumAdditive.proof (hE : InterNumEventual.Statement.{u, w})
    (hZ : InterSumTopVanish.Statement.{u, w}) : InterNumAdditive.Statement.{u, w} := by
  intro k _ Ω _ _ N x n pp L i L' L'' hW
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := i.pos; omega⟩
  set σ := Equiv.swap i (Fin.last m) with hσ
  set L₀ : Fin m → LineBundle k x := fun j => L (σ (Fin.castSucc j)) with hL₀

  have hfam : ∀ B : LineBundle k x, Function.update (fun j => (L j).toSubSystem) i B.toSubSystem =
      fun j => (Function.update L i B j).toSubSystem := fun B => by
    funext j
    exact (Function.apply_update (fun _ B => B.toSubSystem) L i B j).symm

  have hmove : ∀ (Y : SubSystem k x Ω) (c : ℕ),
      interSum pp (Function.update (fun j => (L j).toSubSystem) i Y) c =
        interSum pp (Fin.snoc (α := fun _ => SubSystem k x Ω) (fun j => (L₀ j).toSubSystem) Y) c := by
    intro Y c
    rw [← interSum_comp_perm pp _ σ c]
    congr 1
    funext j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [hσ]
    · have hne : σ (Fin.castSucc j) ≠ i := by
        rw [hσ, Ne, Equiv.swap_apply_eq_iff, Equiv.swap_apply_left]
        exact Fin.castSucc_ne_last j
      simp [Function.update_of_ne hne, hL₀]

  have hev : ∀ B : LineBundle k x, ∀ᶠ c : ℕ in atTop,
      interSum pp (Function.update (fun j => (L j).toSubSystem) i B.toSubSystem) c =
        interNum pp (Function.update (fun j => (L j).toSubSystem) i B.toSubSystem) := fun B => by
    obtain ⟨a, ha⟩ := hE k Ω N x (m + 1) pp (Function.update L i B) hW
    rw [hfam B]
    exact interSum_eventually_eq_interNum pp _ ha
  have hz := hZ k Ω N x (m + 1) pp
    (Fin.snoc (α := fun _ => LineBundle k x) (Fin.snoc (α := fun _ => LineBundle k x) L₀ L') L'') hW
  obtain ⟨c, h1, h2, h3, h4⟩ :=
    ((hev (L'.tensorProd L'')).and ((hev L').and ((hev L'').and hz))).exists
  have hs : (fun j => (Fin.snoc (α := fun _ => LineBundle k x)
      (Fin.snoc (α := fun _ => LineBundle k x) L₀ L') L'' j).toSubSystem) =
      Fin.snoc (α := fun _ => SubSystem k x Ω) (Fin.snoc (α := fun _ => SubSystem k x Ω)
        (fun j => (L₀ j).toSubSystem) L'.toSubSystem) L''.toSubSystem := by
    have e1 := Fin.comp_snoc (fun B : LineBundle k x => B.toSubSystem)
      (Fin.snoc (α := fun _ => LineBundle k x) L₀ L') L''
    have e2 := Fin.comp_snoc (fun B : LineBundle k x => B.toSubSystem) L₀ L'
    simp only [Function.comp_def] at e1 e2
    rw [e1, e2]
  have key := mixDiff_snoc_mul (fun F => restrLen pp (F.twist (twistSys k x (c : ℤ))))
    (fun j => (L₀ j).toSubSystem) L'.toSubSystem L''.toSubSystem
  rw [← interSum_eq_mixDiff, ← interSum_eq_mixDiff, ← interSum_eq_mixDiff, ← interSum_eq_mixDiff, ← hs, h4,
    add_zero, ← hmove, ← hmove, ← hmove] at key
  have e : (L'.tensorProd L'').toSubSystem = L'.toSubSystem.twist L''.toSubSystem := rfl
  rw [e] at h1
  rw [← h1, ← h2, ← h3]
  exact key

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PVeryAmpleZRowsX
section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CechPartitionSt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

def CechPartition.Statement : Prop :=
  ∀ (S : Type u) [CommRing S] (Ω : Type w) [Field Ω] (E : Type v) [AddCommGroup E] [Module Ω E] [Module S E]
    {n : ℕ} (U : Finset (Fin n)) (M : Cell U → Submodule S E) (m : ℕ) (a b : Fin m → Ω) (j : Fin m → Fin n),
    (∀ k, j k ∈ U) → ∑ k, a k * b k = 1 →
    (∀ k I, ∀ z ∈ M I, a k • z ∈ M I) → (∀ k I, ∀ z ∈ M I, b k • z ∈ M I) →
    (∀ k (I I' : Cell U), I'.1 = insert (j k) I.1 → ∀ z ∈ M I', ∃ e : ℕ, b k ^ e • z ∈ M I) →
    ∀ p : ℕ, ∀ s ∈ Cech.Cdeg (fun _ : Cell U => E) M (p + 1),
      Cech.d (fun _ : Cell U => E) (Cech.idRes S E U) (p + 1) s = 0 →
        ∃ t ∈ Cech.Cdeg (fun _ : Cell U => E) M p, Cech.d (fun _ : Cell U => E) (Cech.idRes S E U) p t = s

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmpleZRows
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

namespace VeryAmpleZRows

variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V] {n : ℕ} {U : Finset (Fin n)}

def onSet {i : ℕ} (s : Cech.Cochain (fun _ : Cell U => V) i) (A : Finset (Fin n)) : V :=
  if h : A.card = i + 1 ∧ A ⊆ U then s ⟨⟨A, Finset.card_pos.mp (by omega), h.2⟩, h.1⟩ else 0

theorem onSet_idx {i : ℕ} (s : Cech.Cochain (fun _ : Cell U => V) i) (I : Cech.Idx U i) :
    onSet s I.1.1 = s I := by
  unfold onSet
  rw [dite_eq_left ⟨I.2, I.1.2.2⟩]

theorem d_eq {i : ℕ} (s : Cech.Cochain (fun _ : Cell U => V) i) (K : Cech.Idx U (i + 1)) :
    Cech.d (fun _ : Cell U => V) (Cech.idRes R V U) i s K =
      ∑ j ∈ K.1.1, Cech.sgn K.1.1 j • onSet s (K.1.1.erase j) := by
  rw [Cech.d_apply, ← Finset.sum_coe_sort K.1.1]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← onSet_idx s (Cech.face K j)]
  rfl

theorem onSet_pair {s : Cech.Cochain (fun _ : Cell U => V) 0}
    (hs : Cech.d (fun _ : Cell U => V) (Cech.idRes R V U) 0 s = 0) {a b : Fin n} (ha : a ∈ U) (hb : b ∈ U)
    (hab : a < b) : onSet s {a} = onSet s {b} := by
  have hcard : ({a, b} : Finset (Fin n)).card = 0 + 1 + 1 := Finset.card_pair hab.ne
  have h := congrFun hs ⟨⟨{a, b}, Finset.insert_nonempty _ _,
    Finset.insert_subset ha (Finset.singleton_subset_iff.mpr hb)⟩, hcard⟩
  rw [d_eq] at h
  change ∑ j ∈ ({a, b} : Finset (Fin n)), Cech.sgn {a, b} j • onSet s (({a, b} : Finset _).erase j) = 0 at h
  rw [Finset.sum_pair hab.ne, Finset.erase_insert (Finset.notMem_singleton.mpr hab.ne),
    Finset.erase_insert_of_ne hab.ne, Finset.erase_singleton, insert_empty_eq] at h
  have e1 : Cech.sgn ({a, b} : Finset (Fin n)) a = 1 := by
    simp [Cech.sgn, Finset.filter_insert, Finset.filter_singleton, not_lt.mpr hab.le]
  have e2 : Cech.sgn ({a, b} : Finset (Fin n)) b = -1 := by
    simp [Cech.sgn, Finset.filter_insert, Finset.filter_singleton, hab]
  rw [e1, e2, one_smul, neg_one_smul, ← sub_eq_add_neg, sub_eq_zero] at h
  exact h.symm

theorem const_zero {s : Cech.Cochain (fun _ : Cell U => V) 0}
    (hs : Cech.d (fun _ : Cell U => V) (Cech.idRes R V U) 0 s = 0) (I K : Cech.Idx U 0) : s I = s K := by
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp I.2
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp K.2
  have haU : a ∈ U := I.1.2.2 (ha ▸ Finset.mem_singleton_self a)
  have hbU : b ∈ U := K.1.2.2 (hb ▸ Finset.mem_singleton_self b)
  rw [← onSet_idx s I, ← onSet_idx s K, ha, hb]
  rcases lt_trichotomy a b with h | rfl | h
  · exact onSet_pair hs haU hbU h
  · rfl
  · exact (onSet_pair hs hbU haU h).symm

end VeryAmpleZRows


open VeryAmpleZRows in
theorem VeryAmpleZRows.proof (hPart : CechPartition.Statement.{u, v, w}) (hSmul : ZChartSmul.Statement.{u, v, w})
    (hLoc : ZChartLocal.Statement.{u, v, w}) : VeryAmpleZRows.Statement.{u, v, w} := by
  intro S _ Ω _ _ N x E _ _ _ _ G H r h hH J
  have hmono : ∀ I I' : Chart x, I.1 ⊆ I'.1 →
      secsOnZChart G.toSubSystem H.toSubSystem h I J ≤ secsOnZChart G.toSubSystem H.toSubSystem h I' J := by
    intro I I' hII'
    refine Submodule.span_mono ?_
    rintro e ⟨m, hm⟩
    exact ⟨m, (G.toSubSystem.twist (H.toSubSystem.pow (J.1.card * m))).mono I I' hII' _ hm⟩

  obtain ⟨j, hjJ⟩ := J.2.1
  obtain ⟨n, a, b, K, ha, hb, hab, hK⟩ := hH.affine j ((mem_support h).mp (J.2.2 hjJ))
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp at hab
    · exact hn

  let pt : ∀ i, i ∈ support x → Cech.Idx (support x) 0 := fun i hi =>
    ⟨⟨{i}, Finset.singleton_nonempty _, Finset.singleton_subset_iff.mpr hi⟩, Finset.card_singleton _⟩
  obtain ⟨i₀, hi₀⟩ := (K ⟨0, hn⟩).2.1
  have hi₀x : i₀ ∈ support x := (K ⟨0, hn⟩).2.2 hi₀
  refine ⟨hmono, fun I => iInf_le _ I, fun z _ hz => hz (pt i₀ hi₀x), ?_, ?_⟩
  ·
    intro s hs hds
    refine ⟨s (pt i₀ hi₀x), Submodule.mem_iInf _ |>.mpr fun I => ?_, fun I => const_zero hds I _⟩
    obtain ⟨i, hi⟩ := I.2.1
    rw [const_zero hds (pt i₀ hi₀x) (pt i (I.2.2 hi))]
    exact hmono (pt i (I.2.2 hi)).1 I (Finset.singleton_subset_iff.mpr hi)
      ((Submodule.mem_pi.mp hs) _ (Set.mem_univ _))
  ·
    intro p s hs hds
    have hjk : ∀ k, (K k).2.1.choose ∈ (K k).1 := fun k => (K k).2.1.choose_spec
    exact hPart S Ω E (support x) (fun I => secsOnZChart G.toSubSystem H.toSubSystem h I J) n a b
      (fun k => (K k).2.1.choose) (fun k => (K k).2.2 (hjk k)) hab
      (fun k I z hz => hSmul S Ω N x E G.toSubSystem H.toSubSystem r h hH.mem_secs J j hjJ I (a k) (ha k) z hz)
      (fun k I z hz => hSmul S Ω N x E G.toSubSystem H.toSubSystem r h hH.mem_secs J j hjJ I (b k) (hb k) z hz)
      (fun k I I' hI z hz => hLoc S Ω N x E G H r h hH.mem_secs J j hjJ (b k) (hb k) (K k) (hK k) _ (hjk k)
        I I' hI z hz)
      p s hs hds

end

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCechPartition
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

theorem CechPartition.proof : CechPartition.Statement.{u, v, w} := by
  intro S _ Ω _ E _ _ _ n U M m a b j hjU hab ha hb hloc p s hs hds

  let T : Subring Ω :=
    { carrier := {c | ∀ I, ∀ z ∈ M I, c • z ∈ M I}
      mul_mem' := fun {x y} hx hy I z hz => by rw [mul_smul]; exact hx I _ (hy I z hz)
      one_mem' := fun I z hz => by rwa [one_smul]
      add_mem' := fun {x y} hx hy I z hz => by rw [add_smul]; exact (M I).add_mem (hx I z hz) (hy I z hz)
      zero_mem' := fun I z _ => by rw [zero_smul]; exact (M I).zero_mem
      neg_mem' := fun {x} hx I z hz => by rw [neg_smul]; exact (M I).neg_mem (hx I z hz) }
  have hT : ∀ c ∈ T, ∀ I, ∀ z ∈ M I, c • z ∈ M I := fun c hc => hc
  let b' : Fin m → T := fun k => ⟨b k, hb k⟩

  have hspan : Ideal.span (Set.range b') = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    have h1 : (∑ k, (⟨a k, ha k⟩ : T) * b' k) = 1 := Subtype.ext (by simp [b', hab])
    rw [← h1]
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨k, rfl⟩)

  have hex : ∀ (k : Fin m) (K : Cech.Idx U p), ∃ e0 : ℕ, j k ∉ K.1.1 →
      b k ^ e0 • Cech.Partition.onSet s (insert (j k) K.1.1) ∈ M K.1 := by
    intro k K
    by_cases hk : j k ∈ K.1.1
    · exact ⟨0, fun h => absurd hk h⟩
    · let I' : Cell U := ⟨insert (j k) K.1.1, Finset.insert_nonempty _ _, Finset.insert_subset (hjU k) K.1.2.2⟩
      have hI' : I'.1.card = p + 1 + 1 := by
        change (insert (j k) K.1.1).card = p + 1 + 1
        rw [Finset.card_insert_of_notMem hk, K.2]
      have hz : Cech.Partition.onSet s (insert (j k) K.1.1) ∈ M I' := by
        rw [show insert (j k) K.1.1 = (⟨I', hI'⟩ : Cech.Idx U (p + 1)).1.1 from rfl, Cech.Partition.onSet_idx]
        exact (Submodule.mem_pi.mp hs) ⟨I', hI'⟩ (Set.mem_univ _)
      obtain ⟨e0, he0⟩ := hloc k K.1 I' rfl _ hz
      exact ⟨e0, fun _ => he0⟩
  choose f hf using hex
  obtain ⟨e, he⟩ : ∃ e, ∀ k K, f k K ≤ e := by
    obtain ⟨e, he⟩ := (Set.finite_range (fun x : Fin m × Cech.Idx U p => f x.1 x.2)).bddAbove
    exact ⟨e, fun k K => he ⟨(k, K), rfl⟩⟩

  have hpow := Ideal.span_pow_eq_top (Set.range b') hspan e
  rw [← Set.range_comp, Ideal.eq_top_iff_one, Ideal.mem_span_range_iff_exists_fun] at hpow
  obtain ⟨c, hc⟩ := hpow

  let wt : Fin n → Ω := fun i => ∑ k ∈ Finset.univ.filter (fun k => j k = i), (c k : Ω) * b k ^ e
  have hw : ∑ i ∈ U, wt i = 1 := by
    rw [Finset.sum_fiberwise_of_maps_to (fun k _ => hjU k)]
    have h := congrArg Subtype.val hc
    simpa [b'] using h
  refine Cech.Partition.exact_of_partition M s hds wt hw ?_
  intro K i _ hiK
  simp only [wt, Finset.sum_smul]
  refine Submodule.sum_mem _ fun k hk => ?_
  obtain rfl := (Finset.mem_filter.mp hk).2
  rw [mul_smul, ← Nat.sub_add_cancel (he k K), pow_add, mul_smul]
  exact hT _ (c k).2 _ _ (hT _ (pow_mem (show b k ∈ T from hb k) _) _ _ (hf k K hiK))

end

end GroundTheory.Heights₂.Heights.Kleiman
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

universe u v w

theorem VeryAmpleZRows.proof_closed : VeryAmpleZRows.Statement.{u, v, w} :=
  VeryAmpleZRows.proof CechPartition.proof ZChartSmul.proof (ZChartLocal.proof ZChartSmul.proof)

end GroundTheory.Heights₂.Heights.Kleiman
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PVanishingCechResidue
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.KeyFormula

open Complex Matrix

noncomputable section

open RigSymForm

theorem serreVanishing_graded_holds : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman.SerreVanish.Statement :=
  (GroundTheory.Heights₂.Heights.Kleiman.TranslateEq.SerreVanish.equiv
    GroundTheory.Heights₂.Heights.Kleiman.TranslateEq.GradedCech.proof).1
    GroundTheory.Heights₂.Heights.Kleiman.SerreVanish.full.{0, 0}

end

end GroundTheory.Heights₂.Heights.KeyFormula
end
