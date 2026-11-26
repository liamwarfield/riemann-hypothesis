module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteQuotientCocycleSpansLeContinuousCocycles
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteQuotientCocycleSpansLeContinuousCocycles
noncomputable section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.Cut.CocN

open GlobalTheory.Cut.Coc

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (S : IdempotentChoiceData D.nd i)

theorem blocks (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (hS : Formalism.MainNotions.IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S) (g : GE D.nd) :
    S.ψρ (tw i r S g) = WpO D.nd i ρ π g ∧
    ∀ c : Fin D.R.t, S.ψχ c (tw i r S g) =
      (((chiU D.nd i 1 g)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) * ((chiU D.nd i ((c : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i) := by
  obtain ⟨-, h1, h2, -, -, -, -, -, -, ⟨hp, -⟩, -⟩ := hS
  have key : ∀ w : (Fin D.R.r → KK D.nd i) × (Fin D.R.t → KK D.nd i),
      (((S.ψρ (tw i r S g)).map (toK D.nd i)).mulVec w.1,
        fun c : Fin D.R.t => toK D.nd i (S.ψχ c (tw i r S g)) * w.2 c) =
      toK D.nd i (((chiU D.nd i 1 g)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) •
      ((mapM (toK D.nd i) (rhoO D.nd i ρ π) g).mulVec w.1,
        fun c : Fin D.R.t => toK D.nd i ((chiU D.nd i ((c : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i) * w.2 c) := by
    intro w
    obtain ⟨u, rfl⟩ := S.e.surjective w
    rw [← h2 _ (tw_mem i r S g) u, ← h1 g u, ← map_smul, ← Matrix.smul_mulVec]
    congr 2
    ext p q
    unfold GlobalTheory.Cut.Coc.tw
    simp [hp, mapM]
  have hinj : Function.Injective (toK D.nd i) := IsFractionRing.injective _ _
  constructor
  · ext p q
    apply hinj
    have := congrFun (congrArg Prod.fst (key (Pi.single q 1, 0))) p
    simpa [mapM, WpO, twistM] using this
  · intro c
    apply hinj
    have := congrFun (congrArg Prod.snd (key (0, 1))) c
    simpa using this

theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → Formalism.MainNotions.IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S → π ∈ Xs → cocRho i r S Xs ≤ Z1 (WKG (WpO D.nd i ρ π)) ∧ ∀ c : Fin D.R.t, cocChi i r S Xs c ≤ Z1 (WKG (chiRatO D.nd i ((c : ℕ) + 1))) := by
  intro D i r ρ π Xs S hr hS _
  refine ⟨cocW_le i r S hr Xs _ _ fun g => (blocks i r S ρ π hS g).1, fun c =>
    cocW_le i r S hr Xs _ _ fun g => ?_⟩
  rw [(blocks i r S ρ π hS g).2 c, mul_comm]
  rfl

end GlobalTheory.Cut.CocN

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteQuotientCocycleSpansLeContinuousCocyclesStatement
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteQuotientCocycleSpans_le_continuousCocycles : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → Formalism.MainNotions.IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S → π ∈ Xs → cocRho i r S Xs ≤ Z1 (WKG (WpO D.nd i ρ π)) ∧ ∀ c : Fin D.R.t, cocChi i r S Xs c ≤ Z1 (WKG (chiRatO D.nd i ((c : ℕ) + 1))) := by
  first | exact @GlobalTheory.Cut.CocN.main | exact GlobalTheory.Cut.CocN.main | (intros; apply GlobalTheory.Cut.CocN.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaCocycleBlockLengthLeOfQuadraticRelation
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaCocycleBlockLengthLeOfQuadraticRelation
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.Cut.QuadN

theorem psiChi_group {D : D7} {i : D.nd.Loc} {r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))}
    {ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))} {π : D.nd.X i} {S : IdempotentChoiceData D.nd i}
    (hS : Formalism.MainNotions.IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S) (c : Fin D.R.t) (g : GE D.nd) :
    S.ψχ c (fun x' => rO D.nd i r (S.p x') g) = ((chiU D.nd i ((c : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i) := by
  obtain ⟨-, h1, h2, -, -, -, -, -, -, ⟨hp, -⟩, -⟩ := hS
  have hg : InR' D.nd r S fun x' => rO D.nd i r (S.p x') g :=
    ⟨1, fun _ => 1, fun _ => g, fun _ => one_mem _, by funext x; simp⟩
  have a1 := h1 g (S.e.symm (0, fun _ => 1))
  have a2 := h2 _ hg (S.e.symm (0, fun _ => 1))
  simp only [hp] at a2
  have a3 := congrFun (congrArg Prod.snd (a2.symm.trans a1)) c
  simp only [LinearEquiv.apply_symm_apply, mul_one] at a3
  exact IsFractionRing.injective _ _ a3

theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → Formalism.MainNotions.IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S → π ∈ Xs → ∀ v, v ∈ D.nd.S i ∨ v ∈ D.nd.Q i → QuadAt i r Xs v → ∀ c : Fin D.R.t, Module.length (D.nd.O i) ↥(resIne i (cocChi i r S Xs c) v) ≤ lenQ i (D.nd.zeta i v - 1) := by
  intro D i r ρ π Xs S hr hS hπ v hv hq c
  have hl := D.nd.SQ_l i v hv
  have hchi : ∀ γ ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), chiU D.nd i ((c : ℕ) + 1) γ = chiU D.nd i 1 γ :=
    fun γ hγ => (GlobalTheory.T.cyclotomicChar_unramified_away_from_ell D i v hl γ hγ).2 _ (by omega) c.2
  have hγ0 := D.nd.locNd_chebotarevPlace_mem i v
  have htor : ∀ f ∈ cocChi i r S Xs c, (D.nd.zeta i v - 1) • f (D.nd.gam0 i v) = 0 := by
    intro f hf
    have := Check.cocW_quad i r S Xs _ hq hf _ hγ0
    rw [Check.matKO_smul_one, psiChi_group hS, hchi _ hγ0] at this
    rw [sub_smul, one_smul, sub_eq_zero]
    exact this
  have hdet : ∀ f ∈ cocChi i r S Xs c, f (D.nd.gam0 i v) = 0 →
      ∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), f σ = 0 := by
    intro f hf h0
    obtain ⟨hc, hz⟩ := (GlobalTheory.Cut.CocN.main D i r ρ π Xs S hr hS hπ).2 c hf
    have : DiscreteTopology (KOG (D.nd.O i) 1) := ⟨rfl⟩
    have hlc : IsLocallyConstant f := (IsLocallyConstant.iff_continuous f).2 hc
    have hadd : ∀ a ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), ∀ b ∈ Ine (F := D.host.E) (D.nd.plOm.1 v),
        f (a * b) = f a + f b := by
      intro a ha b _
      have e : chiRatO D.nd i ((c : ℕ) + 1) a = (1 : D.nd.O i) • 1 := by
        change (((chiU D.nd i ((c : ℕ) + 1) a * (chiU D.nd i 1 a)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i)) •
          (1 : Matrix (Fin 1) (Fin 1) (D.nd.O i)) = _
        rw [hchi a ha, mul_inv_cancel, Units.val_one]
      rw [hz, Check.WKG_eq_matKO, e, Check.matKO_smul_one, one_smul]
    exact GlobalTheory.Cut.Quad.eq_zero_of_tameGen (D.nd.restN_tameGenerator_generates i v hv) f hlc hadd (GlobalTheory.T.wildInertia_killed_by_additive_locallyConstant D i v hl f hlc hadd) h0
  refine le_trans ?_ (GlobalTheory.Cut.Quad.length_torsionBy_le (D.nd.zeta i v - 1))
  refine Module.length_le_of_injective
    (LinearMap.restrict (LinearMap.proj (⟨D.nd.gam0 i v, hγ0⟩ : Ine (F := D.host.E) (D.nd.plOm.1 v))) ?_) ?_
  · rintro _ ⟨f, hf, rfl⟩
    exact htor f hf
  · rw [injective_iff_map_eq_zero]
    rintro ⟨_, f, hf, rfl⟩ h0
    refine Subtype.ext (funext fun σ => ?_)
    exact hdet f hf (congrArg Subtype.val h0) σ.1 σ.2

end GlobalTheory.Cut.QuadN
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaCocycleBlockLengthLeOfQuadraticRelationStatement
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertiaCocycleBlock_length_le_of_quadraticRelation : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → Formalism.MainNotions.IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S → π ∈ Xs → ∀ v, v ∈ D.nd.S i ∨ v ∈ D.nd.Q i → QuadAt i r Xs v → ∀ c : Fin D.R.t, Module.length (D.nd.O i) ↥(resIne i (cocChi i r S Xs c) v) ≤ lenQ i (D.nd.zeta i v - 1) := by
  first | exact @GlobalTheory.Cut.QuadN.main | exact GlobalTheory.Cut.QuadN.main | (intros; apply GlobalTheory.Cut.QuadN.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthHeckeValueIdealLeDeterminantBound
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthHeckeValueIdealLeDeterminantBound
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

noncomputable section

namespace GlobalTheory.CutDetOrd

open GlobalTheory.CutDet

theorem value_mem_ccOff :
    ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → Formalism.MainNotions.IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S → π ∈ Xs → ∀ f ∈ S.T', (∀ x', S.p x' ∈ Xs → S.p x' ∉ D.nd.Z i → f x' = 0) → f S.π' ∈ ccOff i Xs π := by
  intro D i r ρ π Xs S _ hS _ f hf h0
  obtain ⟨-, -, -, -, -, -, -, ⟨-, -, -, ⟨b, -, hb⟩, -⟩, -, ⟨hπ, -⟩, -⟩ := hS
  obtain ⟨cf, hcf, -⟩ := hb f hf
  have huniq : ∀ c : Fin D.R.t.factorial → D.nd.T i,
      (0 : S.X' → D.nd.O i) = ∑ k, ((fun x' => (c k : D.nd.X i → D.nd.O i) (S.p x')) :
        S.X' → D.nd.O i) * b k → c = 0 := by
    intro c hc
    obtain ⟨c0, -, hc0⟩ := hb 0 (zero_mem _)
    rw [hc0 c hc, hc0 0 (by funext x'; simp)]
  have hz : ∀ k, ∀ x ∈ Xs, x ∉ D.nd.Z i → (cf k : D.nd.X i → D.nd.O i) x = 0 := by
    intro k x hx hZ
    refine cutVal_coord_eq_zero (D.nd.T i) (D.nd.T_sep i) S.p b huniq cf x (fun x' hp => ?_) k
    rw [← hcf]
    exact h0 x' (hp ▸ hx) (hp ▸ hZ)
  rw [hcf, Finset.sum_apply]
  refine Ideal.sum_mem _ fun k _ => ?_
  rw [Pi.mul_apply]
  refine Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨cf k, (cf k).2, hz k, ?_⟩)
  rw [hπ]

theorem exists_ne_zero : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → Formalism.MainNotions.IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S → π ∈ Xs → NoChiOff i r Xs → ∀ x', S.p x' ∈ Xs → S.p x' ∉ D.nd.Z i → ∃ η : Fin D.R.nV → KK D.nd i, ∃ γ : GE D.nd, ((yg D.nd r S γ x').map (toK D.nd i)).mulVec η ≠ 0 := by
  intro D i r ρ π Xs S _ hG _ hN x' hx hZ
  have hrank : ((Eel D.nd S x').map (toK D.nd i)).rank = 1 := hG.2.2.2.2.2.2.2.2.2.2.1.1 x'
  by_contra hcon
  push Not at hcon
  have h0 : ∀ η : Fin D.R.nV → KK D.nd i, ((Eel D.nd S x').map (toK D.nd i)).mulVec η = 0 := by
    intro η
    apply hN _ hx hZ
    intro g
    have h := hcon η g
    have hy : yg D.nd r S g x' = rTwO D.nd i r (S.p x') g * Eel D.nd S x' - Eel D.nd S x' := by
      unfold yg
      rw [← Matrix.smul_mul]
      rfl
    rw [hy, Matrix.map_sub _ (map_sub _), Matrix.map_mul, Matrix.sub_mulVec, sub_eq_zero,
      ← Matrix.mulVec_mulVec] at h
    exact h
  have hz : ((Eel D.nd S x').map (toK D.nd i)).mulVecLin = 0 := LinearMap.ext h0
  unfold Matrix.rank at hrank
  rw [hz, LinearMap.range_zero, finrank_bot] at hrank
  exact zero_ne_one hrank

theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → Formalism.MainNotions.IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S → π ∈ Xs → π ∈ D.nd.Z i → NoChiOff i r Xs → Module.length (D.nd.O i) (D.nd.O i ⧸ ccOff i Xs π) ≤ Module.length (D.nd.O i) ↥(cocRho i r S Xs) + ∑ c : Fin D.R.t, Module.length (D.nd.O i) ↥(cocChi i r S Xs c) := by
  intro D i r ρ π Xs S hr hS hπ _ hchi
  classical
  have h52 := value_mem_ccOff D i r ρ π Xs S hr hS hπ
  have h54 := exists_ne_zero D i r ρ π Xs S hr hS hπ hchi
  obtain ⟨-, -, hcomp, hsurj, -, -, -, -, -, -, -, h51, -⟩ := hS
  have hinj : Function.Injective (algebraMap (D.nd.O i) (KK D.nd i)) := IsFractionRing.injective _ _
  let A : Subalgebra (D.nd.O i) (S.X' → MatN D.nd i) := spanAlg S.T' (fun x' => rO D.nd i r (S.p x'))
  obtain ⟨g, γ, hγ⟩ := exists_gens A (yg D.nd r S)
  have hY : ∀ m, InY D.nd r S m → ∃ θ : Fin g → A, m = ∑ q, (θ q : S.X' → MatN D.nd i) * yg D.nd r S (γ q) := by
    rintro _ ⟨m, a, s, ha, rfl⟩
    exact hγ m a s ha
  obtain ⟨P, Q, hPQ, hQP, hconj⟩ := exists_conj S.e
  have hbl := fun a (ha : a ∈ A) => hconj _ _ _ (hcomp a ha)
  obtain ⟨⟨fρ, hfρ⟩, hχ⟩ := exists_homs hinj A S.π' P Q hPQ hQP S.ψρ S.ψχ hbl
  choose fχ hfχ using hχ
  let Rel : Submodule A (Fin g → A) :=
    { carrier := {θ | ∀ x', S.p x' ∈ Xs → (∑ q, (θ q : S.X' → MatN D.nd i) * yg D.nd r S (γ q)) x' = 0}
      add_mem' := fun {a b} ha hb x' hx => by
        have := congrArg₂ (· + ·) (ha x' hx) (hb x' hx)
        simpa [add_mul, Finset.sum_add_distrib] using this
      zero_mem' := fun x' _ => by simp
      smul_mem' := fun c θ hθ x' hx => by
        have := congrArg (fun z => (c : S.X' → MatN D.nd i) x' * z) (hθ x' hx)
        simpa [Finset.sum_apply, Finset.mul_sum, mul_assoc] using this }
  let d : Option (Fin D.R.t) → ℕ := blockDim D.R.r
  let ψ := blockHom fρ fχ
  have hψχ : ∀ c (a : A), ψ (some c) a = S.ψχ c a • (1 : Matrix (Fin 1) (Fin 1) (D.nd.O i)) := by
    intro c a
    rw [← hfχ, ← Algebra.algebraMap_eq_smul_one]
    rfl
  have key := GlobalTheory.T.determinantLemma_discreteValuationRing_quotientLength_bound (D.nd.O i) A (Option (Fin D.R.t)) d ψ (by
    rintro (_ | c) B
    · obtain ⟨a, ha, rfl⟩ := hsurj B
      exact ⟨⟨a, ha⟩, hfρ _⟩
    · change Matrix (Fin 1) (Fin 1) (D.nd.O i) at B
      refine ⟨algebraMap _ _ (B 0 0), ((ψ (some c)).commutes _).trans ?_⟩
      change algebraMap _ (Matrix (Fin 1) (Fin 1) (D.nd.O i)) _ = B
      ext a b
      rw [Subsingleton.elim a 0, Subsingleton.elim b 0]
      simp [Matrix.algebraMap_matrix_apply]) g Rel (ccOff i Xs π) (by
    intro n θ hθ m
    have hT := GlobalTheory.BlockDetPoly.main S.T' D.R.nV A h51 n g (fun k p q => θ k p q) (fun k p q => (θ k p q).2) m
    have h2 := h52 _ hT (by
      intro x' hx hz
      obtain ⟨η, s, hs⟩ := h54 x' hx hz
      rw [det_generic_eq_zero hinj (fun k p q => (θ k p q : S.X' → MatN D.nd i) x')
        (fun q => ((yg D.nd r S (γ q) x').map (toK D.nd i)).mulVec η) ?_ ?_, AddMonoidAlgebra.coeff_zero]
      · rfl
      · intro h0
        apply hs
        obtain ⟨t, ht⟩ := hγ 1 (fun _ => 1) (fun _ => s) (fun _ => A.one_mem)
        rw [Fin.sum_univ_one, one_mul] at ht
        set_option synthInstance.maxHeartbeats 100000 in
          rw [ht, Finset.sum_apply, ← RingHom.mapMatrix_apply, map_sum, Matrix.sum_mulVec]
        refine Finset.sum_eq_zero fun q _ => ?_
        rw [Pi.mul_apply, map_mul, ← Matrix.mulVec_mulVec, RingHom.mapMatrix_apply _ (yg D.nd r S (γ q) x'),
          show ((yg D.nd r S (γ q) x').map (toK D.nd i)).mulVec η = 0 from congrFun h0 q, Matrix.mulVec_zero]
      · intro k p
        have h3 := congrArg (fun z => ((toK D.nd i).mapMatrix z).mulVec η) (hθ k p x' hx)
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [Finset.sum_apply, map_sum, Matrix.sum_mulVec, Pi.mul_apply, map_mul, map_zero,
          Matrix.zero_mulVec, ← Matrix.mulVec_mulVec] at h3
        exact h3)
    rw [det_generic_blocks hinj P Q hPQ hQP (fun k p q => (θ k p q : S.X' → MatN D.nd i) S.π')
      (fun k p q => S.ψρ (θ k p q)) (fun c k p q => S.ψχ c (θ k p q))
      (fun k p q => hbl _ (θ k p q).2)] at h2
    rw [Fintype.prod_option]
    convert h2 using 3
    congr 1
    · congr 1
      ext1 pa qb
      simp only [Matrix.of_apply, ← hfρ]
      rfl
    · refine Finset.prod_congr rfl fun c _ => ?_
      refine (Matrix.det_submatrix_equiv_self (Equiv.prodUnique (Fin g) (Fin 1)).symm _).symm.trans ?_
      congr 1
      ext1 p q
      simp [hψχ])
  refine key.trans ?_
  rw [Fintype.sum_option]
  refine add_le_add ?_ (Finset.sum_le_sum fun c _ => ?_)
  · exact length_sol_le A fρ S.ψρ hfρ (yg D.nd r S) γ (InY D.nd r S) (fun y => ∀ x', S.p x' ∈ Xs → y x' = 0)
      hY Rel (fun _ h => h) (fun _ _ => rfl)
  · exact length_sol_le A (ψ (some c)) _ (hψχ c) (yg D.nd r S) γ (InY D.nd r S)
      (fun y => ∀ x', S.p x' ∈ Xs → y x' = 0) hY Rel (fun _ h => h) (fun _ _ => rfl)

end GlobalTheory.CutDetOrd

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthHeckeValueIdealLeDeterminantBoundStatement
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.length_heckeValueIdeal_le_determinant_bound : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → Formalism.MainNotions.IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S → π ∈ Xs → π ∈ D.nd.Z i → NoChiOff i r Xs → Module.length (D.nd.O i) (D.nd.O i ⧸ ccOff i Xs π) ≤ Module.length (D.nd.O i) ↥(cocRho i r S Xs) + ∑ c : Fin D.R.t, Module.length (D.nd.O i) ↥(cocChi i r S Xs c) := by
  first | exact @GlobalTheory.CutDetOrd.main | exact GlobalTheory.CutDetOrd.main | (intros; apply GlobalTheory.CutDetOrd.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaRestrictionPolynomialConditionSecondForm
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaRestrictionPolynomialConditionSecondForm
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.Cut.PolynomialInertiaAction

open GlobalTheory.Cut.PolyInertia

theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → Formalism.MainNotions.IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S → π ∈ Xs → ∀ v ∈ D.nd.S i, PolyAt i r Xs π v → ∀ c : Fin D.R.t, resIne i (cocChi i r S Xs c) v = ⊥ := by
  intro D i r ρ π Xs S _ hG _ v hv hP c
  obtain ⟨P, hP0, hPu⟩ := hP
  obtain ⟨-, hdec, hψ, -, -, -, -, ⟨hT, -⟩, -, ⟨hπ, -⟩, -⟩ := hG
  set γ0 := D.nd.gam0 i v with hγ0
  let a : S.X' → MatN D.nd i := fun x' =>
    Polynomial.aeval (rO D.nd i r (S.p x') γ0) (P.map (evT D.nd i (S.p x')))
  have ha_eq : ∀ x', a x' = ∑ k : Fin (P.natDegree + 1),
      evT D.nd i (S.p x') (P.coeff k) • rO D.nd i r (S.p x') (γ0 ^ (k : ℕ)) := by
    intro x'
    simp only [a, aeval_map_eq_sum, map_pow]
  have ha : InR' D.nd r S a := by
    refine ⟨P.natDegree + 1, fun k x' => evT D.nd i (S.p x') (P.coeff k), fun k => γ0 ^ (k : ℕ),
      fun k => hT _ (P.coeff k).2, ?_⟩
    funext x'
    rw [ha_eq, Finset.sum_apply]
  have h1 : InR' D.nd r S 1 := by
    refine ⟨1, fun _ => 1, fun _ => 1, fun _ => one_mem _, ?_⟩
    funext x'
    simp
  have hchi : chiU D.nd i ((c : ℕ) + 1) γ0 = chiU D.nd i 1 γ0 :=
    (GlobalTheory.T.cyclotomicChar_unramified_away_from_ell D i v (D.nd.SQ_l i v (Or.inl hv)) γ0 (D.nd.locNd_chebotarevPlace_mem i v)).2 _
      (Nat.le_add_left _ _) c.2
  have hval : S.ψχ c a = (P.map (evT D.nd i π)).eval (D.nd.zeta i v) := by
    apply IsFractionRing.injective (D.nd.O i) (KK D.nd i)
    let u := S.e.symm (0, Pi.single c 1)
    have hu : (S.e u).2 c = 1 := by simp [u]
    have e1 := congrArg (fun z => z.2 c) (hψ a ha u)
    simp only [hu, mul_one] at e1
    have e2 : ((a S.π').map (toK D.nd i)).mulVec u = ∑ k : Fin (P.natDegree + 1),
        toK D.nd i (evT D.nd i π (P.coeff k)) •
          (mapM (toK D.nd i) (rO D.nd i r π) (γ0 ^ (k : ℕ))).mulVec u := by
      rw [ha_eq, hπ]
      change ((toK D.nd i).mapMatrix _).mulVec u = _
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Matrix.sum_mulVec]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Matrix.smul_mulVec]
      congr 1
      ext p q
      simp [mapM]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e2, map_sum, Prod.snd_sum, Finset.sum_apply] at e1
    change toK D.nd i _ = toK D.nd i _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← e1, ← Polynomial.coe_aeval_eq_eval, aeval_map_eq_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, hdec]
    simp only [Prod.smul_snd, Pi.smul_apply, hu, mul_one, map_pow, hchi, smul_eq_mul, map_mul,
      Units.val_pow_eq_pow_val]
    rfl
  rw [resIne, cocChi, cocW, Submodule.map_span, Submodule.span_eq_bot]
  rintro _ ⟨_, ⟨φ, hφ, hφ0, rfl⟩, rfl⟩
  funext γ
  change φ (yg D.nd r S γ) = 0
  have hy : InY D.nd r S (yg D.nd r S γ) :=
    ⟨1, fun _ => 1, fun _ => γ, fun _ => h1, by simp⟩
  have hay : InY D.nd r S (a * yg D.nd r S γ) :=
    ⟨1, fun _ => a, fun _ => γ, fun _ => ha, by simp⟩
  have hz : φ (a * yg D.nd r S γ) = 0 := by
    refine hφ0 _ hay fun x' hx' => ?_
    have h := hP0 (S.p x') hx' γ γ.2
    have : yg D.nd r S γ x' = (((chiU D.nd i 1 γ)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) •
        ((rO D.nd i r (S.p x') γ - ((chiU D.nd i 1 γ : (D.nd.O i)ˣ) : D.nd.O i) • (1 : MatN D.nd i)) *
          Eel D.nd S x') := by
      rw [yg, sub_mul, smul_sub, smul_mul_assoc, one_mul, smul_smul, Units.inv_mul, one_smul]
    rw [Pi.mul_apply, this, mul_smul_comm, ← mul_assoc]
    simp only [a]
    rw [h, zero_mul, smul_zero]
  rw [hφ a ha _ hy, matKO_smul_one, hval] at hz
  exact hPu.smul_eq_zero.mp hz

end GlobalTheory.Cut.PolynomialInertiaAction
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaRestrictionPolynomialConditionSecondFormStatement
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertia_restriction_polynomial_condition_second_form : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → Formalism.MainNotions.IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S → π ∈ Xs → ∀ v ∈ D.nd.S i, PolyAt i r Xs π v → ∀ c : Fin D.R.t, resIne i (cocChi i r S Xs c) v = ⊥ := by
  first | exact @GlobalTheory.Cut.PolynomialInertiaAction.main | exact GlobalTheory.Cut.PolynomialInertiaAction.main | (intros; apply GlobalTheory.Cut.PolynomialInertiaAction.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalCocyclesAboveEllInCutUnitDelta
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalCocyclesAboveEllInCutUnitDelta
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.Cut.LocalCocycleConstruction

open GlobalTheory.Cut.LocCoc

theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → Formalism.MainNotions.IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S → π ∈ Xs → ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), (∀ f ∈ cocRho i r S Xs, InCut i r Xs (WpO D.nd i ρ π) w hw f) ∧ ∀ c : Fin D.R.t, ∀ f ∈ cocChi i r S Xs c, InCut i r Xs (chiRatO D.nd i ((c : ℕ) + 1)) w hw f := by
  intro D i r ρ π Xs S _ hG _ w hw
  obtain ⟨-, hdec, hψ, -, -, -, -, -, -, ⟨hπ, -⟩, -⟩ := hG
  have key : ∀ γ u, (((S.ψρ fun x' => rTwO D.nd i r (S.p x') γ).map (toK D.nd i)).mulVec (S.e u).1,
      fun c : Fin D.R.t => toK D.nd i (S.ψχ c fun x' => rTwO D.nd i r (S.p x') γ) * (S.e u).2 c) =
      toK D.nd i (((chiU D.nd i 1 γ)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) •
        ((mapM (toK D.nd i) (rhoO D.nd i ρ π) γ).mulVec (S.e u).1,
        fun c : Fin D.R.t => toK D.nd i ((chiU D.nd i ((c : ℕ) + 1) γ : (D.nd.O i)ˣ) : D.nd.O i) * (S.e u).2 c) := by
    intro γ u
    rw [← hψ _ (GlobalTheory.Cut.LocCoc.inR'_tw i r S γ) u, ← hdec, ← map_smul, hπ, ← Matrix.smul_mulVec]
    congr 2
    ext p q
    simp [mapM, rTwO, twistM]
  refine ⟨fun f hf => GlobalTheory.Cut.LocCoc.inCut_of_cocW i r S Xs _ _ (fun γ => ?_) w hw f hf,
    fun c f hf => GlobalTheory.Cut.LocCoc.inCut_of_cocW i r S Xs _ _ (fun γ => ?_) w hw f hf⟩
  · ext p q
    apply IsFractionRing.injective (D.nd.O i) (KK D.nd i)
    have h := congrArg (fun z => z.1 p) (key γ (S.e.symm (Pi.single q 1, 0)))
    simpa [mapM, WpO, twistM] using h
  · ext p q
    apply IsFractionRing.injective (D.nd.O i) (KK D.nd i)
    have h := congrArg (fun z => z.2 c) (key γ (S.e.symm (0, Pi.single c 1)))
    obtain rfl : p = q := Subsingleton.elim _ _
    simpa [chiRatO, twistM, mul_comm] using h

end GlobalTheory.Cut.LocalCocycleConstruction
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalCocyclesAboveEllInCutUnitDeltaStatement
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localCocycles_aboveEll_inCut_unitDelta : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → Formalism.MainNotions.IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S → π ∈ Xs → ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), (∀ f ∈ cocRho i r S Xs, InCut i r Xs (WpO D.nd i ρ π) w hw f) ∧ ∀ c : Fin D.R.t, ∀ f ∈ cocChi i r S Xs c, InCut i r Xs (chiRatO D.nd i ((c : ℕ) + 1)) w hw f := by
  first | exact @GlobalTheory.Cut.LocalCocycleConstruction.main | exact GlobalTheory.Cut.LocalCocycleConstruction.main | (intros; apply GlobalTheory.Cut.LocalCocycleConstruction.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthCutCoboundaryModuleLeUnitDelta
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthCutCoboundaryModuleLeUnitDelta
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut
open GlobalTheory.Cut.Cob (length_inf_coboundaries_le_two_mul_rank inSpan_add inSpan_mul inSpan_scalar mat_ext map_smul_mulVec matKO_sum)

namespace GlobalTheory.Cut.CobOrd

variable {D : D7} {i : D.nd.Loc} {r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))}
  {ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))} {π : D.nd.X i} {S : IdempotentChoiceData D.nd i}

theorem inR'_comp (hS : Formalism.MainNotions.IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S) {a : D.nd.X i → MatN D.nd i} (ha : InR D.nd i r a) :
    InR' D.nd r S fun x' => a (S.p x') := by
  obtain ⟨-, -, -, -, -, -, -, ⟨hT, -⟩, -⟩ := hS
  obtain ⟨m, f, g, hf, rfl⟩ := ha
  exact ⟨m, fun k x' => f k (S.p x'), g, fun k => hT _ (hf k), by funext x'; simp only [Finset.sum_apply]⟩

theorem inR'_Eel (hS : Formalism.MainNotions.IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S) : InR' D.nd r S (Eel D.nd S) := by
  have hB := inR'_comp hS hS.1.1
  have hX := inR'_comp hS hS.2.2.2.2.2.2.1.1
  have hr := hS.2.2.2.2.2.2.2.1.2.1
  have key : ∀ L : List ℕ, (∀ c ∈ L, c ∈ Finset.Icc 1 D.R.t) → InR' D.nd r S fun x' =>
      (L.map fun c => S.X0 (S.p x') - S.rr c x' • S.eB (S.p x')).prod := by
    intro L
    induction L with
    | nil => exact fun _ => Check.inR'_one i r S
    | cons c L ih =>
      intro h
      have h1 := inSpan_mul (inSpan_add hX (inSpan_mul (inSpan_scalar (neg_mem (hr c (h c (by simp))))) hB))
        (ih fun c hc => h c (by simp [hc]))
      refine Eq.mp (congrArg (InR' D.nd r S) ?_) h1
      funext x'
      simp [sub_eq_add_neg]
  refine key _ fun c hc => ?_
  rw [List.mem_range'_1] at hc
  rw [Finset.mem_Icc]
  omega

theorem del_mem (hS : Formalism.MainNotions.IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S) : del51 D.nd S ∈ S.T' := by
  have hr := hS.2.2.2.2.2.2.2.1.2.1
  have : del51 D.nd S = ∏ c ∈ Finset.Ioc 1 D.R.t, (S.rr 1 - S.rr c) := by
    funext x'
    simp [del51, Finset.prod_apply]
  rw [this]
  refine prod_mem fun c hc => sub_mem (hr 1 ?_) (hr c ?_) <;>
  · rw [Finset.mem_Ioc] at hc
    rw [Finset.mem_Icc]
    omega

theorem del_smul_sum (hS : Formalism.MainNotions.IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S) (Xs : Set (D.nd.X i)) {k : ℕ}
    (ψ : (S.X' → MatN D.nd i) → Matrix (Fin k) (Fin k) (D.nd.O i)) (hE : ψ (Eel D.nd S) = 0)
    (hψ : ∀ f ∈ S.T', ψ (fun x' => f x' • (1 : MatN D.nd i)) = f S.π' • 1)
    {m : ℕ} {f : Fin m → S.X' → D.nd.O i} {g : Fin m → GE D.nd} (hf : ∀ j, f j ∈ S.T')
    (e : Eel D.nd S = ∑ j, fun x' => f j x' • rO D.nd i r (S.p x') (g j))
    {c : GE D.nd → KOG (D.nd.O i) k} (hc : c ∈ cocW i r S Xs ψ) :
    del51 D.nd S S.π' • ∑ j, (((chiU D.nd i 1 (g j) : (D.nd.O i)ˣ) : D.nd.O i) * f j S.π') • c (g j) = 0 := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨φ, h1, -, rfl⟩ := hc
    have hE2 := hS.2.2.2.2.2.2.2.2.2.2.1.2.1
    let s : Fin m → S.X' → D.nd.O i := fun j => ((chiU D.nd i 1 (g j) : (D.nd.O i)ˣ) : D.nd.O i) • f j
    have hs : ∀ j, s j ∈ S.T' := fun j => S.T'.smul_mem (hf j) _
    let z : S.X' → MatN D.nd i := ∑ j, (fun x' => s j x' • (1 : MatN D.nd i)) * yg D.nd r S (g j)
    have hz : InY D.nd r S z := ⟨m, _, g, fun j => inSpan_scalar (hs j), rfl⟩
    have hz1 : ∀ x', z x' = (del51 D.nd S x' - ∑ j, s j x') • Eel D.nd S x' := by
      intro x'
      rw [sub_smul, ← hE2, Finset.sum_smul]
      nth_rewrite 1 [congrFun e x']
      simp only [z, Finset.sum_apply]
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Pi.mul_apply, yg, s, Pi.smul_apply, smul_eq_mul, smul_mul_assoc, one_mul, smul_sub, smul_smul]
      rw [mul_right_comm, Units.mul_inv, one_mul]
    have hz2 : Eel D.nd S * z = (fun x' => del51 D.nd S x' • (1 : MatN D.nd i)) * z := by
      funext x'
      simp only [Pi.mul_apply, hz1, mul_smul_comm, hE2, smul_mul_assoc, one_mul]
    have h2 := congrArg φ hz2
    rw [h1 _ (inR'_Eel hS) _ hz, h1 _ (inSpan_scalar (del_mem hS)) _ hz, hE, hψ _ (del_mem hS),
      Check.matKO_smul_one, ← zero_smul (D.nd.O i) (1 : Matrix (Fin k) (Fin k) (D.nd.O i)),
      Check.matKO_smul_one, zero_smul] at h2
    rw [h2]
    congr 1
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [z, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [h1 _ (inSpan_scalar (hs j)) _ (Check.inY_yg i r S _), hψ _ (hs j), Check.matKO_smul_one]
    rfl
  | zero => simp
  | add a b _ _ ha hb => simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib, ha, hb, add_zero]
  | smul a b _ hb =>
    simp only [Pi.smul_apply, smul_comm _ a, ← Finset.smul_sum]
    rw [hb, smul_zero]

theorem psi_scalar (hS : Formalism.MainNotions.IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S) {f : S.X' → D.nd.O i} (hf : f ∈ S.T') :
    S.ψρ (fun x' => f x' • (1 : MatN D.nd i)) = f S.π' • 1 ∧
      ∀ c, S.ψχ c (fun x' => f x' • (1 : MatN D.nd i)) = f S.π' := by
  have h := fun u => hS.2.2.1 _ (inSpan_scalar hf) (S.e.symm u)
  simp only [map_smul_mulVec, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec, map_smul,
    LinearEquiv.apply_symm_apply] at h
  refine ⟨mat_ext fun v => ?_, fun c => ?_⟩
  · rw [map_smul_mulVec, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
    exact (congrArg Prod.fst (h (v, 0))).symm
  · have := congrFun (congrArg Prod.snd (h (0, fun _ => 1))) c
    simp only [Prod.smul_snd, Pi.smul_apply, smul_eq_mul, mul_one] at this
    exact (IsFractionRing.injective _ _ this).symm

theorem psi_Eel (hS : Formalism.MainNotions.IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S) :
    S.ψρ (Eel D.nd S) = 0 ∧ ∀ c : Fin D.R.t, (c : ℕ) ≠ 0 → S.ψχ c (Eel D.nd S) = 0 := by
  have h := fun u => (hS.2.2.1 _ (inR'_Eel hS) (S.e.symm u)).symm.trans (hS.2.2.2.2.2.2.2.2.2.2.1.2.2.1 _)
  simp only [LinearEquiv.apply_symm_apply] at h
  refine ⟨mat_ext fun v => ?_, fun c hc => ?_⟩
  · rw [Matrix.map_zero _ (map_zero _), Matrix.zero_mulVec]
    exact congrArg Prod.fst (h (v, 0))
  · have := congrFun (congrArg Prod.snd (h (0, fun _ => 1))) c
    simp only [mul_one, if_neg hc] at this
    exact IsFractionRing.injective (D.nd.O i) (KK D.nd i) (this.trans (map_zero _).symm)

theorem sum_blocks (hS : Formalism.MainNotions.IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S)
    {m : ℕ} {f : Fin m → S.X' → D.nd.O i} {g : Fin m → GE D.nd}
    (e : Eel D.nd S = ∑ j, fun x' => f j x' • rO D.nd i r (S.p x') (g j)) :
    ∑ j, f j S.π' • rhoO D.nd i ρ π (g j) = 0 ∧
      ∀ c : Fin D.R.t, ∑ j, f j S.π' * ((chiU D.nd i ((c : ℕ) + 1) (g j) : (D.nd.O i)ˣ) : D.nd.O i) =
        if (c : ℕ) = 0 then del51 D.nd S S.π' else 0 := by
  have hp : S.p S.π' = π := hS.2.2.2.2.2.2.2.2.2.1.1
  have hsum : ∀ {k : ℕ} (A : Fin m → Matrix (Fin k) (Fin k) (D.nd.O i)) (v : Fin k → KK D.nd i),
      ((∑ j, f j S.π' • A j).map (toK D.nd i)).mulVec v =
        ∑ j, toK D.nd i (f j S.π') • ((A j).map (toK D.nd i)).mulVec v := by
    intro k A v
    change ((toK D.nd i).mapMatrix _).mulVec v = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Matrix.sum_mulVec]
    exact Finset.sum_congr rfl fun j _ => map_smul_mulVec _ _ _
  have h1 : ∀ g u, S.e (((rO D.nd i r π g).map (toK D.nd i)).mulVec u) =
      (((rhoO D.nd i ρ π g).map (toK D.nd i)).mulVec (S.e u).1,
        fun c : Fin D.R.t => toK D.nd i ((chiU D.nd i ((c : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i) * (S.e u).2 c) :=
    hS.2.1
  have h := fun u => hS.2.2.2.2.2.2.2.2.2.2.1.2.2.1 (S.e.symm u)
  rw [congrFun e S.π'] at h
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finset.sum_apply, hp, hsum, map_sum, map_smul, h1, LinearEquiv.apply_symm_apply] at h
  refine ⟨mat_ext fun v => ?_, fun c => ?_⟩
  · rw [Matrix.map_zero _ (map_zero _), Matrix.zero_mulVec, hsum]
    have := congrArg Prod.fst (h (v, 0))
    rw [Prod.fst_sum] at this
    exact this
  · have := congrFun (congrArg Prod.snd (h (0, fun _ => 1))) c
    rw [Prod.snd_sum, Finset.sum_apply] at this
    simp only [Prod.smul_snd, Pi.smul_apply, smul_eq_mul, mul_one] at this
    apply IsFractionRing.injective (D.nd.O i) (KK D.nd i)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [apply_ite (algebraMap (D.nd.O i) (KK D.nd i)), map_zero, map_sum]
    simp only [map_mul]
    exact this

theorem del_sq_smul (hS : Formalism.MainNotions.IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S) (Xs : Set (D.nd.X i)) {k : ℕ}
    (ψ : (S.X' → MatN D.nd i) → Matrix (Fin k) (Fin k) (D.nd.O i)) (hE : ψ (Eel D.nd S) = 0)
    (hψ : ∀ f ∈ S.T', ψ (fun x' => f x' • (1 : MatN D.nd i)) = f S.π' • 1)
    (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (hM : ∀ {m : ℕ} {f : Fin m → S.X' → D.nd.O i} {g : Fin m → GE D.nd},
      (Eel D.nd S = ∑ j, fun x' => f j x' • rO D.nd i r (S.p x') (g j)) →
      ∑ j, (((chiU D.nd i 1 (g j) : (D.nd.O i)ˣ) : D.nd.O i) * f j S.π') • M (g j) = 0)
    (w : KOG (D.nd.O i) k) (hw : d0 (WKG M) w ∈ cocW i r S Xs ψ) :
    (del51 D.nd S S.π' * del51 D.nd S S.π') • w = 0 := by
  obtain ⟨m, f, g, hf, e⟩ := inR'_Eel hS
  have h := del_smul_sum hS Xs ψ hE hψ hf e hw
  have h0 := (sum_blocks hS e).2 ⟨0, D.R.t_odd.pos⟩
  simp only [zero_add, if_true, mul_comm (f _ _)] at h0
  simp only [amitsur_d0_apply, smul_sub, Finset.sum_sub_distrib, Check.WKG_eq_matKO] at h
  rw [← matKO_sum, hM e, ← Finset.sum_smul, h0, ← zero_smul (D.nd.O i) (1 : Matrix (Fin k) (Fin k) (D.nd.O i)),
    Check.matKO_smul_one, zero_smul, smul_zero, zero_sub, neg_eq_zero, smul_smul] at h
  exact h

theorem main : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → Formalism.MainNotions.IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S → π ∈ Xs → lenCob i (WpO D.nd i ρ π) (cocRho i r S Xs) ≤ ((2 * D.R.r : ℕ) : ℕ∞) * lenQ i (del51 D.nd S S.π') ∧ ∀ c : Fin D.R.t, lenCob i (chiRatO D.nd i ((c : ℕ) + 1)) (cocChi i r S Xs c) ≤ 2 * lenQ i (del51 D.nd S S.π') := by
  intro D i r ρ π Xs S _ hS _
  refine ⟨length_inf_coboundaries_le_two_mul_rank _ _ _ (del_sq_smul hS Xs _ (psi_Eel hS).1 (fun f hf => (psi_scalar hS hf).1) _ ?_),
    fun c => ?_⟩
  · intro m f g e
    rw [← (sum_blocks hS e).1]
    refine Finset.sum_congr rfl fun j _ => ?_
    change _ • ((((chiU D.nd i 1 (g j))⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) • rhoO D.nd i ρ π (g j)) = _
    rw [smul_smul, mul_right_comm, Units.mul_inv, one_mul]
  have hχ : ∀ g, chiRatO D.nd i ((c : ℕ) + 1) g =
      ((chiU D.nd i ((c : ℕ) + 1) g * (chiU D.nd i 1 g)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) •
        (1 : Matrix (Fin 1) (Fin 1) (D.nd.O i)) := fun _ => rfl
  by_cases hc : (c : ℕ) = 0
  · have : ReciprocityTheory.Gal.B1 (WKG (chiRatO D.nd i ((c : ℕ) + 1))) = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨w, rfl⟩
      funext g
      change WKG _ g w - w = 0
      rw [Check.WKG_eq_matKO, hχ, Check.matKO_smul_one, hc, zero_add, mul_inv_cancel, Units.val_one, one_smul,
        sub_self]
    rw [lenCob, this, inf_bot_eq, Module.length_bot]
    exact zero_le
  · refine length_inf_coboundaries_le_two_mul_rank _ _ _ (del_sq_smul hS Xs _ ?_ (fun f hf => ?_) _ ?_)
    · simp only [(psi_Eel hS).2 c hc, zero_smul]
    · simp only [(psi_scalar hS hf).2 c]
    · intro m f g e
      have h := (sum_blocks hS e).2 c
      rw [if_neg hc] at h
      simp only [hχ, smul_smul]
      rw [← Finset.sum_smul]
      convert zero_smul (D.nd.O i) (1 : Matrix (Fin 1) (Fin 1) (D.nd.O i))
      rw [← h]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Units.val_mul, mul_mul_mul_comm, mul_comm _ ((chiU D.nd i ((c : ℕ) + 1) (g j) : (D.nd.O i)ˣ) : D.nd.O i)]
      have := (chiU D.nd i 1 (g j)).mul_inv
      linear_combination (f j S.π' * ((chiU D.nd i ((c : ℕ) + 1) (g j) : (D.nd.O i)ˣ) : D.nd.O i)) * this

end GlobalTheory.Cut.CobOrd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LengthCutCoboundaryModuleLeUnitDeltaStatement
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.length_cutCoboundaryModule_le_unitDelta : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (Xs : Set (D.nd.X i)) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → Formalism.MainNotions.IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S → π ∈ Xs → lenCob i (WpO D.nd i ρ π) (cocRho i r S Xs) ≤ ((2 * D.R.r : ℕ) : ℕ∞) * lenQ i (del51 D.nd S S.π') ∧ ∀ c : Fin D.R.t, lenCob i (chiRatO D.nd i ((c : ℕ) + 1)) (cocChi i r S Xs c) ≤ 2 * lenQ i (del51 D.nd S S.π') := by
  first | exact @GlobalTheory.Cut.CobOrd.main | exact GlobalTheory.Cut.CobOrd.main | (intros; apply GlobalTheory.Cut.CobOrd.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalCongruenceCountOfRootDifferenceUnit
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut Module

noncomputable section

namespace GlobalTheory.CutCoreUnit

variable {D : D7} (i : D.nd.Loc)

theorem ccOff_univ (π : D.nd.X i) : ccOff i Set.univ π = ccAt (D.nd.T i) (D.nd.Z i) π := by
  rw [ccOff, ccAt, Ideal.map]
  congr 1
  ext a
  constructor
  · rintro ⟨f, hf, h0, rfl⟩
    refine ⟨⟨f, hf⟩, ?_, rfl⟩
    change (⟨f, hf⟩ : D.nd.T i) ∈ RingHom.ker _
    rw [RingHom.mem_ker]
    funext y
    exact h0 y.1 trivial y.2
  · rintro ⟨f, hf, rfl⟩
    refine ⟨f.1, f.2, fun x _ hx => ?_, rfl⟩
    change f ∈ RingHom.ker _ at hf
    rw [RingHom.mem_ker] at hf
    exact congrFun hf ⟨x, hx⟩


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 4000000 in
theorem main : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S → π ∈ D.nd.Z i → NoChiOff i r Set.univ → UnrOut i r Set.univ → (∀ v ∈ D.nd.S i, (QuadAt i r Set.univ v ∧ IsUnit (D.nd.zeta i v - 1)) ∨ PolyAt i r Set.univ π v) → (∀ v ∈ D.nd.Q i, QuadAt i r Set.univ v ∧ D.nd.zeta i v ≠ 1) → (∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)), (LocBound i w hw r Set.univ (WpO D.nd i ρ π) 0 ∧ (∀ c ∈ Finset.Icc 2 D.R.t, ∀ z ∈ cutCoc i w hw r Set.univ (chiRatO D.nd i c), z ∈ BD (Br.locLat D.nbr i w hw (chiRatO D.nd i c))) ∧ ∀ z ∈ cutCoc i w hw r Set.univ (chiRatO D.nd i 1), z ∈ Z1urD (Br.locLat D.nbr i w hw (chiRatO D.nd i 1)) (Br.inert D.nbr i w hw))) → Br.sFin D.loc D.nbr i ρ π → (∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) < ⊤) → D.nd.vcc i π ≤ Br.sPi D.loc D.nbr i ρ π + (∑ e ∈ Finset.Ioo 0 D.R.t, (D.what₂.shaLen (D.nd.l i) e : ℚ)) + (padicValNat (D.nd.l i) (hE D.host) : ℚ) + (D.R.t : ℚ) * ∑ q ∈ D.nd.Q i, lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {D.nd.zeta i q - 1}) := by
  intro hA D i r ρ π S hr hS hZ hN hU hSv hQ hl hsel hsha
  classical
  have hπ : π ∈ (Set.univ : Set (D.nd.X i)) := trivial
  obtain ⟨L, hL⟩ := CutCore.exists_length_quot (GlobalTheory.LenUnitPow.natCast_ne_zero (D.nd.l i) (O := D.nd.O i))
  have hL0 : L ≠ 0 := by
    rintro rfl
    exact GlobalTheory.LenUnitPow.natCast_not_isUnit (D.nd.l i) (O := D.nd.O i) (CutCore.length_quot_eq_zero_iff.mp hL)
  have hd : lenQ i (del51 D.nd S S.π') = 0 :=
    CutCore.length_quot_eq_zero_iff.mpr hS.2.2.2.2.2.2.2.2.2.2.1.2.2.2
  obtain ⟨s, hs⟩ := ENat.ne_top_iff_exists.mp (ne_of_lt hsel)

  have hρ : Module.length (D.nd.O i) ↥(cocRho i r S Set.univ) ≤ (s : ℕ∞) := by
    obtain ⟨C, hC, hfin, hlen⟩ := GlobalTheory.T.length_global_cocycles_le_sum_places_over D i r Set.univ _ (WpO D.nd i ρ π) (cocRho i r S Set.univ) 0
      (fun w hw => ⟨(hl w hw).1, (GlobalTheory.T.localCocycles_aboveEll_inCut_unitDelta D i r ρ π Set.univ S hr hS hπ w hw).1⟩)
    rw [mul_zero, Nat.cast_zero, zero_mul, zero_add] at hlen
    refine hlen.trans ((GlobalTheory.T.length_cocycles_le_coboundaries_add_selmer D i ρ π C (hC.trans (GlobalTheory.T.finiteQuotientCocycleSpans_le_continuousCocycles D i r ρ π Set.univ S hr hS hπ).1) hfin ?_).trans ?_)
    · intro v h1 h2 h3
      exact CutCore.resIne_eq_bot_of_le i hC
        (GlobalTheory.Proof.LocalGlobalSelmer.main D i r Set.univ S _ S.ψρ (CutCore.inR'_one i r S) hU v h1 h2 h3)
    · have hc := (CutCore.lenCob_mono i _ hC).trans (GlobalTheory.T.length_cutCoboundaryModule_le_unitDelta D i r ρ π Set.univ S hr hS hπ).1
      rw [hd, mul_zero, nonpos_iff_eq_zero] at hc
      rw [hc, zero_add, ← hs]

  have hχ : ∀ c : Fin D.R.t, Module.length (D.nd.O i) ↥(cocChi i r S Set.univ c) ≤
      lenQ i ((D.nd.l i : ℕ) : D.nd.O i) * (if (c : ℕ) = 0 then ((padicValNat (D.nd.l i) (hE D.host) : ℕ) : ℕ∞)
          else Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) ((c : ℕ) : ℤ)) +
        ∑ q ∈ D.nd.Q i, lenQ i (D.nd.zeta i q - 1) := by
    intro c
    obtain ⟨C', hC', hq, hlen'⟩ := GlobalTheory.Cut.Peel.main D i 1 (cocChi i r S Set.univ c) (D.nd.Q i)
    have hZ1 := hC'.trans ((GlobalTheory.T.finiteQuotientCocycleSpans_le_continuousCocycles D i r ρ π Set.univ S hr hS hπ).2 c)
    have hunr : ∀ v, v ∉ placesOver D.host.E (D.nd.l i) → resIne i C' v = ⊥ := by
      intro v h1
      by_cases h3 : v ∈ D.nd.Q i
      · exact hq v h3
      refine CutCore.resIne_eq_bot_of_le i hC' ?_
      by_cases h2 : v ∈ D.nd.S i
      · rcases hSv v h2 with ⟨hqd, hu⟩ | hp
        · have h := GlobalTheory.T.inertiaCocycleBlock_length_le_of_quadraticRelation D i r ρ π Set.univ S hr hS hπ v (Or.inl h2) hqd c
          rw [lenQ, CutCore.length_quot_eq_zero_iff.mpr hu, nonpos_iff_eq_zero, Module.length_eq_zero_iff] at h
          exact Submodule.subsingleton_iff_eq_bot.mp h
        · exact GlobalTheory.T.inertia_restriction_polynomial_condition_second_form D i r ρ π Set.univ S hr hS hπ v h2 hp c
      · exact GlobalTheory.Proof.LocalGlobalSelmer.main D i r Set.univ S _ _ (CutCore.inR'_one i r S) hU v h1 h2 h3
    refine hlen'.trans (add_le_add ?_ (Finset.sum_le_sum fun q hq' =>
      GlobalTheory.T.inertiaCocycleBlock_length_le_of_quadraticRelation D i r ρ π Set.univ S hr hS hπ q (Or.inr hq') (hQ q hq').1 c))
    by_cases hc : (c : ℕ) = 0
    · rw [if_pos hc]
      have e : (c : ℕ) + 1 = 1 := by omega
      rw [e] at hZ1
      have hloc : ∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)), ∀ f ∈ C',
          InCut i r Set.univ (chiRatO D.nd i 1) w hw f := by
        intro w hw f hf
        have h := (GlobalTheory.T.localCocycles_aboveEll_inCut_unitDelta D i r ρ π Set.univ S hr hS hπ w hw).2 c f (hC' hf)
        rwa [e] at h
      refine GlobalTheory.UnramHom.length_le_classNumber hA D i C' hZ1 fun v => ?_
      by_cases hv : v ∈ placesOver D.host.E (D.nd.l i)
      · exact GlobalTheory.CutTrivIne.main D i C' v hv fun f hf =>
          (Submodule.span_le.mpr fun z hz => (hl v hv).2.2 z hz) (hloc v hv f hf)
      · exact hunr v hv
    · rw [if_neg hc]
      have h2 : 2 ≤ (c : ℕ) + 1 := by omega
      have ht : (c : ℕ) + 1 ≤ D.R.t := c.2
      have h := GlobalTheory.T.length_cyclotomic_block_cocycles_le_sha D i ((c : ℕ) + 1) C' hZ1 h2 ht
        (fun f hf w hw => (Submodule.span_le.mpr fun z hz =>
          (hl w hw).2.1 _ (Finset.mem_Icc.mpr ⟨h2, ht⟩) z hz)
            ((GlobalTheory.T.localCocycles_aboveEll_inCut_unitDelta D i r ρ π Set.univ S hr hS hπ w hw).2 c f (hC' hf))) hunr
      rw [Nat.add_sub_cancel] at h
      have hc0 := (CutCore.lenCob_mono i _ hC').trans ((GlobalTheory.T.length_cutCoboundaryModule_le_unitDelta D i r ρ π Set.univ S hr hS hπ).2 c)
      rw [hd, mul_zero, nonpos_iff_eq_zero] at hc0
      rw [hc0, zero_add] at h
      exact h

  have hz : ∀ q ∈ D.nd.Q i, lenQ i (D.nd.zeta i q - 1) = ((lenQ i (D.nd.zeta i q - 1)).toNat : ℕ∞) := by
    intro q hq
    obtain ⟨n, hn⟩ := CutCore.exists_length_quot (sub_ne_zero.mpr (hQ q hq).2)
    rw [lenQ, hn, ENat.toNat_coe]
  set z : HeightOneSpectrum (𝓞 D.host.E) → ℕ := fun q => (lenQ i (D.nd.zeta i q - 1)).toNat with hzdef
  set g : ℕ → ℕ := fun e => (Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ)).toNat with hg
  have hg' : ∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) = (g e : ℕ∞) :=
    fun e he => (ENat.coe_toNat (hsha e he).ne).symm
  have ht : 0 < D.R.t := D.R.t_odd.pos
  set h := padicValNat (D.nd.l i) (hE D.host) with hh
  have hχ' : ∀ c : Fin D.R.t, Module.length (D.nd.O i) ↥(cocChi i r S Set.univ c) ≤
      ((L * (if (c : ℕ) = 0 then h else g c) + ∑ q ∈ D.nd.Q i, z q : ℕ) : ℕ∞) := by
    intro c
    refine (hχ c).trans (le_of_eq ?_)
    rw [Finset.sum_congr rfl hz, lenQ, hL]
    by_cases hc : (c : ℕ) = 0
    · rw [if_pos hc, if_pos hc]
      push_cast
      rfl
    · rw [if_neg hc, if_neg hc, hg' c (Finset.mem_Ioo.mpr ⟨Nat.pos_of_ne_zero hc, c.2⟩)]
      push_cast
      rfl
  have htot := (GlobalTheory.T.length_heckeValueIdeal_le_determinant_bound D i r ρ π Set.univ S hr hS hπ hZ hN).trans
    (add_le_add hρ (Finset.sum_le_sum fun c _ => hχ' c))
  rw [← Nat.cast_sum, ← Nat.cast_add] at htot
  have hnat := ENat.toNat_le_of_le_coe htot
  have hsum : ∑ c : Fin D.R.t, (L * (if (c : ℕ) = 0 then h else g c) + ∑ q ∈ D.nd.Q i, z q) =
      L * (h + ∑ e ∈ Finset.Ioo 0 D.R.t, g e) + D.R.t * ∑ q ∈ D.nd.Q i, z q := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, CutCore.sum_fin_ite ht, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
  rw [hsum] at hnat
  have hsp : Br.sPi D.loc D.nbr i ρ π = (s : ℚ) / L := by
    rw [Br.sPi, lenUnit, hL, ← hs, ENat.toNat_coe, ENat.toNat_coe]
  have hsh : ∑ e ∈ Finset.Ioo 0 D.R.t, (D.what₂.shaLen (D.nd.l i) e : ℚ) =
      ((∑ e ∈ Finset.Ioo 0 D.R.t, g e : ℕ) : ℚ) := by
    rw [Nat.cast_sum]
    exact Finset.sum_congr rfl fun e he =>
      D.nd.sha_eq _ e (Finset.mem_Ioo.mp he).1 (Finset.mem_Ioo.mp he).2 _ (hg' e he)
  have hzq : ∑ q ∈ D.nd.Q i,
      lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {D.nd.zeta i q - 1}) =
        ((∑ q ∈ D.nd.Q i, z q : ℕ) : ℚ) / L := by
    rw [Nat.cast_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [lenUnit, hL, ENat.toNat_coe]
    rfl
  show lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ ccAt (D.nd.T i) (D.nd.Z i) π) ≤ _
  rw [← ccOff_univ, hsp, hsh, hzq, lenUnit, hL, ENat.toNat_coe]
  have hLq : (0 : ℚ) < L := by exact_mod_cast Nat.pos_of_ne_zero hL0
  generalize (Module.length (D.nd.O i) (D.nd.O i ⧸ ccOff i Set.univ π)).toNat = a at hnat
  generalize ∑ e ∈ Finset.Ioo 0 D.R.t, g e = G at hnat ⊢
  generalize ∑ q ∈ D.nd.Q i, z q = Z at hnat ⊢
  have hq : (a : ℚ) ≤ ((s + (L * (h + G) + D.R.t * Z) : ℕ) : ℚ) := Nat.cast_le.mpr hnat
  push_cast at hq
  rw [div_le_iff₀ hLq]
  have e : ((s : ℚ) / L + G + (h : ℚ) + (D.R.t : ℚ) * ((Z : ℚ) / L)) * L =
      s + G * L + h * L + D.R.t * Z := by
    field_simp
  rw [e]
  nlinarith [hq]

end GlobalTheory.CutCoreUnit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GlobalCongruenceCountOfRootDifferenceUnitStatement
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass GlobalTheory.Cut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.globalCongruenceCount_of_rootDifference_unit : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (S : IdempotentChoiceData D.nd i), GoodR D.nd i r → IdempotentChoiceDepthZero.IsOrthogonalIdempotentDecomposition D.nd r ρ π S → π ∈ D.nd.Z i → NoChiOff i r Set.univ → UnrOut i r Set.univ → (∀ v ∈ D.nd.S i, (QuadAt i r Set.univ v ∧ IsUnit (D.nd.zeta i v - 1)) ∨ PolyAt i r Set.univ π v) → (∀ v ∈ D.nd.Q i, QuadAt i r Set.univ v ∧ D.nd.zeta i v ≠ 1) → (∀ w (hw : w ∈ placesOver D.host.E (D.nd.l i)), (LocBound i w hw r Set.univ (WpO D.nd i ρ π) 0 ∧ (∀ c ∈ Finset.Icc 2 D.R.t, ∀ z ∈ cutCoc i w hw r Set.univ (chiRatO D.nd i c), z ∈ BD (Br.locLat D.nbr i w hw (chiRatO D.nd i c))) ∧ ∀ z ∈ cutCoc i w hw r Set.univ (chiRatO D.nd i 1), z ∈ Z1urD (Br.locLat D.nbr i w hw (chiRatO D.nd i 1)) (Br.inert D.nbr i w hw))) → Br.sFin D.loc D.nbr i ρ π → (∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) < ⊤) → D.nd.vcc i π ≤ Br.sPi D.loc D.nbr i ρ π + (∑ e ∈ Finset.Ioo 0 D.R.t, (D.what₂.shaLen (D.nd.l i) e : ℚ)) + (padicValNat (D.nd.l i) (hE D.host) : ℚ) + (D.R.t : ℚ) * ∑ q ∈ D.nd.Q i, lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {D.nd.zeta i q - 1}) := by
  first | exact @GlobalTheory.CutCoreUnit.main | exact GlobalTheory.CutCoreUnit.main | (intros; apply GlobalTheory.CutCoreUnit.main <;> assumption)
end
