module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrbitThickSt
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeLatticeDvrDegree
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsHodgeLatticeGermSystem
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsGermSystem
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GermSystemHeightFree
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ModelFibresPowerFree
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FibreLatticeBaseChangeConj

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HermitianSignatureCharacter
section -- merged from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.HodgeCharacterGeneric
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.Xgn.HodgeCharacterGeneric

open Polynomial GlobalTheory.CompanionTheory.Ar.HT GlobalTheory.CompanionTheory.Ar.HT.LatBasic TensorProduct

variable {E : Type} [Field E] [NumberField E] {K : Type} [Field K] [CharZero K]

theorem sum_emb [Fintype (E →+* K)] (h : Nat.card (E →+* K) = Module.finrank ℚ E) (x : E) :
    ∑ s : E →+* K, s x = algebraMap ℚ K (Algebra.trace ℚ E x) := by
  classical
  letI : CharZero (AlgebraicClosure K) :=
    charZero_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective
  let f : (E →+* K) → (E →ₐ[ℚ] AlgebraicClosure K) := fun s =>
    ((algebraMap K (AlgebraicClosure K)).comp s).toRatAlgHom
  have hf : Function.Injective f := by
    intro s t hst
    ext y
    have := congrArg (fun g : E →ₐ[ℚ] AlgebraicClosure K => g y) hst
    exact (algebraMap K (AlgebraicClosure K)).injective this
  have hcard : Fintype.card (E →+* K) = Fintype.card (E →ₐ[ℚ] AlgebraicClosure K) := by
    rw [AlgHom.card, ← h, Nat.card_eq_fintype_card]
  have hb : Function.Bijective f := (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, hcard⟩
  apply (algebraMap K (AlgebraicClosure K)).injective
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  calc ∑ s : E →+* K, algebraMap K (AlgebraicClosure K) (s x) = ∑ s, f s x := rfl
    _ = ∑ σ : E →ₐ[ℚ] AlgebraicClosure K, σ x := hb.sum_comp (fun σ => σ x)
    _ = algebraMap ℚ (AlgebraicClosure K) (Algebra.trace ℚ E x) :=
        (trace_eq_sum_embeddings (AlgebraicClosure K) (x := x)).symm
    _ = _ := by simp [eq_ratCast]

variable {V : Type} [AddCommGroup V] [Module K V]

theorem sum_eigProj [Fintype (E →+* K)] (h : Nat.card (E →+* K) = Module.finrank ℚ E)
    (ρ : 𝓞 E →+* Module.End K V) : ∑ s, eigProj ρ s = 1 := by
  classical
  set b := RingOfIntegers.basis E with hb
  have h1 : (1 : E) = ∑ j, ((b.repr 1 j : ℤ) : E) * integralBasis E j := by
    have := congrArg (algebraMap (𝓞 E) E) (b.sum_repr 1)
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [integralBasis_apply, map_sum, zsmul_eq_mul] using this.symm
  have hrep : ∀ k, Algebra.trace ℚ E (dualInt E k) = ((b.repr 1 k : ℤ) : ℚ) := by
    intro k
    set_option synthInstance.maxHeartbeats 100000 in
      conv_lhs => rw [← mul_one (dualInt E k), h1, Finset.mul_sum, map_sum]
    simp_rw [mul_left_comm (dualInt E _), ← zsmul_eq_mul, map_zsmul, trace_dualInt]
    simp
  simp only [eigProj]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, sum_emb h, hrep]
  calc ∑ k, algebraMap ℚ K ((b.repr 1 k : ℤ) : ℚ) • ρ (b k) = ρ (∑ k, b.repr 1 k • b k) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [map_zsmul, map_intCast, Int.cast_smul_eq_zsmul]
    _ = 1 := by rw [b.sum_repr, map_one]

theorem isInternal [Fintype (E →+* K)] [DecidableEq (E →+* K)] (h : Nat.card (E →+* K) = Module.finrank ℚ E)
    (ρ : 𝓞 E →+* Module.End K V) : DirectSum.IsInternal (HT.eigSp ρ) := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  constructor
  · intro s
    rw [Submodule.disjoint_def]
    intro x hx hy
    have hk : (⨆ j, ⨆ (_ : j ≠ s), HT.eigSp ρ j) ≤ LinearMap.ker (eigProj ρ s) :=
      iSup₂_le fun j hj y hy => eigProj_of_ne hj.symm hy
    rw [← eigProj_of_mem hx]
    exact hk hy
  · rw [eq_top_iff]
    intro x _
    have : x = ∑ s, eigProj ρ s x := by
      rw [← LinearMap.sum_apply, sum_eigProj h]; rfl
    rw [this]
    exact Submodule.sum_mem _ fun s _ => Submodule.mem_iSup_of_mem s (eigProj_mem ρ s x)

theorem charpoly_eq [Fintype (E →+* K)] [FiniteDimensional K V]
    (h : Nat.card (E →+* K) = Module.finrank ℚ E) (ρ : 𝓞 E →+* Module.End K V) :
    (∀ a : 𝓞 E, (ρ a).charpoly =
      ∏ s : E →+* K, (X - Polynomial.C (s (a : E))) ^ Module.finrank K (HT.eigSp ρ s)) ∧
    ∑ s : E →+* K, Module.finrank K (HT.eigSp ρ s) = Module.finrank K V := by
  classical
  let b := (isInternal h ρ).collectedBasis fun s => Module.finBasis K (HT.eigSp ρ s)
  have hb : ∀ i, b i ∈ HT.eigSp ρ i.1 := fun i => (isInternal h ρ).collectedBasis_mem _ i
  refine ⟨fun a => ?_, ?_⟩
  · have hm : LinearMap.toMatrix b b (ρ a) = Matrix.diagonal fun i => i.1 (a : E) := by
      ext i j
      rw [LinearMap.toMatrix_apply, mem_eigSp.1 (hb j) a, map_smul, b.repr_self, Matrix.diagonal_apply]
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij, Finsupp.single_apply, Ne.symm hij]
    rw [← LinearMap.charpoly_toMatrix _ b, hm, Matrix.charpoly_diagonal, Fintype.prod_sigma]
    simp
  · rw [Module.finrank_eq_card_basis b]
    simp

theorem reg_ne (σ : E →+* K) : eigProj (regAct K E) σ 1 ≠ 0 := by
  classical
  intro h0
  have hne : Nonempty (Module.Free.ChooseBasisIndex ℤ (𝓞 E)) := by
    by_contra hn
    rw [not_nonempty_iff] at hn
    have := sum_dualInt_mul (E := E)
    simp [Finset.univ_eq_empty] at this
  obtain ⟨k⟩ := hne
  simp only [eigProj, LinearMap.sum_apply, LinearMap.smul_apply, regAct_basis] at h0
  have hk := Fintype.linearIndependent_iff.mp
    (Algebra.TensorProduct.basis K (RingOfIntegers.basis E)).linearIndependent _ h0 k
  have hd : dualInt E k = 0 := by
    rw [← map_zero σ] at hk
    exact σ.injective hk
  have ht := trace_dualInt (E := E) k k
  simp [hd] at ht

theorem charpoly_lmul [Fintype (E →+* K)] (h : Nat.card (E →+* K) = Module.finrank ℚ E) (a : 𝓞 E) :
    (Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E)).charpoly.map (Int.castRingHom K) =
      ∏ s : E →+* K, (X - Polynomial.C (s (a : E))) := by
  classical
  have hfr : Module.finrank K (K ⊗[ℤ] 𝓞 E) = Module.finrank ℚ E := by
    rw [Module.finrank_baseChange, RingOfIntegers.rank]
  obtain ⟨hc, hs⟩ := charpoly_eq h (regAct K E)
  have hpos : ∀ s : E →+* K, 1 ≤ Module.finrank K (HT.eigSp (regAct K E) s) := fun s =>
    Module.finrank_pos_iff_exists_ne_zero.mpr
      ⟨⟨_, eigProj_mem _ s 1⟩, fun h0 => reg_ne s (congrArg Subtype.val h0)⟩
  have hone : ∀ s, Module.finrank K (HT.eigSp (regAct K E) s) = 1 := by
    by_contra hn
    push_neg at hn
    obtain ⟨t, ht⟩ := hn
    have hlt : ∑ _s : E →+* K, 1 < ∑ s, Module.finrank K (HT.eigSp (regAct K E) s) :=
      Finset.sum_lt_sum (fun s _ => hpos s)
        ⟨t, Finset.mem_univ _, lt_of_le_of_ne (hpos t) (Ne.symm ht)⟩
    rw [hs, hfr, ← h, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hlt
    simp [Nat.card_eq_fintype_card] at hlt
  have hbc : regAct K E a = (Algebra.lmul ℤ (𝓞 E) a).baseChange K := by
    apply TensorProduct.AlgebraTensorModule.curry_injective
    ext c y
    simp [regAct]
  rw [← algebraMap_int_eq, ← LinearMap.charpoly_baseChange, ← hbc, hc a]
  simp [hone]

theorem charpoly_rhoH {O : Type} [CommRing O] [StarRing O] {d : ℕ} (B : Germ.FB K d O) (a : O) :
    (rhoH B a).charpoly = (rho B a).charpoly * (rho B (star a)).charpoly := by
  classical
  let b := (Pi.basisFun K (Fin d)).prod (Pi.basisFun K (Fin d))
  have hM : LinearMap.toMatrix b b (rhoH B a) =
      Matrix.fromBlocks (rho B a) 0 (-Matrix.transpose (bil (B.ad a) 1 1))
        (Matrix.transpose (rho B (star a))) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [b, LinearMap.toMatrix_apply, rhoH, Matrix.toLin'_apply, Matrix.mulVec_single_one]
  rw [← LinearMap.charpoly_toMatrix (rhoH B a) b, hM, Matrix.charpoly_fromBlocks_zero₁₂,
    Matrix.charpoly_transpose]

end PositivityTheory.Xgn.HodgeCharacterGeneric

theorem PositivityTheory.Xgn.hodge_character_generic : ∀ (E : Type) [Field E] [NumberField E] [StarRing (𝓞 E)] (K : Type) [Field K] [CharZero K] (d r : ℕ) (B : Germ.FB K d (𝓞 E)) (ρ : 𝓞 E →+* Module.End K (Fin d → K)), (∀ a v, ρ a v = (rho B a).mulVec v) → Nat.card (E →+* K) = Module.finrank ℚ E → (∀ s s' : E →+* K, (∀ a : 𝓞 E, s' (a : E) = s ((star a : 𝓞 E) : E)) → Module.finrank K (HT.eigSp ρ s) + Module.finrank K (HT.eigSp ρ s') = r) → HChar B r := by
  classical
  intro E _ _ _ K _ _ d r B ρ hρ h hdim
  have hinj : ∀ s : E →+* K,
      Function.Injective (s.comp ((algebraMap (𝓞 E) E).comp (starRingEnd (𝓞 E)))) :=
    fun s x y hxy => star_injective (IsFractionRing.injective (𝓞 E) E (s.injective hxy))
  let φ : (E →+* K) → (E →+* K) := fun s => IsFractionRing.lift (hinj s)
  have hφ : ∀ s (x : 𝓞 E), φ s (algebraMap (𝓞 E) E x) = s (algebraMap (𝓞 E) E (star x)) :=
    fun s x => IsFractionRing.lift_algebraMap (hinj s) x
  have hφφ : ∀ s, φ (φ s) = s := fun s =>
    IsFractionRing.ringHom_ext (A := 𝓞 E) fun x => by rw [hφ, hφ, star_star]
  have hbij : Function.Bijective φ := Function.Involutive.bijective hφφ
  have hsum : ∀ s, Module.finrank K (HT.eigSp ρ s) + Module.finrank K (HT.eigSp ρ (φ s)) = r :=
    fun s => hdim s (φ s) fun a => hφ s a
  have hrho : ∀ a, (rho B a).charpoly = (ρ a).charpoly := by
    intro a
    rw [← Matrix.charpoly_toLin']
    congr 1
    exact LinearMap.ext fun v => by rw [Matrix.toLin'_apply, hρ]
  obtain ⟨hc, -⟩ := PositivityTheory.Xgn.HodgeCharacterGeneric.charpoly_eq h ρ
  intro a
  rw [PositivityTheory.Xgn.HodgeCharacterGeneric.charpoly_rhoH, hrho, hrho, hc, hc,
    PositivityTheory.Xgn.HodgeCharacterGeneric.charpoly_lmul h, ← Finset.prod_pow]
  have h2 : ∏ s : E →+* K, (Polynomial.X - Polynomial.C (s ((star a : 𝓞 E) : E))) ^
        Module.finrank K (HT.eigSp ρ s) =
      ∏ s : E →+* K, (Polynomial.X - Polynomial.C (s (a : E))) ^
        Module.finrank K (HT.eigSp ρ (φ s)) := by
    symm
    refine Fintype.prod_bijective φ hbij _ _ fun s => ?_
    have := hφ s (star a)
    rw [star_star] at this
    simp only [this]
  rw [h2, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [← pow_add, hsum s]
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HermitianSignatureCharacter
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem hChar_of_eigSp_ranks : ∀ (E : Type) [Field E] [NumberField E] [StarRing (𝓞 E)] (K : Type) [Field K] [CharZero K] (d r : ℕ) (B : Germ.FB K d (𝓞 E)) (ρ : 𝓞 E →+* Module.End K (Fin d → K)), (∀ a v, ρ a v = (rho B a).mulVec v) → Nat.card (E →+* K) = Module.finrank ℚ E → (∀ s s' : E →+* K, (∀ a : 𝓞 E, s' (a : E) = s ((star a : 𝓞 E) : E)) → Module.finrank K (HT.eigSp ρ s) + Module.finrank K (HT.eigSp ρ s') = r) → HChar B r :=
  @PositivityTheory.Xgn.hodge_character_generic

end GlobalTheory.CompanionTheory.Ar.Flat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HermitianSignatureCharacterStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_signature_character : ∀ (E : Type) [Field E] [NumberField E] [StarRing (𝓞 E)] (K : Type) [Field K] [CharZero K] (d r : ℕ) (B : Germ.FB K d (𝓞 E)) (ρ : 𝓞 E →+* Module.End K (Fin d → K)), (∀ a v, ρ a v = (rho B a).mulVec v) → Nat.card (E →+* K) = Module.finrank ℚ E → (∀ s s' : E →+* K, (∀ a : 𝓞 E, s' (a : E) = s ((star a : 𝓞 E) : E)) → Module.finrank K (HT.eigSp ρ s) + Module.finrank K (HT.eigSp ρ s') = r) → HChar B r := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.hChar_of_eigSp_ranks | exact GlobalTheory.CompanionTheory.Ar.Flat.hChar_of_eigSp_ranks | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.hChar_of_eigSp_ranks <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeLatticeTransportEquiv
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeLatticeTransportEquiv
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Flat

namespace HodgeTransport

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {V V' : Type} [AddCommGroup V] [Module Ω V]
  [AddCommGroup V'] [Module Ω V'] {F F' : Type} [AddCommGroup F] [Module Ω F] [AddCommGroup F'] [Module Ω F']
  {E : Type} [Field E] [NumberField E]

def conjE (e : V ≃ₗ[Ω] V') : (V × Module.Dual Ω V) ≃ₗ[Ω] (V' × Module.Dual Ω V') :=
  e.prodCongr e.symm.dualMap

theorem conjE_apply (e : V ≃ₗ[Ω] V') (y : V × Module.Dual Ω V) :
    conjE e y = (e y.1, y.2 ∘ₗ e.symm.toLinearMap) := rfl

theorem conjE_symm_apply (e : V ≃ₗ[Ω] V') (y : V' × Module.Dual Ω V') :
    (conjE e).symm y = (e.symm y.1, y.2 ∘ₗ e.toLinearMap) := rfl

def cj (g : F ≃ₗ[Ω] F') (ρ : 𝓞 E →+* Module.End Ω F) : 𝓞 E →+* Module.End Ω F' :=
  (g.conjRingEquiv : Module.End Ω F →+* Module.End Ω F').comp ρ

theorem cj_apply (g : F ≃ₗ[Ω] F') (ρ : 𝓞 E →+* Module.End Ω F) (a : 𝓞 E) (y : F') :
    cj g ρ a y = g (ρ a (g.symm y)) := rfl

theorem mem_map_equiv (M : Lat ξ F) (g : F ≃ₗ[Ω] F') (p : Cpt ξ) (y : F') :
    y ∈ M.map g.toLinearMap p ↔ g.symm y ∈ M p := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro h
    exact ⟨_, h, by simp⟩

theorem map_symm_map (M : Lat ξ F) (g : F ≃ₗ[Ω] F') :
    (M.map g.toLinearMap).map g.symm.toLinearMap = M := by
  funext p
  ext y
  rw [mem_map_equiv, mem_map_equiv]
  simp

theorem isFrameAt_map {M : Lat ξ F} (g : F ≃ₗ[Ω] F') {r : ℕ} {b : Fin r → F} {p : Cpt ξ}
    (h : M.IsFrameAt b p) : (M.map g.toLinearMap).IsFrameAt (g ∘ b) p := by
  refine ⟨(LinearMap.linearIndependent_iff g.toLinearMap (LinearEquiv.ker g)).2 h.1, ?_⟩
  change Submodule.map _ (M p) = _
  rw [h.2, Submodule.map_span, Set.range_comp]
  rfl

theorem isFrameAt_map_iff {M : Lat ξ F} (g : F ≃ₗ[Ω] F') {r : ℕ} {b : Fin r → F'} {p : Cpt ξ} :
    (M.map g.toLinearMap).IsFrameAt b p ↔ M.IsFrameAt (g.symm ∘ b) p := by
  constructor
  · intro h
    have := isFrameAt_map g.symm h
    rwa [map_symm_map] at this
  · intro h
    have := isFrameAt_map g h
    have e : g ∘ g.symm ∘ b = b := by funext i; simp
    rwa [e] at this

theorem detLat_map (M : Lat ξ F) (g : F ≃ₗ[Ω] F') {r : ℕ} (u : Fin r → F') :
    detLat (M.map g.toLinearMap) u = detLat M (g.symm ∘ u) := by
  funext p
  simp only [detLat]
  congr 1
  ext t
  refine exists_congr fun A => and_congr_left fun _ => ?_
  rw [isFrameAt_map_iff]
  have e : (g.symm ∘ fun i => ∑ j, A i j • u j) = fun i => ∑ j, A i j • (g.symm ∘ u) j := by
    funext i
    simp
  rw [e]

theorem isFreeOn_map {M : Lat ξ F} (g : F ≃ₗ[Ω] F') {ρ : 𝓞 E →+* Module.End Ω F} {p : Cpt ξ} {N : ℕ}
    {t : Fin N → F} (h : HT.IsFreeOn ρ (M p) t) :
    HT.IsFreeOn (cj g ρ) (M.map g.toLinearMap p) (g ∘ t) := by
  have e : (fun q : Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
      cj g ρ (RingOfIntegers.basis E q.2) ((g ∘ t) q.1)) =
      g ∘ fun q : Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
        ρ (RingOfIntegers.basis E q.2) (t q.1) := by
    funext q
    simp [cj_apply]
  refine ⟨?_, ?_, ?_⟩
  · rw [e]
    exact (LinearMap.linearIndependent_iff g.toLinearMap (LinearEquiv.ker g)).2 h.1
  · have e2 : ((M.map g.toLinearMap p : Submodule _ F') : Set F') = g '' (M p : Set F) := rfl
    rw [e2]
    have := Submodule.map_span g.toLinearMap (M p : Set F)
    rw [h.2.1, Submodule.map_top, LinearEquiv.range] at this
    exact this.symm
  · rw [e]
    change Submodule.map _ (M p) = _
    rw [h.2.2, Submodule.map_span, Set.range_comp]
    rfl

theorem eigProj_cj (g : F ≃ₗ[Ω] F') (ρ : 𝓞 E →+* Module.End Ω F) (σ : E →+* Ω) (y : F') :
    HT.eigProj (cj g ρ) σ y = g (HT.eigProj ρ σ (g.symm y)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [HT.eigProj, LinearMap.sum_apply, cj_apply, map_sum]

theorem mem_eigSp_cj (g : F ≃ₗ[Ω] F') (ρ : 𝓞 E →+* Module.End Ω F) (σ : E →+* Ω) (y : F') :
    y ∈ HT.eigSp (cj g ρ) σ ↔ g.symm y ∈ HT.eigSp ρ σ := by
  rw [HT.LatBasic.mem_eigSp, HT.LatBasic.mem_eigSp]
  refine forall_congr' fun a => ?_
  rw [cj_apply, ← map_smul, LinearEquiv.eq_symm_apply]

theorem eigQuot_map (M : Lat ξ F) (g : F ≃ₗ[Ω] F') (ρ : 𝓞 E →+* Module.End Ω F) (σ : E →+* Ω) :
    (M.map g.toLinearMap).map (HT.eigProj (cj g ρ) σ) = (M.map (HT.eigProj ρ σ)).map g.toLinearMap := by
  funext p
  ext y
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, by simp [eigProj_cj]⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, by simp [eigProj_cj]⟩

variable {L : Lat ξ V} {ρ : 𝓞 E →+* Module.End Ω V} {ρ' : 𝓞 E →+* Module.End Ω V'} {bar : 𝓞 E ≃+* 𝓞 E} {r : ℕ}

def transport (e : V ≃ₗ[Ω] V') (𝓗 : HodgeLat L ρ bar r) (h : ∀ a v, e (ρ a v) = ρ' a (e v)) :
    HodgeLat (L.map e.toLinearMap) ρ' bar r where
  ρH := cj (conjE e) 𝓗.ρH
  HL := 𝓗.HL.map (conjE e).toLinearMap
  act_fst a y := by
    rw [cj_apply, conjE_apply, 𝓗.act_fst, h, conjE_symm_apply]
    simp
  act_inr a φ := by
    rw [cj_apply, conjE_symm_apply]
    simp only [map_zero]
    rw [𝓗.act_inr, conjE_apply]
    refine Prod.ext (by simp) (LinearMap.ext fun x => ?_)
    simp [h]
  map_fst := by
    funext p
    conv_rhs => rw [← 𝓗.map_fst]
    ext y
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  comap_inr := by
    funext p
    ext φ
    have h1 : (φ ∈ (𝓗.HL.map (conjE e).toLinearMap).comap (LinearMap.inr Ω V' (Module.Dual Ω V')) p) ↔
        ((0, φ ∘ₗ e.toLinearMap) : V × Module.Dual Ω V) ∈ 𝓗.HL p := by
      change ((0, φ) : V' × Module.Dual Ω V') ∈ 𝓗.HL.map (conjE e).toLinearMap p ↔ _
      rw [mem_map_equiv, conjE_symm_apply]
      simp
    have h2 : ((0, φ ∘ₗ e.toLinearMap) : V × Module.Dual Ω V) ∈ 𝓗.HL p ↔
        φ ∘ₗ e.toLinearMap ∈ L.dual p := by
      rw [← 𝓗.comap_inr]
      rfl
    rw [h1, h2]
    change (∀ x ∈ L p, φ (e x) ∈ regAt ξ p) ↔ ∀ x ∈ L.map e.toLinearMap p, φ x ∈ regAt ξ p
    constructor
    · rintro hφ _ ⟨z, hz, rfl⟩
      exact hφ z hz
    · intro hφ z hz
      exact hφ _ ⟨z, hz, rfl⟩
  free p := by
    obtain ⟨U, hU, x, hx⟩ := 𝓗.free p
    exact ⟨U, hU, conjE e ∘ x, fun q hq => isFreeOn_map (conjE e) (hx q hq)⟩
  vb := by
    rw [← e.finrank_eq]
    intro p hp
    obtain ⟨U, hU, b, hb, hf⟩ := 𝓗.vb p hp
    refine ⟨U, hU, e ∘ b, ?_, fun q hq hqU => isFrameAt_map e (hf q hq hqU)⟩
    rw [Set.range_comp]
    have := Submodule.map_span e.toLinearMap (Set.range b)
    rw [hb, Submodule.map_top, LinearEquiv.range] at this
    exact this.symm

theorem transport_degZero (e : V ≃ₗ[Ω] V') (𝓗 : HodgeLat L ρ bar r) (h : ∀ a v, e (ρ a v) = ρ' a (e v))
    (σ : E →+* Ω) (ϖ : Ω) (hd : 𝓗.DegZero σ ϖ) : (transport e 𝓗 h).DegZero σ ϖ := by
  intro u hu hsp
  have hq : (transport e 𝓗 h).quot σ = (𝓗.quot σ).map (conjE e).toLinearMap :=
    eigQuot_map 𝓗.HL (conjE e) 𝓗.ρH σ
  rw [hq, detLat_map]
  refine hd _ ((LinearMap.linearIndependent_iff (conjE e).symm.toLinearMap (LinearEquiv.ker _)).2 hu) ?_
  ext y
  have h1 : Set.range ((conjE e).symm ∘ u) = (conjE e).symm.toLinearMap '' Set.range u := Set.range_comp _ _
  rw [h1, ← Submodule.map_span, hsp]
  change _ ↔ y ∈ HT.eigSp 𝓗.ρH σ
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (mem_eigSp_cj (conjE e) 𝓗.ρH σ z).1 hz
  · intro hy
    refine ⟨conjE e y, (mem_eigSp_cj (conjE e) 𝓗.ρH σ _).2 (by simpa using hy), by simp⟩

end HodgeTransport

theorem hodgeLat_transport : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (E : Type) [Field E] [NumberField E] (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω V'] (e : V ≃ₗ[Ω] V') (L : Lat ξ V) (ρ : 𝓞 E →+* Module.End Ω V) (ρ' : 𝓞 E →+* Module.End Ω V') (bar : 𝓞 E ≃+* 𝓞 E) (r : ℕ) (𝓗 : HodgeLat L ρ bar r), (∀ a v, e (ρ a v) = ρ' a (e v)) → ∃ 𝓗' : HodgeLat (L.map e.toLinearMap) ρ' bar r, ∀ σ ϖ, 𝓗.DegZero σ ϖ → 𝓗'.DegZero σ ϖ := by
  intro X Ω _ ξ E _ _ V V' _ _ _ _ e L ρ ρ' bar r 𝓗 h
  exact ⟨HodgeTransport.transport e 𝓗 h, fun σ ϖ hd => HodgeTransport.transport_degZero e 𝓗 h σ ϖ hd⟩

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeLatticeTransportEquivStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_lattice_transport_equiv : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (E : Type) [Field E] [NumberField E] (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω V'] (e : V ≃ₗ[Ω] V') (L : Lat ξ V) (ρ : 𝓞 E →+* Module.End Ω V) (ρ' : 𝓞 E →+* Module.End Ω V') (bar : 𝓞 E ≃+* 𝓞 E) (r : ℕ) (𝓗 : HodgeLat L ρ bar r), (∀ a v, e (ρ a v) = ρ' a (e v)) → ∃ 𝓗' : HodgeLat (L.map e.toLinearMap) ρ' bar r, ∀ σ ϖ, 𝓗.DegZero σ ϖ → 𝓗'.DegZero σ ϖ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.hodgeLat_transport | exact GlobalTheory.CompanionTheory.Ar.Flat.hodgeLat_transport | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.hodgeLat_transport <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLinePAdicBound
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.CptHodge

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem emb_factor {l : Level H} (c : Coeff l) {Ω : Type} [Field Ω] (inc : c.F →+* Ω) :
    Nat.card (E →+* Ω) = Module.finrank ℚ E ∧
      ∀ s : E →+* Ω, ∃ τ : E →+* ℂ, ∀ a : 𝓞 E, s (a : E) = inc (tauIn c τ a) := by
  haveI : CharZero Ω := charZero_of_injective_ringHom inc.injective
  let g : (E →+* ℂ) → (E →+* c.F) := fun τ => τ.codRestrict c.F.toSubfield (c.conj τ)
  let f₁ : (E →+* ℂ) → (E →+* Ω) := fun τ => inc.comp (g τ)
  let f₂ : (E →+* Ω) → (E →+* AlgebraicClosure Ω) := fun s => (algebraMap Ω (AlgebraicClosure Ω)).comp s
  have h₁ : Function.Injective f₁ := fun τ τ' h => by
    ext x
    have := DFunLike.congr_fun h x
    exact congrArg (fun y : c.F => (y : ℂ)) (inc.injective this)
  have h₂ : Function.Injective f₂ := fun s s' h => by
    ext x
    exact (algebraMap Ω (AlgebraicClosure Ω)).injective (DFunLike.congr_fun h x)
  have hb : Function.Bijective (f₂ ∘ f₁) := (Fintype.bijective_iff_injective_and_card _).2
    ⟨h₂.comp h₁, by rw [NumberField.Embeddings.card, NumberField.Embeddings.card]⟩
  have hs : Function.Surjective f₁ := Function.Surjective.of_comp_left hb.2 h₂
  refine ⟨?_, fun s => ?_⟩
  · rw [Nat.card_eq_fintype_card, ← Fintype.card_of_bijective ⟨h₁, hs⟩, NumberField.Embeddings.card]
  · obtain ⟨τ, rfl⟩ := hs s
    exact ⟨τ, fun a => rfl⟩

theorem tauIn_conj {l : Level H} (c : Coeff l) (τ : E →+* ℂ) (a : 𝓞 E) :
    tauIn c (ComplexEmbedding.conjugate τ) a = tauIn c τ (H.bar a) := by
  apply Subtype.ext
  change (ComplexEmbedding.conjugate τ) (a : E) = τ ((H.bar a : 𝓞 E) : E)
  rw [H.bar_eq, ComplexEmbedding.conjugate_coe_eq, IsCMField.complexEmbedding_complexConj]

theorem rt_cases (τ : E →+* ℂ) : τ (H.rt : E) = H.rt0 ∨ (ComplexEmbedding.conjugate τ) (H.rt : E) = H.rt0 := by
  have h1 : (τ (H.rt : E)) ^ 2 = H.rt0 ^ 2 := by
    rw [H.sqrt_neg_disc_sq, ← map_pow]
    have : ((H.rt : E)) ^ 2 = -(H.d : E) := by
      have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
      simpa using this
    rw [this]
    simp
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have hc : (starRingEnd ℂ) H.rt0 = -H.rt0 := by
    have h2 := H.sqrt_neg_disc_sq
    apply Complex.ext
    · have hre : H.rt0.re = 0 := by
        by_contra hx
        have e1 := congrArg Complex.re h2
        have e2 := congrArg Complex.im h2
        simp [pow_two] at e1 e2
        have hi : H.rt0.im = 0 := by
          have : 2 * H.rt0.re * H.rt0.im = 0 := by linarith
          rcases mul_eq_zero.1 this with h | h
          · exact absurd (by linarith) hx
          · exact h
        rw [hi] at e1
        nlinarith [mul_self_nonneg H.rt0.re]
      simp [hre]
    · simp
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
  · exact Or.inl h
  · right
    rw [ComplexEmbedding.conjugate_coe_eq, h, map_neg, hc, neg_neg]

section Transport

variable {Ω : Type} [Field Ω] {W V : Type} [AddCommGroup W] [Module Ω W] [AddCommGroup V] [Module Ω V]

theorem finrank_eig (e : W ≃ₗ[Ω] V) (ρ' : 𝓞 E →+* Module.End Ω W) (ρ : 𝓞 E →+* Module.End Ω V)
    (h : ∀ a v, e (ρ' a v) = ρ a (e v)) (s : E →+* Ω) (χ : 𝓞 E →+* Ω) (hχ : ∀ a : 𝓞 E, χ a = s (a : E)) :
    Module.finrank Ω (HT.eigSp ρ' s) = Module.finrank Ω (eigSp ρ χ) := by
  have hm : eigSp ρ χ = (HT.eigSp ρ' s).map (e : W →ₗ[Ω] V) := by
    ext y
    simp only [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, sub_eq_zero, Submodule.mem_map, HT.LatBasic.mem_eigSp]
    constructor
    · intro hy
      refine ⟨e.symm y, fun a => e.injective ?_, by simp⟩
      rw [h, map_smul, e.apply_symm_apply, hy, hχ]
    · rintro ⟨x, hx, rfl⟩ a
      change ρ a (e x) = χ a • e x
      rw [← h, hx, map_smul, hχ]
  rw [hm]
  exact (LinearEquiv.finrank_eq (e.submoduleMap _))

end Transport

section LatMap

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {W V : Type} [AddCommGroup W] [Module Ω W] [AddCommGroup V] [Module Ω V]

theorem lat_map (M : LieModel G ξ W) (M' : LieModel G ξ V) (e : W ≃ₗ[Ω] V) (h : ∀ w, M'.pt (e w) = M.pt w) :
    M.lat.map e.toLinearMap = M'.lat := by
  funext p
  change Submodule.map _ (Submodule.span _ _) = Submodule.span _ _
  rw [Submodule.map_span]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨v, hv⟩, rfl⟩
    refine ⟨v, hv.1, ?_⟩
    change (M'.pt (e x)).left = _
    rw [h]
    exact hv.2
  · rintro ⟨v, hv⟩
    refine ⟨e.symm y, ⟨v, hv.1, ?_⟩, by simp⟩
    rw [← h, e.apply_symm_apply]
    exact hv.2

end LatMap

section Model

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O]
  [IsDedekindDomain O] [Algebra O c.F] [IsFractionRing O c.F]

theorem generic_mem_abLocus (Y : Model Xo c (algebraMap O c.F)) (z : Y.X) (hz : ∀ z' : Y.X, z' ⤳ z → z' = z) :
    z ∈ abLocus Y.t.G := by
  have h0 : IsDomain (Y.X.presheaf.stalk z) := (Y.normal z).1
  have hfl : (Scheme.stalkClosedPointTo (Y.X.fromSpecStalk z)).hom.Flat := by
    rw [Scheme.stalkClosedPointTo_fromSpecStalk]
    exact RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _)
  obtain ⟨y, hy⟩ := @GlobalTheory.TorRef.DomFine.exists_generic_point O c.F _ _ _ _ _ Y.X (Xo.XF c) Y.s Y.jQ Y.flat Y.proj
    Y.jQ_open Y.jQ_dense (Y.X.presheaf.stalk z) _ h0 _ (Y.X.fromSpecStalk z) hfl
  obtain ⟨pt⟩ : Nonempty (Sp (FractionRing (Y.X.presheaf.stalk z))) := inferInstance
  have h1 : (y ≫ Y.jQ ≫ pullback.fst _ _) pt ⤳ z := by
    have : (y ≫ Y.jQ ≫ pullback.fst _ _) pt ∈ Set.range (Y.X.fromSpecStalk z) := by
      rw [hy]
      exact ⟨_, by rw [Scheme.Hom.comp_apply]⟩
    rw [Scheme.range_fromSpecStalk] at this
    exact this
  have h2 := hz _ h1
  have h3 : Y.jQ (y pt) ∈ pullback.fst Y.s (spMap (algebraMap O c.F)) ⁻¹' abLocus Y.t.G := by
    rw [Y.ab_gen]
    exact ⟨_, rfl⟩
  rw [← h2]
  simpa [Scheme.Hom.comp_apply] using h3

end Model

end GlobalTheory.CompanionTheory.Ar.Flat.CptHodge

namespace GlobalTheory.CompanionTheory.Ar.Flat


open CptHodge in
theorem hodgeLat_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (ϖ : O) (p : ℕ), Irreducible ϖ → p.Prime → ϖ ∣ (p : O) → Function.Injective β → (∀ x : c.F, x ∈ β.range ∨ x⁻¹ ∈ β.range) → Y.SplitFibres → Y.N3 → ∃ 𝓗 : HodgeLat Z.M.lat Z.ρ H.bar (D.p + D.q), ∀ σ : E →+* Z.Ω, 𝓗.DegZero σ (Z.inc (β ϖ)) := by
  intro E _ _ _ H D l Xo c O _ _ _ β Y U Z τ ϖ p hϖ hp hdvd hβ hval hsplit hN3
  letI : StarRing (𝓞 E) := H.starRing
  have hstar : ∀ a : 𝓞 E, star a = H.bar a := fun _ => rfl
  have hfrac : ∀ x : c.F, ∃ a b : O, b ≠ 0 ∧ x * β b = β a := by
    intro x
    rcases hval x with ⟨a, rfl⟩ | ⟨b, hb⟩
    · exact ⟨a, 1, one_ne_zero, by simp⟩
    · by_cases hx : x = 0
      · exact ⟨0, 1, one_ne_zero, by simp [hx]⟩
      · refine ⟨1, b, ?_, ?_⟩
        · rintro rfl
          rw [map_zero] at hb
          exact inv_ne_zero hx hb.symm
        · rw [hb, mul_inv_cancel₀ hx, map_one]
  letI algF : Algebra O c.F := β.toAlgebra
  haveI : FaithfulSMul O c.F := (faithfulSMul_iff_algebraMap_injective O c.F).2 hβ
  haveI : IsFractionRing O c.F := IsFractionRing.of_field O c.F fun z => by
    obtain ⟨a, b, hb, h⟩ := hfrac z
    refine ⟨a, b, ?_⟩
    have hb' : β b ≠ 0 := fun h0 => hb (hβ (by rw [h0, map_zero]))
    change z = β a / β b
    rw [← h, mul_div_cancel_right₀ _ hb']
  obtain ⟨hLN, -, -, -, -, hdom, -⟩ := GlobalTheory.genericPart_dense_proOpen O c.F Y.X (Xo.XF c) Y.s Y.jQ Y.flat Y.proj
    Y.jQ_open Y.jQ_dense
  have hdense : Dense (Set.range Y.j) := hdom.denseRange
  have hFib := GlobalTheory.T.model_fibres_power_free E H D l Xo c O β Y hdense hsplit hN3
  haveI : ∀ x : Y.X, _root_.IsReduced (Y.X.presheaf.stalk x) := fun x => by
    have := (Y.normal x).1
    infer_instance
  have hred : AlgebraicGeometry.IsReduced Y.X := isReduced_of_isReduced_stalk Y.X
  have hPow : PowFns Y.t := GlobalTheory.T.powFns_of_abelian_generic E H Y.X Y.t hred hLN (fun z hz => generic_mem_abLocus (O := O) Y z hz)
  haveI : CharZero Z.Ω := charZero_of_injective_ringHom Z.inc.injective
  obtain ⟨hcard, hfac⟩ := emb_factor (E := E) c Z.inc
  have facts := fun τ' h => GlobalTheory.T.proper_normal_compactification E H D l Xo c O β Y U Z τ' hβ hfrac h
  have hτ₀ : ∃ τ₀ : E →+* ℂ, τ₀ (H.rt : E) = H.rt0 := (rt_cases τ).elim (fun h => ⟨τ, h⟩) fun h => ⟨_, h⟩
  obtain ⟨τ₀, hτ₀⟩ := hτ₀
  obtain ⟨hprop, -, hover, -, hfd, -, -⟩ := facts τ₀ hτ₀
  haveI : IsProper Y.s := hprop
  obtain ⟨d, M, ⟨S⟩⟩ := GlobalTheory.T.exists_germ_system E H hstar Y.X Y.t Z.Ω (Z.ξ₀ ≫ Y.j) hPow Z.gen
  obtain ⟨e, he, -⟩ := GlobalTheory.T.lie_model_existsUnique_equiv Y.X Y.t.G Z.Ω (Z.ξ₀ ≫ Y.j) (Fin d → Z.Ω) Z.V M Z.M
  let ρ' : 𝓞 E →+* Module.End Z.Ω (Fin d → Z.Ω) := (e.symm.conjRingEquiv : _ ≃+* _).toRingHom.comp Z.ρ
  have hρ' : ∀ a v, e (ρ' a v) = Z.ρ a (e v) := fun a v => by
    simp [ρ', LinearEquiv.conjRingEquiv, LinearEquiv.conj_apply]
  have hact : M.IsActOf Y.t.act.act ρ' := fun a v => by
    rw [← he, hρ', Z.act a (e v), he]
  have hrho : ∀ a v, ρ' a v = (rho S.g₀.B a).mulVec v := fun a v => M.inj (by rw [S.act₀, hact a v])
  have hsum : ∀ s s' : E →+* Z.Ω, (∀ a : 𝓞 E, s' (a : E) = s ((star a : 𝓞 E) : E)) →
      Module.finrank Z.Ω (HT.eigSp ρ' s) + Module.finrank Z.Ω (HT.eigSp ρ' s') = D.p + D.q := by
    intro s s' hss
    obtain ⟨τ', hτ'⟩ := hfac s
    have h1 := finrank_eig e ρ' Z.ρ hρ' s (Z.inc.comp (tauIn c τ')) fun a => (hτ' a).symm
    have h2 := finrank_eig e ρ' Z.ρ hρ' s' (Z.inc.comp (tauIn c (ComplexEmbedding.conjugate τ'))) fun a => by
      rw [hss, hτ', hstar, RingHom.comp_apply, tauIn_conj]
    rw [h1, h2]
    rcases rt_cases (H := H) τ' with h | h
    · obtain ⟨-, -, -, -, -, e1, e2⟩ := facts τ' h
      rw [e1, e2]
    · obtain ⟨-, -, -, -, -, e1, e2⟩ := facts _ h
      have hcc : ComplexEmbedding.conjugate (ComplexEmbedding.conjugate τ') = τ' := by
        ext x
        simp [ComplexEmbedding.conjugate_coe_eq]
      rw [hcc] at e2
      rw [e1, e2, add_comm]
  have hC : HChar S.g₀.B (D.p + D.q) := GlobalTheory.T.hermitian_signature_character E Z.Ω d (D.p + D.q) S.g₀.B ρ' hrho hcard hsum
  have hfree := GlobalTheory.T.germ_system_height_free E H hstar Y.X Y.t Z.Ω (Z.ξ₀ ≫ Y.j) d (D.p + D.q) M S hPow Z.gen hC
    (fun q p' hp' h => hFib p' hp' q.1 h)
  obtain ⟨𝓗, hG⟩ := GlobalTheory.T.exists_hodge_lattice_germ_system E H hstar Y.X Y.t Z.Ω (Z.ξ₀ ≫ Y.j) d (D.p + D.q) M S ρ' Z.gen hact hfree
  letI algΩ : Algebra O Z.Ω := (Z.inc.comp β).toAlgebra
  have hint : ∀ (s' : E →+* Z.Ω) (a : 𝓞 E), s' (a : E) ∈ (algebraMap O Z.Ω).range := by
    intro s' a
    obtain ⟨τ', hτ'⟩ := hfac s'
    have h1 : IsIntegral ℤ (tauIn c τ' a) :=
      (RingOfIntegers.isIntegral a).map (tauIn c τ').toIntAlgHom
    have h2 : IsIntegral O (tauIn c τ' a) := h1.tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
    refine ⟨y, ?_⟩
    rw [hτ', ← hy]
    rfl
  have hdeg : ∀ σ : E →+* Z.Ω, 𝓗.DegZero σ (Z.inc (β ϖ)) := fun σ =>
    GlobalTheory.T.hodge_lattice_dvr_degree E H hstar Y.X Y.t Z.Ω (Z.ξ₀ ≫ Y.j) d (D.p + D.q) M S ρ' 𝓗 O Y.s ϖ p σ hϖ hp hdvd hover Z.gen
      hPow hG (fun q h => hFib p hp q.1 h) hcard hint
  have htr := GlobalTheory.T.hodge_lattice_transport_equiv Y.X Z.Ω (Z.ξ₀ ≫ Y.j) E (Fin d → Z.Ω) Z.V e M.lat ρ' Z.ρ H.bar (D.p + D.q) 𝓗 hρ'
  rw [lat_map M Z.M e he] at htr
  obtain ⟨𝓗', h'⟩ := htr
  exact ⟨𝓗', fun σ => h' σ _ (hdeg σ)⟩

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLinePAdicBoundStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigen_line_p_adic_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (ϖ : O) (p : ℕ), Irreducible ϖ → p.Prime → ϖ ∣ (p : O) → Function.Injective β → (∀ x : c.F, x ∈ β.range ∨ x⁻¹ ∈ β.range) → Y.SplitFibres → Y.N3 → ∃ 𝓗 : HodgeLat Z.M.lat Z.ρ H.bar (D.p + D.q), ∀ σ : E →+* Z.Ω, 𝓗.DegZero σ (Z.inc (β ϖ)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.hodgeLat_model | exact GlobalTheory.CompanionTheory.Ar.Flat.hodgeLat_model | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.hodgeLat_model <;> assumption)
end
