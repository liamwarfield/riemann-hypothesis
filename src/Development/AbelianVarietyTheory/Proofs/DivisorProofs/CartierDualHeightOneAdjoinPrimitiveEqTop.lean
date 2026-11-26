module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderedCechFiniteAffineCoverModelsStructureSheaf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowSmulEqOfLogDerivationExtendEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueStalkHomPadicAlgClosureValuation
public import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExpandsAtSectionUniformised
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGenLab

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDualHeightOneAdjoinPrimitiveEqTop
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDualHeightOneAdjoinPrimitiveEqTop
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.HeightOneDual

variable {K H : Type} [Field K] [CommRing H] [HopfAlgebra K H] [IsCocomm K H] [Module.Finite K H]

theorem cobOne_toConv_eq_zero {δ : H →ₗ[K] K} (hδ : ReciprocityTheory.PGsh.IsPtDer δ) :
    cobOne K (CartierDual K H) (WithConv.toConv δ) = 0 := by
  rw [cobOne_apply, sub_sub, sub_eq_zero, CartierDual.comul_eq_iff]
  intro a b
  rw [map_add (f := _), LinearMap.add_apply, CartierDual.pair_tmul_tmul, CartierDual.pair_tmul_tmul,
    CartierDual.one_apply, CartierDual.one_apply]
  change _ = δ (a * b)
  rw [hδ a b]
  change δ a * counit b + counit a * δ b = _
  ring

theorem apply_convD (φ : CartierDual K H) (δ : H →ₗ[K] K) (y : H) :
    φ (ReciprocityTheory.PGsh.convD δ y) = (φ * WithConv.toConv δ) y := by
  rw [CartierDual.mul_apply, CartierDual.pair_tmul]
  simp only [ReciprocityTheory.PGsh.convD, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  generalize comul (R := K) y = t
  induction t with
  | add u v hu hv => simp only [map_add (f := _), hu, hv]
  | tmul a b => simp [mul_comm]

theorem adjoin_primitive_eq_top : ∀ (p : ℕ) [Fact p.Prime] (K H : Type) [Field K] [CharP K p]
    [CommRing H] [HopfAlgebra K H] [IsCocomm K H] [Module.Finite K H],
    (∀ a ∈ augIdeal K H, a ^ p = 0) →
    Algebra.adjoin K {φ : CartierDual K H | cobOne K (CartierDual K H) φ = 0} = ⊤ := by
  intro p hp K H _ _ _ _ _ _ hpow
  classical
  set ε := counitAlgHom K H with hεdef
  set S := Algebra.adjoin K {φ : CartierDual K H | cobOne K (CartierDual K H) φ = 0} with hSdef
  haveI : Module.Finite K (AugCot ε) := Module.Finite.of_surjective _ (AugCot.d_surjective ε)
  let b := Module.finBasis K (AugCot ε)
  choose x hx using fun i => (RingHom.ker ε).toCotangent_surjective (b i)
  let y : Fin (Module.finrank K (AugCot ε)) → H := fun i => (x i : H)
  have hy : ∀ i, y i ∈ RingHom.ker ε := fun i => (x i).2
  have hsum : ∀ l : Fin (Module.finrank K (AugCot ε)) → K,
      AugCot.d ε (∑ i, l i • y i) = ∑ i, l i • b i := by
    intro l
    set_option synthInstance.maxHeartbeats 100000 in
      simp [y, map_sum, hx]
  have hmem : ∀ l : Fin (Module.finrank K (AugCot ε)) → K, (∑ i, l i • y i) ∈ RingHom.ker ε := by
    intro l
    refine Ideal.sum_mem _ fun i _ => ?_
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ (hy i)
  have hspan : ∀ z ∈ RingHom.ker ε, ∃ l : Fin (Module.finrank K (AugCot ε)) → K,
      z - ∑ i, l i • y i ∈ RingHom.ker ε ^ 2 := by
    intro z hz
    refine ⟨b.repr (AugCot.d ε z), ?_⟩
    have h1 : AugCot.d ε (z - ∑ i, b.repr (AugCot.d ε z) i • y i) = 0 := by
      rw [map_sub, hsum, b.sum_repr, sub_self]
    rwa [AugCot.d_of_mem _ (sub_mem hz (hmem _)), Ideal.toCotangent_eq_zero] at h1
  have hind : ∀ l : Fin (Module.finrank K (AugCot ε)) → K,
      ∑ i, l i • y i ∈ RingHom.ker ε ^ 2 → l = 0 := by
    intro l hl
    have h1 : AugCot.d ε (∑ i, l i • y i) = 0 := by
      rw [AugCot.d_of_mem _ (hmem _), Ideal.toCotangent_eq_zero]
      exact hl
    rw [hsum] at h1
    funext i
    exact Fintype.linearIndependent_iff.1 b.linearIndependent l h1 i
  have : IsNoetherianRing H := isNoetherian_of_tower K inferInstance
  have hnil : IsNilpotent (RingHom.ker ε) := by
    rw [Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)]
    intro f hf
    exact ⟨p, hpow f hf⟩
  have hsurj := GlobalTheory.HeightOneHopf.aeval_surjective_of_span_cotangent ε hnil y hy hspan
  obtain ⟨δ, hδ, hδx⟩ := GlobalTheory.HeightOneHopf.exists_isPtDer_dual y hy hind

  let Z : Set H := {h | ∀ φ ∈ S, φ h = 0}
  have hZε : ∀ h ∈ Z, ε h = 0 := fun h hh => by
    have h1 := hh 1 S.one_mem
    rwa [CartierDual.one_apply] at h1
  have hZD : ∀ i, ∀ h ∈ Z, ReciprocityTheory.PGsh.convD (δ i) h ∈ Z := fun i h hh φ hφ => by
    rw [apply_convD]
    exact hh _ (S.mul_mem hφ (Algebra.subset_adjoin (cobOne_toConv_eq_zero (hδ i))))
  have hZ0 : ∀ h ∈ Z, h = 0 := by
    intro h hh
    obtain ⟨P, rfl⟩ := hsurj h
    have hc := ReciprocityTheory.PGsh.coeff_eq_zero_of_stable ε y hy (fun i => ReciprocityTheory.PGsh.convD (δ i))
      (fun i => ReciprocityTheory.PGsh.convD_mul _ (hδ i)) (fun i j =>
        (ReciprocityTheory.PGsh.counit_convD (δ i) (y j)).trans (hδx i j)) hsurj
      (CharP.cast_eq_zero K p) (fun n h0 hn => by
        rw [isUnit_iff_ne_zero, Ne, CharP.cast_eq_zero_iff K p]
        exact Nat.not_dvd_of_pos_of_lt h0 hn) Z hZε hZD P hh
    exact ReciprocityTheory.PGsh.aeval_eq_zero_of_mem_span y (fun j => hpow _ (hy j))
      (ReciprocityTheory.PGsh.mem_span_pow_of_coeff hc)

  let W : Submodule K (Module.Dual K H) :=
    (Subalgebra.toSubmodule S).map (CartierDual.toDual K H).toLinearMap
  have hW : W.dualCoannihilator = ⊥ := by
    refine eq_bot_iff.2 fun h hh => ?_
    rw [Submodule.mem_dualCoannihilator] at hh
    rw [Submodule.mem_bot]
    exact hZ0 h fun φ hφ => hh _ ⟨φ, hφ, rfl⟩
  have hWtop : W = ⊤ := by
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := W), hW, Submodule.dualAnnihilator_bot]
  rw [← Algebra.toSubmodule_eq_top, eq_top_iff]
  intro φ _
  have h1 : CartierDual.toDual K H φ ∈ W := hWtop ▸ Submodule.mem_top
  obtain ⟨ψ, hψ, e⟩ := h1
  rwa [(CartierDual.toDual K H).injective e] at hψ

end GlobalTheory.HeightOneDual
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDualHeightOneAdjoinPrimitiveEqTopStatement
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cartierDual_height_one_adjoin_primitive_eq_top : ∀ (p : ℕ) [Fact p.Prime] (K H : Type) [Field K] [CharP K p] [CommRing H] [HopfAlgebra K H] [IsCocomm K H] [Module.Finite K H], (∀ a ∈ augIdeal K H, a ^ p = 0) → Algebra.adjoin K {φ : CartierDual K H | cobOne K (CartierDual K H) φ = 0} = ⊤ := by
  first | exact @GlobalTheory.HeightOneDual.adjoin_primitive_eq_top | exact GlobalTheory.HeightOneDual.adjoin_primitive_eq_top | (intros; apply GlobalTheory.HeightOneDual.adjoin_primitive_eq_top <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureCohomologyFlatBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureCohomologyFlatBaseChange
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem flat_cohomology_baseChange {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] [Module.Flat R R']
    {A B C H H' : Type} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    [AddCommGroup H] [Module R H] [AddCommGroup H'] [Module R' H']
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) (hfg : ∀ a, g (f a) = 0)
    (θ : LinearMap.ker (g.baseChange R) →ₗ[R] H) (θ' : LinearMap.ker (g.baseChange R') →ₗ[R'] H')
    (hs : Function.Surjective θ) (hk : ∀ z, θ z = 0 ↔ z.1 ∈ LinearMap.range (f.baseChange R))
    (hs' : Function.Surjective θ') (hk' : ∀ z, θ' z = 0 ↔ z.1 ∈ LinearMap.range (f.baseChange R'))
    (p : H → H')
    (hp : ∀ z z', z'.1 = (Algebra.ofId R R').toLinearMap.rTensor B z.1 → θ' z' = p (θ z)) :
    ∃ e : R' ⊗[R] H ≃ₗ[R'] H', ∀ c, e (1 ⊗ₜ c) = p c := by
  let Z := LinearMap.ker g
  let f' : A →ₗ[R] Z := f.codRestrict Z hfg
  let i : Z →ₗ[R] LinearMap.ker (g.baseChange R) :=
    ((TensorProduct.mk R R B 1) ∘ₗ Z.subtype).codRestrict _ (fun z ↦ by
      have : g z.1 = 0 := z.2
      simp [this])
  have hi : ∀ z : Z, (i z).1 = (1 : R) ⊗ₜ[R] z.1 := fun z ↦ rfl
  have his : Function.Surjective i := by
    rintro ⟨x, hx⟩
    obtain ⟨b, rfl⟩ := (TensorProduct.lid R B).symm.surjective x
    have hb : g b = 0 := by
      have h1 : (1 : R) ⊗ₜ[R] g b = 0 := by simpa using hx
      have := congrArg (TensorProduct.lid R C) h1
      simpa using this
    exact ⟨⟨b, hb⟩, Subtype.ext (by simp [hi])⟩
  let τ : Z →ₗ[R] H := θ ∘ₗ i
  have hτs : Function.Surjective τ := hs.comp his
  have hex : Function.Exact f' τ := by
    intro z
    change θ (i z) = 0 ↔ _
    rw [hk, hi]
    constructor
    · rintro ⟨x, hx⟩
      obtain ⟨a, rfl⟩ := (TensorProduct.lid R A).symm.surjective x
      refine ⟨a, Subtype.ext ?_⟩
      have := congrArg (TensorProduct.lid R B) hx
      change f a = z.1
      simpa using this
    · rintro ⟨a, rfl⟩
      exact ⟨1 ⊗ₜ a, rfl⟩
  have hexZ : Function.Exact (Z.subtype.baseChange R') (g.baseChange R') :=
    Module.Flat.lTensor_exact R' (LinearMap.exact_subtype_ker_map g)
  have hinj : Function.Injective (Z.subtype.baseChange R') :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := R') Z.subtype Z.subtype_injective
  let j : R' ⊗[R] Z →ₗ[R'] LinearMap.ker (g.baseChange R') :=
    (Z.subtype.baseChange R').codRestrict _ (fun x ↦ hexZ.apply_apply_eq_zero x)
  have hjs : Function.Surjective j := by
    rintro ⟨x, hx⟩
    obtain ⟨y, rfl⟩ := (hexZ x).1 hx
    exact ⟨y, rfl⟩
  let a : R' ⊗[R] Z →ₗ[R'] R' ⊗[R] H := τ.baseChange R'
  let b : R' ⊗[R] Z →ₗ[R'] H' := θ' ∘ₗ j
  have has : Function.Surjective a := LinearMap.lTensor_surjective R' hτs
  have hbs : Function.Surjective b := hs'.comp hjs
  have hexa : Function.Exact (f'.baseChange R') a := lTensor_exact R' hex hτs
  have hcomp : ∀ y, Z.subtype.baseChange R' (f'.baseChange R' y) = f.baseChange R' y := by
    intro y
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
    rfl
  have hker : LinearMap.ker a = LinearMap.ker b := by
    ext x
    rw [LinearMap.mem_ker, LinearMap.mem_ker, hexa x]
    change _ ↔ θ' (j x) = 0
    rw [hk']
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, (hcomp y).symm⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, hinj ((hcomp y).trans hy)⟩
  refine ⟨(a.quotKerEquivOfSurjective has).symm ≪≫ₗ Submodule.quotEquivOfEq _ _ hker ≪≫ₗ
    b.quotKerEquivOfSurjective hbs, fun c ↦ ?_⟩
  obtain ⟨z, rfl⟩ := hτs c
  have h1 : (a.quotKerEquivOfSurjective has).symm ((1 : R') ⊗ₜ[R] τ z) =
      Submodule.Quotient.mk ((1 : R') ⊗ₜ[R] z) := by
    rw [LinearEquiv.symm_apply_eq]
    rfl
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, h1]
  change θ' (j (1 ⊗ₜ z)) = p (θ (i z))
  apply hp
  rw [hi, LinearMap.rTensor_tmul]
  change (1 : R') ⊗ₜ[R] z.1 = (algebraMap R R' 1) ⊗ₜ[R] z.1
  rw [map_one]

theorem exists_fin_affine_cover {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) [QuasiCompact s] :
    ∃ (n : ℕ) (D : Fin n → X.Opens), (∀ i, IsAffineOpen (D i)) ∧ ⨆ i, D i = ⊤ := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  obtain ⟨S, hS, e⟩ := (isCompact_iff_finite_and_eq_biUnion_affineOpens (U := (⊤ : X.Opens))).1 isCompact_univ
  have := hS.fintype
  let q := (Fintype.equivFin S).symm
  refine ⟨_, fun i ↦ (q i).1.1, fun i ↦ (q i).1.2, ?_⟩
  rw [e]
  apply le_antisymm
  · exact iSup_le fun i ↦ le_iSup₂_of_le (q i).1 (q i).2 le_rfl
  · refine iSup₂_le fun U hU ↦ ?_
    obtain ⟨i, hi⟩ := q.surjective ⟨U, hU⟩
    exact le_iSup_of_le i (by simp only [hi]; exact le_rfl)

theorem flat_baseChange_HO : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] [Module.Flat R R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (φ : X' ⟶ X) (h : IsPullback φ s' s (spMap (algebraMap R R'))), IsSeparated s → QuasiCompact s → (∃ e : R' ⊗[R] HO1 s ≃ₗ[R'] HO1 s', ∀ c, e (1 ⊗ₜ c) = pullHO1 h.w c) ∧ ∃ e : R' ⊗[R] HO2 s ≃ₗ[R'] HO2 s', ∀ c, e (1 ⊗ₜ c) = pullHO2 h.w c := by
  intro R R' _ _ _ _ X X' s s' φ h hsep hqc
  obtain ⟨n, D, hD, hcov⟩ := exists_fin_affine_cover s
  obtain ⟨M⟩ := GlobalTheory.T.orderedCech_finiteAffineCover_models_structureSheafCohomology R X s (Fin n) D hsep hD hcov
  generalize GlobalTheory.AbLaw.cechLB s (LB.triv X) D = K at M
  have h0 : IsPullback (𝟙 X) s s (spMap (algebraMap R R)) := by
    have e : spMap (algebraMap R R) = 𝟙 _ := spMap_id R
    rw [e]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  have hdd : ∀ i j k a, (K.d j k).hom ((K.d i j).hom a) = 0 := by
    intro i j k a
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, K.d_comp_d]
    rfl
  obtain ⟨a1, a2, a3, a4⟩ := M.exact h0
  obtain ⟨b1, b2, b3, b4⟩ := M.exact h
  obtain ⟨c1, c2⟩ := M.nat h0 h (Algebra.ofId R R') φ h.w (Category.comp_id φ)
  exact ⟨flat_cohomology_baseChange _ _ (hdd 0 1 2) (M.θ1 h0) (M.θ1 h) a1 a2 b1 b2 _ c1,
    flat_cohomology_baseChange _ _ (hdd 1 2 3) (M.θ2 h0) (M.θ2 h) a3 a4 b3 b4 _ c2⟩

end GlobalTheory.AbCoh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureCohomologyFlatBaseChangeStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.structure_cohomology_flat_base_change : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] [Module.Flat R R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (φ : X' ⟶ X) (h : IsPullback φ s' s (spMap (algebraMap R R'))), IsSeparated s → QuasiCompact s → (∃ e : R' ⊗[R] HO1 s ≃ₗ[R'] HO1 s', ∀ c, e (1 ⊗ₜ c) = pullHO1 h.w c) ∧ ∃ e : R' ⊗[R] HO2 s ≃ₗ[R'] HO2 s', ∀ c, e (1 ⊗ₜ c) = pullHO2 h.w c := by
  first | exact @GlobalTheory.AbCoh.flat_baseChange_HO | exact GlobalTheory.AbCoh.flat_baseChange_HO | (intros; apply GlobalTheory.AbCoh.flat_baseChange_HO <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiUnitOnUniv
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PullDegTop

open GlobalTheory.ArcPull GlobalTheory.ArcQ
open GlobalTheory.PsiEvenPull (proj)

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

theorem psi_val_on {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'} (h : IsPullDeg φ D D') {W : (Sp R).Opens}
    (ψW : PsiOn D W) (g : (TK R').left ⟶ (TW W).left) (hg : g ≫ W.ι = jK R' ≫ specOf φ) (x : D'.X) (z : (TK R').left)
    {J J'} (hJ : Good D.P.L z J) (hJ' : Good D'.P.L z J') :
    val (ψW.psi (h.xe x)) g z J = (om h.w z J J' (D'.xK x))⁻¹ * val (D'.psi x) (𝟙 _) z J' := by
  have v := PsiEvenPull.psi_pull h x (𝟙 _) z hJ hJ'
  have ag : val (ψW.psi (h.xe x)) g z J = val (h.psiW.psi (h.xe x)) (𝟙 _ ≫ h.g) z J :=
    ArcSpecialise.psiOn_agree ψW h.psiW _ _ _ (by rw [hg, Category.id_comp, h.g_comm]) hJ
  change _ = (om h.w z J J' (𝟙 _ ≫ D'.xK x))⁻¹ * _ at v
  rw [ag, v, Category.id_comp]

def reopen {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'} (h : IsPullDeg φ D D') {W : (Sp R).Opens}
    (ψW : PsiOn D W) (g : (TK R').left ⟶ (TW W).left) (hg : g ≫ W.ι = jK R' ≫ specOf φ) : IsPullDeg φ D D' :=
  { h with
    W := W
    psiW := ψW
    g := g
    g_comm := hg
    psi_pr := fun x => by
      obtain ⟨b, hb, hc⟩ := h.psi_pr x
      refine ⟨b, hb, corr_of_val D.P.isLB fun y J hJ => (val_corr hJ hc (𝟙 _)).trans ?_⟩
      rw [val_pull hJ, val_pull hJ]
      exact ArcSpecialise.psiOn_agree h.psiW ψW _ _ _ (by
        rw [Category.id_comp, Category.id_comp, hg, h.g_comm]) hJ }

theorem exists_top {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'} (h : IsPullDeg φ D D')
    (hU : ∀ y, PsiUnitOn D y Set.univ) : ∃ h' : IsPullDeg φ D D', h'.W = ⊤ ∧ proj h' = proj h ∧ h'.xe = h.xe := by
  obtain ⟨ψ⟩ := nonempty_psiOn_top D hU
  exact ⟨reopen h ψ ((jK R' ≫ specOf φ) ≫ (Sp R).topIso.inv) (by
    rw [Category.assoc, ← Scheme.topIso_hom, Iso.inv_hom_id, Category.comp_id]), rfl, rfl, rfl⟩

theorem psiUnitOn_univ {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'} (h : IsPullDeg φ D D')
    (hU : ∀ y, PsiUnitOn D y Set.univ) (x : D'.X) : PsiUnitOn D' x Set.univ := by
  obtain ⟨h', hW, -, -⟩ := exists_top h hU
  obtain ⟨ψ, -⟩ := GlobalTheory.PullDegCancelTop.exists_psiOn_pull h'
  have := GlobalTheory.PsiUnitOfPsiOn.psiUnitOn_of_psiOn _ _ _ ψ x
  rw [hW] at this
  exact this

theorem act_iff {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'} (h : IsPullDeg φ D D') (f : D.P.A ⟶ D.P.A)
    (f' : D'.P.A ⟶ D'.P.A) :
    f' ≫ h.e.hom = h.e.hom ≫ (Over.pullback (specOf φ)).map f ↔ f'.left ≫ proj h = proj h ≫ f.left := by
  have a : ((Over.pullback (specOf φ)).map f).left ≫ pullback.fst D.P.A.hom (specOf φ) =
      pullback.fst D.P.A.hom (specOf φ) ≫ f.left := by
    simp [Over.pullback_map_left, pullback.lift_fst]
  constructor
  · intro H
    have := congrArg (fun q => q.left ≫ pullback.fst D.P.A.hom (specOf φ)) H
    simp only [Over.comp_left, Category.assoc] at this
    rw [a] at this
    exact this.trans (Category.assoc _ _ _).symm
  · intro H
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simp only [Over.comp_left, Category.assoc]
      rw [a]
      exact H.trans (Category.assoc _ _ _)
    · exact (Over.w (f' ≫ h.e.hom)).trans (Over.w (h.e.hom ≫ (Over.pullback (specOf φ)).map f)).symm

theorem exists_comp {R R' R'' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']
    [CommRing R''] [IsDomain R''] {i : R →+* R'} {j : R' →+* R''}
    {D : DegPre R} {D' : DegPre R'} {D'' : DegPre R''} (p₀ : IsPullDeg i D D') (q : IsPullDeg j D' D'')
    (hU : ∀ y, PsiUnitOn D y Set.univ) :
    ∃ r : IsPullDeg (j.comp i) D D'', proj r = proj q ≫ proj p₀ ∧ ∀ x, r.xe x = p₀.xe (q.xe x) := by
  obtain ⟨p, hW, e₁, e₂⟩ := exists_top p₀ hU
  rw [← e₁, ← e₂]
  have sc : spMap j ≫ spMap i = spMap (j.comp i) := (spMap_comp i j).symm
  have gp : IsGrpPullback D''.P.A D.P.A (spMap (j.comp i)) (proj q ≫ proj p) :=
    ((pull_grp q).comp (pull_grp p)).congr sc rfl
  have g₁ := (isGen_iff _).1 p.w_gen
  have g₂ := (isGen_iff _).1 q.w_gen
  obtain ⟨w, T⟩ := Geo.Tor.exists_comp D'.P.isLB p.w q.w g₁ g₂ D.P.isLB D''.P.isLB
  have hr := T.pmaps_comp D'.P.isLB (fun _ => q.he) (FieldPull.pmaps_rig p) (FieldPull.pmaps_rig q)
  rw [sc] at hr
  have hc : ∀ x, (D''.c x).left ≫ proj q ≫ proj p = spMap (j.comp i) ≫ (D.c ((q.xe.trans p.xe) x)).left := fun x =>
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ proj p) (q.c_pr x)).trans ((Category.assoc _ _ _).trans
      ((congrArg (_ ≫ ·) (p.c_pr _)).trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) sc)))))
  obtain ⟨ψ, hv⟩ := GlobalTheory.PullDegCancelTop.exists_psiOn_pull p
  obtain ⟨g, hg⟩ : ∃ g : (TK R'').left ⟶ (specOf i ⁻¹ᵁ p.W).toScheme,
      g ≫ (specOf i ⁻¹ᵁ p.W).ι = jK R'' ≫ specOf j :=
    ⟨IsOpenImmersion.lift _ _ (by
      rintro y -
      rw [Scheme.Opens.range_ι, hW]
      trivial), IsOpenImmersion.lift_fac _ _ _⟩
  have hg' : (g ≫ (specOf i ∣_ p.W)) ≫ p.W.ι = jK R'' ≫ specOf (j.comp i) := by
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hg, Category.assoc]
    exact congrArg (jK R'' ≫ ·) sc
  obtain ⟨r, hr₁, hr₂, -⟩ := GlobalTheory.PullDegCompData.exists_isPullDeg_of_valW D D'' p.psiW (g ≫ (specOf i ∣_ p.W)) hg' gp w
    (T.pgen_comp D'.P.isLB g₁ g₂) hr (q.xe.trans p.xe) hc (fun x z J J'' hJ hJ'' => by
      obtain ⟨J', hJ'⟩ := DegPull.exists_good' D'.P.isLB z
      have v₁ := hv (q.xe x) _ g z J J' hJ hJ'
      have v₂ := psi_val_on q ψ g hg x z hJ' hJ''
      have hx : D''.xK x ≫ proj q = g ≫ (specOf i ⁻¹ᵁ p.W).ι ≫ (D'.c (q.xe x)).left := by
        show (jK R'' ≫ (D''.c x).left) ≫ proj q = _
        rw [Category.assoc, q.c_pr, ← Category.assoc g, hg, Category.assoc]
      have t : om w z J J'' (D''.xK x) = om p.w z J J' (D''.xK x ≫ proj q) * om q.w z J' J'' (D''.xK x) :=
        (congrArg (fun u => Geo.Tor.gw w (D''.xK x) z (J u) (J'' (D''.xK x)))
          (Category.assoc (D''.xK x) (proj q) (proj p)).symm).trans
          (T _ _ z _ _ _ (hJ ((D''.xK x ≫ proj q) ≫ proj p)) (hJ' (D''.xK x ≫ proj q)) (hJ'' _))
      rw [v₂, ← hx, ← _root_.mul_assoc, ← mul_inv, ← t] at v₁
      exact v₁)
  exact ⟨r, hr₁, hr₂⟩

theorem exists_cancel {R₀ R₁ R₂ : Type} [CommRing R₀] [IsDomain R₀] [CommRing R₁] [IsDomain R₁]
    [CommRing R₂] [IsDomain R₂] {α : R₀ →+* R₁} {β : R₁ →+* R₂} {θ : R₀ →+* R₂} (hθ : β.comp α = θ)
    {D₀ : DegPre R₀} {D₁ : DegPre R₁} {D : DegPre R₂}
    (h₀ : IsPullDeg α D₀ D₁) (h : IsPullDeg θ D₀ D) (hU : ∀ y, PsiUnitOn D₀ y Set.univ) :
    ∃ h' : IsPullDeg β D₁ D, proj h' ≫ proj h₀ = proj h ∧ ∀ x, h₀.xe (h'.xe x) = h.xe x := by
  subst hθ
  obtain ⟨h₁, hW₁, e₁', e₂'⟩ := exists_top h₀ hU
  rw [← e₁', ← e₂']
  have hW : specOf α ⁻¹ᵁ h₁.W = ⊤ := by rw [hW₁]; rfl
  have p₁ : IsGrpPullback D₁.P.A D₀.P.A (spMap α) (proj h₁) := pull_grp h₁
  have sc : spMap β ≫ spMap α = spMap (β.comp α) := (spMap_comp α β).symm
  have p : IsGrpPullback D.P.A D₀.P.A (spMap β ≫ spMap α) (proj h) := (pull_grp h).congr sc.symm rfl
  obtain ⟨Φ, e₁, e₂⟩ : ∃ Φ : D.P.A.left ⟶ D₁.P.A.left, Φ ≫ proj h₁ = proj h ∧ Φ ≫ D₁.P.A.hom = D.P.A.hom ≫ spMap β :=
    ⟨p₁.1.lift (proj h) (D.P.A.hom ≫ spMap β) (p.1.w.trans (Category.assoc _ _ _).symm), p₁.1.lift_fst _ _ _,
      p₁.1.lift_snd _ _ _⟩
  have gp : IsGrpPullback D.P.A D₁.P.A (spMap β) Φ := IsGrpPullback.cancel p₁ (p.congr rfl e₁.symm) e₂
  obtain ⟨w, hw, hr, T⟩ := FieldPull.exists_cancel_of_eq e₁ D₀.P.isLB D₁.P.isLB D.P.isLB h₁.w h.w
    ((isGen_iff _).1 h₁.w_gen) ((isGen_iff _).1 h.w_gen) sc (cubeMapOf gp).e_comm (FieldPull.pmaps_rig h₁)
    (FieldPull.pmaps_rig h)
  let xe : D.X ≃+ D₁.X := h.xe.trans h₁.xe.symm
  have hxe : ∀ x, h₁.xe (xe x) = h.xe x := fun x => h₁.xe.apply_symm_apply _
  have hc : ∀ x, (D.c x).left ≫ Φ = spMap β ≫ (D₁.c (xe x)).left := fun x => by
    apply p₁.1.hom_ext
    · rw [Category.assoc, e₁, Category.assoc, h₁.c_pr, hxe]
      exact (h.c_pr x).trans ((congrArg (· ≫ _) sc.symm).trans (Category.assoc _ _ _))
    · rw [Category.assoc, e₂, ← Category.assoc, Over.w, Category.assoc, Over.w]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
  obtain ⟨ψW, hv⟩ := GlobalTheory.PullDegCancelTop.exists_psiOn_pull h₁
  obtain ⟨g, hg⟩ : ∃ g : (TK R₂).left ⟶ (specOf α ⁻¹ᵁ h₁.W).toScheme,
      g ≫ (specOf α ⁻¹ᵁ h₁.W).ι = jK R₂ ≫ specOf β :=
    ⟨IsOpenImmersion.lift _ _ (by
      rintro y -
      rw [Scheme.Opens.range_ι, hW]
      trivial), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨hD, k₁, k₂, -⟩ := GlobalTheory.PullDegCompData.exists_isPullDeg_of_valW D₁ D ψW g hg gp w hw hr xe hc
    (fun x z J₁ J hJ₁ hJ => by
    obtain ⟨J₀, hJ₀⟩ := DegPull.exists_good' D₀.P.isLB z
    have v := PsiEvenPull.psi_pull h x (𝟙 _) z hJ₀ hJ
    have v₁ := hv (xe x) _ g z J₀ J₁ hJ₀ hJ₁
    have ag : val (h₁.psiW.psi (h.xe x)) (g ≫ (specOf α ∣_ h₁.W)) z J₀ =
        val (h.psiW.psi (h.xe x)) (𝟙 _ ≫ h.g) z J₀ :=
      ArcSpecialise.psiOn_agree h₁.psiW h.psiW _ _ _ (by
        rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hg, Category.id_comp, h.g_comm, Category.assoc]
        exact congrArg (jK R₂ ≫ ·) sc) hJ₀
    have hx : D.xK x ≫ Φ = g ≫ (specOf α ⁻¹ᵁ h₁.W).ι ≫ (D₁.c (xe x)).left := by
      show (jK R₂ ≫ (D.c x).left) ≫ Φ = _
      rw [Category.assoc, hc, ← Category.assoc g, hg, Category.assoc]
    change _ = (om h.w z J₀ J (𝟙 _ ≫ D.xK x))⁻¹ * _ at v
    rw [hxe, ag, v, Category.id_comp, T _ z J₀ J₁ J hJ₀ hJ₁ hJ, hx, mul_inv, _root_.mul_assoc] at v₁
    exact (mul_left_cancel v₁).symm)
  exact ⟨hD, by rw [k₁, e₁], fun x => by rw [k₂, hxe]⟩

theorem main : (∀ {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'} (_ : IsPullDeg φ D D'), (∀ y, PsiUnitOn D y Set.univ) → ∀ x, PsiUnitOn D' x Set.univ) ∧ (∀ {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R} {D' : DegPre R'} (h : IsPullDeg φ D D') (f : D.P.A ⟶ D.P.A) (f' : D'.P.A ⟶ D'.P.A), f' ≫ h.e.hom = h.e.hom ≫ (Over.pullback (specOf φ)).map f ↔ f'.left ≫ h.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) = (h.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) ≫ f.left) ∧ (∀ {R R' R'' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] [CommRing R''] [IsDomain R''] {i : R →+* R'} {j : R' →+* R''} {D : DegPre R} {D' : DegPre R'} {D'' : DegPre R''} (p : IsPullDeg i D D') (q : IsPullDeg j D' D''), (∀ y, PsiUnitOn D y Set.univ) → ∃ r : IsPullDeg (j.comp i) D D'', r.e.hom.left ≫ pullback.fst D.P.A.hom (specOf (j.comp i)) = (q.e.hom.left ≫ pullback.fst D'.P.A.hom (specOf j)) ≫ p.e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) ∧ ∀ x, r.xe x = p.xe (q.xe x)) ∧ (∀ {R₀ R₁ R₂ : Type} [CommRing R₀] [IsDomain R₀] [CommRing R₁] [IsDomain R₁] [CommRing R₂] [IsDomain R₂] {α : R₀ →+* R₁} {β : R₁ →+* R₂} {θ : R₀ →+* R₂}, β.comp α = θ → ∀ {D₀ : DegPre R₀} {D₁ : DegPre R₁} {D : DegPre R₂} (h₀ : IsPullDeg α D₀ D₁) (h : IsPullDeg θ D₀ D), (∀ y, PsiUnitOn D₀ y Set.univ) → ∃ h' : IsPullDeg β D₁ D, (h'.e.hom.left ≫ pullback.fst D₁.P.A.hom (specOf β)) ≫ h₀.e.hom.left ≫ pullback.fst D₀.P.A.hom (specOf α) = h.e.hom.left ≫ pullback.fst D₀.P.A.hom (specOf θ) ∧ ∀ x, h₀.xe (h'.xe x) = h.xe x) :=
  ⟨fun h hU x => psiUnitOn_univ h hU x, fun h f f' => act_iff h f f', fun p q hU => exists_comp p q hU,
    fun e _ _ _ h₀ h hU => exists_cancel e h₀ h hU⟩

end GlobalTheory.PullDegTop
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSemiAbelianTensorOverScheme
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSemiAbelianTensorOverScheme
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.SemiProd

theorem torus_prod_iso : ∀ (S : Scheme.{0}) (X₁ X₂ : Type) [AddCommGroup X₁] [AddCommGroup X₂], IsIso (lift (GlobalTheory.SplitTorusPow.torusMap S (AddMonoidHom.inl X₁ X₂)) (GlobalTheory.SplitTorusPow.torusMap S (AddMonoidHom.inr X₁ X₂))) := by
  intro S X₁ X₂ _ _
  let comb : ∀ {M : Type} [CommGroup M], (Multiplicative X₁ →* M) → (Multiplicative X₂ →* M) →
      (Multiplicative (X₁ × X₂) →* M) := fun u v =>
    u.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.fst X₁ X₂)) *
      v.comp (AddMonoidHom.toMultiplicative (AddMonoidHom.snd X₁ X₂))
  let l : ∀ {Z : Over S}, (Z ⟶ splitTorus S X₁) → (Z ⟶ splitTorus S X₂) → (Z ⟶ splitTorus S (X₁ × X₂)) :=
    fun {Z} f g => (splitTorusPointsEquiv S (X₁ × X₂) Z).symm
      (comb (splitTorusPointsEquiv S X₁ Z f) (splitTorusPointsEquiv S X₂ Z g))
  have f₁ : ∀ {Z : Over S} (f : Z ⟶ splitTorus S X₁) (g : Z ⟶ splitTorus S X₂),
      l f g ≫ SplitTorusPow.torusMap S (AddMonoidHom.inl X₁ X₂) = f := by
    intro Z f g
    apply (splitTorusPointsEquiv S X₁ Z).injective
    rw [SplitTorusPow.points_comp_torusMap, MulEquiv.apply_symm_apply]
    refine MonoidHom.ext fun x => ?_
    simp [comb]
  have f₂ : ∀ {Z : Over S} (f : Z ⟶ splitTorus S X₁) (g : Z ⟶ splitTorus S X₂),
      l f g ≫ SplitTorusPow.torusMap S (AddMonoidHom.inr X₁ X₂) = g := by
    intro Z f g
    apply (splitTorusPointsEquiv S X₂ Z).injective
    rw [SplitTorusPow.points_comp_torusMap, MulEquiv.apply_symm_apply]
    refine MonoidHom.ext fun x => ?_
    simp [comb]
  have u : ∀ {Z : Over S} (m : Z ⟶ splitTorus S (X₁ × X₂)),
      m = l (m ≫ SplitTorusPow.torusMap S (AddMonoidHom.inl X₁ X₂))
        (m ≫ SplitTorusPow.torusMap S (AddMonoidHom.inr X₁ X₂)) := by
    intro Z m
    apply (splitTorusPointsEquiv S (X₁ × X₂) Z).injective
    rw [MulEquiv.apply_symm_apply, SplitTorusPow.points_comp_torusMap,
      SplitTorusPow.points_comp_torusMap]
    refine MonoidHom.ext fun x => ?_
    have hx : x = Multiplicative.ofAdd (AddMonoidHom.inl X₁ X₂ x.toAdd.1) *
        Multiplicative.ofAdd (AddMonoidHom.inr X₁ X₂ x.toAdd.2) := by
      rw [← ofAdd_add]; simp
    conv_lhs => rw [hx]
    rw [map_mul]
    rfl
  have hl : IsLimit (BinaryFan.mk (SplitTorusPow.torusMap S (AddMonoidHom.inl X₁ X₂))
      (SplitTorusPow.torusMap S (AddMonoidHom.inr X₁ X₂))) :=
    BinaryFan.IsLimit.mk _ (fun f g => l f g) (fun f g => f₁ f g) (fun f g => f₂ f g)
      (fun f g m h₁ h₂ => by rw [u m]; exact congrArg₂ l h₁ h₂)
  have e : lift (SplitTorusPow.torusMap S (AddMonoidHom.inl X₁ X₂))
      (SplitTorusPow.torusMap S (AddMonoidHom.inr X₁ X₂)) =
      (hl.conePointUniqueUpToIso (tensorProductIsBinaryProduct _ _)).hom := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [lift_fst]
      exact (hl.conePointUniqueUpToIso_hom_comp (tensorProductIsBinaryProduct _ _) ⟨.left⟩).symm
    · rw [lift_snd]
      exact (hl.conePointUniqueUpToIso_hom_comp (tensorProductIsBinaryProduct _ _) ⟨.right⟩).symm
  rw [e]
  infer_instance

theorem tensorHom_prop : ∀ (S : Scheme.{0}) (P : MorphismProperty Scheme.{0}) [P.IsMultiplicative] [P.IsStableUnderBaseChange] (A B C D : Over S) (f : A ⟶ B) (g : C ⟶ D), P f.left → P g.left → P (f ⊗ₘ g).left := by
  intro S P _ _ A B C D f g hf hg
  have e : (f ⊗ₘ g).left = pullback.map A.hom C.hom B.hom D.hom f.left g.left (𝟙 S) (by simp) (by simp) := by
    first | rfl | simp
  rw [e]
  exact P.pullbackMap hf hg (Over.w f).symm (Over.w g).symm

theorem kernel_tensor : ∀ (S : Scheme.{0}) (T₁ T₂ G₁ G₂ B₁ B₂ : Over S) [GrpObj B₁] [GrpObj B₂] (i₁ : T₁ ⟶ G₁) (i₂ : T₂ ⟶ G₂) (q₁ : G₁ ⟶ B₁) (q₂ : G₂ ⟶ B₂), IsPullback i₁ (toUnit T₁) q₁ (η : 𝟙_ (Over S) ⟶ B₁) → IsPullback i₂ (toUnit T₂) q₂ (η : 𝟙_ (Over S) ⟶ B₂) → IsPullback (i₁ ⊗ₘ i₂) (toUnit (T₁ ⊗ T₂)) (q₁ ⊗ₘ q₂) (η : 𝟙_ (Over S) ⟶ B₁ ⊗ B₂) := by
  intro S T₁ T₂ G₁ G₂ B₁ B₂ _ _ i₁ i₂ q₁ q₂ h₁ h₂
  have e₁ : (η : 𝟙_ (Over S) ⟶ B₁ ⊗ B₂) ≫ fst _ _ = η := by simp [MonObj.tensorObj.one_def]
  have e₂ : (η : 𝟙_ (Over S) ⟶ B₁ ⊗ B₂) ≫ snd _ _ = η := by simp [MonObj.tensorObj.one_def]
  have c₁ : ∀ {W : Over S} (a : W ⟶ G₁ ⊗ G₂) (b : W ⟶ 𝟙_ (Over S)), a ≫ (q₁ ⊗ₘ q₂) = b ≫ η →
      (a ≫ fst _ _) ≫ q₁ = toUnit W ≫ η := by
    intro W a b h
    have := congrArg (· ≫ fst _ _) h
    simp only [Category.assoc, tensorHom_fst, e₁] at this
    rw [Category.assoc, this, toUnit_unique b (toUnit W)]
  have c₂ : ∀ {W : Over S} (a : W ⟶ G₁ ⊗ G₂) (b : W ⟶ 𝟙_ (Over S)), a ≫ (q₁ ⊗ₘ q₂) = b ≫ η →
      (a ≫ snd _ _) ≫ q₂ = toUnit W ≫ η := by
    intro W a b h
    have := congrArg (· ≫ snd _ _) h
    simp only [Category.assoc, tensorHom_snd, e₂] at this
    rw [Category.assoc, this, toUnit_unique b (toUnit W)]
  have w : (i₁ ⊗ₘ i₂) ≫ (q₁ ⊗ₘ q₂) = toUnit (T₁ ⊗ T₂) ≫ (η : 𝟙_ (Over S) ⟶ B₁ ⊗ B₂) := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, tensorHom_fst, e₁, tensorHom_fst_assoc]
      rw [h₁.w, ← Category.assoc, toUnit_unique (fst T₁ T₂ ≫ toUnit T₁) (toUnit _)]
    · simp only [Category.assoc, tensorHom_snd, e₂, tensorHom_snd_assoc]
      rw [h₂.w, ← Category.assoc, toUnit_unique (snd T₁ T₂ ≫ toUnit T₂) (toUnit _)]
  refine ⟨⟨w⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => lift (h₁.lift (s.fst ≫ fst _ _) (toUnit _) (c₁ _ _ s.condition))
      (h₂.lift (s.fst ≫ snd _ _) (toUnit _) (c₂ _ _ s.condition)))
    (fun s => ?_) (fun s => toUnit_unique _ _) (fun s m hm _ => ?_)⟩⟩
  · apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, tensorHom_fst, lift_fst_assoc, h₁.lift_fst]
    · rw [Category.assoc, tensorHom_snd, lift_snd_assoc, h₂.lift_fst]
  · apply CartesianMonoidalCategory.hom_ext
    · rw [lift_fst]
      apply h₁.hom_ext
      · rw [h₁.lift_fst, Category.assoc, ← tensorHom_fst, ← Category.assoc, hm]
      · exact toUnit_unique _ _
    · rw [lift_snd]
      apply h₂.hom_ext
      · rw [h₂.lift_fst, Category.assoc, ← tensorHom_snd, ← Category.assoc, hm]
      · exact toUnit_unique _ _

variable {S : Scheme.{0}}

theorem isAbelianScheme_tensor {A B : Over S} [GrpObj A] [GrpObj B] (hA : IsAbelianScheme A)
    (hB : IsAbelianScheme B) : IsAbelianScheme (A ⊗ B) := by
  haveI := hA.comm; haveI := hB.comm; haveI := hA.smooth; haveI := hB.smooth
  haveI := hA.proper; haveI := hB.proper; haveI := hA.geomConnected; haveI := hB.geomConnected
  refine ⟨inferInstance, ?_, ?_, ?_⟩
  · show Smooth (pullback.fst A.hom B.hom ≫ A.hom); infer_instance
  · show IsProper (pullback.fst A.hom B.hom ≫ A.hom); infer_instance
  · show GeometricallyConnected (pullback.fst A.hom B.hom ≫ A.hom); exact GeometricallyConnected.comp _ _

theorem torusExtension_of_prod {K : Type} [Field K] {G G₁ G₂ : Over (Spec (.of K))} [GrpObj G] [GrpObj G₁]
    [GrpObj G₂] (a₁ : G ⟶ G₁) (a₂ : G ⟶ G₂) [IsMonHom a₁] [IsMonHom a₂] [IsIso (lift a₁ a₂)]
    (E₁ : TorusExtension G₁) (E₂ : TorusExtension G₂) : Nonempty (TorusExtension G) := by
  letI := E₁.addCommGroup; haveI := E₁.free; haveI := E₁.finite; letI := E₁.grpB
  letI := E₂.addCommGroup; haveI := E₂.free; haveI := E₂.finite; letI := E₂.grpB
  haveI := E₁.q_hom; haveI := E₂.q_hom; haveI := E₁.i_hom; haveI := E₂.i_hom
  haveI := torus_prod_iso (Spec (.of K)) E₁.X E₂.X
  have hmon : ∀ {X X' : Type} [AddCommGroup X] [AddCommGroup X'] (φ : X →+ X'),
      IsMonHom (SplitTorusPow.torusMap (Spec (.of K)) φ) := by
    intro X X' _ _ φ
    constructor
    · have h : (1 : 𝟙_ (Over (Spec (.of K))) ⟶ splitTorus _ X') ≫ SplitTorusPow.torusMap _ φ = 1 := by
        apply (splitTorusPointsEquiv _ X _).injective
        rw [SplitTorusPow.points_comp_torusMap, map_one, map_one, MonoidHom.one_comp]
      simpa [Hom.one_def] using h
    · have h : ∀ {Z : Over (Spec (.of K))} (a b : Z ⟶ splitTorus _ X'),
          (a * b) ≫ SplitTorusPow.torusMap _ φ = (a ≫ SplitTorusPow.torusMap _ φ) * (b ≫ SplitTorusPow.torusMap _ φ) := by
        intro Z a b
        apply (splitTorusPointsEquiv _ X Z).injective
        rw [map_mul, SplitTorusPow.points_comp_torusMap, SplitTorusPow.points_comp_torusMap,
          SplitTorusPow.points_comp_torusMap, map_mul, MonoidHom.mul_comp]
      simpa only [Hom.mul_def, lift_fst_snd, Category.id_comp, lift_fst_comp_snd_comp] using
        h (fst (splitTorus _ X') (splitTorus _ X')) (snd _ _)
  haveI := hmon (AddMonoidHom.inl E₁.X E₂.X)
  haveI := hmon (AddMonoidHom.inr E₁.X E₂.X)
  have key := kernel_tensor _ _ _ _ _ _ _ E₁.i E₂.i E₁.q E₂.q E₁.isKernel E₂.isKernel
  haveI : IsIso (lift a₁ a₂).left := inferInstanceAs (IsIso ((Over.forget _).map (lift a₁ a₂)))
  haveI : IsMonHom (inv (lift a₁ a₂)) := inferInstanceAs (IsMonHom (asIso (lift a₁ a₂)).inv)
  have hP : ∀ (P : MorphismProperty Scheme.{0}) [P.IsMultiplicative] [P.IsStableUnderBaseChange],
      P E₁.q.left → P E₂.q.left → P (lift a₁ a₂ ≫ (E₁.q ⊗ₘ E₂.q)).left := by
    intro P _ _ h₁ h₂
    rw [Over.comp_left]
    exact P.comp_mem _ _ (P.of_isIso _) (tensorHom_prop _ P _ _ _ _ _ _ h₁ h₂)
  refine ⟨{ X := E₁.X × E₂.X
            B := E₁.B ⊗ E₂.B
            isAbelian := isAbelianScheme_tensor E₁.isAbelian E₂.isAbelian
            q := lift a₁ a₂ ≫ (E₁.q ⊗ₘ E₂.q)
            q_hom := inferInstance
            q_flat := hP @Flat E₁.q_flat E₂.q_flat
            q_surjective := hP @Surjective E₁.q_surjective E₂.q_surjective
            q_quasiCompact := hP @QuasiCompact E₁.q_quasiCompact E₂.q_quasiCompact
            i := lift (SplitTorusPow.torusMap _ (AddMonoidHom.inl E₁.X E₂.X))
                (SplitTorusPow.torusMap _ (AddMonoidHom.inr E₁.X E₂.X)) ≫ (E₁.i ⊗ₘ E₂.i) ≫ inv (lift a₁ a₂)
            i_hom := inferInstance
            isKernel := ?_ }⟩
  refine IsPullback.of_iso key (asIso (lift (SplitTorusPow.torusMap _ (AddMonoidHom.inl E₁.X E₂.X))
    (SplitTorusPow.torusMap _ (AddMonoidHom.inr E₁.X E₂.X)))).symm (asIso (lift a₁ a₂)).symm
    (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom, asIso_inv, Category.assoc, IsIso.inv_hom_id]
    simp only [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  · exact toUnit_unique _ _
  · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom, asIso_inv, Category.assoc, IsIso.inv_hom_id_assoc]
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]

theorem isSemiAbelian_tensor : ∀ (S : Scheme.{0}) (G₁ G₂ : Over S) [GrpObj G₁] [GrpObj G₂], IsSemiAbelian G₁ → IsSemiAbelian G₂ → IsSemiAbelian (G₁ ⊗ G₂) := by
  intro S G₁ G₂ _ _ h₁ h₂
  haveI := h₁.comm; haveI := h₂.comm; haveI := h₁.smooth; haveI := h₂.smooth
  haveI := h₁.separated; haveI := h₂.separated; haveI := h₁.quasiCompact; haveI := h₂.quasiCompact
  haveI := h₁.geomConnected; haveI := h₂.geomConnected
  refine ⟨inferInstance, ?_, ?_, ?_, ?_, fun Ω _ _ p => ?_⟩
  · show Smooth (pullback.fst G₁.hom G₂.hom ≫ G₁.hom); infer_instance
  · show IsSeparated (pullback.fst G₁.hom G₂.hom ≫ G₁.hom); infer_instance
  · show QuasiCompact (pullback.fst G₁.hom G₂.hom ≫ G₁.hom); infer_instance
  · show GeometricallyConnected (pullback.fst G₁.hom G₂.hom ≫ G₁.hom); exact GeometricallyConnected.comp _ _
  · obtain ⟨E₁⟩ := h₁.fibres Ω p
    obtain ⟨E₂⟩ := h₂.fibres Ω p
    haveI : IsIso (lift ((Over.pullback p).map (fst G₁ G₂)) ((Over.pullback p).map (snd G₁ G₂))) :=
      isIso_prodComparison_of_preservesLimit_pair (Over.pullback p) G₁ G₂
    exact torusExtension_of_prod ((Over.pullback p).map (fst G₁ G₂)) ((Over.pullback p).map (snd G₁ G₂)) E₁ E₂

end GlobalTheory.SemiProd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSemiAbelianTensorOverSchemeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSemiAbelian_tensor_over_scheme : ∀ (S : Scheme.{0}) (G₁ G₂ : Over S) [GrpObj G₁] [GrpObj G₂], IsSemiAbelian G₁ → IsSemiAbelian G₂ → IsSemiAbelian (G₁ ⊗ G₂) := by
  first | exact @GlobalTheory.SemiProd.isSemiAbelian_tensor | exact GlobalTheory.SemiProd.isSemiAbelian_tensor | (intros; apply GlobalTheory.SemiProd.isSemiAbelian_tensor <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MK
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

namespace GlobalTheory.HomMum

abbrev MK : Type := ULift.{0} (Finset (Fin 2)) ⊕ ULift.{0} (Finset (Fin 2))

variable {S : Scheme.{0}}

def mφ (H₁ H₂ : Over S) [GrpObj H₁] [IsCommMonObj H₁] [GrpObj H₂] [IsCommMonObj H₂] (a b : H₁ ⟶ H₂) :
    MK → ((H₁ ⊗ H₁).left ⟶ H₁.left ⨿ H₂.left) :=
  Sum.elim (fun I => (lift (fst H₁ H₁ ≫ a) (snd H₁ H₁ ≫ b)).left ≫ (psum H₂ (x2 H₂) I.down).left ≫ coprod.inr)
    (fun I => (psum H₁ (x2 H₁) I.down).left ≫ coprod.inl)

def mε : MK → ℤ :=
  Sum.elim (fun I => (-1 : ℤ) ^ (2 - I.down.card)) (fun I => -((-1 : ℤ) ^ (2 - I.down.card)))

def IsNrm {H₁ H₂ : Over S} [GrpObj H₁] [IsCommMonObj H₁] [GrpObj H₂] [IsCommMonObj H₂] {a b : H₁ ⟶ H₂}
    {L₁ : LB H₁.left} {L₂ : LB H₂.left} (u : LB.Gen (LB.LinComb (join L₁ L₂) (mφ H₁ H₂ a b) mε)) : Prop :=
  u.IsGen ∧ ∀ (y : (𝟙_ (Over S)).left) (J), Good (join L₁ L₂) y J →
    val u (lift (1 : 𝟙_ (Over S) ⟶ H₁) (1 : 𝟙_ (Over S) ⟶ H₁)).left y J = 1

end GlobalTheory.HomMum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NzEverywhere
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin

theorem nz_everywhere {S : Scheme.{0}} (G : Over S) [GrpObj G] [Smooth G.hom] (L : LB G.left) {R : Type} [CommRing R]
    [IsLocalRing R] (χ : Sp R ⟶ S) (σ : LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk χ))) (h : NZ G L χ σ) :
    ∀ y : (Over.mk χ).left, ∃ g, (fst (Over.mk χ) G).left g = y ∧ g ∈ nonzeroLocus σ := by
  obtain ⟨x, hc, hx⟩ := h
  haveI : Smooth (fst (Over.mk χ) G).left := by
    change Smooth (pullback.fst χ G.hom)
    infer_instance
  have ho : IsOpen ((fst (Over.mk χ) G).left '' (nonzeroLocus σ : Set _)) :=
    (fst (Over.mk χ) G).left.isOpenMap _ (nonzeroLocus σ).isOpen
  intro y
  obtain ⟨g, hg, e⟩ := (IsLocalRing.specializes_closedPoint (R := R) y).mem_open ho ⟨x, hx, hc⟩
  exact ⟨g, e, hg⟩

theorem nz_pull : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left), L.IsLB → IsSemiAbelian G →
    ∀ (R V : Type) [CommRing R] [IsLocalRing R] [CommRing V] [IsLocalRing V] (χ : Sp R ⟶ S) (σ : SecAt G L χ)
      (φ : R →+* V), NZ G L χ σ → NZ G L (spMap φ ≫ χ) (SecAt.pull G L σ φ) := by
  intro S G _ L hL hG R V _ _ _ _ χ σ φ h
  haveI : Smooth G.hom := hG.smooth
  exact nz_pullS G hL σ (nz_everywhere G L χ σ h) (spMap φ ≫ χ) _

end GlobalTheory.UMin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularFderivConstantVectorUniformised
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularFderivConstantVectorUniformised
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechPer

theorem isReg_fderiv_val : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A →
    ∀ (U : A.left.Opens) (b : Γ(A.left, U)) (w : Fin g → ℂ), IsReg u.ex U fun z => fderiv ℂ (val u.ex U b) z w := by
  intro A _ g L u hA U b w
  have hs := GlobalTheory.AHPos.smoothOfRelativeDimension_of_holUnif hA u
  obtain ⟨v, ⟨hv, hd⟩, -⟩ := (GlobalTheory.TorusTransfer.tangent_bijective u hs).2 w
  obtain ⟨d, -, hdv⟩ := GlobalTheory.KS.exists_locDer_of_isDiff A u w v hv hd
  exact ⟨d U b, fun z hz => (hdv U b z hz).symm⟩

end GlobalTheory.CechPer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularFderivConstantVectorUniformisedStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRegular_fderiv_constant_vector_uniformised : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (U : A.left.Opens) (b : Γ(A.left, U)) (w : Fin g → ℂ), IsReg u.ex U fun z => fderiv ℂ (val u.ex U b) z w := by
  first | exact @GlobalTheory.CechPer.isReg_fderiv_val | exact GlobalTheory.CechPer.isReg_fderiv_val | (intros; apply GlobalTheory.CechPer.isReg_fderiv_val <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageGenericBaseChangeModificatio
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageGenericBaseChangeModificatio
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem isAffineOpen_preimage_genericBaseChange : ∀ (R : Type) [CommRing R] [IsDomain R] (M : Modif R) (G : Over M.S) (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)), IsPullback α t G.hom M.gp → ∀ W : G.left.Opens, IsAffineOpen W → IsAffineOpen (α ⁻¹ᵁ W) := by
  intro R _ _ M G Y α t h W hW
  haveI := M.proper
  haveI : M.S.IsSeparated := by
    constructor
    rw [← terminal.comp_from M.π]
    infer_instance
  haveI : IsAffineHom M.gp := by
    haveI : IsAffineHom (M.gp ≫ terminal.from M.S) := inferInstance
    exact IsAffineHom.of_comp M.gp (terminal.from M.S)
  haveI : IsAffineHom α := MorphismProperty.of_isPullback (P := @IsAffineHom) h.flip inferInstance
  exact hW.preimage α

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageGenericBaseChangeModificatioStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAffineOpen_preimage_genericBaseChange_modification : ∀ (R : Type) [CommRing R] [IsDomain R] (M : Modif R) (G : Over M.S) (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)), IsPullback α t G.hom M.gp → ∀ W : G.left.Opens, IsAffineOpen W → IsAffineOpen (α ⁻¹ᵁ W) := by
  first | exact @GlobalTheory.Mum.isAffineOpen_preimage_genericBaseChange | exact GlobalTheory.Mum.isAffineOpen_preimage_genericBaseChange | (intros; apply GlobalTheory.Mum.isAffineOpen_preimage_genericBaseChange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialSumCompMonHomEqPartialSum
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialSumCompMonHomEqPartialSum
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

namespace GlobalTheory.MumProd.PsumMap

theorem psum_comp_hom : ∀ (S : Scheme.{0}) (B B₁ T : Over S) [GrpObj B] [IsCommMonObj B] [GrpObj B₁] [IsCommMonObj B₁] (n : ℕ) (p : B ⟶ B₁) (x : Fin n → (T ⟶ B)) (x₁ : Fin n → (T ⟶ B₁)), IsMonHom p → (∀ i, x i ≫ p = x₁ i) → ∀ I : Finset (Fin n), psum B x I ≫ p = psum B₁ x₁ I := by
  intro S B B₁ T _ _ _ _ n p x x₁ hp hx I
  unfold psum
  induction ((List.finRange n).filter (· ∈ I)) with
  | nil =>
    show (toUnit T ≫ η[B]) ≫ p = toUnit T ≫ η[B₁]
    rw [Category.assoc, IsMonHom.one_hom]
  | cons a l ih =>
    rw [List.foldr_cons, List.foldr_cons, ← ih]
    show (lift (x a) _ ≫ μ[B]) ≫ p = lift (x₁ a) _ ≫ μ[B₁]
    rw [Category.assoc, IsMonHom.mul_hom, ← Category.assoc, lift_map, hx a]

end GlobalTheory.MumProd.PsumMap
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialSumCompMonHomEqPartialSumStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partialSum_comp_monHom_eq_partialSum : ∀ (S : Scheme.{0}) (B B₁ T : Over S) [GrpObj B] [IsCommMonObj B] [GrpObj B₁] [IsCommMonObj B₁] (n : ℕ) (p : B ⟶ B₁) (x : Fin n → (T ⟶ B)) (x₁ : Fin n → (T ⟶ B₁)), IsMonHom p → (∀ i, x i ≫ p = x₁ i) → ∀ I : Finset (Fin n), psum B x I ≫ p = psum B₁ x₁ I := by
  first | exact @GlobalTheory.MumProd.PsumMap.psum_comp_hom | exact GlobalTheory.MumProd.PsumMap.psum_comp_hom | (intros; apply GlobalTheory.MumProd.PsumMap.psum_comp_hom <;> assumption)
end
end
