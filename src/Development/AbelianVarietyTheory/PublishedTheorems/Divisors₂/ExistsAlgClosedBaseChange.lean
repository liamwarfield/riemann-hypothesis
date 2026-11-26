module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNonzeroLocusFormMap
public import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqGenericPoint
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.QCoh GlobalTheory.CechPic

namespace GlobalTheory.Published

def NefProductNonneg : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)] (d : ℕ),
    IsProjOver (strHom k (X := X)) → topologicalKrullDim X = d →
    ∀ N : Fin d → LB X, (∀ i, IsNef k (N i)) → 0 ≤ interNum k (structureModule X) N

def NefBigIff : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (X : Scheme.{0}) [IsIntegral X] [Algebra k Γ(X, ⊤)]
    (D : ℕ), IsProjOver (strHom k (X := X)) → topologicalKrullDim X = D →
    ∀ N : LB X, IsNef k N → (IsBig k N ↔ 0 < topSelfIntersection k N D)

def NefRiemannRoch : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)] (D : ℕ),
    IsProjOver (strHom k (X := X)) → topologicalKrullDim X = D →
    ∀ L : LB X, IsNef k L →
      (fun m : ℕ => (lbH0 k (lbPow L m) : ℝ) - (topSelfIntersection k L D : ℝ) * (m : ℝ) ^ D / D.factorial)
        =O[atTop] fun m : ℕ => (m : ℝ) ^ ((D : ℤ) - 1)

def NefNumerics : Prop := NefProductNonneg ∧ NefBigIff ∧ NefRiemannRoch

theorem dim_affineOpen {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) :
    topologicalKrullDim (U : Set X) = ringKrullDim Γ(X, U) :=
  (topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding
    hU.range_fromSpec).trans (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := Γ(X, U)))

theorem dim_le_of_isIntegralHom {X Y : Scheme.{0}} (π : Y ⟶ X) [IsIntegralHom π] :
    topologicalKrullDim Y ≤ topologicalKrullDim X := by
  refine topologicalKrullDim_le_of_forall_exists_isOpen fun y => ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hy, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (π y)) isOpen_univ
  refine ⟨(π ⁻¹ᵁ U : Y.Opens), (π ⁻¹ᵁ U).isOpen, hy, ?_⟩
  refine le_trans ?_ (topologicalKrullDim_subspace_le X (U : Set X))
  rw [dim_affineOpen (hU.preimage π), dim_affineOpen hU]
  letI := (π.app U).hom.toAlgebra
  have : Algebra.IsIntegral Γ(X, U) Γ(Y, π ⁻¹ᵁ U) := ⟨IsIntegralHom.isIntegral_app π U hU⟩
  exact Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap Γ(X, U) Γ(Y, π ⁻¹ᵁ U)))
    fun I J h => Ideal.IsIntegral.comap_lt_comap (I := I.asIdeal) (J := J.asIdeal) h

theorem exists_algClosed_baseChange {k : Type} [Field k] {X : Scheme.{0}} [a : Algebra k Γ(X, ⊤)]
    (hp : IsProjOver (strHom k (X := X))) :
    ∃ (X' : Scheme.{0}) (_ : Algebra (AlgebraicClosure k) Γ(X', ⊤)) (π : X' ⟶ X),
      IsProjOver (strHom (AlgebraicClosure k) (X := X')) ∧
      topologicalKrullDim X' = topologicalKrullDim X ∧
      (∀ L : LB X, IsNef k L → IsNef (AlgebraicClosure k) (L.pull π)) ∧
      (∀ L : LB X, L.IsLB → lbH0 (AlgebraicClosure k) (L.pull π) = lbH0 k L) ∧
      ∀ (d : ℕ) (L : Fin d → LB X), (∀ i, (L i).IsLB) →
        interNum (AlgebraicClosure k) (structureModule X') (fun i => (L i).pull π) =
          interNum k (structureModule X) L := by
  obtain ⟨f, rfl⟩ : ∃ f : X ⟶ Sp k, a = algebraΓOfHom f :=
    ⟨strHom k X, Algebra.algebra_ext _ _ (algebraMap_eq_strHom k X)⟩
  letI := algebraΓOfHom f
  rw [strHom_eq (f := f) fun _ => rfl] at hp
  have H := IsPullback.of_hasPullback f (spMap (algebraMap k (AlgebraicClosure k)))
  set π := pullback.fst f (spMap (algebraMap k (AlgebraicClosure k)))
  set f' := pullback.snd f (spMap (algebraMap k (AlgebraicClosure k)))
  letI := algebraΓOfHom f'
  obtain ⟨hpr, A, hA⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB f).1 hp
  have : IsIntegralHom (spMap (algebraMap k (AlgebraicClosure k))) :=
    IsIntegralHom.SpecMap_iff.mpr (algebraMap_isIntegral_iff.mpr inferInstance)
  have : IsIntegralHom π := MorphismProperty.of_isPullback (P := @IsIntegralHom) H.flip this
  have : IsProper (strHom k (X := X)) := by rwa [strHom_eq (f := f) fun _ => rfl]
  refine ⟨_, algebraΓOfHom f', π, ?_, ?_, fun L h => ?_, fun L hL => ?_, fun d L hL => ?_⟩
  · rw [strHom_eq (f := f') fun _ => rfl]
    exact PosBaseChange.isProjOver_of_isPullback H hp
  · exact (dim_le_of_isIntegralHom π).antisymm
      (PosBaseChange.dim_le_of_isClosedMap π.isClosedMap (PosBaseChange.surjective_proj H))
  · exact PosBaseChange.isNef_pull h hA (hA.pull_of_isAffineHom π) π π.isClosedMap
  · exact FieldChangeInter.hdim_pull H hL 0
  · exact FieldChangeInter.interNum_pull H hL

section AnyField

variable {k : Type} [Field k] {X : Scheme.{0}} [Algebra k Γ(X, ⊤)] {D : ℕ}

theorem NefProductNonneg.interNum_nonneg (h : NefProductNonneg) (hp : IsProjOver (strHom k (X := X)))
    (hD : topologicalKrullDim X = D) {N : Fin D → LB X} (hN : ∀ i, IsNef k (N i)) :
    0 ≤ interNum k (structureModule X) N := by
  obtain ⟨X', _, π, hp', hd, hn, -, hi⟩ := exists_algClosed_baseChange hp
  rw [← hi D N fun i => (hN i).isLB]
  exact h _ X' D hp' (hd.trans hD) _ fun i => hn _ (hN i)

theorem NefRiemannRoch.isBigO (h : NefRiemannRoch) (hp : IsProjOver (strHom k (X := X)))
    (hD : topologicalKrullDim X = D) {L : LB X} (hL : IsNef k L) :
    (fun m : ℕ => (lbH0 k (lbPow L m) : ℝ) - (topSelfIntersection k L D : ℝ) * (m : ℝ) ^ D / D.factorial)
      =O[atTop] fun m : ℕ => (m : ℝ) ^ ((D : ℤ) - 1) := by
  obtain ⟨X', _, π, hp', hd, hn, h0, hi⟩ := exists_algClosed_baseChange hp
  have hL' := LB.isLB_pull hL.isLB π
  refine (h _ X' D hp' (hd.trans hD) _ (hn _ hL)).congr_left fun m => ?_
  rw [lineBundleGlobalSectionsDim_congr_picardClass (isLB_lbPow hL' m) (LB.isLB_pull (isLB_lbPow hL.1 m) π)
    (by exact (cls_eq_iff _ _).2 (lbIso_lbPow_pull hL.1 π m)),
    h0 _ (isLB_lbPow hL.1 m), topSelf_def, hi D (fun _ => L) fun _ => hL.1, topSelf_def]

theorem NefRiemannRoch.tendsto (h : NefRiemannRoch) (hp : IsProjOver (strHom k (X := X)))
    (hD : topologicalKrullDim X = D) {L : LB X} (hL : IsNef k L) :
    Tendsto (fun m : ℕ => (lbH0 k (lbPow L m) : ℝ) / (m : ℝ) ^ D) atTop
      (nhds ((topSelfIntersection k L D : ℝ) / D.factorial)) := by
  have ho : (fun m : ℕ => (m : ℝ) ^ ((D : ℤ) - 1)) =o[atTop] fun m : ℕ => (m : ℝ) ^ D := by
    refine (isLittleO_iff_tendsto' ?_).2 ((tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).congr' ?_)
    · filter_upwards [eventually_gt_atTop 0] with m hm h0
      exact absurd h0 (by positivity)
    · filter_upwards [eventually_gt_atTop 0] with m hm
      have : (m : ℝ) ≠ 0 := by positivity
      rw [zpow_sub_one₀ this, zpow_natCast]
      field_simp
  have ht := ((h.isBigO hp hD hL).trans_isLittleO ho).tendsto_div_nhds_zero.add_const
    ((topSelfIntersection k L D : ℝ) / D.factorial)
  rw [zero_add] at ht
  refine ht.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with m hm
  have : (m : ℝ) ≠ 0 := by positivity
  field_simp
  ring

theorem NefRiemannRoch.topSelf_nonneg (h : NefRiemannRoch) (hp : IsProjOver (strHom k (X := X)))
    (hD : topologicalKrullDim X = D) {L : LB X} (hL : IsNef k L) : 0 ≤ topSelfIntersection k L D := by
  have h0 := ge_of_tendsto' (h.tendsto hp hD hL) fun m => (by positivity : (0 : ℝ) ≤ _)
  have hf : (0 : ℝ) < D.factorial := by positivity
  exact_mod_cast (div_nonneg_iff.1 h0).elim And.left fun h' => absurd h'.2 hf.not_ge

theorem NefRiemannRoch.isBig_iff (h : NefRiemannRoch) (hp : IsProjOver (strHom k (X := X)))
    (hD : topologicalKrullDim X = D) {L : LB X} (hL : IsNef k L) :
    IsBig k L ↔ 0 < topSelfIntersection k L D := by
  have ht := h.tendsto hp hD hL
  have hf : (0 : ℝ) < D.factorial := by positivity
  rw [GlobalTheory.isBig_iff (algebraMap_eq_strHom k X) hp hD, ← Int.cast_pos (R := ℝ),
    ← div_pos_iff_of_pos_right hf]
  refine ⟨fun ⟨_, c, hc, hm⟩ => hc.trans_le (ge_of_tendsto_of_frequently ht
    ((hm.and_eventually (eventually_gt_atTop 0)).mono fun m hm => ?_)),
    fun ha => ⟨hL.isLB, _, half_pos ha, Eventually.frequently ?_⟩⟩
  · have := hm.2
    exact (le_div_iff₀ (by positivity)).2 hm.1
  · filter_upwards [ht.eventually_const_le (half_lt_self ha), eventually_gt_atTop 0] with m h₁ h₂
    exact (le_div_iff₀ (by positivity)).1 h₁

end AnyField

theorem NefRiemannRoch.nefBigIff (h : NefRiemannRoch) : NefBigIff :=
  fun _ _ _ _ _ _ _ hp hD _ hL => h.isBig_iff hp hD hL


end GlobalTheory.Published
end
end

section -- merged from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Published

namespace AbVarRed

section Reduction

variable (R K : Type) [CommRing R] [Field K] [Algebra R K]

def IsAbove {L : Type} [Field L] [Algebra K L] (V : Subring L) : Prop :=
  V.comap (algebraMap K L) = (algebraMap R K).range

def HasGoodReduction (A : Over (Sp K)) [GrpObj A] : Prop :=
  ∃ (G : Over (Sp R)) (_ : GrpObj G), IsAbelianScheme G ∧
    ∃ e : (Over.pullback (spMap (algebraMap R K))).obj G ≅ A, IsMonHom e.hom

def HasPotentialGoodReduction (A : Over (Sp K)) [GrpObj A] : Prop :=
  ∃ (L W : Type) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L) (_ : CommRing W) (_ : IsDomain W)
    (_ : IsDiscreteValuationRing W) (_ : Algebra W L) (_ : IsFractionRing W L),
    IsAbove R K (algebraMap W L).range ∧
      HasGoodReduction W L ((Over.pullback (spMap (algebraMap K L))).obj A)

end Reduction

section Galois

variable {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω]

def specAut (σ : Ω ≃ₐ[K] Ω) : ptOver K Ω ⟶ ptOver K Ω :=
  Over.homMk (spMap (σ : Ω →+* Ω)) (by
    change spMap _ ≫ spMap _ = spMap _
    rw [← Spec.map_comp]
    congr 1
    ext x
    simp)

theorem specAut_one : specAut (1 : Ω ≃ₐ[K] Ω) = 𝟙 _ :=
  Over.OverMorphism.ext (Spec.map_id (CommRingCat.of Ω))

theorem specAut_mul (σ τ : Ω ≃ₐ[K] Ω) : specAut (σ * τ) = specAut σ ≫ specAut τ :=
  Over.OverMorphism.ext (by
    change spMap _ = spMap _ ≫ spMap _
    rw [← Spec.map_comp]
    rfl)

variable (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A]

def galPts (σ : Ω ≃ₐ[K] Ω) : (ptOver K Ω ⟶ A) →* (ptOver K Ω ⟶ A) :=
  MonoidHom.mk' (fun x => specAut σ ≫ x) fun x y => MonObj.comp_mul _ x y

omit [IsCommMonObj A] in
theorem galPts_left (σ : Ω ≃ₐ[K] Ω) (x : ptOver K Ω ⟶ A) :
    (galPts A σ x).left = spMap (σ : Ω →+* Ω) ≫ x.left := rfl

def galTate (l : ℕ) [Fact l.Prime] : (Ω ≃ₐ[K] Ω) →* Module.End ℤ_[l] (Tate l (ptOver K Ω ⟶ A)) where
  toFun σ := Tate.map l (galPts A σ)
  map_one' := LinearMap.ext fun t => Tate.ext fun n => by
    change specAut 1 ≫ t.lev n = t.lev n
    rw [specAut_one, Category.id_comp]
  map_mul' σ τ := LinearMap.ext fun t => Tate.ext fun n => by
    change specAut (σ * τ) ≫ t.lev n = specAut σ ≫ specAut τ ≫ t.lev n
    rw [specAut_mul, Category.assoc]

theorem lev_galTate (l : ℕ) [Fact l.Prime] (σ : Ω ≃ₐ[K] Ω) (t : Tate l (ptOver K Ω ⟶ A)) (n : ℕ) :
    (galTate A l σ t).lev n = galPts A σ (t.lev n) := rfl


variable (K) in
def inertia (V : ValuationSubring Ω) : Subgroup (Ω ≃ₐ[K] Ω) :=
  (V.inertiaSubgroup K).map (V.decompositionSubgroup K).subtype

def TorsionUnramified (V : ValuationSubring Ω) (m : ℕ) : Prop :=
  ∀ σ ∈ inertia K V, ∀ x : ptOver K Ω ⟶ A, x ^ m = 1 → galPts A σ x = x

def TateUnramified (V : ValuationSubring Ω) (l : ℕ) [Fact l.Prime] : Prop :=
  ∀ σ ∈ inertia K V, galTate A l σ = 1

end Galois

def HasCMBy {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] (F : Type) [Field F] [NumberField F] : Prop :=
  (∃ d : ℕ, SmoothOfRelativeDimension d A.hom ∧ Module.finrank ℚ F = 2 * d) ∧
    ∃ (O : Type) (_ : CommRing O) (_ : Algebra O F) (_ : IsFractionRing O F), Nonempty (OAct O A)

end AbVarRed

open AbVarRed IsLocalRing

def NeronOggShafarevichSt : Prop :=
  ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)]
    [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    (V : ValuationSubring Ω), IsAbove R K V.toSubring →
    ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
      List.TFAE [HasGoodReduction R K A,
        ∀ m : ℕ, (m : ResidueField R) ≠ 0 → TorsionUnramified A V m,
        {m : ℕ | (m : ResidueField R) ≠ 0 ∧ TorsionUnramified A V m}.Infinite,
        ∃ (l : ℕ) (_ : Fact l.Prime), (l : ResidueField R) ≠ 0 ∧ TateUnramified A V l]

def PotentialGoodReductionSt : Prop :=
  ∀ (R K Ω : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [PerfectField (ResidueField R)]
    [Field K] [Algebra R K] [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
    (V : ValuationSubring Ω), IsAbove R K V.toSubring →
    ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
    ∀ (l : ℕ) [Fact l.Prime], (l : ResidueField R) ≠ 0 →
      (HasPotentialGoodReduction R K A ↔ (galTate A l '' (inertia K V : Set (Ω ≃ₐ[K] Ω))).Finite)

def CMPotentialGoodReductionSt : Prop :=
  ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Finite (ResidueField R)]
    [Field K] [Algebra R K] [IsFractionRing R K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A →
    ∀ (F : Type) [Field F] [NumberField F], HasCMBy A F → HasPotentialGoodReduction R K A

def SerreTateGoodReductionSt : Prop :=
  NeronOggShafarevichSt ∧ PotentialGoodReductionSt ∧ CMPotentialGoodReductionSt

namespace AbVarRed

theorem mem_inertia_iff {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (V : ValuationSubring Ω) (σ : Ω ≃ₐ[K] Ω) :
    σ ∈ inertia K V ↔ σ • V = V ∧ ∀ x ∈ V, V.valuation (σ x - x) < 1 := by
  have key : ∀ τ : V.decompositionSubgroup K, τ ∈ V.inertiaSubgroup K ↔
      ∀ x ∈ V, V.valuation ((τ : Ω ≃ₐ[K] Ω) x - x) < 1 := fun τ => by
    have h : ∀ x : V, τ • residue V x = residue V x ↔ V.valuation ((τ : Ω ≃ₐ[K] Ω) x - x) < 1 := fun x => by
      rw [← ResidueField.residue_smul, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff,
        ValuationSubring.valuation_lt_one_iff]
      rfl
    rw [ValuationSubring.inertiaSubgroup, MonoidHom.mem_ker]
    constructor
    · intro e x hx
      exact (h ⟨x, hx⟩).1 (DFunLike.congr_fun e (residue V ⟨x, hx⟩))
    · intro e
      refine RingEquiv.ext fun y => ?_
      obtain ⟨x, rfl⟩ := residue_surjective y
      exact (h x).2 (e x x.2)
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    exact ⟨τ.2, (key τ).1 hτ⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨σ, h1⟩, (key _).2 h2, rfl⟩

theorem exists_isAbove (R K Ω : Type) [CommRing R] [IsDomain R] [ValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] [Field Ω] [Algebra K Ω] : ∃ V : ValuationSubring Ω, IsAbove R K V.toSubring := by
  obtain ⟨V, -, -, -, h⟩ := exists_valuationSubring_dominating (V := R) (algebraMap K Ω)
  exact ⟨V, Subring.ext h⟩

theorem tateUnramified_of_torsionUnramified {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {A : Over (Sp K)}
    [GrpObj A] [IsCommMonObj A] {V : ValuationSubring Ω} {l : ℕ} [Fact l.Prime]
    (h : ∀ n, TorsionUnramified A V (l ^ n)) : TateUnramified A V l :=
  fun σ hσ => LinearMap.ext fun t => Tate.ext fun n => h n σ hσ _ (t.lev_pow n)

end AbVarRed

section Consequences

variable {R K Ω : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
  [IsFractionRing R K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] {V : ValuationSubring Ω}
  {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A]

theorem NeronOggShafarevichSt.iff_tateUnramified (h : NeronOggShafarevichSt) [PerfectField (ResidueField R)]
    (hV : IsAbove R K V.toSubring) (hA : IsAbelianScheme A) (l : ℕ) [Fact l.Prime]
    (hl : (l : ResidueField R) ≠ 0) : HasGoodReduction R K A ↔ TateUnramified A V l := by
  have t := h R K Ω V hV A hA
  have t01 : HasGoodReduction R K A ↔ ∀ m : ℕ, (m : ResidueField R) ≠ 0 → TorsionUnramified A V m := t.out 1 2
  have t03 : HasGoodReduction R K A ↔
      ∃ (l : ℕ) (_ : Fact l.Prime), (l : ResidueField R) ≠ 0 ∧ TateUnramified A V l := t.out 1 4
  exact ⟨fun hg => tateUnramified_of_torsionUnramified fun n =>
    t01.1 hg (l ^ n) (by rw [Nat.cast_pow]; exact pow_ne_zero _ hl), fun ht => t03.2 ⟨l, _, hl, ht⟩⟩

end Consequences

namespace AbVarRed

open GlobalTheory.WeierstrassCurve

theorem factPrimeFive : Fact (Nat.Prime 5) := ⟨by norm_num⟩

attribute [local instance] factPrimeFive

end AbVarRed

end GlobalTheory.Published
end
end

section -- merged from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EisensteinIsotropicLine
noncomputable section

open NumberField MeasureTheory Matrix Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open Formalism.UG (cT bc)
open GlobalTheory.Doubling (absE)
open scoped TensorProduct NNReal

namespace GlobalTheory.EisLine

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ}

structure IsAdapted (X Y : Matrix (Fin n) (Fin r) E) (L : Submodule (𝓞 E) (Fin n → E))
    (a : GL (Fin n) (AF F ⊗[F] E)) : Prop where
  lat : Submodule.IsFullLattice E L
  dual : ∀ v, IsSelfDualAt σ J L v
  split : ∀ z ∈ L, ∀ i, ((cT (σ : E →+* E) Y * J) *ᵥ z) i • Xᵀ i ∈ L ∧ ((cT (σ : E →+* E) X * J) *ᵥ z) i • Yᵀ i ∈ L
  maj : IsMajorantFrame σ J a
  cartan : ∀ w : InfinitePlace F, ∃ c : Fin r → w.Completion ⊗[F] E,
    cT (sigR _ σ) (bc (compInf F E w) a⁻¹).1 * (bc (compInf F E w) a⁻¹).1 * X.map (inclR (F := F) w.Completion) =
      (JR w.Completion J * Y.map (inclR (F := F) w.Completion) : Matrix (Fin n) (Fin r) (w.Completion ⊗[F] E)) * diagonal c

def IsModerateForm (μ : (GAd σ J → ℂ) →ₗ[ℂ] ℂ) : Prop :=
  ∀ N : ℕ, ∃ (S : List (List (ℝ → GAd σ J))) (C : ℝ), (∀ l ∈ S, ∀ γ ∈ l, IsRealLine σ J γ) ∧
    ∀ f, IsSmoothModerate σ J f →
      (∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) →
        ∃ B : ℝ, ∀ g, ‖l.foldr lineDer f g‖ ≤ B * (height σ J g : ℝ) ^ N) →
      (∀ l ∈ S, ∀ g, ‖l.foldr lineDer f g‖ ≤ (height σ J g : ℝ) ^ N) → ‖μ f‖ ≤ C

end GlobalTheory.EisLine

namespace GlobalTheory.Published


open GlobalTheory.EisLine in
def EisensteinIsotropicLine : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    Algebra.Unramified (𝓞 F) (𝓞 E) →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
      ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsWittFrame σ J X Y →
      ∀ (x y : Matrix (Fin n) (Fin 1) E), x = X.submatrix id (fun _ => 0) → y = Y.submatrix id (fun _ => 0) →
      ∀ (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)), IsAdapted σ J X Y L a →
      ∀ h : GAd σ J → ℝ,
        (∀ g, ∃ p, ∃ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J p).1 * adMat F x = l.1 • adMat F x ∧
          ∃ k ∈ levelAll σ J L a, g = p * k) →
        (∀ p, ∀ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J p).1 * adMat F x = l.1 • adMat F x →
          ∀ k ∈ levelAll σ J L a, h (p * k) = absE F E l) →
      ∃ (Eis : ℂ → GAd σ J → ℂ) (c : ℂ → ℂ),
        (∀ T : Set (ratPts σ J), (∀ γ : ratPts σ J, ∃! t, t ∈ T ∧ ∃ l : (AF F ⊗[F] E)ˣ,
            (matHom _ σ J (γ * t⁻¹ : ratPts σ J).1).1 * adMat F x = l.1 • adMat F x) →
          ∀ s : ℂ, ((n : ℝ) - 1) / 2 < s.re → ∀ g,
            HasSum (fun t : T => (h (t.1.1 * g) : ℂ) ^ (s + ((n : ℂ) - 1) / 2)) (Eis s g)) ∧
        (∀ w ∈ ratPts σ J, (matHom _ σ J w).1 * adMat F y = adMat F x →
          ∀ (μ : Measure (unipRad σ J x)) (𝓕 : Set (unipRad σ J x)), μ.IsHaarMeasure →
            IsFundamentalDomain ((ratPts σ J).subgroupOf (unipRad σ J x)) 𝓕 μ → μ 𝓕 = 1 →
            ∀ s : ℂ, ((n : ℝ) - 1) / 2 < s.re → ∀ g,
              Integrable (fun u : unipRad σ J x => (h (w * u * g) : ℂ) ^ (s + ((n : ℂ) - 1) / 2)) μ ∧
              ∫ u : unipRad σ J x, (h (w * u * g) : ℂ) ^ (s + ((n : ℂ) - 1) / 2) ∂μ =
                c s * (h g : ℂ) ^ (-s + ((n : ℂ) - 1) / 2)) ∧
        MeromorphicOn c Set.univ ∧
        (∀ s₀ : ℂ, ∃ (k : ℕ) (U : Set ℂ) (H : ℂ → GAd σ J → ℂ), U ∈ 𝓝 s₀ ∧
          (∀ s ∈ U, s ≠ s₀ → ∀ g, H s g = (s - s₀) ^ k * Eis s g) ∧ (∀ s ∈ U, IsSmoothModerate σ J (H s)) ∧
          ∀ μ, IsModerateForm σ J μ → DifferentiableOn ℂ (fun s => μ (H s)) U) ∧
        ∀ s₀ : ℂ, ∀ᶠ s in 𝓝[≠] s₀, c s * c (-s) = 1 ∧ ∀ g, Eis s g = c s * Eis (-s) g

end GlobalTheory.Published

end
end

section -- merged from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.TwistTop

namespace GlobalTheory.HermLB

variable {k : Type} [CommRing k] {X Y Z : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {t : Z ⟶ Sp k}

theorem refines_pull_pull (L : HermLB p) (f : Y ⟶ X) (hf : f ≫ p = q) (g : Z ⟶ Y) (hg : g ≫ q = t)
    (h : (g ≫ f) ≫ p = t) :
    Refines ((L.pull f hf).pull g hg) (L.pull (g ≫ f) h) (fun c => c PUnit.unit) 0 := by
  refine ⟨fun c y hy => mem_iInter.2 fun a => mem_iInter.1 (mem_iInter.1 hy PUnit.unit) a, ?_, ?_⟩
  · intro W r z c c' hc hc'
    have h₁ := mem_iInter.1 hc PUnit.unit
    have h₂ := mem_iInter.1 hc' PUnit.unit
    refine (gm_pull_g _ g r z c c' hc hc').trans ((gm_pull_g _ f (r ≫ g) z _ _ h₁ h₂).trans ?_)
    refine Eq.trans ?_ (gm_pull_g _ (g ≫ f) r z (c PUnit.unit) (c' PUnit.unit)
      (mem_iInter.2 fun a => mem_iInter.1 h₁ a) (mem_iInter.2 fun a => mem_iInter.1 h₂ a)).symm
    rw [Category.assoc]
  · intro σ c y hy
    refine (((L.pull f hf).φ σ).pull_φ g hg c y).trans (((L.φ σ).pull_φ f hf _ _).trans ?_)
    refine Eq.trans ?_ (((L.φ σ).pull_φ (g ≫ f) h (c PUnit.unit) y).symm.trans (add_zero _).symm)
    exact congrArg _ (Subtype.ext (Category.assoc _ _ _))

theorem refines_pull_comp (L : HermLB p) (f : Y ⟶ X) (hf : f ≫ p = q) (g : Z ⟶ Y) (hg : g ≫ q = t)
    (h : (g ≫ f) ≫ p = t) :
    Refines (L.pull (g ≫ f) h) ((L.pull f hf).pull g hg) (fun c _ => c) 0 := by
  refine ⟨fun c y hy => mem_iInter.2 fun _ => mem_iInter.2 fun a => mem_iInter.1 hy a, ?_, ?_⟩
  · intro W r z c c' hc hc'
    have h₁ : (r ≫ g) z ∈ (L.B.pull f).U c := mem_iInter.2 fun a => mem_iInter.1 hc a
    have h₂ : (r ≫ g) z ∈ (L.B.pull f).U c' := mem_iInter.2 fun a => mem_iInter.1 hc' a
    have h₃ : r z ∈ ((L.B.pull f).pull g).U fun _ => c := mem_iInter.2 fun _ => h₁
    have h₄ : r z ∈ ((L.B.pull f).pull g).U fun _ => c' := mem_iInter.2 fun _ => h₂
    have e₁ := gm_pull_g (L.B.pull f) g r z (fun _ => c) (fun _ => c') h₃ h₄
    have e₂ := gm_pull_g L.B f (r ≫ g) z c c' h₁ h₂
    have e₃ := gm_pull_g L.B (g ≫ f) r z c c' hc hc'
    rw [← Category.assoc] at e₃
    exact e₃.trans (e₁.trans e₂).symm
  · intro σ c y hy
    refine ((L.φ σ).pull_φ (g ≫ f) h c y).trans (Eq.symm ((add_zero _).trans ?_))
    refine (((L.pull f hf).φ σ).pull_φ g hg (fun _ => c) y).trans (((L.φ σ).pull_φ f hf _ _).trans ?_)
    exact congrArg _ (Subtype.ext (Category.assoc _ _ _))

variable {L : HermLB p} {h : X → ℝ} {D : ℕ}

theorem IsArithHeight.restrict (hX : IsArithVar p D) (H : L.IsArithHeight h) (i : Y ⟶ X) [IsClosedImmersion i]
    (hi : i ≫ p = q) : (L.pull i hi).IsArithHeight fun y => h (i y) := by
  refine ⟨?_, ?_, ?_⟩
  · intro Z j _ _ κ _ _ _ d hd
    exact (H.vertical Z (j ≫ i) κ d hd).trans (congrArg (fun n : ℤ => (n : ℝ) * _)
      (topSelf_congr κ (L.restr (j ≫ i)).isLB ((L.pull i hi).restr j).isLB
        (L.refines_pull_comp i hi j rfl (by rw [Category.assoc, hi])).lbIso d))
  · intro Z j _ _ _ hc hd r hr
    have key (t : Z ⟶ Sp k) (ht : (j ≫ i) ≫ p = t) (r) (hr : IsRatSec (L.pull (j ≫ i) ht).B r) :
        h (i (j (genericPoint Z))) = (L.pull (j ≫ i) ht).curveDeg hr ∧ IsArithVar t 0 := by
      subst ht
      exact ⟨H.point Z (j ≫ i) hc hd r hr, hX.of_isClosedImmersion (j ≫ i) hc hd⟩
    have e : (j ≫ i) ≫ p = j ≫ q := by rw [Category.assoc, hi]
    have h' := L.refines_pull_comp i hi j rfl e
    obtain ⟨h₁, h₂⟩ := key _ e _ (h'.isRatSec hr)
    refine h₁.trans ?_
    rw [HermLB.curveDeg, HermLB.curveDeg, h'.div hr]
    refine congrArg _ (finsum_congr fun σ => finsum_congr fun y => h'.logNorm hr (mem_offSupp.2 ?_))
    rw [under_eq_genericPoint h₂ y]
    exact CartierDiv.genericPoint_notMem_supp _
  · intro Z j _ _ _ hc e he hd m r hr
    have key (t : Z ⟶ Sp k) (ht : (j ≫ i) ≫ p = t) (r) (hr : IsRatSec ((L.pull (j ≫ i) ht).pow m).B r) :
        (L.pull (j ≫ i) ht).ArchIntegrable ((L.pull (j ≫ i) ht).pow m) e hr ∧
        m * h (i (j (genericPoint Z))) =
          ∑ᶠ z, ((((L.pull (j ≫ i) ht).pow m).div hr).mult z : ℝ) * h (i (j z)) -
            (L.pull (j ≫ i) ht).archInt ((L.pull (j ≫ i) ht).pow m) e hr := by
      subst ht
      exact H.recursion Z (j ≫ i) hc e he hd m r hr
    have e' : (j ≫ i) ≫ p = j ≫ q := by rw [Category.assoc, hi]
    let N := L.pull (j ≫ i) e'
    let M := (L.pull i hi).restr j
    have h' : Refines N M (fun c _ => c) 0 := L.refines_pull_comp i hi j rfl e'
    have h'' : Refines (N.pow m) (M.pow m) (fun c a _ => c a) 0 := by
      refine ⟨fun c y hy => mem_iInter.2 fun a => h'.le _ (mem_iInter.1 hy a), ?_, ?_⟩
      · intro W s z c c' hc hc'
        rw [gm_pow N m s z c c' hc hc',
          gm_pow M m s z _ _ (mem_iInter.2 fun a => h'.le _ (mem_iInter.1 hc a))
            (mem_iInter.2 fun a => h'.le _ (mem_iInter.1 hc' a)),
          h'.g W s z _ _ (mem_iInter.1 hc PUnit.unit) (mem_iInter.1 hc' PUnit.unit)]
      · intro σ c y hy
        exact ((N.φ σ).zpow_φ m c y).trans
          ((congrArg _ ((h'.φ σ _ _ (mem_pow_iff.1 hy)).trans (add_zero _))).trans
            (((M.φ σ).zpow_φ m (fun a _ => c a) y).symm.trans (add_zero _).symm))
    obtain ⟨h₁, h₂⟩ := key _ e' _ (h''.isRatSec hr)
    change N.ArchIntegrable (N.pow m) e (h''.isRatSec hr) at h₁
    unfold HermLB.ArchIntegrable Weight.ChernIntegrableOn at h₁
    unfold HermLB.archInt at h₂
    rw [h''.div hr] at h₁ h₂
    simp only [h'.chernPart] at h₁
    refine ⟨fun σ => Weight.ChernIntegrableOn.congr (h₁ σ) (isOpen_offSupp _).measurableSet
      fun y hy => h''.logNorm hr hy, h₂.trans (congrArg _ (finsum_congr fun σ => ?_))⟩
    rw [h'.chernInt]
    exact Weight.chernInt_congr (isOpen_offSupp _).measurableSet fun y hy => h''.logNorm hr hy

theorem IsArithHeight.isSelfInter_restrict (hX : IsArithVar p D) (H : L.IsArithHeight h) [IsIntegral Y] (i : Y ⟶ X)
    [IsClosedImmersion i] (hi : i ≫ p = q) : (L.pull i hi).IsSelfInter (h (i (genericPoint Y))) :=
  ⟨_, H.restrict hX i hi, rfl⟩

end GlobalTheory.HermLB

namespace GlobalTheory.Published

def HeightProjection : Prop :=
  ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D e : ℕ),
    IsArithVar p D → IsArithVar q e → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q),
      topologicalKrullDim (closure ({π (genericPoint Y)} : Set X)) = (e + 1 : ℕ) →
      π.residueDegree (genericPoint Y) ≠ 0 → ∀ (L : HermLB p) (h : X → ℝ), L.IsArithHeight h →
        (L.pull π hπ).IsSelfInter ((π.residueDegree (genericPoint Y) : ℝ) * h (π (genericPoint Y)))

def CycleHeights : Prop := ArExists ∧ ArMix ∧ HeightProjection

theorem residueDegree_of_isClosedImmersion {X Y : Scheme.{0}} (f : X ⟶ Y) [IsClosedImmersion f] (x : X) :
    f.residueDegree x = 1 := by
  let := (f.residueFieldMap x).hom.toAlgebra
  have h : Function.Bijective (algebraMap (Y.residueField (f x)) (X.residueField x)) :=
    ⟨RingHom.injective _, fun a => by
      obtain ⟨b, rfl⟩ := X.residue_surjective x a
      obtain ⟨c, rfl⟩ := f.stalkMap_surjective x b
      exact ⟨Y.residue _ c, congr($(Scheme.residue_residueFieldMap f x).hom c)⟩⟩
  exact (LinearEquiv.ofBijective (Algebra.linearMap _ _) h).finrank_eq.symm.trans (CommSemiring.finrank_self _)

theorem heightProjection_of_arProj (H : ArProj) : HeightProjection := by
  intro k _ X Y _ p q D e hX hY π hπ hd hm L h hh
  obtain ⟨Z, i, _, _, hi⟩ := exists_isClosedImmersion_genericPoint (π (genericPoint Y))
  have hr : range i = closure {π (genericPoint Y)} := by
    have h₁ := (genericPoint_spec Z).image i.continuous
    rw [image_univ, i.isClosedEmbedding.isClosed_range.closure_eq, hi] at h₁
    exact h₁.def.symm
  have : Surjective (Limits.pullback.snd i π) := ⟨by
    rw [← Set.range_eq_univ, Scheme.Pullback.range_snd, hr]
    exact eq_univ_of_forall fun y => ((genericPoint_specializes y).map π.continuous).mem_closure⟩
  have := isIso_of_isClosedImmersion_of_surjective (Limits.pullback.snd i π)
  obtain ⟨g, rfl⟩ : ∃ g : Y ⟶ Z, g ≫ i = π := ⟨inv (Limits.pullback.snd i π) ≫ Limits.pullback.fst i π, by
    rw [Category.assoc, Limits.pullback.condition, IsIso.inv_hom_id_assoc]⟩
  have hg : g (genericPoint Y) = genericPoint Z := i.isClosedEmbedding.injective hi.symm
  have hdeg : (g ≫ i).residueDegree (genericPoint Y) = g.residueDegree (genericPoint Y) := by
    rw [GlobalTheory.CurveDegreesCompare.residueDegree_comp, residueDegree_of_isClosedImmersion i, one_mul]
  have hc : CharZero Γ(Z, ⊤) := have := hY.charZero; g.appTop.hom.charZero
  have hZ : IsArithVar (i ≫ p) e := hX.of_isClosedImmersion i hc
    ((topologicalKrullDim_eq_of_isEmbedding i.isClosedEmbedding.isEmbedding hr).symm.trans hd)
  have hq : g ≫ i ≫ p = q := (Category.assoc _ _ _).symm.trans hπ
  obtain ⟨f, hf, e₁⟩ := (H k Z Y (i ≫ p) q e hZ hY g hq hg (hdeg ▸ hm)).1 _ _ (hh.isSelfInter_restrict hX i rfl)
  refine ⟨f, ?_, by rw [e₁, hdeg, hi]⟩
  let N := (L.pull i rfl).pull g hq
  let M := L.pull (g ≫ i) hπ
  have hRef : Refines N M (fun c => c PUnit.unit) 0 := L.refines_pull_pull i rfl g hq hπ
  have pullRefines (W : Scheme.{0}) (j : W ⟶ Y) :
      Refines (N.restr j) (M.restr j) (fun c a => c a PUnit.unit) 0 := by
    refine ⟨fun c y hy => mem_iInter.2 fun a => hRef.le _ (mem_iInter.1 hy a), ?_, ?_⟩
    · intro V s z c c' hc hc'
      refine (gm_pull_g _ j s z c c' hc hc').trans ((hRef.g V (s ≫ j) z _ _
        (mem_iInter.1 hc PUnit.unit) (mem_iInter.1 hc' PUnit.unit)).trans ?_)
      exact (gm_pull_g M.B j s z (fun a => c a PUnit.unit) (fun a => c' a PUnit.unit)
        (mem_iInter.2 fun a => hRef.le _ (mem_iInter.1 hc a))
        (mem_iInter.2 fun a => hRef.le _ (mem_iInter.1 hc' a))).symm
    · intro σ c y hy
      refine ((N.φ σ).pull_φ j rfl c y).trans ((hRef.φ σ _ _
        (mem_of_mem_linComb (m := fun _ => Points.PtsOver.map j rfl _ y) (fun _ => rfl) hy PUnit.unit)).trans ?_)
      exact congrArg (· + _) ((M.φ σ).pull_φ j rfl (fun a => c a PUnit.unit) y).symm
  change M.IsArithHeight f
  refine ⟨?_, ?_, ?_⟩
  · intro W j _ _ κ _ _ _ d hd
    exact (hf.vertical W j κ d hd).trans (congrArg (fun n : ℤ => (n : ℝ) * _)
      (topSelf_congr κ (N.restr j).isLB (M.restr j).isLB (pullRefines W j).lbIso d))
  · intro W j _ _ _ hc hd r hr
    have h' := pullRefines W j
    rw [hf.point W j hc hd _ (h'.isRatSec hr), HermLB.curveDeg, HermLB.curveDeg, h'.div hr]
    refine congrArg _ (finsum_congr fun σ => finsum_congr fun y => h'.logNorm hr (mem_offSupp.2 ?_))
    rw [under_eq_genericPoint (hY.of_isClosedImmersion j hc hd) y]
    exact CartierDiv.genericPoint_notMem_supp _
  · intro W j _ _ _ hc d hd hdim m r hr
    have h' := pullRefines W j
    have h'' : Refines ((N.restr j).pow m) ((M.restr j).pow m) (fun c a b => c a b PUnit.unit) 0 := by
      refine ⟨fun c y hy => mem_iInter.2 fun a => h'.le _ (mem_iInter.1 hy a), ?_, ?_⟩
      · intro V s z c c' hs hs'
        rw [gm_pow (N.restr j) m s z c c' hs hs',
          gm_pow (M.restr j) m s z _ _ (mem_iInter.2 fun a => h'.le _ (mem_iInter.1 hs a))
            (mem_iInter.2 fun a => h'.le _ (mem_iInter.1 hs' a)),
          h'.g V s z _ _ (mem_iInter.1 hs PUnit.unit) (mem_iInter.1 hs' PUnit.unit)]
      · intro σ c y hy
        exact (((N.restr j).φ σ).zpow_φ m c y).trans
          ((congrArg _ ((h'.φ σ _ _ (mem_pow_iff.1 hy)).trans (add_zero _))).trans
            ((((M.restr j).φ σ).zpow_φ m (fun a b => c a b PUnit.unit) y).symm.trans (add_zero _).symm))
    obtain ⟨h₁, h₂⟩ := hf.recursion W j hc d hd hdim m _ (h''.isRatSec hr)
    change (N.restr j).ArchIntegrable ((N.restr j).pow m) d (h''.isRatSec hr) at h₁
    unfold HermLB.ArchIntegrable Weight.ChernIntegrableOn at h₁
    unfold HermLB.archInt at h₂
    rw [h''.div hr] at h₁ h₂
    simp only [h'.chernPart] at h₁
    refine ⟨fun σ => Weight.ChernIntegrableOn.congr (h₁ σ) (isOpen_offSupp _).measurableSet
      fun y hy => h''.logNorm hr hy, h₂.trans (congrArg _ (finsum_congr fun σ => ?_))⟩
    rw [h'.chernInt]
    exact Weight.chernInt_congr (isOpen_offSupp _).measurableSet fun y hy => h''.logNorm hr hy

theorem cycleHeights_of_arCalc (H : ArCalc) : CycleHeights :=
  ⟨H.arExists, H.arMix, heightProjection_of_arProj H.arProj⟩

namespace CycleHeights

theorem heightProjection (H : CycleHeights) : HeightProjection := H.2.2

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {D e : ℕ}

theorem existsUnique (H : CycleHeights) (hX : IsArithVar p D) (L : HermLB p) : ∃! h, L.IsArithHeight h :=
  have := hX.isIntegral
  have ⟨h, hh⟩ := (H.1 k X p D hX).1 L
  ⟨h, hh, fun _ h' => h'.unique hX hh⟩

end CycleHeights

end GlobalTheory.Published
end
end

section -- merged from Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RallisTowerUnitary
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.Published

def RallisTowerUnitary : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ →
  ∀ (n m : ℕ) (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin m) (Fin m) E),
    (∀ i j, σ (JX j i) = JX i j) → JX.det ≠ 0 → (∀ i j, σ (JW j i) = -JW i j) → JW.det ≠ 0 →
  ∀ χX χW : Chr F E, IsHecke F E χX → IsHecke F E χW →
    ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
    ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW m →
  ∀ f : UA σ JW → ℂ,
    (∃ (c₀ : E) (K : Subgroup (GAd σ (c₀ • JW.map σ))) (φ : GAd σ (c₀ • JW.map σ) → ℂ), IsHermND σ (c₀ • JW.map σ) ∧
      GlobalTheory.UAut.IsMaxCpt σ (c₀ • JW.map σ) K ∧ GlobalTheory.UAut.IsAut σ (c₀ • JW.map σ) K φ ∧
      GlobalTheory.SiegelSet.IsCuspidal σ (c₀ • JW.map σ) φ ∧
      ∀ (h : UA σ JW) (h' : GAd σ (c₀ • JW.map σ)), h.1 = h'.1 → φ h' = f h) →
    (∀ (n₁ k : ℕ) (J₁ : Matrix (Fin n₁) (Fin n₁) E), 1 ≤ k → n₁ + 2 * k = n → (∀ i j, σ (J₁ j i) = J₁ i j) → J₁.det ≠ 0 →
      ∀ co₁ : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) J₁) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JW)) (Fin n₁ × Fin m),
        (∀ x : Matrix (Fin n₁) (Fin m) E, ∃ y z : Fin n₁ × Fin m → F,
          co₁.e ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      ∀ om₁ : UA σ J₁ × UA σ JW →* Module.End ℂ ((Fin n₁ × Fin m → AF F) → ℂ),
        IsUWeilPair (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) ψ (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) J₁) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JW) co₁ χX χW om₁ →
      ∀ Φ₁ ∈ schA F (Fin n₁ × Fin m), ∀ (g : UA σ J₁) (μ : Measure (UA σ JW)) (𝓕 : Set (UA σ JW)), μ.IsHaarMeasure →
        IsFundamentalDomain (ratU σ JW) 𝓕 μ → ∫ h in 𝓕, f h * (starRingEnd ℂ) (thetaSum F (om₁ (g, h) Φ₁)) ∂μ = 0) →
  ∀ co : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JX) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JW)) (Fin n × Fin m),
    (∀ x : Matrix (Fin n) (Fin m) E, ∃ y z : Fin n × Fin m → F,
      co.e ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
  ∀ om : UA σ JX × UA σ JW →* Module.End ℂ ((Fin n × Fin m → AF F) → ℂ),
    IsUWeilPair (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) ψ (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JX) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JW) co χX χW om →
  ∀ Φ ∈ schA F (Fin n × Fin m), ∀ (μ : Measure (UA σ JW)) (𝓕 : Set (UA σ JW)), μ.IsHaarMeasure →
    IsFundamentalDomain (ratU σ JW) 𝓕 μ →
  ∀ c : E, IsHermND σ (c • JX.map σ) → ∀ th : GAd σ (c • JX.map σ) → ℂ,
    (∀ (g : UA σ JX) (g' : GAd σ (c • JX.map σ)), g.1 = g'.1 →
      th g' = ∫ h in 𝓕, f h * (starRingEnd ℂ) (thetaSum F (om (g, h) Φ)) ∂μ) →
    GlobalTheory.SiegelSet.IsCuspidal σ (c • JX.map σ) th

end GlobalTheory.Published

end
end
