module

public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NonemptyPerfectSectionsComplexOfSmoothProj
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AppellHumbertUnifTangentWeilPairing
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.ExistsLevelStructureOfWeilPairing
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFinsetIsProjOverDescends
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsTwoPoints
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FamilyUniformisationFibreTheta
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOpenNonzeroLocusOfUniversallyClosed
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.GeometricallyConnectedOpenConditionSmoothProject
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.GeometricallyConnectedOpenConditionSmoothProject
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section
namespace GlobalTheory.ConnOpen

open GlobalTheory.AbLaw GlobalTheory.AbLaw.Seesaw ReciprocityTheory.ChartRestriction.G.Out

theorem preconnectedSpace_of_functions (Y : Scheme.{0})
    (H : ∀ s : Γ(Y, ⊤), Y.basicOpen s = ⊥ ∨ Y.basicOpen s = ⊤) : PreconnectedSpace Y := by
  refine ⟨fun U W hU hW hc ⟨u, _, hu⟩ ⟨w, _, hw⟩ => ?_⟩
  by_contra hne
  let O : Bool → Y.Opens := fun i => bif i then ⟨U, hU⟩ else ⟨W, hW⟩
  have hd : O true ⊓ O false = ⊥ := le_bot_iff.1 fun y hy => hne ⟨y, trivial, hy⟩
  have hcov : ⨆ i, O i = ⊤ := top_unique fun y _ => by
    rcases hc (Set.mem_univ y) with h | h
    · exact TopologicalSpace.Opens.mem_iSup.2 ⟨true, h⟩
    · exact TopologicalSpace.Opens.mem_iSup.2 ⟨false, h⟩
  obtain ⟨s, hs⟩ := TLinPf.glue O hcov (fun i => bif i then 1 else 0) (fun i j => by
    have sub : ∀ T : Y.Opens, T = ⊥ → Subsingleton Γ(Y, T) := fun T hT => by
      subst hT; infer_instance
    cases i <;> cases j
    · exact (map_zero _).trans (map_zero _).symm
    · exact (sub _ ((inf_comm _ _).trans hd)).elim _ _
    · exact (sub _ hd).elim _ _
    · exact (map_one _).trans (map_one _).symm)
  rcases H s with h | h
  · have h₁ : u ∈ Y.basicOpen s := (mem_basicOpen_rs (le_top : O true ≤ ⊤) s hu).1 (by
      rw [show rs Y (le_top : O true ≤ ⊤) s = 1 from hs true]
      exact mem_of_isUnit isUnit_one hu)
    rw [h] at h₁
    exact h₁
  · have h₁ := (mem_basicOpen_rs (le_top : O false ≤ ⊤) s hw).2 (h.ge (Set.mem_univ w))
    rw [show rs Y (le_top : O false ≤ ⊤) s = 0 from hs false, Scheme.basicOpen_zero] at h₁
    exact h₁

theorem surjective_appTop {k : Type} [Field k] [IsAlgClosed k] {X : Scheme.{0}}
    (p : X ⟶ Spec (.of k)) [IsIntegral X] [UniversallyClosed p] :
    Function.Surjective p.appTop.hom := by
  let F := (Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop
  have hF : F.hom.IsIntegral := by
    apply RingHom.isIntegral_respectsIso.2 (e := (Scheme.ΓSpecIso _).symm.commRingCatIsoToRingEquiv)
    exact isIntegral_appTop_of_universallyClosed p
  algebraize [F.hom]
  have h : Function.Surjective F.hom :=
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := Γ(X, ⊤))).2
  intro s
  obtain ⟨c, hc⟩ := h s
  exact ⟨_, hc⟩

variable {X X' : Scheme.{0}}

def fnSec (π : X' ⟶ X) (s : Γ(X', ⊤)) : LB.Sec ((Inh.trivLB X).pull π) where
  f := fun _ => rs X' le_top s
  compat := fun i j => by
    rw [Inh.linComb_triv_g, Units.val_one, _root_.one_mul]
    exact (rs_rs _ _ s).trans (rs_rs _ _ s).symm

theorem triv_pull (π : X' ⟶ X) : Triv ((Inh.trivLB X).pull π) :=
  ⟨⟨fun _ => 1⟩, fun i j => by
    erw [Inh.linComb_triv_g, _root_.one_mul]
    exact (map_one _).trans (map_one _).symm⟩

theorem preconnectedSpace_of_line {R F : Type} [CommRing R] [Field F]
    {f : X ⟶ Spec (CommRingCat.of R)} (P : Perf f (Inh.trivLB X)) {g : R →+* F} {π : X' ⟶ X}
    {f' : X' ⟶ Spec (CommRingCat.of F)} (h : IsPullback π f' f (Spec.map (CommRingCat.ofHom g)))
    (v : Fin P.a → F) (hv : ∀ w, (P.D₀.map g).mulVec w = 0 → ∃ c : F, w = c • v) :
    PreconnectedSpace X' := by
  obtain ⟨E, hE⟩ := P.sec F g X' π f' h
  have key : ∀ s : Γ(X', ⊤), ∃ c : F, ∀ i,
      rs X' (le_top : π ⁻¹ᵁ P.W i ≤ ⊤) s = GlobalTheory.AbLaw.cst f' _ c * loc P π f' v i := fun s => by
    obtain ⟨w, hw⟩ := E.surjective (fnSec π s)
    obtain ⟨c, hc⟩ := hv w.1 w.2
    refine ⟨c, fun i => ?_⟩
    have e := hE w i
    rw [hw] at e
    refine ((rs_rs _ _ s).symm.trans e).trans ?_
    rw [← loc_smul, ← hc]
    rfl
  obtain ⟨c₁, h₁⟩ := key 1
  have hu : ∀ i, IsUnit (loc P π f' v i) := fun i =>
    isUnit_of_mul_isUnit_right (by rw [← h₁ i, map_one]; exact isUnit_one)
  refine preconnectedSpace_of_functions X' fun s => ?_
  obtain ⟨c, hc⟩ := key s
  by_cases h0 : c = 0
  · refine Or.inl (le_bot_iff.1 fun y hy => ?_)
    obtain ⟨i, hi⟩ := exists_mem P (π y)
    have := (mem_basicOpen_rs (le_top : π ⁻¹ᵁ P.W i ≤ ⊤) s hi).2 hy
    rwa [hc, h0, map_zero, zero_mul, Scheme.basicOpen_zero] at this
  · refine Or.inr (top_unique fun y _ => ?_)
    obtain ⟨i, hi⟩ := exists_mem P (π y)
    refine (mem_basicOpen_rs (le_top : π ⁻¹ᵁ P.W i ≤ ⊤) s hi).1 ?_
    rw [hc]
    exact mem_of_isUnit (((IsUnit.mk0 c h0).map _).mul (hu i)) hi

theorem exists_nonempty_fibre {R K : Type} [CommRing R] [Field K] {Z Z₀ : Scheme.{0}} (s : Z ⟶ Sp R)
    (hs : IsOpenMap s) (x : R →+* K) {π : Z₀ ⟶ Z} {q : Z₀ ⟶ Sp K} (h : π ≫ s = q ≫ spMap x) (z : Z₀) :
    ∃ e : R, x e ≠ 0 ∧ ∀ p : PrimeSpectrum R, e ∉ p.asIdeal → ∃ y : Z, s y = p := by
  have hz : s (π z) ∈ Set.range s := ⟨_, rfl⟩
  obtain ⟨_, ⟨e, rfl⟩, he, hle⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hz hs.isOpen_range
  refine ⟨e, fun h0 => ?_, fun p hp => hle hp⟩
  have e' : s (π z) = spMap x (q z) := congrArg (fun t => t z) h
  rw [e'] at he
  refine he ?_
  change x e ∈ (q z).asIdeal
  rw [h0]
  exact zero_mem _

theorem geometricallyConnected_near : ∀ (R : Type) [CommRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) (K : Type) [Field K] (x : R →+* K), IsProjOver s → Smooth s → GeometricallyConnected (pullback.snd s (spMap x)) → ∃ f : R, x f ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (φ : R →+* R'), IsUnit (φ f) → GeometricallyConnected (pullback.snd s (spMap φ)) := by
  intro R _ Z s K _ x hp hs hc
  have hp' := (GlobalTheory.ProjSpace.isProjBy_iff_isProjOver s).2 hp
  obtain ⟨P⟩ := GlobalTheory.T.nonempty_perfectSectionsComplex_of_smooth_proj R Z s hs hp' _ (Inh.trivLB_isLB _)
  have hpr : IsProper s := GlobalTheory.AbLaw.isProper_of_isProjBy R Z s hp'
  let L := AlgebraicClosure K
  let g₀ : R →+* L := (algebraMap K L).comp x
  let q := pullback.snd s (spMap x)
  let y₀ : Sp L ⟶ Sp K := spMap (algebraMap K L)
  have h₀ : IsPullback (pullback.fst q y₀ ≫ pullback.fst s (spMap x)) (pullback.snd q y₀) s
      (Spec.map (CommRingCat.ofHom g₀)) := by
    have := (IsPullback.of_hasPullback q y₀).paste_horiz (IsPullback.of_hasPullback s (spMap x))
    rwa [← Spec.map_comp] at this
  have hi := GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ q inferInstance hc
  have hint : IsIntegral (pullback q y₀) :=
    GeometricallyIntegral.geometrically_isIntegral _ _ _ (.of_hasPullback q y₀)
  have hpr₀ : IsProper (pullback.snd q y₀) := MorphismProperty.of_isPullback h₀ hpr
  obtain ⟨v, -, hu, hline⟩ := loc_of_triv P h₀ (Inh.trivLB_isLB _) (triv_pull _)
  obtain ⟨x₀⟩ : Nonempty ↥(pullback q y₀) := inferInstance
  have hv0 : v ≠ 0 := by
    rintro rfl
    obtain ⟨i, hi⟩ := exists_mem P ((pullback.fst q y₀ ≫ pullback.fst s (spMap x)) x₀)
    have h₁ := mem_of_isUnit (hu i) (y := x₀) hi
    rw [← zero_smul L (0 : Fin P.a → L), loc_smul, map_zero, zero_mul, Scheme.basicOpen_zero] at h₁
    exact h₁
  obtain ⟨δ, v₀, hδ, hker⟩ := exists_kernel_vector g₀ P.D₀ v hv0 (hline (surjective_appTop _))
  obtain ⟨e, he, him⟩ := exists_nonempty_fibre s s.isOpenMap g₀ h₀.w x₀
  refine ⟨δ * e, fun h0 => mul_ne_zero hδ he ?_, fun R' _ φ hφ => ?_⟩
  · rw [← map_mul]
    exact (congrArg (algebraMap K L) h0).trans (map_zero _)
  refine ⟨geometrically_iff_of_commRing.2 fun F _ _ Y fst snd h => ?_⟩
  let g : R →+* F := (algebraMap R' F).comp φ
  have h₁ : IsPullback (fst ≫ pullback.fst s (spMap φ)) snd s (Spec.map (CommRingCat.ofHom g)) := by
    have := h.paste_horiz (IsPullback.of_hasPullback s (spMap φ))
    rwa [← Spec.map_comp] at this
  have hg : IsUnit (g δ * g e) := by
    rw [← map_mul]
    exact hφ.map (algebraMap R' F)
  have := preconnectedSpace_of_line P h₁ _ (hker F g (isUnit_of_mul_isUnit_left hg))
  obtain ⟨y, hy⟩ := him (PrimeSpectrum.comap g ⊥) fun hm =>
    (isUnit_of_mul_isUnit_right hg).ne_zero hm
  obtain ⟨z, -⟩ := Scheme.exists_preimage_of_isPullback h₁ y (⊥ : PrimeSpectrum F) hy
  exact ⟨⟨z⟩⟩

end GlobalTheory.ConnOpen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.GeometricallyConnectedOpenConditionSmoothProjectStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometricallyConnected_open_condition_smooth_projective : ∀ (R : Type) [CommRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) (K : Type) [Field K] (x : R →+* K), IsProjOver s → Smooth s → GeometricallyConnected (pullback.snd s (spMap x)) → ∃ f : R, x f ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (φ : R →+* R'), IsUnit (φ f) → GeometricallyConnected (pullback.snd s (spMap φ)) := by
  first | exact @GlobalTheory.ConnOpen.geometricallyConnected_near | exact GlobalTheory.ConnOpen.geometricallyConnected_near | (intros; apply GlobalTheory.ConnOpen.geometricallyConnected_near <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSymplecticSystem
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.EllipticLevel

theorem exists_stdSymp_of_rel {k g : ℕ} (hk : 0 < k) {G R : Type} [CommGroup G] [CommRing R] [IsDomain R]
    (hc : ∀ d, d ∣ k → Nat.card {x : G // x ^ d = 1} = d ^ (2 * g)) {ze : Rˣ} (hz : IsPrimitiveRoot ze k)
    (W : G → G → Rˣ → Prop) (hW : ∀ x y, x ^ k = 1 → y ^ k = 1 → ∃! c, W x y c)
    (hmul : ∀ x x' y c c', W x y c → W x' y c' → W (x * x') y (c * c')) (halt : ∀ x, x ^ k = 1 → W x x 1)
    (hsymm : ∀ x y c, W x y c → W y x c⁻¹)
    (hnd : ∀ x, x ^ k = 1 → (∀ y, y ^ k = 1 → W x y 1) → x = 1) :
    ∃ v : Fin (2 * g) → G, (∀ i, v i ^ k = 1) ∧ ∀ i j, W (v i) (v j) (ze ^ Out.stdSymp g i j) := by
  classical

  set H : Subgroup G := (powMonoidHom k : G →* G).ker with hH
  have memH : ∀ x : G, x ∈ H ↔ x ^ k = 1 := fun x => by
    rw [hH, MonoidHom.mem_ker, powMonoidHom_apply]
  have torsH : ∀ x : H, (x : G) ^ k = 1 := fun x => (memH x).1 x.2

  let f : H → H → Rˣ := fun x y => (hW x y (torsH x) (torsH y)).exists.choose
  have hf : ∀ x y : H, W x y (f x y) := fun x y => (hW x y (torsH x) (torsH y)).exists.choose_spec
  have uniq : ∀ (x y : H) (c : Rˣ), W x y c → c = f x y := fun x y c h =>
    (hW x y (torsH x) (torsH y)).unique h (hf x y)
  have fswap : ∀ x y : H, f y x = (f x y)⁻¹ := fun x y =>
    (uniq y x _ (hsymm _ _ _ (hf x y))).symm
  have fmulL : ∀ x x' y : H, f (x * x') y = f x y * f x' y := fun x x' y =>
    (uniq _ _ _ (hmul _ _ _ _ _ (hf x y) (hf x' y))).symm
  have fmulR : ∀ x y y' : H, f x (y * y') = f x y * f x y' := fun x y y' => by
    rw [← uniq x (y * y') _ (hsymm _ _ _ (hmul _ _ _ _ _ (hf y x) (hf y' x))), fswap x y, fswap x y',
      mul_inv, inv_inv, inv_inv]
  let e : H →* H →* Rˣ :=
    MonoidHom.mk' (fun x => MonoidHom.mk' (f x) (fmulR x)) (fun x x' => by
      ext y
      simp only [MonoidHom.mk'_apply, MonoidHom.mul_apply]
      rw [fmulL])
  have heq : ∀ x y : H, e x y = f x y := fun _ _ => rfl

  have hcH : ∀ d : ℕ, d ∣ k → Nat.card {x : H // x ^ d = 1} = d ^ (2 * g) := by
    intro d hd
    obtain ⟨m, hm⟩ := hd
    have eqv : {x : H // x ^ d = 1} ≃ {x : G // x ^ d = 1} :=
      { toFun := fun x => ⟨x.1, by simpa using congrArg Subtype.val x.2⟩
        invFun := fun y => ⟨⟨y.1, (memH _).2 (by rw [hm, pow_mul, y.2, one_pow])⟩,
          Subtype.ext (by simpa using y.2)⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Nat.card_congr eqv]
    exact hc d ⟨m, hm⟩
  have hkH : ∀ x : H, x ^ k = 1 := fun x => Subtype.ext (by simpa using torsH x)
  have halt' : ∀ x : H, e x x = 1 := fun x => by
    rw [heq]
    exact (uniq x x 1 (halt x (torsH x))).symm
  have hnd' : ∀ x : H, (∀ y, e x y = 1) → x = 1 := by
    intro x hx
    apply Subtype.ext
    refine hnd x (torsH x) (fun y hy => ?_)
    have h1 := hf x ⟨y, (memH y).2 hy⟩
    rwa [← heq, hx] at h1
  obtain ⟨v, hv⟩ := GlobalTheory.exists_stdSymp_of_alternating_pairing k g H R ze hk hz hkH hcH e halt' hnd'
  refine ⟨fun i => (v i : G), fun i => torsH (v i), fun i j => ?_⟩
  have h2 := hf (v i) (v j)
  rwa [← heq, hv i j] at h2

theorem exists_symplectic_system (hL : Out.Laws) {K : Type} [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (k : ℕ)
    (hk : (k : K) ≠ 0) (ze : Kˣ) (hze : IsPrimitiveRoot ze k) :
    ∃ pt : Fin (2 * P.g) → (Out.baseOver (Sp K) ⟶ P.A), (∀ i, pt i ^ k = 1) ∧
      ∀ i j, Out.WeilIs P.A P.L k (pt i) (pt j) (unitOn ze ^ Out.stdSymp P.g i j) := by
  obtain ⟨-, -, -, -, -, hmn, -, -, -, hw, hwn, -⟩ := hL
  have hk0 : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; exact hk Nat.cast_zero)
  have := P.isAb.comm

  have hc : ∀ d, d ∣ k → Nat.card {x : Out.baseOver (Sp K) ⟶ P.A // x ^ d = 1} = d ^ (2 * P.g) := by
    intro d hd
    have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hd hk0
    have hdK : (d : K) ≠ 0 := by
      obtain ⟨m, rfl⟩ := hd
      intro h0
      apply hk
      rw [Nat.cast_mul, h0, zero_mul]
    exact ((hmn (Sp K) P d hd0).2.2.2.2 K (𝟙 _) hdK)

  have hleft : ∀ a, (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom a) = a := fun a => by simp
  have hleft' : ∀ a, (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
      ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom a) = a := fun a => by simp
  haveI : IsDomain Γ(Sp K, ⊤) := Function.Injective.isDomain (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom
    (Function.LeftInverse.injective hleft')
  have hz' : IsPrimitiveRoot (unitOn ze) k :=
    hze.map_of_injective (f := Units.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom.toMonoidHom)
      (Units.map_injective (Function.LeftInverse.injective hleft))
  have hwB := hw (Sp K) P k (Out.baseOver (Sp K))
  obtain ⟨v, hv1, hv2⟩ := exists_stdSymp_of_rel (G := Out.baseOver (Sp K) ⟶ P.A) (R := Γ(Sp K, ⊤)) hk0 hc hz'
    (fun x y c => Out.WeilIs P.A P.L k x y c) hwB.1 hwB.2.1 hwB.2.2.1
    (fun _ _ _ h => GlobalTheory.CommPairing.weilIs_symm P.isLB h) (fun x hx h => hwn K P k hk x hx h)
  exact ⟨v, hv1, hv2⟩

end GlobalTheory.EllipticLevel

namespace GlobalTheory

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ProjCoordRepresentationGeometricFibreSpanning
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ProjCoordRepresentationGeometricFibreSpanning
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.FibreEmbed

open GlobalTheory.AmpleSpan GlobalTheory.SegreCoord GlobalTheory.ProjSpace GlobalTheory.Cartier TopologicalSpace

theorem embedsBy_fibre (hA : Out.AmpleSt) (hB : Out.PolBaseChangeSt) {S : Scheme.{0}} (P : Out.PolAV S) {K : Type}
    [Field K] (x : Sp K ⟶ S) {N : ℕ} (hN : 4 ≤ N) {I : Type} [Fintype I]
    (t : I → LB.Sec (Out.LPow P.A P.L N (Over.mk x)))
    (ht : Submodule.span Γ((Over.mk x).left, ⊤)
      (Set.range fun a => (Out.SecM.ofSec P.A (t a) : Out.SecM P.A P.L N (Over.mk x))) = ⊤) :
    EmbedsBy (fst (Over.mk x) P.A).left t := by
  obtain ⟨P', g, hg, -, -, w⟩ := hB S _ x P
  have h : IsPullback (snd (Over.mk x) P.A).left (fst (Over.mk x) P.A).left P.A.hom x :=
    (IsPullback.of_hasPullback x P.A.hom).flip
  let e := h.isoIsPullback _ _ hg
  have he : e.hom ≫ g = (snd (Over.mk x) P.A).left := h.isoIsPullback_hom_fst _ _ hg
  have he' : e.hom ≫ P'.A.hom = (fst (Over.mk x) P.A).left := h.isoIsPullback_hom_snd _ _ hg
  have haff : IsAffine (Over.mk x).left := inferInstanceAs (IsAffine (Sp K))
  have sq : IsPullback e.hom (fst (Over.mk x) P.A).left P'.A.hom
      ((𝟙 (Sp K) ≫ (Sp K).topIso.inv) ≫ Scheme.Opens.ι (⊤ : (Sp K).Opens)) := by
    rw [comp_topIso_inv_ι]
    exact @IsPullback.of_horiz_isIso _ _ _ _ _ _ _ _ _ _ inferInstance (IsIso.id (Sp K))
      ⟨he'.trans (Category.comp_id _).symm⟩
  obtain ⟨M, s, hs⟩ := exists_embedsBy_of_isPullback P'.A P'.isLB (hA _ P' N hN).2 (isAffineOpen_top _) sq
    (K := Fin 1) (ε := fun _ => (N : ℤ)) (by simp)
  obtain ⟨w', hw'⟩ := LBIso.symm w
  have hP := DVR.linComb_isLB P'.L P'.isLB (K := Fin 1) (fun _ => e.hom) (fun _ => (N : ℤ))
  have hQ : (Out.LPow P.A P.L N (Over.mk x)).IsLB := DVR.linComb_isLB P.L P.isLB _ _
  obtain ⟨W, hW⟩ : LBIso (Out.LPow P.A P.L N (Over.mk x))
      ((LB.LinComb P'.L (K := Fin 1) (fun _ => e.hom) (fun _ => (N : ℤ))).pull (𝟙 _)) :=
    LBIso.chartPull (chartPullSame P.L _ _ _ (𝟙 _) fun _ => he.symm.trans (Category.id_comp _).symm)
      (Geo.Tor.chartPullPull _ _ _ rfl)
      (LBIso.symm (iso_linComb ((isGen_iff w').1 hw') (fun _ : Fin 1 => e.hom) (fun _ => (N : ℤ))))
  choose s' hs' using fun i => sec_pull_down ((isGen_iff W).1 hW) hP hQ (s i)
  have hs₂ : EmbedsBy (fst (Over.mk x) P.A).left s' := by
    refine hs.pull (ψ := 𝟙 _) (g := 𝟙 _) IsPullback.of_id_fst fun y => ?_
    obtain ⟨j, hj⟩ := exists_chart hP y
    obtain ⟨k, hk⟩ := exists_chart hQ y
    refine ⟨j, k, hj, hk, gw W (𝟙 _) y j k, fun i => ?_⟩
    have := hs' i _ (𝟙 _) y j k hj hk
    rwa [Category.id_comp] at this
  have := P.isAb.proper
  have : UniversallyClosed (fst (Over.mk x) P.A).left :=
    MorphismProperty.of_isPullback (P := @UniversallyClosed) h inferInstance
  exact hs₂.of_inSpan fun j => (inSpan_iff_mem_span P.A t _).2 (by rw [ht]; trivial)

variable {X : Scheme.{0}} {A B : LB X} {σ : Type} {a : σ → A.Sec} {b : σ → B.Sec} {T : Type} [CommRing T]
  {x : Sp T ⟶ X} {v : σ → T}

theorem gs_of_secMaps {w : LB.Iso A B} (hw : ∀ i, SecMaps w (a i) (b i)) (y : Sp T) {p : B.ι} {q : A.ι}
    (hp : x y ∈ B.U p) (hq : x y ∈ A.U q) :
    ∃ u : ((Sp T).presheaf.stalk y)ˣ, ∀ i, gs x y _ ((b i).f p) = u * gs x y _ ((a i).f q) := by
  have hm : x y ∈ B.U p ⊓ A.U q := ⟨hp, hq⟩
  refine ⟨gm x y (B.U p ⊓ A.U q) (w.s (p, q)), fun i => ?_⟩
  exact (gs_res x y _ hm _).symm.trans ((congrArg (gs x y _) (hw i (p, q))).trans ((gs_mul x y _ hm _ _).trans
    (congrArg₂ (· * ·) (gs_unit x y _ hm _) (gs_res x y _ hm _))))

theorem loc_iff_of_secMaps (hA : A.IsLB) (hB : B.IsLB) {w : LB.Iso A B} (hw : ∀ i, SecMaps w (a i) (b i)) :
    Loc A a x v ↔ Loc B b x v := by
  refine ⟨fun h y p hp => ?_, fun h y q hq => ?_⟩
  · obtain ⟨q, hq⟩ := exists_chart hA (x y)
    obtain ⟨u, hu⟩ := h y q hq
    obtain ⟨u', hu'⟩ := gs_of_secMaps hw y hp hq
    exact ⟨u' * u, fun i => by rw [hu', hu, Units.val_mul, mul_left_comm]⟩
  · obtain ⟨p, hp⟩ := exists_chart hB (x y)
    obtain ⟨u, hu⟩ := h y p hp
    obtain ⟨u', hu'⟩ := gs_of_secMaps hw y hp hq
    exact ⟨u'⁻¹ * u, fun i => by rw [Units.val_mul, mul_left_comm, ← hu, hu', Units.inv_mul_cancel_left]⟩

theorem span_eq_top_of_loc (hc : ⨆ i, Out.nonzeroLocus (a i) = ⊤) (h : Loc A a x v) :
    Ideal.span (Set.range v) = ⊤ := by
  by_contra hne
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  let y : Sp T := ⟨m, hm.isPrime⟩
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hc.ge (Set.mem_univ (x y)))
  obtain ⟨k, hk⟩ := exists_chart_of_mem _ hi
  obtain ⟨u, hu⟩ := h y k hk
  have h1 := (mem_nonzeroLocus_iff_gs (a i) x y hk).1 hi
  rw [hu] at h1
  have h2 := ((Sp T).mem_basicOpen ((Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom (v i)) y trivial).2
    (isUnit_of_mul_isUnit_left h1)
  have h3 := (basicOpen_eq_of_affine (R := CommRingCat.of T) (v i)).le h2
  exact h3 (hle (Ideal.subset_span ⟨i, rfl⟩))

theorem secCoord_iff_of_secMaps (hA : A.IsLB) (hB : B.IsLB) {w : LB.Iso A B} (hw : ∀ i, SecMaps w (a i) (b i))
    (ha : ⨆ i, Out.nonzeroLocus (a i) = ⊤) (hb : ⨆ i, Out.nonzeroLocus (b i) = ⊤) :
    SecCoord A a x v ↔ SecCoord B b x v :=
  ⟨fun h => secCoord_of_loc (span_eq_top_of_loc ha (loc_of_secCoord h))
      ((loc_iff_of_secMaps hA hB hw).1 (loc_of_secCoord h)),
    fun h => secCoord_of_loc (span_eq_top_of_loc hb (loc_of_secCoord h))
      ((loc_iff_of_secMaps hA hB hw).2 (loc_of_secCoord h))⟩

theorem projRep_bot (R : Type) [CommRing R] {N : ℕ} (e : σ ≃ Fin (N + 1)) :
    ProjRep (⊥ : Ideal (MvPolynomial σ R)) (PSpace.str R N) ((O1 R N).pull (𝟙 _))
      (fun c => secPull (coord R N (e c)) (𝟙 _)) := by
  refine ⟨pull_isLB (O1_isLB R N) _, fun R' _ β x v hx h => ?_, fun R' _ β v hv _ => ?_⟩
  · obtain ⟨hv, -⟩ := (ProjCoord.secCoord_iff e (𝟙 _) β x (by simpa using hx) v).1 h
    rw [ProjCoord.range_comp_symm] at hv
    exact ⟨hv, fun F hF => by rw [Ideal.mem_bot.1 hF, MvPolynomial.eval₂_zero]⟩
  · rw [← ProjCoord.range_comp_symm e] at hv
    have pt_str : ∀ (c : R →+* R') (v : Fin (N + 1) → R')
        (hv : Ideal.span (Set.range v) = ⊤), pt c v hv ≫ PSpace.str R N = spMap c := by
      intro c v hv
      rw [pt, PSpace.str, ProjPoint.ofHom_toSpecZero_assoc, ← Spec.map_comp]
      congr 1
      ext1
      exact RingHom.ext fun r => MvPolynomial.eval₂Hom_C c v r
    refine ⟨pt β _ hv, ⟨pt_str _ _ _, ?_⟩, fun x hx => ?_⟩
    · exact (ProjCoord.secCoord_iff e (𝟙 _) β _ (by simpa using pt_str β _ hv) v).2 ⟨hv, Category.comp_id _⟩
    · obtain ⟨_, h⟩ := (ProjCoord.secCoord_iff e (𝟙 _) β x (by simpa using hx.1) v).1 hx.2
      exact (Category.comp_id _).symm.trans h

theorem projRep_of_embedsBy {R : Type} [CommRing R] (f : X ⟶ Sp R) (hA : A.IsLB) {N : ℕ} (e : σ ≃ Fin (N + 1))
    (h : EmbedsBy f (fun j => a (e.symm j))) : ProjRep (idealOf f A a (𝟙 X)) f A a := by
  have : Finite σ := Finite.of_equiv _ e.symm
  obtain ⟨hs, hcl⟩ := (veryAmpleBy_iff f (fun j => a (e.symm j))).1 ((embedsBy_spec_iff f _).1 h)
  have key := GlobalTheory.T.isProjectiveCoordinateRepresentation_closedSubscheme R σ ⊥ _ X (PSpace.str R N) _ _ (toProj f _ hs) A a (projRep_bot R e) hcl hA
    fun R' _ y v => by
      let c : R →+* R' := (Spec.preimage (y ≫ f)).hom
      have hc : (y ≫ toProj f _ hs) ≫ PSpace.str R N = spMap c := by
        rw [Category.assoc, toProj_str]
        exact (Spec.map_preimage (y ≫ f)).symm
      have h1 := ProjCoord.secCoord_iff e (toProj f _ hs) c y hc v
      have h2 := ProjCoord.secCoord_iff e (𝟙 _) c (y ≫ toProj f _ hs) (by rw [Category.comp_id]; exact hc) v
      rw [Category.comp_id] at h2
      refine Iff.trans ?_ (h1.trans h2.symm)
      refine (secCoord_iff_of_secMaps (pull_isLB (O1_isLB R N) _) hA (w := toProjIso f _ hs) (fun i => ?_) ?_ ?_).symm
      · simpa only [Equiv.symm_apply_apply] using secMaps_toProjIso f _ hs (e i)
      · exact (e.iSup_comp (g := fun j => Out.nonzeroLocus (secPull (coord R N j) (toProj f _ hs)))).trans
          (iSup_nonzeroLocus_secPull (iSup_nonzeroLocus_coord R N) _)
      · exact (e.symm.iSup_comp (g := fun c => Out.nonzeroLocus (a c))).symm.trans hs
  rwa [toProj_str] at key

theorem projRep_fibre : Out.Laws → Out.Laws2 → ∀ (S : Scheme.{0}) (P : Out.PolAV S) (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (k : ℤ) (I : Type) [Finite I] (σ : I → LB.Sec (Out.LPow P.A P.L k (Over.mk x))), 4 ≤ k → Submodule.span Γ((Over.mk x).left, ⊤) (Set.range fun a => (Out.SecM.ofSec P.A (σ a) : Out.SecM P.A P.L k (Over.mk x))) = ⊤ → ProjRep (idealOf (fst (Over.mk x) P.A).left _ σ (𝟙 _)) (fst (Over.mk x) P.A).left _ σ := by
  intro hL _ S P K _ _ x k I _ σ hk hσ
  obtain ⟨N, rfl⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ k by omega)
  have hN : 4 ≤ N := by exact_mod_cast hk
  have := Fintype.ofFinite I
  have h₀ := embedsBy_fibre hL.ample hL.polBaseChange P x hN σ hσ
  have hne : Nonempty I := by
    obtain ⟨p⟩ : Nonempty (Sp K) := inferInstance
    obtain ⟨i, -⟩ := Opens.mem_iSup.1 (h₀.1.ge (Set.mem_univ
      ((lift (𝟙 (Over.mk x)) (1 : Over.mk x ⟶ P.A)).left p)))
    exact ⟨i⟩
  obtain ⟨M, hM⟩ : ∃ M, Fintype.card I = M + 1 := ⟨_, (Nat.succ_pred_eq_of_pos Fintype.card_pos).symm⟩
  let e := Fintype.equivFinOfCardEq hM
  refine projRep_of_embedsBy _ (DVR.linComb_isLB P.L P.isLB _ _) e
    (embedsBy_fibre hL.ample hL.polBaseChange P x hN _ ?_)
  rw [← hσ]
  exact congrArg _ (e.symm.surjective.range_comp
    fun a => (Out.SecM.ofSec P.A (σ a) : Out.SecM P.A P.L N (Over.mk x)))

end GlobalTheory.FibreEmbed
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ProjCoordRepresentationGeometricFibreSpanningStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projCoordRepresentation_geometric_fibre_spanning : Out.Laws → Out.Laws2 → ∀ (S : Scheme.{0}) (P : Out.PolAV S) (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (k : ℤ) (I : Type) [Finite I] (σ : I → LB.Sec (Out.LPow P.A P.L k (Over.mk x))), 4 ≤ k → Submodule.span Γ((Over.mk x).left, ⊤) (Set.range fun a => (Out.SecM.ofSec P.A (σ a) : Out.SecM P.A P.L k (Over.mk x))) = ⊤ → ProjRep (idealOf (fst (Over.mk x) P.A).left _ σ (𝟙 _)) (fst (Over.mk x) P.A).left _ σ := by
  first | exact @GlobalTheory.FibreEmbed.projRep_fibre | exact GlobalTheory.FibreEmbed.projRep_fibre | (intros; apply GlobalTheory.FibreEmbed.projRep_fibre <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsAffineOpenPreimageBasicOpen
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open TopologicalSpace

namespace GlobalTheory.AmpleSpread

open GlobalTheory.SecSpread GlobalTheory.LBGerm

variable {R : Type} [CommRing R] [IsDomain R] {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]
  {X X' : Scheme.{0}} {p : X ⟶ Sp R} {φ : X' ⟶ X} {π : X' ⟶ Sp K}

theorem exists_const_mul_eq_zero (H : IsPullback φ π p (spMap (algebraMap R K))) {U : X.Opens}
    (hU : IsAffineOpen U) (a : Γ(X, U)) (h : ∀ z, φ z ∈ U → gs φ z U a = 0) :
    ∃ d : R, d ≠ 0 ∧ ∀ y ∈ U, cst p y d * gs (𝟙 X) y U a = 0 := by
  have e : (φ.app U).hom a = 0 := fn_ext fun z hz => by
    have hz' : φ z ∈ U := hz
    refine (gs_pull (𝟙 X') φ z U hz' _).trans ?_
    rw [Category.id_comp, h z hz', gs_zero (𝟙 X') z _ hz]
  let _ := (φ.app U).hom.toAlgebra
  have hl := GlobalTheory.QCoh.Qcqs.isLocalization_app (R := .of R) (L := .of K) (nonZeroDivisors R) H hU
  obtain ⟨⟨_, d, hd, rfl⟩, hm⟩ := (@IsLocalization.map_eq_zero_iff _ _ _ _ _ _ hl a).1 e
  refine ⟨d, nonZeroDivisors.ne_zero hd, fun y hy => ?_⟩
  have e' := congrArg (gs (𝟙 X) y U) (show constFn p U d * a = 0 from hm)
  rwa [gs_mul _ y _ hy, gs_constFn p U _ y hy, Category.id_comp, gs_zero _ y _ hy] at e'

theorem exists_sec_preimage_nonzeroLocus_eq (H : IsPullback φ π p (spMap (algebraMap R K))) [CompactSpace X]
    [X.IsSeparated] {L : LB X} (hL : L.IsLB) (s : (L.pull φ).Sec) :
    ∃ θ : L.Sec, φ ⁻¹ᵁ Out.nonzeroLocus θ = Out.nonzeroLocus s := by
  classical
  obtain ⟨α, _, V, c, hV, hle, hc⟩ := exists_finite_affine_refinement hL
  have loc : ∀ x : α, ∃ (d : R) (_ : d ≠ 0) (a : Γ(X, V x)), ∀ z, φ z ∈ V x → gs φ z (V x) a =
      cst (φ ≫ p) z d * gs (𝟙 X') z ((L.pull φ).U (fun _ => c x)) (s.f (fun _ => c x)) := by
    intro x
    have hle' : φ ⁻¹ᵁ V x ≤ (L.pull φ).U (fun _ => c x) := fun z hz => mem_pull.2 (hle x hz)
    obtain ⟨d, hd, a, ha⟩ := exists_denom_of_isAffineOpen H (hV x) (resG X' hle' (s.f (fun _ => c x)))
    refine ⟨d, hd, a, fun z hz => ?_⟩
    have e := congrArg (gs (𝟙 X') z _) ha
    have hz' : (𝟙 X' : X' ⟶ X') z ∈ φ ⁻¹ᵁ V x := hz
    rw [gs_mul _ z _ hz', gs_res _ z hle' hz', gs_pull (𝟙 X') φ z _ hz, gs_pull (𝟙 X') φ z _ hz,
      Category.id_comp, gs_constFn p _ φ z hz] at e
    exact e.symm
  choose d hd a ha using loc
  obtain ⟨b, hb⟩ : ∃ b : ∀ x, Γ(X, V x), ∀ x z, φ z ∈ V x → gs φ z (V x) (b x) =
      cst (φ ≫ p) z (∏ x, d x) * gs (𝟙 X') z ((L.pull φ).U (fun _ => c x)) (s.f (fun _ => c x)) :=
    ⟨fun x => constFn p _ (∏ w ∈ Finset.univ.erase x, d w) * a x, fun x z hz => by
      rw [gs_mul φ z _ hz, gs_constFn p _ φ z hz, ha x z hz, ← Finset.mul_prod_erase _ d (Finset.mem_univ x), cst_mul]
      ring⟩
  have kill : ∀ q : α × α, ∃ e : R, e ≠ 0 ∧ ∀ y ∈ V q.1 ⊓ V q.2, cst p y e * (gs (𝟙 X) y _ (b q.1) -
      (gm (𝟙 X) y (L.U (c q.1) ⊓ L.U (c q.2)) (L.g (c q.1) (c q.2))).val * gs (𝟙 X) y _ (b q.2)) = 0 := by
    rintro ⟨x, w⟩
    have l : V x ⊓ V w ≤ L.U (c x) ⊓ L.U (c w) := inf_le_inf (hle x) (hle w)
    have hx : ∀ {Z : Scheme.{0}} (r : Z ⟶ X) (y : Z), r y ∈ V x ⊓ V w → gs r y (V x ⊓ V w) (resG X inf_le_left (b x) -
        resG X l (L.g (c x) (c w)).val * resG X inf_le_right (b w)) =
        gs r y _ (b x) - (gm r y (L.U (c x) ⊓ L.U (c w)) (L.g (c x) (c w))).val * gs r y _ (b w) := fun r y hy => by
      rw [gs_sub _ y _ hy, gs_mul _ y _ hy, gs_res _ y _ hy, gs_res _ y _ hy, gs_res _ y _ hy, gs_unit r y _ (l hy)]
    obtain ⟨e, he, h⟩ := exists_const_mul_eq_zero H ((hV x).inf (hV w)) _ fun z hz => (hx φ z hz).trans (by
      rw [hb x z hz.1, hb w z hz.2, pull_sec_trans s z (l hz).1 (l hz).2]
      ring)
    exact ⟨e, he, fun y hy => (congrArg _ (hx (𝟙 X) y hy)).symm.trans (h y hy)⟩
  choose e he hk using kill
  obtain ⟨θ, hθ⟩ := exists_sec_of_refinement hL V c hle hc (fun x => constFn p _ (∏ q, e q) * b x)
    fun y x w hx hw => by
      have h := hk (x, w) y ⟨hx, hw⟩
      rw [gs_mul _ y _ hx, gs_mul _ y _ hw, gs_constFn p _ _ y hx, gs_constFn p _ _ y hw, Category.id_comp,
        ← Finset.mul_prod_erase _ e (Finset.mem_univ (x, w)), cst_mul]
      linear_combination cst p y (∏ q ∈ Finset.univ.erase (x, w), e q) * h
  refine ⟨θ, Opens.ext (Set.ext fun z => ?_)⟩
  obtain ⟨x, hx⟩ := hc (φ z)
  have h₁ := congrArg (φ.stalkMap z).hom (hθ (φ z) (c x) x (hle x hx) hx)
  rw [map_mul, ← gs_stalkMap φ z _ (hle x hx), ← gs_stalkMap φ z _ hx, gs_mul φ z _ hx, gs_constFn p _ φ z hx,
    hb x z hx] at h₁
  refine (mem_nonzeroLocus_iff_pull θ φ z (hle x hx)).trans (Iff.trans ?_
    (mem_nonzeroLocus_iff_isUnit s (k := fun _ => c x) (mem_pull.2 (hle x hx))).symm)
  rw [h₁, IsUnit.mul_iff, IsUnit.mul_iff, IsUnit.mul_iff]
  exact ⟨fun h => h.2.2.2, fun h => ⟨(Units.isUnit _).map _,
    isUnit_cst H.w z (Finset.prod_ne_zero_iff.2 fun q _ => he q),
    isUnit_cst H.w z (Finset.prod_ne_zero_iff.2 fun q _ => hd q), h⟩⟩

theorem exists_basicOpen_le {V : (Sp R).Opens} (hV : genericPoint (Sp R) ∈ V) :
    ∃ f : R, f ≠ 0 ∧ PrimeSpectrum.basicOpen f ≤ V := by
  obtain ⟨_, ⟨f, rfl⟩, hf, hle⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hV V.isOpen
  refine ⟨f, ?_, hle⟩
  rintro rfl
  exact (PrimeSpectrum.mem_basicOpen _ _).1 hf (Ideal.zero_mem _)


omit [IsDomain R] in
theorem isAffineOpen_inf_preimage_basicOpen (p : X ⟶ Sp R) {U : X.Opens} (hU : IsAffineOpen U) (f : R) :
    IsAffineOpen (U ⊓ p ⁻¹ᵁ PrimeSpectrum.basicOpen f) := by
  have := hU.basicOpen (constFn p U f)
  have e := Scheme.basicOpen_appLE p U ⊤ le_top ((Scheme.ΓSpecIso (CommRingCat.of R)).inv f)
  rw [basicOpen_eq_of_affine] at e
  exact e ▸ this


set_option backward.isDefEq.respectTransparency false in
theorem exists_isAffineOpen_preimage_basicOpen (H : IsPullback φ π p (spMap (algebraMap R K))) [QuasiCompact p]
    [QuasiSeparated p] [IsAffine X'] : ∃ f : R, f ≠ 0 ∧ IsAffineOpen (p ⁻¹ᵁ PrimeSpectrum.basicOpen f) := by
  obtain ⟨e, he⟩ := IsGenericPointHom.fractionField R K
  have H' : IsPullback φ (π ≫ e.hom) p ((Sp R).fromSpecStalk (genericPoint (Sp R))) := by
    have h₀ : IsPullback (spMap (algebraMap R K)) e.hom (𝟙 _) ((Sp R).fromSpecStalk (genericPoint (Sp R))) :=
      IsPullback.of_vert_isIso ⟨(Category.comp_id _).trans he.symm⟩
    have := H.paste_vert h₀
    rwa [Category.comp_id] at this
  obtain ⟨hc⟩ := StalkLimit.nonempty_isLimit H'
  have (V : StalkLimit.AffNhd (genericPoint (Sp R))) : CompactSpace ((StalkLimit.diagram _ p).obj V) := by
    have : IsAffine V.1.toScheme := V.2.2
    exact QuasiCompact.compactSpace_of_compactSpace (pullback.snd p V.1.ι)
  have (V : StalkLimit.AffNhd (genericPoint (Sp R))) : QuasiSeparatedSpace ((StalkLimit.diagram _ p).obj V) := by
    have : IsAffine V.1.toScheme := V.2.2
    exact quasiSeparatedSpace_of_quasiSeparated (pullback.snd p V.1.ι)
  have : IsAffine (StalkLimit.cone H').pt := ‹IsAffine X'›
  obtain ⟨V, hV⟩ := Scheme.exists_isAffine_of_isLimit _ _ hc
  have : IsAffine (pullback p V.1.ι) := hV
  have h₁ : IsAffineOpen (p ⁻¹ᵁ V.1) := IsAffine.of_isIso (pullbackRestrictIsoRestrict p V.1).inv
  obtain ⟨f, hf, hle⟩ := exists_basicOpen_le V.2.1
  refine ⟨f, hf, ?_⟩
  have h₂ := isAffineOpen_inf_preimage_basicOpen p h₁ f
  rwa [inf_eq_right.2 (p.preimage_mono hle)] at h₂

theorem exists_preimage_basicOpen_le (H : IsPullback φ π p (spMap (algebraMap R K))) [UniversallyClosed p]
    {U : X.Opens} (hU : φ ⁻¹ᵁ U = ⊤) : ∃ f : R, f ≠ 0 ∧ p ⁻¹ᵁ PrimeSpectrum.basicOpen f ≤ U := by
  have hc : IsClosed (p '' (U : Set X)ᶜ) := p.isClosedMap _ U.isOpen.isClosed_compl
  obtain ⟨f, hf, hle⟩ := exists_basicOpen_le (V := ⟨_, hc.isOpen_compl⟩) (by
    rintro ⟨x, hx, e⟩
    obtain ⟨y, hy⟩ : genericPoint (Sp R) ∈ Set.range (spMap (algebraMap R K)) :=
      (IsGenericPointHom.fractionField R K).range_eq.ge rfl
    obtain ⟨z, rfl, -⟩ := Scheme.exists_preimage_of_isPullback H x y (e.trans hy.symm)
    exact hx (hU.ge (Set.mem_univ z)))
  exact ⟨f, hf, fun x hx => by_contra fun h => hle hx ⟨x, h, rfl⟩⟩

theorem exists_cover (H : IsPullback φ π p (spMap (algebraMap R K))) [IsProper p] {L : LB X} (hL : L.IsLB)
    (h : IsAmpleLB (L.pull φ)) :
    ∃ f : R, f ≠ 0 ∧ ∃ n, 1 ≤ n ∧ ∃ (N : ℕ) (θ : Fin (N + 1) → (lbPow L n).Sec),
      p ⁻¹ᵁ PrimeSpectrum.basicOpen f ≤ ⨆ i, Out.nonzeroLocus (θ i) ∧
      ∀ i, IsAffineOpen (Out.nonzeroLocus (θ i) ⊓ p ⁻¹ᵁ PrimeSpectrum.basicOpen f) := by
  classical
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from p]; infer_instance⟩
  obtain ⟨n, hn, N, s, hs, ha⟩ := h.exists_cover
  have hP := isLB_lbPow hL n
  choose t ht using fun i => exists_sec_nonzeroLocus_eq_of_lbIso (LB.isLB_pull hP φ) (isLB_lbPow h.isLB n)
    (lbIso_lbPow_pull hL φ n).symm (s i)
  choose θ hθ using fun i => exists_sec_preimage_nonzeroLocus_eq H hP (t i)
  obtain ⟨f₀, hf₀, h₀⟩ := exists_preimage_basicOpen_le H (U := ⨆ i, Out.nonzeroLocus (θ i)) (by
    rw [Scheme.Hom.preimage_iSup, ← hs]
    exact iSup_congr fun i => (hθ i).trans (ht i))
  have aff : ∀ i, ∃ g : R, g ≠ 0 ∧ IsAffineOpen (Out.nonzeroLocus (θ i) ⊓ p ⁻¹ᵁ PrimeSpectrum.basicOpen g) := fun i => by
    have := isAffineHom_nonzeroLocus_ι hP (θ i)
    have : IsAffine (φ ⁻¹ᵁ Out.nonzeroLocus (θ i)) := by
      rw [hθ, ht]; exact ha i
    obtain ⟨g, hg, h₁⟩ := exists_isAffineOpen_preimage_basicOpen
      ((isPullback_morphismRestrict φ (Out.nonzeroLocus (θ i))).paste_vert H)
    refine ⟨g, hg, ?_⟩
    have h₂ : IsAffineOpen ((Out.nonzeroLocus (θ i)).ι ''ᵁ (Out.nonzeroLocus (θ i)).ι ⁻¹ᵁ
        p ⁻¹ᵁ PrimeSpectrum.basicOpen g) := h₁.image_of_isOpenImmersion (Out.nonzeroLocus (θ i)).ι
    rwa [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι] at h₂
  choose g hg hga using aff
  refine ⟨f₀ * ∏ i, g i, mul_ne_zero hf₀ (Finset.prod_ne_zero_iff.2 fun i _ => hg i), n, hn, N, θ,
    (p.preimage_mono (PrimeSpectrum.basicOpen_mul_le_left _ _)).trans h₀, fun i => ?_⟩
  have h₁ := isAffineOpen_inf_preimage_basicOpen p (hga i) (f₀ * ∏ i, g i)
  have hle : PrimeSpectrum.basicOpen (f₀ * ∏ i, g i) ≤ PrimeSpectrum.basicOpen (g i) := by
    rw [← Finset.mul_prod_erase _ g (Finset.mem_univ i), mul_left_comm]
    exact PrimeSpectrum.basicOpen_mul_le_left _ _
  rwa [inf_assoc, inf_eq_right.2 (p.preimage_mono hle)] at h₁

theorem relAmple_spread : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (A : Over (Sp R)) (M : LB A.left), IsProper A.hom → M.IsLB → Out.RelAmple (Over.mk (pullback.snd A.hom (spMap (algebraMap R K)))) (M.pull (pullback.fst A.hom (spMap (algebraMap R K)))) → ∃ f : R, f ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (φ : R →+* R'), IsUnit (φ f) → Out.RelAmple (Over.mk (pullback.snd A.hom (spMap φ))) (M.pull (pullback.fst A.hom (spMap φ))) := by
  intro R K _ _ _ _ _ _ A M _ hM h
  obtain ⟨f, hf, n, hn, N, θ, hc, ha⟩ := exists_cover (IsPullback.of_hasPullback A.hom (spMap (algebraMap R K))) hM
    (isAmpleLB_of_relAmple_of_isAffine _ (LB.isLB_pull hM _) h)
  refine ⟨f, hf, fun R' _ φ hu => ?_⟩
  let ψ := pullback.fst A.hom (spMap φ)
  have : IsProper (Over.mk (pullback.snd A.hom (spMap φ))).hom := inferInstanceAs (IsProper (pullback.snd _ _))
  have : IsAffineHom ψ := MorphismProperty.of_isPullback (P := @IsAffineHom)
    (IsPullback.of_hasPullback A.hom (spMap φ)).flip inferInstance
  have hD : ∀ z, ψ z ∈ A.hom ⁻¹ᵁ PrimeSpectrum.basicOpen f := fun z => by
    have e : A.hom (ψ z) = spMap φ (pullback.snd A.hom (spMap φ) z) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
    show A.hom (ψ z) ∈ PrimeSpectrum.basicOpen f
    rw [e]
    exact fun hm => (pullback.snd A.hom (spMap φ) z).isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hm hu)
  have hs : ⨆ i, Out.nonzeroLocus (secPowPull (θ i) ψ) = ⊤ := top_le_iff.1 fun z _ => by
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hc (hD z))
    exact Opens.mem_iSup.2 ⟨i, (nonzeroLocus_secPowPull (θ i) ψ).ge hi⟩
  have ha' : ∀ i, IsAffineOpen (Out.nonzeroLocus (secPowPull (θ i) ψ)) := fun i => by
    have e : ψ ⁻¹ᵁ (Out.nonzeroLocus (θ i) ⊓ A.hom ⁻¹ᵁ PrimeSpectrum.basicOpen f) =
        Out.nonzeroLocus (secPowPull (θ i) ψ) :=
      (le_antisymm (fun z hz => hz.1) fun z hz => ⟨hz, hD z⟩).trans (nonzeroLocus_secPowPull (θ i) ψ).symm
    exact e ▸ (ha i).preimage ψ
  refine (relAmple_iff_isAmpleLB_of_isAffine _ (LB.isLB_pull hM _)).2 ?_
  refine ⟨LB.isLB_pull hM _, ⟨?_⟩, ?_⟩
  · have e : (Set.univ : Set (pullback A.hom (spMap φ) : Scheme)) = ⋃ i, (Out.nonzeroLocus (secPowPull (θ i) ψ) : Set (pullback A.hom (spMap φ) : Scheme)) := by
      rw [← Opens.coe_iSup, hs, Opens.coe_top]
    rw [e]
    exact isCompact_iUnion fun i => (ha' i).isCompact
  · intro x
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hs.ge (Set.mem_univ x))
    exact ⟨n, hn, secPowPull (θ i) ψ, hi, ha' i⟩

end GlobalTheory.AmpleSpread
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsOfFinOrderOfQuadratic
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.CMSpreadCompare

open GlobalTheory.PureType

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

section Unif

theorem exists_pointEquiv {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') {s : T.left ⟶ S} (hs : s = T.hom ≫ f) :
    ∃ p : (T ⟶ G') ≃* (Over.mk s ⟶ G), ∀ x, (p x).left = x.left ≫ φ := by
  subst hs
  exact ⟨MulEquiv.ofBijective (pushHom h T) ⟨fun _ _ e => eq_of_comp_eq h.1 (congrArg (fun z => z.left) e), fun p =>
    ⟨Over.homMk (h.1.lift p.left T.hom (Over.w p)) (h.1.lift_snd _ _ _),
      Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩⟩, fun _ => rfl⟩

theorem isHolTo_postcomp {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X Y : Scheme.{0}} {B : Set V}
    {y : V → (Sp ℂ ⟶ X)} (h : IsHolTo B y) (φ : X ⟶ Y) : IsHolTo B (fun b => y b ≫ φ) := by
  intro U s
  rw [show (fun b => valAt' (y b ≫ φ) U s) = fun b => valAt' (y b) (φ ⁻¹ᵁ U) ((φ.app U).hom s) from
    funext fun b => (valAt'_comp _ φ U s).symm]
  exact h (φ ⁻¹ᵁ U) _

variable {k : Type} [Field k] {κ : k →+* ℂ} {A : Over (Sp k)} [GrpObj A] {PC : Out.PolAV (Sp ℂ)}
  {ψ : PC.A.left ⟶ A.left} (hψ : IsGrpPullback PC.A A (spMap κ) ψ) (u : HolUnif PC.A PC.L PC.g)

include hψ

end Unif

section Quadratic

end Quadratic

section Transport

variable {D : Datum H} {R : Type} [CommRing R] {t : SAB H (Sp R)} {B B' : Over (Sp R)} [GrpObj B] [GrpObj B']
  {M : LB B.left} {M' : LB B'.left} {L : Submodule (𝓞 E) D.La} {ρ : R} {S S' : Set L} {φ : L → (B ⟶ t.G)}

end Transport

section Multiplication

end Multiplication

end GlobalTheory.CMSpreadCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAffineOpenNonzeroLocusOfFibrewiseAmple
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAffineOpenNonzeroLocusOfFibrewiseAmple
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.FibreAmple

theorem isAffineOpen_preimage_nonzeroLocus {k : Type} [CommRing k] {X Y : Scheme.{0}} (g : Y ⟶ Sp k) [IsProper g]
    (π : Y ⟶ X) {M : LB X} (hM : M.IsLB) (hA : Out.RelAmple (Over.mk g) (M.pull π)) {d : ℕ} (hd : 1 ≤ d)
    (u : LB.Sec (pw M d)) : IsAffineOpen (π ⁻¹ᵁ Out.nonzeroLocus u) := by
  let s : (lbPow M d).Sec := powSecMk d u.f fun i j =>
    (u.compat i j).trans (congrArg (· * _) (by
      change (M.g i j ^ (d : ℤ)).val = _
      rw [zpow_natCast, Units.val_pow_eq_pow_val]))
  have hs : Out.nonzeroLocus s = Out.nonzeroLocus u := nonzeroLocus_powSecMk _ _ _
  have h := isAmpleLB_of_relAmple_of_isAffine (Over.mk g) (LB.isLB_pull hM π) hA
  have := IsAmpleLB.isAffineOpen_nonzeroLocus g h hd (secPowPull s π)
  rwa [nonzeroLocus_secPowPull, hs] at this

theorem isFinite_of_fibres {R : Type} [CommRing R] {X : Scheme.{0}} {m : ℕ} (φ : X ⟶ PSpace R m)
    (f : X ⟶ Sp R) [IsProper f] (hf : φ ≫ PSpace.str R m = f)
    (H : ∀ q : Ideal R, q.IsPrime → ∃ (k : Type) (_ : Field k) (β : R →+* k), RingHom.ker β = q ∧
      ∀ i, IsAffineOpen (pullback.fst f (spMap β) ⁻¹ᵁ (φ ⁻¹ᵁ ProjSpace.chart R m i))) : IsFinite φ := by
  have := isProper_str R m
  have : IsProper (φ ≫ PSpace.str R m) := by rw [hf]; infer_instance
  have : IsProper φ := .of_comp φ (PSpace.str R m)
  suffices LocallyQuasiFinite φ from .of_isProper_of_locallyQuasiFinite _
  refine LocallyQuasiFinite.of_finite_preimage_singleton _ fun p => ?_
  obtain ⟨k, _, β, hβ, hk⟩ := H (PSpace.str R m p).asIdeal (PSpace.str R m p).isPrime
  have B := ProjSpace.isPullback_baseChange m β
  let φ' : pullback f (spMap β) ⟶ PSpace k m :=
    B.lift (pullback.fst f (spMap β) ≫ φ) (pullback.snd f (spMap β))
      (by rw [Category.assoc, hf, pullback.condition])
  have e₁ : φ' ≫ ProjSpace.baseChange m β = pullback.fst f (spMap β) ≫ φ := B.lift_fst _ _ _
  have e₂ : φ' ≫ PSpace.str k m = pullback.snd f (spMap β) := B.lift_snd _ _ _
  have P : IsPullback (pullback.fst f (spMap β)) φ' φ (ProjSpace.baseChange m β) :=
    IsPullback.of_bot (by rw [e₂, hf]; exact IsPullback.of_hasPullback f (spMap β)) e₁.symm B
  have : IsProper φ' := MorphismProperty.of_isPullback (P := @IsProper) P inferInstance
  have : IsAffineHom φ' := isAffineHom_of_forall_exists_isAffineOpen _ fun y => by
    obtain ⟨i, hi⟩ := ProjSpace.exists_mem_chart k m y
    refine ⟨_, hi, ProjSpace.isAffineOpen_chart k m i, ?_⟩
    rw [← ProjSpace.baseChange_preimage_chart m β i, ← Scheme.Hom.comp_preimage, e₁, Scheme.Hom.comp_preimage]
    exact hk i
  have : IsFinite φ' := IsFinite.iff_isProper_and_isAffineHom.2 ⟨inferInstance, inferInstance⟩
  obtain ⟨p', hp', -⟩ := Scheme.exists_preimage_of_isPullback B p (⊥ : PrimeSpectrum k)
    (PrimeSpectrum.ext hβ.symm)
  refine ((φ'.finite_preimage_singleton p').image (pullback.fst f (spMap β))).subset fun x hx => ?_
  obtain ⟨z, h₁, h₂⟩ := Scheme.exists_preimage_of_isPullback P x p' (hx.trans hp'.symm)
  exact ⟨z, h₂, h₁⟩

theorem isAffineOpen_nonzeroLocus_of_fibres : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R) (M : LB X) (d : ℕ) (m : ℕ) (u : Fin (m + 1) → LB.Sec (pw M d)), 1 ≤ d → IsProper f → M.IsLB → (⨆ i, Out.nonzeroLocus (u i) = ⊤) → (∀ q : Ideal R, q.IsPrime → ∃ (k : Type) (_ : Field k) (β : R →+* k), RingHom.ker β = q ∧ Out.RelAmple (Over.mk (pullback.snd f (spMap β))) (M.pull (pullback.fst f (spMap β)))) → ∀ i, IsAffineOpen (Out.nonzeroLocus (u i)) := by
  intro R _ X f M d m u hd _ hM hu H i
  have : IsFinite (ProjSpace.toProj f u hu) :=
    isFinite_of_fibres (ProjSpace.toProj f u hu) f (ProjSpace.toProj_str f u hu) fun q hq => by
      obtain ⟨k, _, β, hβ, hA⟩ := H q hq
      refine ⟨k, _, β, hβ, fun j => ?_⟩
      rw [ProjSpace.toProj_preimage_chart]
      exact isAffineOpen_preimage_nonzeroLocus _ _ hM hA hd (u j)
  rw [← ProjSpace.toProj_preimage_chart f u hu]
  exact (ProjSpace.isAffineOpen_chart R m i).preimage _

end GlobalTheory.FibreAmple
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAffineOpenNonzeroLocusOfFibrewiseAmpleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.isAffineOpen_nonzeroLocus_of_fibrewise_ample : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R) (M : LB X) (d : ℕ) (m : ℕ) (u : Fin (m + 1) → LB.Sec (pw M d)), 1 ≤ d → IsProper f → M.IsLB → (⨆ i, Out.nonzeroLocus (u i) = ⊤) → (∀ q : Ideal R, q.IsPrime → ∃ (k : Type) (_ : Field k) (β : R →+* k), RingHom.ker β = q ∧ Out.RelAmple (Over.mk (pullback.snd f (spMap β))) (M.pull (pullback.fst f (spMap β)))) → ∀ i, IsAffineOpen (Out.nonzeroLocus (u i)) := by
  first | exact @GlobalTheory.FibreAmple.isAffineOpen_nonzeroLocus_of_fibres | exact GlobalTheory.FibreAmple.isAffineOpen_nonzeroLocus_of_fibres | (intros; apply GlobalTheory.FibreAmple.isAffineOpen_nonzeroLocus_of_fibres <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsProjOverIsPullbackOfIsLocalization
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.ProjClosure

theorem exists_isProjOver_isPullback_of_isLocalization {O R : Type} [CommRing O] [CommRing R] [Algebra O R]
    (M : Submonoid O) [IsLocalization M R] {X : Scheme.{0}} (s : X ⟶ Sp R) (hs : IsProjOver s) :
    ∃ (X' : Scheme.{0}) (s' : X' ⟶ Sp O) (i : X ⟶ X'),
      IsProjOver s' ∧ IsPullback i s s' (spMap (algebraMap O R)) := by
  obtain ⟨N, c, hc, rfl⟩ := hs
  have P := GlobalTheory.ProjSpace.isPullback_baseChange N (algebraMap O R)
  have hf : Flat (spMap (algebraMap O R)) := GlobalTheory.flat_specMap_localization M R
  have hm : Mono (spMap (algebraMap O R)) := GlobalTheory.mono_specMap_localization M R
  have hq : QuasiCompact (spMap (algebraMap O R)) := inferInstance
  have : Flat (GlobalTheory.ProjSpace.baseChange N (algebraMap O R)) := MorphismProperty.of_isPullback P.flip hf
  have : Mono (GlobalTheory.ProjSpace.baseChange N (algebraMap O R)) :=
    (MorphismProperty.monomorphisms _).of_isPullback P.flip hm
  have : QuasiCompact (GlobalTheory.ProjSpace.baseChange N (algebraMap O R)) :=
    MorphismProperty.of_isPullback P.flip hq
  let j := c ≫ GlobalTheory.ProjSpace.baseChange N (algebraMap O R)
  have H := GlobalTheory.isPullback_toImage_of_isClosedImmersion j c _ rfl
  exact ⟨j.image, j.imageι ≫ PSpace.str O N, j.toImage, ⟨N, j.imageι, inferInstance, rfl⟩,
    H.flip.paste_vert P⟩

theorem exists_projective_closure : ∀ (O R : Type) [CommRing O] [CommRing R] [Algebra O R] (a : O) [IsLocalization.Away a R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsProjOver s → ∃ (X' : Scheme.{0}) (s' : X' ⟶ Sp O) (i : X ⟶ X'), IsProjOver s' ∧ IsPullback i s s' (spMap (algebraMap O R)) :=
  fun _ _ _ _ _ a _ _ s hs =>
    exists_isProjOver_isPullback_of_isLocalization (Submonoid.powers a) s hs

end GlobalTheory.ProjClosure
end
