module

public import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsRayFieldInRestrictScalars
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletedLatticeStabilizerCompactOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletedLatticeStabilizerCompactOpen
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open Formalism.MainNotions.S hiding Af
open scoped TensorProduct Topology

namespace GlobalTheory.Mem.Vol.StabGroup

theorem exists_compact_latHat (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {M : ℕ} (L : Submodule (𝓞 E) (Fin M → E)) (hL : L.FG) :
    ∃ C : Set (Fin M → Af F ⊗[F] E), IsCompact C ∧ ∀ y ∈ latHat F E (L : Set (Fin M → E)), y ∈ C := by
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (Af F ⊗[F] E) := IsModuleTopology.toContinuousAdd (Af F) _
  haveI : ContinuousSMul (Af F) (Af F ⊗[F] E) := IsModuleTopology.toContinuousSMul _ _
  have hZ : (L.restrictScalars ℤ).FG := hL.restrictScalars
  obtain ⟨m, x, hx⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hZ
  let g : (Fin m → Af F) → Fin M → Af F ⊗[F] E := fun c i => ∑ k, c k ⊗ₜ[F] x k i
  have hg : Continuous g := by
    refine continuous_pi fun i => continuous_finsetSum _ fun k _ => ?_
    have : (fun c : Fin m → Af F => c k ⊗ₜ[F] x k i) = fun c => c k • ((1 : Af F) ⊗ₜ[F] x k i) := by
      funext c
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this]
    have hk : Continuous fun c : Fin m → Af F => c k := continuous_apply k
    have ho : Continuous fun _ : Fin m → Af F => (1 : Af F) ⊗ₜ[F] x k i := continuous_const
    exact hk.smul ho
  have hI : IsCompact (intAf F) := GlobalTheory.AdeleCocompact.isCompact_integral F
  refine ⟨g '' Set.pi Set.univ fun _ => intAf F, (isCompact_univ_pi fun _ => hI).image hg, fun y hy => ?_⟩
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, v, hv, rfl⟩ := hy
    have hv' : v ∈ Submodule.span ℤ (Set.range x) := by rw [hx]; exact hv
    obtain ⟨n, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hv'
    refine ⟨fun k => n k • a, fun k _ w => ?_, ?_⟩
    · rw [map_zsmul]
      exact zsmul_mem (ha w) _
    · funext i
      simp only [g, Finset.sum_apply, Pi.smul_apply, TensorProduct.tmul_sum, TensorProduct.smul_tmul]
  | zero =>
    refine ⟨0, fun k _ w => ?_, ?_⟩
    · rw [Pi.zero_apply, map_zero]
      exact zero_mem _
    · funext i
      simp [g]
  | add y z _ _ hy hz =>
    obtain ⟨c, hc, rfl⟩ := hy
    obtain ⟨d, hd, rfl⟩ := hz
    refine ⟨c + d, fun k _ w => ?_, ?_⟩
    · rw [Pi.add_apply, map_add (f := _)]
      exact add_mem (hc k trivial w) (hd k trivial w)
    · funext i
      simp only [g, Pi.add_apply, TensorProduct.add_tmul, Finset.sum_add_distrib]
  | neg y _ hy =>
    obtain ⟨c, hc, rfl⟩ := hy
    refine ⟨-c, fun k _ w => ?_, ?_⟩
    · rw [Pi.neg_apply, map_neg]
      exact neg_mem (hc k trivial w)
    · funext i
      simp only [g, Pi.neg_apply, TensorProduct.neg_tmul, Finset.sum_neg_distrib]

theorem exists_compact_entries (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {M : ℕ} (L : Submodule (𝓞 E) (Fin M → E)) (hL : L.FG)
    (hsp : Submodule.span E (L : Set (Fin M → E)) = ⊤) :
    ∃ C : Set (Af F ⊗[F] E), IsCompact C ∧ ∀ A : Matrix (Fin M) (Fin M) (Af F ⊗[F] E),
      (∀ y ∈ latHat F E (L : Set (Fin M → E)), A.mulVec y ∈ latHat F E (L : Set (Fin M → E))) →
      ∀ i j, A i j ∈ C := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Af F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Af F) _
  obtain ⟨C, hC, hLC⟩ := exists_compact_latHat F E L hL
  choose d hd hdL using fun j => GlobalTheory.AdLat.OpenLat.exists_denom L hsp (Pi.single j 1)
  refine ⟨⋃ p : Fin M × Fin M, (fun y : Fin M → Af F ⊗[F] E =>
      y p.1 * ((1 : Af F) ⊗ₜ[F] ((d p.2 : E)⁻¹))) '' C,
    isCompact_iUnion fun p => hC.image ((continuous_apply p.1).mul continuous_const), fun A hA i j => ?_⟩
  have h1 : (1 : Af F) ∈ intAf F := fun w => by rw [map_one]; exact one_mem _
  have hy : (fun k => (1 : Af F) ⊗ₜ[F] (d j • (Pi.single j 1 : Fin M → E)) k) ∈
      latHat F E (L : Set (Fin M → E)) := AddSubgroup.subset_closure ⟨1, h1, _, hdL j, rfl⟩
  refine Set.mem_iUnion.2 ⟨(i, j), _, hLC _ (hA _ hy), ?_⟩
  have hd0 : (d j : E) ≠ 0 := Nat.cast_ne_zero.2 (hd j).ne'
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single j (fun k _ hk => by simp [hk]) (by simp), mul_assoc,
    Algebra.TensorProduct.tmul_mul_tmul]
  simp only [Pi.smul_apply, Pi.single_eq_same, nsmul_eq_mul, mul_one, mul_inv_cancel₀ hd0]
  rw [← Algebra.TensorProduct.one_def, mul_one]

theorem congr_mem_nhds (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG) (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (N : ℕ) (hN : 0 < N) :
    {m : Matrix (Fin n) (Fin n) (Af F ⊗[F] E) | ∀ z ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)),
      ∃ y ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)), m.mulVec z - z = N • y} ∈
      𝓝 (1 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) := by
  have : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have : IsTopologicalRing (Af F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Af F) _
  have ho : IsOpen {z : Fin n → Af F ⊗[F] E | ∃ y ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)), z = N • y} :=
    (GlobalTheory.AdLat.OpenLat.isOpen_nsmul_hat F E n L hL).1 N hN
  have hfz : (L.restrictScalars ℤ).FG := by
    have : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.mpr hfg
    have : Module.Finite ℤ L := Module.Finite.trans (𝓞 E) L
    exact (Module.Finite.iff_fg (N := L.restrictScalars ℤ)).mp (inferInstanceAs (Module.Finite ℤ L))
  obtain ⟨s, hs⟩ := hfz
  have hev : ∀ᶠ m : Matrix (Fin n) (Fin n) (Af F ⊗[F] E) in 𝓝 1, ∀ x ∈ s,
      ∃ y ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)),
        m.mulVec (GlobalTheory.AdLat.fv F x) - GlobalTheory.AdLat.fv F x = N • y := by
    rw [Filter.eventually_all_finset]
    intro x _
    have hc : Continuous fun m : Matrix (Fin n) (Fin n) (Af F ⊗[F] E) =>
        m.mulVec (GlobalTheory.AdLat.fv F x) - GlobalTheory.AdLat.fv F x :=
      (continuous_id.matrix_mulVec continuous_const).sub continuous_const
    exact (ho.preimage hc).mem_nhds ⟨0, zero_mem _, by simp⟩
  refine Filter.mem_of_superset hev fun m hm => ?_
  have hsm : ∀ a : Af F, (∀ v, a v ∈ v.adicCompletionIntegers F) →
      ∀ y ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)), a • y ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)) := by
    intro a ha y hy
    induction hy using AddSubgroup.closure_induction with
    | mem x hx =>
      obtain ⟨b, hb, x, hx, rfl⟩ := hx
      exact AddSubgroup.subset_closure ⟨a * b, fun v => mul_mem (ha v) (hb v), x, hx, rfl⟩
    | zero => rw [smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | neg x _ hx => rw [smul_neg]; exact neg_mem hx
  have hadd : ∀ z w : Fin n → Af F ⊗[F] E,
      (∃ y ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)), m.mulVec z - z = N • y) →
      (∃ y ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)), m.mulVec w - w = N • y) →
      ∃ y ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)), m.mulVec (z + w) - (z + w) = N • y := by
    rintro z w ⟨y, hy, h⟩ ⟨y', hy', h'⟩
    exact ⟨y + y', add_mem hy hy', by rw [smul_add, ← h, ← h', Matrix.mulVec_add]; abel⟩
  have hx : ∀ x ∈ Submodule.span ℤ (s : Set (Fin n → E)), ∃ y ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E)),
      m.mulVec (GlobalTheory.AdLat.fv F x) - GlobalTheory.AdLat.fv F x = N • y := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact hm x hx
    | zero =>
      have : GlobalTheory.AdLat.fv F (0 : Fin n → E) = 0 := funext fun i => TensorProduct.tmul_zero _ _
      exact ⟨0, zero_mem _, by simp [this]⟩
    | add x y _ _ hx hy =>
      have : GlobalTheory.AdLat.fv F (x + y) = GlobalTheory.AdLat.fv F x + GlobalTheory.AdLat.fv F y :=
        funext fun i => TensorProduct.tmul_add _ _ _
      rw [this]; exact hadd _ _ hx hy
    | smul c x _ hx =>
      obtain ⟨y, hy, h⟩ := hx
      have : GlobalTheory.AdLat.fv F (c • x) = c • GlobalTheory.AdLat.fv F x :=
        funext fun i => map_zsmul (TensorProduct.mk F (Af F) E 1) c (x i)
      refine ⟨c • y, zsmul_mem hy c, ?_⟩
      rw [this, Matrix.mulVec_smul, ← smul_sub, h, smul_comm]
  intro z hz
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hxL, rfl⟩ := hz
    obtain ⟨y, hy, h⟩ := hx x (by rw [hs]; exact hxL)
    have : (fun i => a ⊗ₜ[F] x i) = a • GlobalTheory.AdLat.fv F x := by
      funext i
      simp [GlobalTheory.AdLat.fv, TensorProduct.smul_tmul']
    refine ⟨a • y, hsm a ha y hy, ?_⟩
    rw [this, Matrix.mulVec_smul, ← smul_sub, h, smul_comm]
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add z w _ _ hz hw => exact hadd z w hz hw
  | neg z _ hz =>
    obtain ⟨y, hy, h⟩ := hz
    exact ⟨-y, neg_mem hy, by rw [smul_neg, ← h, Matrix.mulVec_neg]; abel⟩

noncomputable def stabGrp (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (L : Set (Fin M → E)) :
    Subgroup (HA (Af F) σ J) where
  carrier := {h | StabHat F L (HA.mat (Af F) σ J h).1}
  one_mem' := fun y => by
    change _ ↔ (1 : Matrix (Fin M) (Fin M) (Af F ⊗[F] E)).mulVec y ∈ _
    rw [Matrix.one_mulVec]
  mul_mem' := by
    intro a b ha hb y
    change _ ↔ ((HA.mat (Af F) σ J a).1 * (HA.mat (Af F) σ J b).1).mulVec y ∈ _
    rw [← Matrix.mulVec_mulVec]
    exact (hb y).trans (ha _)
  inv_mem' := by
    intro a ha y
    change _ ↔ ((HA.mat (Af F) σ J a)⁻¹).1.mulVec y ∈ _
    rw [ha (((HA.mat (Af F) σ J a)⁻¹).1.mulVec y), Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.one_mulVec]

theorem exists_compact_open_stab : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (L : Submodule (𝓞 E) (Fin M → E)), L.FG → Submodule.span E (L : Set (Fin M → E)) = ⊤ → ∃ K : Subgroup (HA (Af F) σ J), (∀ h, h ∈ K ↔ StabHat F (L : Set (Fin M → E)) ((HA.mat (Af F) σ J h : GL (Fin M) (Af F ⊗[F] E)) : Matrix (Fin M) (Fin M) (Af F ⊗[F] E))) ∧ IsOpen (K : Set (HA (Af F) σ J)) ∧ IsCompact (K : Set (HA (Af F) σ J)) := by
  intro F E _ _ _ _ _ σ M J L hfg hsp
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (Af F) (Af F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Af F ⊗[F] E) := IsModuleTopology.isTopologicalRing (Af F) _
  haveI : T2Space (Af F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (Af F)
  haveI : T2Space (Af F ⊗[F] E) := e.isEmbedding.t2Space
  haveI : IsTopologicalGroup (HA (Af F) σ J) := inferInstanceAs (IsTopologicalGroup (HR (Af F) σ J))
  have hcl : IsClosed (HR (Af F) σ J : Set (GL (Fin M) (Af F ⊗[F] E))) := by
    have hv : Continuous fun g : GL (Fin M) (Af F ⊗[F] E) => (g : Matrix (Fin M) (Fin M) (Af F ⊗[F] E)) :=
      Units.continuous_val
    exact isClosed_eq (((hv.matrix_map (GlobalTheory.AdelicUnitaryTop.continuous_sigR (Af F) σ)).matrix_transpose.matrix_mul
      continuous_const).matrix_mul hv) continuous_const
  have hc : Continuous fun h : HA (Af F) σ J => (HA.mat (Af F) σ J h).1 :=
    Units.continuous_val.comp continuous_subtype_val
  have hopen : IsOpen (stabGrp F σ J (L : Set (Fin M → E)) : Set (HA (Af F) σ J)) := by
    have hn := congr_mem_nhds F E M L hfg hsp 1 one_pos
    have h1 := hc.continuousAt (x := 1) |>.preimage_mem_nhds hn
    have h2 := (hc.comp continuous_inv).continuousAt (x := 1) |>.preimage_mem_nhds
      (by rw [Function.comp_apply, inv_one]; exact hn)
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
    refine Filter.mem_of_superset (Filter.inter_mem h1 h2) ?_
    rintro k ⟨hk1, hk2⟩ y
    constructor
    · intro hy
      obtain ⟨w, hw, h⟩ := hk1 y hy
      rw [eq_add_of_sub_eq h]
      exact add_mem (nsmul_mem hw 1) hy
    · intro hy
      obtain ⟨w, hw, h⟩ := hk2 _ hy
      have hk : (HA.mat (Af F) σ J k⁻¹).1 * (HA.mat (Af F) σ J k).1 = 1 :=
        (HA.mat (Af F) σ J k).inv_mul
      rw [Function.comp_apply, Matrix.mulVec_mulVec, hk, Matrix.one_mulVec] at h
      rw [eq_add_of_sub_eq h]
      exact add_mem (nsmul_mem hw 1) hy
  refine ⟨stabGrp F σ J (L : Set (Fin M → E)), fun h => Iff.rfl, hopen, ?_⟩
  obtain ⟨C, hC, hCe⟩ := exists_compact_entries F E L hfg hsp
  let S : Set (Matrix (Fin M) (Fin M) (Af F ⊗[F] E)) := Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => C
  have hS : IsCompact S := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hC
  have hemb := (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin M) (Fin M) (Af F ⊗[F] E))).comp
    hcl.isClosedEmbedding_subtypeVal
  have hK : IsCompact (X := HA (Af F) σ J) _ :=
    hemb.isCompact_preimage (hS.prod (hS.image MulOpposite.continuous_op))
  refine hK.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hopen) fun h hh => ?_
  have hi := (stabGrp F σ J (L : Set (Fin M → E))).inv_mem hh
  exact ⟨fun i _ j _ => hCe _ (fun y hy => (hh y).1 hy) i j,
    (HA.mat (Af F) σ J h⁻¹).1, fun i _ j _ => hCe _ (fun y hy => (hi y).1 hy) i j, rfl⟩

end GlobalTheory.Mem.Vol.StabGroup
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletedLatticeStabilizerCompactOpenStatement
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open Formalism.MainNotions.S hiding Af
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completedLattice_stabilizer_compact_open : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (L : Submodule (𝓞 E) (Fin M → E)), L.FG → Submodule.span E (L : Set (Fin M → E)) = ⊤ → ∃ K : Subgroup (HA (Af F) σ J), (∀ h, h ∈ K ↔ StabHat F (L : Set (Fin M → E)) ((HA.mat (Af F) σ J h : GL (Fin M) (Af F ⊗[F] E)) : Matrix (Fin M) (Fin M) (Af F ⊗[F] E))) ∧ IsOpen (K : Set (HA (Af F) σ J)) ∧ IsCompact (K : Set (HA (Af F) σ J)) := by
  first | exact @GlobalTheory.Mem.Vol.StabGroup.exists_compact_open_stab | exact GlobalTheory.Mem.Vol.StabGroup.exists_compact_open_stab | (intros; apply GlobalTheory.Mem.Vol.StabGroup.exists_compact_open_stab <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLineBundleSectionsGenerateIdealSheaf
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLineBundleSectionsGenerateIdealSheaf
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.ProjBlowup

variable {R : Type} [CommRing R] {N : ℕ} {X : Scheme.{0}}

theorem val_res_pullO_g (φ : X ⟶ PSpace R N) (e : ℕ) (i j : (pullO φ e).ι)
    {V : X.Opens} (h : V ≤ (pullO φ e).U i ⊓ (pullO φ e).U j) :
    ((res h ((pullO φ e).g i j) : Γ(X, V)ˣ) : Γ(X, V)) = pullRatio φ V i (h.trans inf_le_left) j ^ e := by
  have : (((pullO φ e).g i j : Γ(X, (pullO φ e).U i ⊓ (pullO φ e).U j)ˣ) :
      Γ(X, (pullO φ e).U i ⊓ (pullO φ e).U j)) = pullRatio φ _ i inf_le_left j ^ e :=
    Units.val_pow_eq_pow_val _ _
  rw [res, Units.coe_map, MonoidHom.coe_coe, this]
  exact (map_pow _ _ e).trans (congrArg (· ^ e) (resG_pullRatio h))

theorem isLB_pullO (φ : X ⟶ PSpace R N) (e : ℕ) : (pullO φ e).IsLB := {
  cover := (isCoordFamily_pullRatio φ).cover
  g_self i := by
    ext
    rw [val_res_pullO_g, Units.val_one]
    exact (congrArg (· ^ e) pullRatio_self).trans (one_pow e)
  cocycle i j k := by
    ext
    rw [Units.val_mul, val_res_pullO_g, val_res_pullO_g, val_res_pullO_g]
    exact (mul_pow _ _ e).symm.trans (congrArg (· ^ e) pullRatio_mul_pullRatio) }

theorem exists_generates_isLB (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) (s : X ⟶ Sp R)
    (J : X.IdealSheafData) (hs : IsProjOver s) :
    ∃ (L₀ : LB X) (m : ℕ) (σ : Fin (m + 1) → L₀.Sec), L₀.IsLB ∧ Generates J σ := by
  classical
  obtain ⟨N, φ, _, -⟩ := hs
  have fg : ∀ a, (J.ideal (affChart φ a)).FG := fun a => by
    have : IsNoetherianRing Γ(PSpace R N, chart R N a) :=
      isNoetherianRing_of_ringEquiv _ (chartAlgEquiv R N a).toRingEquiv
    have : IsNoetherianRing Γ(X, (affChart φ a).1) :=
      isNoetherianRing_of_surjective _ _ _ (φ.app_surjective _ (isAffineOpen_chart R N a))
    exact IsNoetherian.noetherian _
  change ∀ a, ∃ S : Finset Γ(X, (affChart φ a).1),
    Ideal.span (S : Set _) = J.ideal (affChart φ a) at fg
  choose S hS using fg
  choose e₀ he₀ using fun p : Σ a, S a =>
    exists_form_of_mem φ J p.1 p.2.1 (hS p.1 ▸ Ideal.subset_span p.2.2)
  choose F hF hFa hFb using fun p => he₀ p (Finset.univ.sup e₀) (Finset.le_sup (Finset.mem_univ p))
  let q := (Fintype.equivFinOfCardEq (Fintype.card_option (α := Σ a, S a))).symm
  let τ : Option (Σ a, S a) → (pullO φ (Finset.univ.sup e₀)).Sec := fun o =>
    o.elim (pullFormSec φ 0 (isHomogeneous_zero _ R _)) fun p => pullFormSec φ (F p) (hF p)
  refine ⟨_, _, fun j => τ (q j), isLB_pullO φ _, (isCoordFamily_pullRatio φ).cover, fun k V h => ?_⟩
  have key : J.ideal (affChart φ k) = Ideal.span (Set.range fun j => (τ (q j)).f k) := by
    refine le_antisymm ?_ (Ideal.span_le.2 ?_)
    · rw [← hS k]
      refine Ideal.span_mono fun g hg => ⟨q.symm (some ⟨k, g, hg⟩), ?_⟩
      simp only [q.apply_symm_apply]
      exact hFa ⟨k, g, hg⟩
    · rintro _ ⟨j, rfl⟩
      dsimp only
      cases q j with
      | none =>
        exact (congrArg (· ∈ J.ideal (affChart φ k)) (pullForm_zero (φ := φ) (hi := le_rfl))).mpr (zero_mem _)
      | some p => exact hFb p k
  rw [← J.map_ideal (V := affChart φ k) h, key]
  erw [Ideal.map_span, ← Set.range_comp]
  rfl

end GlobalTheory.ProjBlowup
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLineBundleSectionsGenerateIdealSheafStatement
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lineBundle_sections_generate_idealSheaf : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (J : X.IdealSheafData),
    IsProjOver s → ∃ (L₀ : LB X) (m : ℕ) (σ : Fin (m + 1) → L₀.Sec), L₀.IsLB ∧ GlobalTheory.ProjBlowup.Generates J σ := by
  first | exact @GlobalTheory.ProjBlowup.exists_generates_isLB | exact GlobalTheory.ProjBlowup.exists_generates_isLB | (intros; apply GlobalTheory.ProjBlowup.exists_generates_isLB <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensorNiceRingArtinianReducedOpenUnits
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensorNiceRingArtinianReducedOpenUnits
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx

theorem _root_.GlobalTheory.GaugeEx.isOpenUnits_of_basis {R S ι : Type} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [IsOpenUnits R] [CommRing S] [Algebra R S] [TopologicalSpace S]
    [IsModuleTopology R S] [IsTopologicalRing S] [Fintype ι] (b : Module.Basis ι R S) :
    IsOpenUnits S := by
  classical
  have hR : IsOpenEmbedding (Units.val : Rˣ → R) := IsOpenUnits.isOpenEmbedding_unitsVal
  have hLc : Continuous (fun x : S => Algebra.leftMulMatrix b x) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.leftMulMatrix b).toLinearMap
  have hopenR : IsOpen {r : R | IsUnit r} := hR.isOpen_range
  have hinvR : ContinuousOn (Ring.inverse : R → R) {r | IsUnit r} := by
    rintro _ ⟨u, rfl⟩
    apply ContinuousAt.continuousWithinAt
    rw [← hR.continuousAt_iff]
    have h : (Ring.inverse ∘ Units.val : Rˣ → R) = fun v => ↑v⁻¹ := by
      funext v
      simp [Ring.inverse_unit]
    rw [h]
    exact Units.continuous_coe_inv.continuousAt
  obtain ⟨g, hg⟩ : ∃ g : S → S, ∀ x, g x =
      b.equivFun.symm (Matrix.mulVec (Algebra.leftMulMatrix b x)⁻¹ (b.equivFun 1)) :=
    ⟨_, fun _ => rfl⟩
  have key : ∀ x, IsUnit (Algebra.leftMulMatrix b x).det → x * g x = 1 := by
    intro x hx
    apply b.equivFun.injective
    rw [Module.Basis.equivFun_apply, ← Algebra.leftMulMatrix_mulVec_repr,
      ← Module.Basis.equivFun_apply, hg, LinearEquiv.apply_symm_apply, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ hx, Matrix.one_mulVec, Module.Basis.equivFun_apply]
  have hunit : ∀ x : S, IsUnit x ↔ IsUnit (Algebra.leftMulMatrix b x).det := by
    intro x
    constructor
    · intro h
      exact (Matrix.isUnit_iff_isUnit_det _).mp (h.map (Algebra.leftMulMatrix b))
    · intro h
      exact ⟨⟨x, g x, key x h, by rw [mul_comm]; exact key x h⟩, rfl⟩
  have hopenS : IsOpen {x : S | IsUnit x} := by
    have h : {x : S | IsUnit x} =
        (fun x : S => (Algebra.leftMulMatrix b x).det) ⁻¹' {r : R | IsUnit r} :=
      Set.ext hunit
    rw [h]
    exact hopenR.preimage hLc.matrix_det
  have hc1 : ContinuousOn (fun x : S => Ring.inverse (Algebra.leftMulMatrix b x).det)
      {x : S | IsUnit x} :=
    hinvR.comp hLc.matrix_det.continuousOn (fun x hx => (hunit x).mp hx)
  have hc2 : ContinuousOn (fun x : S => (Algebra.leftMulMatrix b x)⁻¹) {x : S | IsUnit x} := by
    simp_rw [Matrix.inv_def]
    exact hc1.smul hLc.matrix_adjugate.continuousOn
  have hsymm : Continuous (b.equivFun.symm : (ι → R) → S) :=
    LinearMap.continuous_on_pi b.equivFun.symm.toLinearMap
  have hc3 : ContinuousOn g {x : S | IsUnit x} := by
    have h : g = (fun M : Matrix ι ι R => b.equivFun.symm (Matrix.mulVec M (b.equivFun 1))) ∘
        (fun x : S => (Algebra.leftMulMatrix b x)⁻¹) := by
      funext x
      exact hg x
    rw [h]
    exact (hsymm.comp (continuous_id.matrix_mulVec continuous_const)).comp_continuousOn hc2
  have hgu : ∀ u : Sˣ, g u = ↑u⁻¹ := by
    intro u
    calc g u = ↑u⁻¹ * (↑u * g u) := by rw [← mul_assoc, Units.inv_mul, one_mul]
      _ = ↑u⁻¹ := by rw [key _ ((hunit _).mp u.isUnit), mul_one]
  exact ⟨⟨Units.isEmbedding_val_mk' hc3 hgu, hopenS⟩⟩

theorem _root_.GlobalTheory.GaugeEx.nice_tensor : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], _root_.GlobalTheory.GaugeEx.Nice R → IsArtinianRing (R ⊗[F] E) ∧ IsReduced (R ⊗[F] E) ∧ IsOpenUnits (R ⊗[F] E) := by
  intro F E _ _ _ _ _ R _ _ _ _ _ _ _ _ _ hR
  obtain ⟨hArt, hRed, hOpen, -⟩ := hR
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  refine ⟨?_, ?_, ?_⟩
  · exact IsArtinianRing.of_finite R (R ⊗[F] E)
  · exact _root_.GlobalTheory.ReducedAlg.isReduced_tensor (k := F) R E
  · haveI := _root_.GlobalTheory.GaugeEx.modTopTens (F := F) (E := E) R
    haveI := _root_.GlobalTheory.GaugeEx.topRingTens (F := F) (E := E) R
    exact _root_.GlobalTheory.GaugeEx.isOpenUnits_of_basis
      (Algebra.TensorProduct.basis R (Module.finBasis F E))

end GlobalTheory.GaugeEx
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TensorNiceRingArtinianReducedOpenUnitsStatement
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_niceRing_artinian_reduced_openUnits : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], Nice R → IsArtinianRing (R ⊗[F] E) ∧ IsReduced (R ⊗[F] E) ∧ IsOpenUnits (R ⊗[F] E) := by
  first | exact @GlobalTheory.GaugeEx.nice_tensor | exact GlobalTheory.GaugeEx.nice_tensor | (intros; apply GlobalTheory.GaugeEx.nice_tensor <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianQuadraticUnitaryLocalComponents
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianQuadraticUnitaryLocalComponents
noncomputable section

namespace GlobalTheory.GaugeEx

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct NNReal ENNReal

section BaseMap

variable {F E : Type} [Field F] [Field E] [Algebra F E]
  {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R']

theorem qloc_trace_tmul [FiniteDimensional F E] (r : R) (e : E) :
    Algebra.trace R (R ⊗[F] E) (r ⊗ₜ[F] e) = r * algebraMap F R (Algebra.trace F E e) := by
  have h1 : (r ⊗ₜ[F] e : R ⊗[F] E) = r • ((1 : R) ⊗ₜ[F] e) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [h1, map_smul, Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
    LinearMap.trace_baseChange, smul_eq_mul]

variable (φ : R →ₐ[F] R') (π : R ⊗[F] E →+* R' ⊗[F] E)
  (hπ : ∀ r e, π (r ⊗ₜ[F] e) = φ r ⊗ₜ[F] e)
include hπ

theorem qloc_trace [FiniteDimensional F E] (z : R ⊗[F] E) :
    Algebra.trace R' (R' ⊗[F] E) (π z) = φ (Algebra.trace R (R ⊗[F] E) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => rw [hπ, qloc_trace_tmul, qloc_trace_tmul, map_mul, AlgHom.commutes]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem qloc_sig (σ : E →ₐ[F] E) (z : R ⊗[F] E) : sigR R' σ (π z) = π (sigR R σ z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [sigR, hπ]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem qloc_incl (e : E) : π (inclR R e) = inclR R' e := by
  simp [inclR, hπ]

theorem qloc_q [FiniteDimensional F E] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (z : Fin M → R ⊗[F] E) : qR R' σ J (fun i => π (z i)) = φ (qR R σ J z) := by
  have h : hR R' σ J (fun i => π (z i)) (fun i => π (z i)) = π (hR R σ J z z) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hR, Formalism.UG.hform, JR, Matrix.map_apply, map_sum, map_mul, qloc_sig φ π hπ,
      qloc_incl φ π hπ]
  rw [qR, qR, h, qloc_trace φ π hπ, map_mul, AlgHom.commutes]

theorem qloc_group (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (g : HA R σ J) :
    ∃ g' : HA R' σ J, (HA.mat R' σ J g').val = (HA.mat R σ J g).val.map π := by
  have hg : Formalism.UG.cT (sigR R σ) (HA.mat R σ J g).val * JR R J * (HA.mat R σ J g).val = JR R J :=
    Subtype.property (p := fun x => x ∈ HR R σ J) g
  have hJ : (JR R J).map π = JR R' J := by
    ext i j
    exact qloc_incl φ π hπ _
  have hc : Formalism.UG.cT (sigR R' σ) ((HA.mat R σ J g).val.map π) =
      (Formalism.UG.cT (sigR R σ) (HA.mat R σ J g).val).map π := by
    ext i j
    exact qloc_sig φ π hπ σ _
  have hm : Formalism.UG.bc π (HA.mat R σ J g) ∈ HR R' σ J := by
    change Formalism.UG.cT (sigR R' σ) ((HA.mat R σ J g).val.map π) * JR R' J *
      ((HA.mat R σ J g).val.map π) = JR R' J
    rw [hc, ← hJ, ← Matrix.map_mul, ← Matrix.map_mul, hg]
  exact ⟨(⟨_, hm⟩ : HR R' σ J), rfl⟩

end BaseMap

theorem qloc_adele_ext {F : Type} [Field F] [NumberField F] (a b : AF F)
    (h1 : fstA F a = fstA F b) (h2 : ∀ v, evalV F v (sndA F a) = evalV F v (sndA F b)) : a = b := by
  refine Prod.ext h1 ?_
  exact FiniteAdeleRing.ext F fun v => h2 v

theorem q_and_unitary_local_components : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E), (∀ (z : Fin M → AF F ⊗[F] E) (β : F), qR (AF F) σ J z = algebraMap F (AF F) β ↔ qR (Ainf F) σ J (fun i => prInf (z i)) = algebraMap F (Ainf F) β ∧ ∀ v : HeightOneSpectrum (𝓞 F), qR (Fv F v) σ J (fun i => prV v (z i)) = algebraMap F (Fv F v) β) ∧ ∀ g : HA (AF F) σ J, (∃ gi : HA (Ainf F) σ J, (HA.mat (Ainf F) σ J gi).val = (HA.mat (AF F) σ J g).val.map prInf) ∧ ∀ v : HeightOneSpectrum (𝓞 F), ∃ gv : HA (Fv F v) σ J, (HA.mat (Fv F v) σ J gv).val = (HA.mat (AF F) σ J g).val.map (prV v) := by
  intro F E _ _ _ _ _ σ M J
  have hI : ∀ (r : AF F) (e : E), prInf (r ⊗ₜ[F] e) = fstA F r ⊗ₜ[F] e := fun r e => rfl
  have hV : ∀ v (r : AF F) (e : E),
      prV v (r ⊗ₜ[F] e) = ((evalV F v).comp (sndA F)) r ⊗ₜ[F] e := fun v r e => rfl
  refine ⟨fun z β => ?_, fun g => ⟨qloc_group _ _ hI σ J g, fun v => qloc_group _ _ (hV v) σ J g⟩⟩
  simp only [qloc_q _ _ hI, qloc_q _ _ (hV _)]
  constructor
  · intro h
    rw [h]
    exact ⟨AlgHom.commutes _ _, fun v => AlgHom.commutes _ _⟩
  · rintro ⟨h1, h2⟩
    refine qloc_adele_ext _ _ (by rw [h1, AlgHom.commutes]) fun v => ?_
    rw [AlgHom.commutes, AlgHom.commutes]
    exact h2 v

end GlobalTheory.GaugeEx
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianQuadraticUnitaryLocalComponentsStatement
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianQuadratic_unitary_local_components : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E), (∀ (z : Fin M → AF F ⊗[F] E) (β : F), qR (AF F) σ J z = algebraMap F (AF F) β ↔ qR (Ainf F) σ J (fun i => prInf (z i)) = algebraMap F (Ainf F) β ∧ ∀ v : HeightOneSpectrum (𝓞 F), qR (Fv F v) σ J (fun i => prV v (z i)) = algebraMap F (Fv F v) β) ∧ ∀ g : HA (AF F) σ J, (∃ gi : HA (Ainf F) σ J, (HA.mat (Ainf F) σ J gi).val = (HA.mat (AF F) σ J g).val.map prInf) ∧ ∀ v : HeightOneSpectrum (𝓞 F), ∃ gv : HA (Fv F v) σ J, (HA.mat (Fv F v) σ J gv).val = (HA.mat (AF F) σ J g).val.map (prV v) := by
  first | exact @GlobalTheory.GaugeEx.q_and_unitary_local_components | exact GlobalTheory.GaugeEx.q_and_unitary_local_components | (intros; apply GlobalTheory.GaugeEx.q_and_unitary_local_components <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibreFamilyHermitianQuadraticFormAtUnitProps
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibreFamilyHermitianQuadraticFormAtUnitProps
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.GaugeEx.FibBasic

section General

variable {V X : Type} [TopologicalSpace V] [MeasurableSpace V] [TopologicalSpace X]
  [MeasurableSpace X] {μ : Measure V} {f : V → X} {ν : Measure X} {B : Set X}

theorem lintegral_preimage {fib : X → Measure V} (hf : Measurable f)
    (h : IsFibreFamily μ f id Set.univ ν B fib) (φ : V → ℝ≥0∞) (hφ : Measurable φ)
    (S : Set X) (hS : MeasurableSet S) :
    ∫⁻ v, (f ⁻¹' S).indicator φ v ∂μ = ∫⁻ b in S, ∫⁻ v, φ v ∂(fib b) ∂ν := by
  have h2 := h.2.1 ((f ⁻¹' S).indicator φ) (hφ.indicator (hf hS))
  rw [Measure.restrict_univ] at h2
  rw [h2, ← lintegral_indicator hS]
  congr 1
  funext b
  have hb : ∀ᵐ v ∂(fib b), f v = b := by
    have : ∀ᵐ v ∂(fib b), v ∈ f ⁻¹' {id b} ∩ Set.univ := h.1 b
    filter_upwards [this] with v hv using hv.1
  by_cases hbS : b ∈ S
  · rw [Set.indicator_of_mem hbS]
    apply lintegral_congr_ae
    filter_upwards [hb] with v hv
    exact Set.indicator_of_mem (by simpa [hv] using hbS) _
  · rw [Set.indicator_of_notMem hbS, ← lintegral_zero (μ := fib b)]
    apply lintegral_congr_ae
    filter_upwards [hb] with v hv
    exact Set.indicator_of_notMem (by simpa [hv] using hbS) _

theorem finite_on_compacts [T2Space V] [LocallyCompactSpace V] [BorelSpace V]
    {fib : X → Measure V} (h : IsFibreFamily μ f id Set.univ ν B fib) {β : X} (hβ : β ∈ B) :
    IsFiniteMeasureOnCompacts (fib β) := by
  refine ⟨fun K hK => ?_⟩
  obtain ⟨φ, h1, -, hc, h01⟩ :=
    exists_continuous_one_zero_of_isCompact hK isClosed_empty (Set.disjoint_empty _)
  have hi := (h.2.2 φ φ.continuous hc (Set.subset_univ _)).1 β hβ
  refine lt_of_le_of_lt (measure_mono ?_) (hi.measure_ge_lt_top (ε := 1) one_pos)
  intro v hv
  exact (h1 hv).ge

theorem eq_at [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V] [BorelSpace V]
    [BorelSpace X] [SigmaFinite ν] [ν.IsOpenPosMeasure]
    {fib fib' : X → Measure V} (hf : Measurable f) (hB : IsOpen B)
    (h : IsFibreFamily μ f id Set.univ ν B fib) (h' : IsFibreFamily μ f id Set.univ ν B fib')
    {β : X} (hβ : β ∈ B) : fib β = fib' β := by
  haveI := finite_on_compacts h hβ
  haveI := finite_on_compacts h' hβ
  refine Measure.ext_of_integral_eq_on_compactlySupported_nnreal fun g => ?_
  set φ : V → ℝ := fun v => (g v : ℝ) with hφdef
  have hφ : Continuous φ := NNReal.continuous_coe.comp g.continuous
  have hc : HasCompactSupport φ := HasCompactSupport.comp_left g.hasCompactSupport rfl
  have h0 : ∀ v, 0 ≤ φ v := fun v => (g v).2
  obtain ⟨hi, hg⟩ := h.2.2 φ hφ hc (Set.subset_univ _)
  obtain ⟨hi', hg'⟩ := h'.2.2 φ hφ hc (Set.subset_univ _)
  have hφm : Measurable fun v => ENNReal.ofReal (φ v) :=
    ENNReal.measurable_ofReal.comp hφ.measurable
  have c : ContinuousOn (fun b => ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib b)) B :=
    (ENNReal.continuous_ofReal.comp_continuousOn hg).congr fun b hb =>
      (ofReal_integral_eq_lintegral_ofReal (hi b hb) (Filter.Eventually.of_forall h0)).symm
  have c' : ContinuousOn (fun b => ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib' b)) B :=
    (ENNReal.continuous_ofReal.comp_continuousOn hg').congr fun b hb =>
      (ofReal_integral_eq_lintegral_ofReal (hi' b hb) (Filter.Eventually.of_forall h0)).symm
  have hae : (fun b => ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib b)) =ᵐ[ν.restrict B]
      (fun b => ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib' b)) := by
    refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite₀ (c.aemeasurable hB.measurableSet)
      (c'.aemeasurable hB.measurableSet) fun S hS _ => ?_
    rw [Measure.restrict_restrict hS,
      ← lintegral_preimage hf h _ hφm _ (hS.inter hB.measurableSet),
      ← lintegral_preimage hf h' _ hφm _ (hS.inter hB.measurableSet)]
  have e := Measure.eqOn_open_of_ae_eq hae hB c c' hβ
  simp only at e
  rw [← ofReal_integral_eq_lintegral_ofReal (hi β hβ) (Filter.Eventually.of_forall h0),
    ← ofReal_integral_eq_lintegral_ofReal (hi' β hβ) (Filter.Eventually.of_forall h0)] at e
  exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg h0) (integral_nonneg h0)).1 e

end General

theorem continuous_qR {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
    [IsTopologicalRing R] {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    Continuous fun X : Fin 1 → Fin M → R ⊗[F] E => qR R σ J (X 0) := by
  have h1 : Continuous (Algebra.trace R (R ⊗[F] E)) :=
    IsModuleTopology.continuous_of_linearMap _
  have h2 := GlobalTheory.AdelicUnitaryTop.continuous_sigR R σ
  unfold qR hR Formalism.UG.hform
  refine continuous_const.mul (h1.comp ?_)
  fun_prop

theorem fibAt_basic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], Nice R → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (μ : Measure (Fin 1 → Fin M → R ⊗[F] E)) (ν : Measure R) (β : R) (m : Measure (Fin 1 → Fin M → R ⊗[F] E)), ν.IsAddHaarMeasure → IsUnit β → FibAt R σ J μ ν β m → m {X | qR R σ J (X 0) ≠ β} = 0 ∧ IsFiniteMeasureOnCompacts m ∧ ∀ m', FibAt R σ J μ ν β m' → m' = m := by
  intro F E _ _ _ _ _ σ R _ _ _ _ _ _ _ _ _ hN M J μ ν β m hν hβ hm
  obtain ⟨fib, h, rfl⟩ := hm
  haveI := hN.2.2.1
  have hB : IsOpen {c : R | IsUnit c} :=
    (IsOpenUnits.isOpenEmbedding_unitsVal (M := R)).isOpen_range
  refine ⟨?_, finite_on_compacts h hβ, ?_⟩
  · refine measure_mono_null ?_ (h.1 β)
    intro X hX hX'
    exact hX hX'.1
  · rintro m' ⟨fib', h', rfl⟩
    exact eq_at (continuous_qR σ R J).measurable hB h' h hβ

end GlobalTheory.GaugeEx.FibBasic
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibreFamilyHermitianQuadraticFormAtUnitPropsStatement
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibreFamily_hermitian_quadratic_form_at_unit_props : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R], Nice R → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (μ : Measure (Fin 1 → Fin M → R ⊗[F] E)) (ν : Measure R) (β : R) (m : Measure (Fin 1 → Fin M → R ⊗[F] E)), ν.IsAddHaarMeasure → IsUnit β → FibAt R σ J μ ν β m → m {X | qR R σ J (X 0) ≠ β} = 0 ∧ IsFiniteMeasureOnCompacts m ∧ ∀ m', FibAt R σ J μ ν β m' → m' = m := by
  first | exact @GlobalTheory.GaugeEx.FibBasic.fibAt_basic | exact GlobalTheory.GaugeEx.FibBasic.fibAt_basic | (intros; apply GlobalTheory.GaugeEx.FibBasic.fibAt_basic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VectorTupleProductMeasureTwoSidedAction
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VectorTupleProductMeasureTwoSidedAction
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx Matrix
open scoped TensorProduct NNReal ENNReal Pointwise Kronecker

namespace GlobalTheory.GaugeEx.ModDet

theorem induction_pi {S : Type} [CommRing S] {ι : Type} [Fintype ι] [DecidableEq ι] {K : ι → Type}
    [∀ k, Field (K k)] (e : S ≃+* ∀ k, K k) {κ : Type} [Fintype κ] [DecidableEq κ]
    (P : Matrix κ κ S → Prop) (hd : ∀ d : κ → S, (∀ i, IsUnit (d i)) → P (diagonal d))
    (ht : ∀ (i j : κ) (c : S), i ≠ j → P (transvection i j c))
    (hm : ∀ A B, P A → P B → P (A * B)) (g : Matrix κ κ S) (hg : IsUnit g.det) : P g := by
  let E : Matrix κ κ S ≃+* ∀ k, Matrix κ κ (K k) := e.mapMatrix.trans Matrix.piRingEquiv
  have hE : ∀ A k i j, E A k i j = e (A i j) k := fun _ _ _ _ => rfl
  have h1 : ∀ k (A : Matrix κ κ (K k)), A.det ≠ 0 → P (E.symm (Pi.mulSingle k A)) := by
    intro k A hA
    apply diagonal_transvection_induction_of_det_ne_zero
      (fun A => P (E.symm (Pi.mulSingle k A))) A hA
    · intro D hD
      rw [det_diagonal] at hD
      have : E.symm (Pi.mulSingle k (diagonal D)) =
          diagonal fun i => e.symm (Pi.mulSingle k (D i)) := by
        rw [RingEquiv.symm_apply_eq]
        funext k'
        ext i j
        rw [hE]
        by_cases hk : k' = k
        · subst hk
          by_cases hij : i = j
          · subst hij; simp
          · simp [hij]
        · by_cases hij : i = j
          · subst hij; simp [hk]
          · simp [hij, hk]
      rw [this]
      refine hd _ fun i => ?_
      have : IsUnit (D i) := (Finset.prod_ne_zero_iff.1 hD i (Finset.mem_univ i)).isUnit
      exact (this.map (MonoidHom.mulSingle K k)).map e.symm
    · intro t
      obtain ⟨a, b, hab, c⟩ := t
      have : E.symm (Pi.mulSingle k (transvection a b c)) =
          transvection a b (e.symm (Pi.single k c)) := by
        rw [RingEquiv.symm_apply_eq]
        funext k'
        ext i j
        rw [hE]
        by_cases hk : k' = k
        · subst hk
          simp [transvection, Matrix.one_apply, Matrix.single, apply_ite e, ite_apply]
        · simp [transvection, Matrix.one_apply, Matrix.single, apply_ite e, ite_apply, hk]
      rw [TransvectionStruct.toMatrix_mk, this]
      exact ht _ _ _ hab
    · intro A B _ _ hA hB
      rw [Pi.mulSingle_mul, map_mul]
      exact hm _ _ hA hB
  have hdet : ∀ k, (E g k).det ≠ 0 := by
    intro k
    have : E g k = ((Pi.evalRingHom K k).comp e.toRingHom).mapMatrix g := rfl
    rw [this, ← RingHom.map_det]
    exact (hg.map _).ne_zero
  have h2 : ∀ s : Finset ι, P (E.symm fun k => if k ∈ s then E g k else 1) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have : (fun k => if k ∈ (∅ : Finset ι) then E g k else 1) = 1 := by funext k; simp
      rw [this, map_one, ← diagonal_one]
      exact hd _ fun _ => isUnit_one
    | insert a s ha ih =>
      have : (fun k => if k ∈ insert a s then E g k else 1) =
          Pi.mulSingle a (E g a) * fun k => if k ∈ s then E g k else 1 := by
        funext k
        by_cases hk : k = a
        · subst hk; simp [ha]
        · simp [hk]
      rw [this, map_mul]
      exact hm _ _ (h1 a _ (hdet a)) ih
  simpa using h2 Finset.univ

section

variable {S : Type} [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] [LocallyCompactSpace S]

theorem modu_coe (u : Sˣ) : modu S u = distribHaarChar S u := by
  simp [modu]

theorem modu_mul {a b : S} (ha : IsUnit a) (hb : IsUnit b) : modu S (a * b) = modu S a * modu S b := by
  obtain ⟨a, rfl⟩ := ha
  obtain ⟨b, rfl⟩ := hb
  rw [← Units.val_mul, modu_coe, modu_coe, modu_coe, map_mul]

theorem modu_pow {a : S} (ha : IsUnit a) (n : ℕ) : modu S (a ^ n) = modu S a ^ n := by
  obtain ⟨a, rfl⟩ := ha
  rw [← Units.val_pow_eq_pow_val, modu_coe, modu_coe, map_pow]

variable [T2Space S] [SecondCountableTopology S] [MeasurableSpace S] [BorelSpace S]

theorem smul_map_mulVec_pi [IsArtinianRing S] [IsReduced S] (ν : Measure S) [ν.IsAddHaarMeasure]
    {κ : Type} [Fintype κ] [DecidableEq κ] (M : Matrix κ κ S) (hM : IsUnit M.det) :
    (modu S M.det : ℝ≥0∞) • Measure.map M.mulVec (Measure.pi fun _ : κ => ν) =
      Measure.pi fun _ : κ => ν := by
  classical
  have hm : ∀ A : Matrix κ κ S, Measurable A.mulVec := fun A =>
    (continuous_const.matrix_mulVec continuous_id).measurable
  letI := Fintype.ofFinite (MaximalSpectrum S)
  letI : ∀ m : MaximalSpectrum S, Field (S ⧸ m.asIdeal) := fun m =>
    haveI := m.isMaximal
    Ideal.Quotient.field m.asIdeal
  refine (induction_pi (IsArtinianRing.equivPi S).toRingEquiv (fun M : Matrix κ κ S => IsUnit M.det ∧
    (modu S M.det : ℝ≥0∞) • Measure.map M.mulVec (Measure.pi fun _ : κ => ν) =
      Measure.pi fun _ : κ => ν) ?_ ?_ ?_ M hM).2
  · intro D A
    have hu' : (diagonal D).det = ((∏ i, (A i).unit : Sˣ) : S) := by simp
    refine ⟨hu' ▸ Units.isUnit _, (Measure.pi_eq fun s hs => ?_).symm⟩
    rw [Measure.smul_apply, Measure.map_apply (hm _) (MeasurableSet.univ_pi hs)]
    have : ((diagonal D).mulVec ⁻¹' Set.pi Set.univ fun i : κ => s i) =
        Set.pi Set.univ fun i : κ => ((A i).unit)⁻¹ • s i := by
      ext f
      simp only [Set.mem_preimage, Set.mem_univ_pi, mulVec_diagonal]
      exact forall_congr' fun i => (Set.mem_inv_smul_set_iff (a := (A i).unit)).symm
    rw [this, Measure.pi_pi, hu', modu_coe, map_prod, smul_eq_mul]
    change ENNReal.ofNNRealHom (∏ i, distribHaarChar S (A i).unit) * _ = _
    rw [map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    change ((distribHaarChar S (A i).unit : ℝ≥0) : ℝ≥0∞) * _ = _
    rw [distribHaarChar_mul, smul_inv_smul]
  · intro a b c hab
    rw [det_transvection_of_ne _ _ hab]
    refine ⟨isUnit_one, ?_⟩
    rw [← Units.val_one, modu_coe, map_one, ENNReal.coe_one, one_smul]
    refine (Measure.pi_eq fun s hs ↦ ?_).symm
    have h2s : MeasurableSet (Set.univ.pi s) := .pi Set.countable_univ fun i _ ↦ hs i
    simp_rw [← Measure.pi_pi, ← lintegral_indicator_one h2s]
    rw [lintegral_map (measurable_one.indicator h2s) (hm _)]
    refine lintegral_eq_of_lmarginal_eq {a} ((measurable_one.indicator h2s).comp (hm _))
      (measurable_one.indicator h2s) ?_
    simp_rw [lmarginal_singleton]
    ext x
    simp [transvection, add_mulVec, single_mulVec, hab.symm, ← Function.update_add,
      lintegral_add_right_eq_self fun xᵢ ↦ Set.indicator (Set.univ.pi s) 1 (Function.update x a xᵢ)]
  · rintro A B ⟨hA, IHA⟩ ⟨hB, IHB⟩
    have e : (A * B).mulVec = A.mulVec ∘ B.mulVec := funext fun x => (mulVec_mulVec x A B).symm
    rw [det_mul]
    refine ⟨hA.mul hB, ?_⟩
    rw [modu_mul hA hB, ENNReal.coe_mul, mul_smul, e, ← Measure.map_map (hm _) (hm _),
      ← Measure.map_smul, IHB, IHA]
    exact (hm A).aemeasurable

end

theorem tupMeas_eq_map {S : Type} [MeasurableSpace S] (lam : Measure S) [SigmaFinite lam] (n M : ℕ) :
    tupMeas lam n M = (Measure.pi fun _ : Fin n × Fin M => lam).map Function.curry := by
  have hu : Measurable (Function.uncurry : (Fin n → Fin M → S) → Fin n × Fin M → S) :=
    Measurable.of_eval fun p => (measurable_pi_apply p.2).comp (measurable_pi_apply p.1)
  have hc : Measurable (Function.curry : (Fin n × Fin M → S) → Fin n → Fin M → S) :=
    Measurable.of_eval fun a => Measurable.of_eval fun i => measurable_pi_apply (a, i)
  have : (Measure.pi fun _ : Fin n × Fin M => lam) = (tupMeas lam n M).map Function.uncurry := by
    refine Measure.pi_eq fun s hs => ?_
    rw [Measure.map_apply hu (MeasurableSet.univ_pi hs)]
    have : (Function.uncurry ⁻¹' Set.pi Set.univ s : Set (Fin n → Fin M → S)) =
        Set.pi Set.univ fun a => Set.pi Set.univ fun i => s (a, i) := by
      ext X
      simp [Function.uncurry]
    rw [this, tupMeas, Measure.pi_pi, Fintype.prod_prod_type]
    simp_rw [Measure.pi_pi]
  rw [this, Measure.map_map hc hu]
  exact Measure.map_id.symm

theorem tupMeas_lrAct : ∀ (S : Type) [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] [T2Space S] [LocallyCompactSpace S] [SecondCountableTopology S] [MeasurableSpace S] [BorelSpace S], IsArtinianRing S → IsReduced S → ∀ (lam : Measure S), lam.IsAddHaarMeasure → ∀ (n M : ℕ) (g : Matrix (Fin M) (Fin M) S) (γ : Matrix (Fin n) (Fin n) S), IsUnit g.det → IsUnit γ.det → tupMeas lam n M = (modu S g.det ^ n * modu S γ.det ^ M) • (tupMeas lam n M).map (lrAct g γ) := by
  intro S _ _ _ _ _ _ _ _ _ _ lam _ n M g γ hg hγ
  have hc : Measurable (Function.curry : (Fin n × Fin M → S) → Fin n → Fin M → S) :=
    Measurable.of_eval fun a => Measurable.of_eval fun i => measurable_pi_apply (a, i)
  have hl : Measurable (lrAct g γ) := by
    refine Continuous.measurable (continuous_pi fun a => continuous_const.matrix_mulVec ?_)
    fun_prop
  have hdet : (γᵀ ⊗ₖ g).det = γ.det ^ M * g.det ^ n := by simp [det_kronecker]
  have key := smul_map_mulVec_pi lam (γᵀ ⊗ₖ g) (hdet ▸ (hγ.pow M).mul (hg.pow n))
  rw [hdet, modu_mul (hγ.pow M) (hg.pow n), modu_pow hγ, modu_pow hg, mul_comm] at key
  have hcomm : lrAct g γ ∘ Function.curry = Function.curry ∘ (γᵀ ⊗ₖ g).mulVec := by
    funext X a i
    simp only [Function.comp, lrAct, Function.curry, mulVec, dotProduct, Fintype.sum_prod_type,
      kroneckerMap_apply, transpose_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hm : Measurable (γᵀ ⊗ₖ g).mulVec := (continuous_const.matrix_mulVec continuous_id).measurable
  rw [tupMeas_eq_map, Measure.map_map hl hc, hcomm, ← Measure.map_map hc hm, ← Measure.map_smul]
  · exact congrArg _ key.symm
  · exact hc.aemeasurable

end GlobalTheory.GaugeEx.ModDet

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VectorTupleProductMeasureTwoSidedActionStatement
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vectorTupleProductMeasure_two_sided_action : ∀ (S : Type) [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] [T2Space S] [LocallyCompactSpace S] [SecondCountableTopology S] [MeasurableSpace S] [BorelSpace S], IsArtinianRing S → IsReduced S → ∀ (lam : Measure S), lam.IsAddHaarMeasure → ∀ (n M : ℕ) (g : Matrix (Fin M) (Fin M) S) (γ : Matrix (Fin n) (Fin n) S), IsUnit g.det → IsUnit γ.det → tupMeas lam n M = (modu S g.det ^ n * modu S γ.det ^ M) • (tupMeas lam n M).map (lrAct g γ) := by
  first | exact @GlobalTheory.GaugeEx.ModDet.tupMeas_lrAct | exact GlobalTheory.GaugeEx.ModDet.tupMeas_lrAct | (intros; apply GlobalTheory.GaugeEx.ModDet.tupMeas_lrAct <;> assumption)
end
end
