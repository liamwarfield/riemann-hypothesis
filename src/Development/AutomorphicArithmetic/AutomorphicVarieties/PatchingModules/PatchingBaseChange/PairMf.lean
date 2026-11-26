module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.AlgebraMapEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FinE

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.PairMf
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

theorem UpperTheory.V.Pa.BC.pair_mf :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [IsLocalRing O] [Finite (ResidueField O)] [CharP (ResidueField O) l] [Algebra ℤ_[l] O] (n : ℕ) (r : Resid F O n) (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (u : Pair r B), PhiCond F.G₀ l → Finite (ResidueField B) ∧ (∃ (χ : Fin n → F.G₀ →* (ResidueField B)ˣ) (h : ℕ), u.D.map (residue B) = GDet.ofChars χ ∧ UpperTheory.V.CA.MultFree χ h) ∧ ∀ Z : Set (MonoidAlgebra B F.G₀), ∃ s : Finset F.G₀, ∀ y : MonoidAlgebra B F.G₀, ∃ c : F.G₀ → B, y - ∑ g ∈ s, MonoidAlgebra.single g (c g) ∈ u.D.chBar Z := by
  intro l _ F O _ _ _ _ _ n r B _ _ _ u hPhi
  haveI : CompactSpace F.G₀ :=
    isCompact_iff_compactSpace.mp (Subgroup.isClosed_of_isOpen _ F.η_open).isCompact
  let e : ResidueField O ≃+* ResidueField B :=
    RingEquiv.ofBijective (ResidueField.map (algebraMap O B)) (resMap_bijective O B)
  haveI hfin : Finite (ResidueField B) := Finite.of_equiv _ e.toEquiv
  haveI : CharP (ResidueField B) l :=
    charP_of_injective_ringHom (f := (e : ResidueField O →+* ResidueField B)) e.injective l
  have hE : Function.Injective (Units.map (e : ResidueField O →* ResidueField B)) :=
    Units.map_injective (f := (e : ResidueField O →* ResidueField B)) e.injective
  let χ : Fin n → F.G₀ →* (ResidueField B)ˣ :=
    fun i => (Units.map (e : ResidueField O →* ResidueField B)).comp (r.chib i)
  have hker : ∀ i, (χ i).ker = (r.chib i).ker := by
    intro i
    ext g
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    show Units.map (e : ResidueField O →* ResidueField B) (r.chib i g) = 1 ↔ r.chib i g = 1
    rw [← map_one (Units.map (e : ResidueField O →* ResidueField B)), hE.eq_iff]
  have hopen : ∀ i, IsOpen ((χ i).ker : Set F.G₀) := fun i => by
    rw [hker]
    exact r.chib_open i
  have hinj : Function.Injective χ := by
    intro i j hij
    exact r.chib_inj (MonoidHom.ext fun g => hE (DFunLike.congr_fun hij g))
  have hres : (residue B) = (e : ResidueField O →+* ResidueField B).comp (res O B : B →+* ResidueField O) :=
    RingHom.ext fun b => (e.apply_symm_apply (residue B b)).symm
  obtain ⟨-, hcomp, -, -⟩ := UpperTheory.V.CA.d_gmap u.D
  obtain ⟨-, -, -, hrep⟩ := UpperTheory.V.CA.d_gmap (GDet.ofRep (diagRep r.chib))
  have hmap : u.D.map (residue B) = GDet.ofChars χ := by
    rw [hres, ← hcomp, u.red]
    show (GDet.ofRep (diagRep r.chib)).map _ = GDet.ofRep (GDet.diagRep χ)
    rw [hrep]
    congr 1
    ext g i j
    simp [diagRep, GDet.diagRep, χ, Matrix.diagonal_apply]
    split_ifs <;> simp
  obtain ⟨h, hmf⟩ := UpperTheory.V.CA.exists_multFree_of_phiCond_of_injective_chars l χ hPhi hopen hinj
  refine ⟨hfin, ⟨χ, h, hmap, hmf⟩, fun Z => ?_⟩
  obtain ⟨⟨s, -, hs⟩, -, -⟩ := UpperTheory.V.CA.finE u.D χ u.cont hmap hmf Z
  refine ⟨s, fun y => ?_⟩
  have hy : u.D.toQuot Z y ∈ Submodule.span B
      ((fun g ↦ (u.D.toQuot Z) (MonoidAlgebra.single g 1)) '' (s : Set F.G₀)) := by
    rw [hs]
    exact Submodule.mem_top
  obtain ⟨c, hc, hcy⟩ := (Finsupp.mem_span_image_iff_linearCombination B).mp hy
  rw [Finsupp.linearCombination_apply_of_mem_supported B hc] at hcy
  refine ⟨c, ?_⟩
  have hz : u.D.toQuot Z (y - ∑ g ∈ s, MonoidAlgebra.single g (c g)) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sum, ← hcy, sub_eq_zero]
    refine Finset.sum_congr rfl (fun g _ => ?_)
    rw [← map_smul, MonoidAlgebra.smul_single', mul_one]
  rw [TwoSidedIdeal.mem_iff]
  exact (u.D.chBar Z).ringCon.eq.mp hz
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.ClosureBc
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

private theorem cbc_krull {B E : Type} [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [AddCommGroup E]
    [Module B E] [Module.Finite B E] (x : E)
    (hx : ∀ N : ℕ, x ∈ (maximalIdeal B ^ N) • (⊤ : Submodule B E)) : x = 0 := by
  have h := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := E) (maximalIdeal B) (maximalIdeal.isMaximal B).ne_top
  rw [← Submodule.mem_bot B, ← h, Submodule.mem_iInf]
  exact hx

private theorem cbc_lin {B E : Type} [CommRing B] [AddCommGroup E] [Module B E] (I : Ideal B)
    (f : E →ₗ[B] E) {x : E} (hx : x ∈ I • (⊤ : Submodule B E)) : f x ∈ I • (⊤ : Submodule B E) := by
  have h1 : f x ∈ (I • (⊤ : Submodule B E)).map f := Submodule.mem_map_of_mem hx
  rw [Submodule.map_smul''] at h1
  exact Submodule.smul_mono le_rfl le_top h1

private theorem cbc_span {B R E : Type} [CommRing B] [Ring R] [Algebra B R] [Ring E] [Algebra B E]
    (π : R →ₐ[B] E) (I : Ideal B) (S : Set R)
    (hS : ∀ s ∈ S, π s ∈ I • (⊤ : Submodule B E)) {y : R}
    (hy : y ∈ TwoSidedIdeal.span S) : π y ∈ I • (⊤ : Submodule B E) := by
  induction hy using TwoSidedIdeal.span_induction with
  | mem x hx => exact hS x hx
  | zero => rw [map_zero]; exact zero_mem _
  | add x z _ _ hx hz => rw [map_add]; exact add_mem hx hz
  | neg x _ hx => rw [map_neg]; exact neg_mem hx
  | left_absorb a x _ hx =>
    rw [map_mul]
    exact cbc_lin I (LinearMap.mulLeft B (π a)) hx
  | right_absorb a x _ hx =>
    rw [map_mul]
    exact cbc_lin I (LinearMap.mulRight B (π a)) hx

private theorem cbc_sub {A G : Type} [CommRing A] [Group G] [TopologicalSpace G] (I : Ideal A)
    (S : Set (MonoidAlgebra A G)) {x : MonoidAlgebra A G} (hx : x ∈ S) : x ∈ closureIdeal I S := by
  simp only [closureIdeal, TwoSidedIdeal.mem_iInf]
  exact fun N H => TwoSidedIdeal.subset_span (Or.inl (Or.inl hx))

private theorem cbc_zero {n : ℕ} {B G : Type} [CommRing B] [IsLocalRing B] [Group G] [TopologicalSpace G]
    (D : GDet n B G) (Z : Set (MonoidAlgebra B G)) (x : MonoidAlgebra B G) :
    D.toQuot Z x = 0 ↔ x ∈ D.chBar Z := by
  rw [← map_zero (D.toQuot Z)]
  exact (RingCon.eq _).trans (TwoSidedIdeal.mem_iff _ _).symm

private theorem cbc_exists {B' R : Type} [CommRing B'] [Ring R] [Algebra B' R] (J : TwoSidedIdeal R) :
    ∃ π : R →ₐ[B'] J.ringCon.Quotient, Function.Surjective π ∧ ∀ x, π x = 0 ↔ x ∈ J := by
  refine ⟨{ J.ringCon.mk' with commutes' := fun _ => rfl }, fun x => Quot.inductionOn x fun z => ⟨z, rfl⟩, fun x => ?_⟩
  exact (RingCon.eq _).trans (TwoSidedIdeal.mem_iff _ _).symm

private theorem cbc_semi {B B' R R' E E' : Type} [CommRing B] [CommRing B'] [Ring R] [Ring R'] [Ring E] [Ring E']
    [Algebra B R] [Algebra B E] [Algebra B' R'] [Algebra B' E'] (g : B →+* B') (φ : R →+* R')
    (hφ : ∀ b, φ (algebraMap B R b) = algebraMap B' R' (g b)) (p : R →ₐ[B] E) (hp : Function.Surjective p)
    (π : R' →ₐ[B'] E') (hk : ∀ x, p x = 0 → π (φ x) = 0) :
    ∃ ψ : E →+* E', (∀ x, ψ (p x) = π (φ x)) ∧ ∀ (b : B) (x : E), ψ (b • x) = g b • ψ x := by
  let ψ : E →+* E' := (p : R →+* E).liftOfSurjective hp ⟨(π : R' →+* E').comp φ, fun x hx => hk x hx⟩
  have h1 : ∀ x, ψ (p x) = π (φ x) := fun x =>
    RingHom.liftOfRightInverse_comp_apply (p : R →+* E) _ _ _ x
  refine ⟨ψ, h1, fun b x => ?_⟩
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, ← p.commutes, h1, hφ, π.commutes]

theorem UpperTheory.V.Pa.BC.closure_bc :
    ∀ (n h : ℕ) (B B' : Type) [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [IsAdicComplete (maximalIdeal B) B] [Finite (ResidueField B)] [CommRing B'] [IsLocalRing B'] [IsNoetherianRing B'] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (D : GDet n B G) (χ : Fin n → G →* (ResidueField B)ˣ), D.IsCont (maximalIdeal B) → D.map (residue B) = GDet.ofChars χ → UpperTheory.V.CA.MultFree χ h → ∀ (g : B →+* B') [IsLocalHom g] (Z : Set (MonoidAlgebra B G)) (Z' : Set (MonoidAlgebra B' G)), (∀ z ∈ Z', z ∈ TwoSidedIdeal.span (MonoidAlgebra.mapRingHom G g '' {y | y ∈ D.chBar Z})) → ∀ z ∈ (D.map g).chBar Z', z ∈ TwoSidedIdeal.span (MonoidAlgebra.mapRingHom G g '' {y | y ∈ D.chBar Z}) := by
  intro n h B B' _ _ _ _ _ _ _ _ G _ _ _ _ _ D χ hc hr hm g _ Z Z' hZ' z hz
  obtain ⟨⟨s, -, hs⟩, -, hU⟩ := UpperTheory.V.CA.finE D χ hc hr hm Z
  set J := TwoSidedIdeal.span (MonoidAlgebra.mapRingHom G g '' {y | y ∈ D.chBar Z}) with hJ
  obtain ⟨π, hπ, hπ0⟩ := cbc_exists (B' := B') J
  have hsurj : Function.Surjective (D.toQuot Z) := fun x => Quot.inductionOn x fun z => ⟨z, rfl⟩
  have hsing : ∀ u : G, MonoidAlgebra.mapRingHom G g (MonoidAlgebra.single u 1) = MonoidAlgebra.single u 1 := by
    intro u
    simp
  obtain ⟨ψ, hψ, hψs⟩ := cbc_semi g (MonoidAlgebra.mapRingHom G g) (fun b => by simp)
    (D.toQuot Z) hsurj π (fun x hx => (hπ0 _).2 (TwoSidedIdeal.subset_span ⟨x, (cbc_zero D Z x).1 hx, rfl⟩))
  have hsp : ∀ x, ψ x ∈ Submodule.span B' ((fun u => π (MonoidAlgebra.single u 1)) '' (s : Set G)) := by
    intro x
    have hx : x ∈ Submodule.span B ((fun g => D.toQuot Z (MonoidAlgebra.single g 1)) '' (s : Set G)) :=
      hs ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, hu, rfl⟩ := hx
      rw [hψ, hsing]
      exact Submodule.subset_span ⟨u, hu, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [hψs]; exact Submodule.smul_mem _ _ hx
  have hfin : Module.Finite B' J.ringCon.Quotient := by
    refine ⟨Submodule.fg_def.2 ⟨_, s.finite_toSet.image (fun u => π (MonoidAlgebra.single u 1)), ?_⟩⟩
    rw [eq_top_iff]
    intro x _
    obtain ⟨y, rfl⟩ := hπ x
    induction y using MonoidAlgebra.induction_linear with
    | zero => rw [map_zero]; exact zero_mem _
    | add x y hx hy => rw [map_add]; exact add_mem (hx trivial) (hy trivial)
    | single u a =>
      have : (MonoidAlgebra.single u a : MonoidAlgebra B' G) = a • MonoidAlgebra.single u 1 := by
        rw [MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
      rw [this, map_smul]
      refine Submodule.smul_mem _ _ ?_
      have := hsp (D.toQuot Z (MonoidAlgebra.single u 1))
      rwa [hψ, hsing] at this
  refine (hπ0 z).1 (cbc_krull (B := B') _ fun N => ?_)
  obtain ⟨U, hU⟩ := hU N
  simp only [GDet.chBar, closureIdeal, TwoSidedIdeal.mem_iInf] at hz
  refine cbc_span π _ _ ?_ (hz N U)
  rintro t (((ht | ht) | ⟨a, ha, rfl⟩) | ⟨u, hu, rfl⟩)
  · have h1 : t ∈ TwoSidedIdeal.span (D.map g).CH := TwoSidedIdeal.subset_span ht
    rw [UpperTheory.V.CA.g_chmap] at h1
    have h2 : t ∈ J := TwoSidedIdeal.span_mono (Set.image_mono fun y hy => cbc_sub _ _ (Or.inl hy)) h1
    rw [(hπ0 t).2 h2]
    exact zero_mem _
  · rw [(hπ0 t).2 (hZ' t ht)]
    exact zero_mem _
  · have : (MonoidAlgebra.single 1 a : MonoidAlgebra B' G) = a • 1 := by
      rw [MonoidAlgebra.one_def, MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
    rw [this, map_smul]
    exact Submodule.smul_mem_smul ha Submodule.mem_top
  · have hle : (maximalIdeal B ^ N).map g ≤ maximalIdeal B' ^ N := by
      rw [Ideal.map_pow]
      exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 fun a ha => Ideal.mem_comap.2 (map_nonunit g a ha)) N
    have key : ∀ x ∈ (maximalIdeal B ^ N) • (⊤ : Submodule B (D.CHQuot Z)),
        ψ x ∈ (maximalIdeal B' ^ N) • (⊤ : Submodule B' J.ringCon.Quotient) := by
      intro x hx
      refine Submodule.smul_induction_on hx (fun a ha y _ => ?_) (fun x y hx hy => ?_)
      · rw [hψs]
        exact Submodule.smul_mem_smul (hle (Ideal.mem_map_of_mem g ha)) Submodule.mem_top
      · rw [map_add]; exact add_mem hx hy
    have := key _ (hU u hu)
    rw [map_sub, map_one, hψ, hsing] at this
    rw [map_sub, map_one]
    exact this
end
