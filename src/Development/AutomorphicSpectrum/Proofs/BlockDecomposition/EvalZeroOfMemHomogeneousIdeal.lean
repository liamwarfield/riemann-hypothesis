module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.TopologicalKrullDimLeOfIrreducibleCloseds

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalZeroOfMemHomogeneousIdeal
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace GlobalTheory.CompanionTheory.GeoVanish

open HomogeneousLocalization MvPolynomial

variable {K : Type} [Field K] {N : ℕ}

theorem away_mk_zero {x : MvPolynomial (Fin (N + 1)) K} (hx : x ∈ grK K N 1) (n : ℕ)
    (h0 : (0 : MvPolynomial (Fin (N + 1)) K) ∈ grK K N (n • 1)) :
    Away.mk (grK K N) hx n 0 h0 = 0 := by
  apply HomogeneousLocalization.val_injective
  simp only [Away.val_mk, HomogeneousLocalization.val_zero, Localization.mk_zero]

theorem away_mk_add {x : MvPolynomial (Fin (N + 1)) K} (hx : x ∈ grK K N 1) (n : ℕ)
    {a b : MvPolynomial (Fin (N + 1)) K} (ha : a ∈ grK K N (n • 1)) (hb : b ∈ grK K N (n • 1))
    (hab : a + b ∈ grK K N (n • 1)) :
    Away.mk (grK K N) hx n (a + b) hab = Away.mk (grK K N) hx n a ha + Away.mk (grK K N) hx n b hb := by
  apply HomogeneousLocalization.val_injective
  simp only [Away.val_mk, HomogeneousLocalization.val_add, Localization.add_mk_self]

theorem away_mk_mul {x : MvPolynomial (Fin (N + 1)) K} (hx : x ∈ grK K N 1) {k m n : ℕ} (hn : k + m = n)
    {a b : MvPolynomial (Fin (N + 1)) K} (ha : a ∈ grK K N (k • 1)) (hb : b ∈ grK K N (m • 1))
    (hab : a * b ∈ grK K N (n • 1)) :
    Away.mk (grK K N) hx n (a * b) hab = Away.mk (grK K N) hx k a ha * Away.mk (grK K N) hx m b hb := by
  subst hn
  apply HomogeneousLocalization.val_injective
  simp only [Away.val_mk, HomogeneousLocalization.val_mul, Localization.mk_mul]
  congr 1
  exact Subtype.ext (pow_add x k m)

theorem chart_zero {R : Type} [CommRing R] {x : MvPolynomial (Fin (N + 1)) K} (hx : x ∈ grK K N 1)
    (φ : Away (grK K N) x →+* R) (S : Set (MvPolynomial (Fin (N + 1)) K))
    (hS : ∀ f ∈ S, ∃ (d : ℕ) (hf : f ∈ grK K N (d • 1)), φ (Away.mk (grK K N) hx d f hf) = 0)
    {p : MvPolynomial (Fin (N + 1)) K} (hp : p ∈ Ideal.span S) :
    ∀ (n : ℕ) (f : MvPolynomial (Fin (N + 1)) K) (hf : f ∈ grK K N (n • 1)),
      f = (DirectSum.decompose (grK K N) p n : MvPolynomial (Fin (N + 1)) K) →
        φ (Away.mk (grK K N) hx n f hf) = 0 := by
  have hmem : ∀ (q : MvPolynomial (Fin (N + 1)) K) (n : ℕ),
      (DirectSum.decompose (grK K N) q n : MvPolynomial (Fin (N + 1)) K) ∈ grK K N (n • 1) := by
    intro q n
    simpa using (DirectSum.decompose (grK K N) q n).2
  have hzero : ∀ (n : ℕ) (f : MvPolynomial (Fin (N + 1)) K) (hf : f ∈ grK K N (n • 1)),
      f = (DirectSum.decompose (grK K N) (0 : MvPolynomial (Fin (N + 1)) K) n : MvPolynomial (Fin (N + 1)) K) →
        φ (Away.mk (grK K N) hx n f hf) = 0 := by
    intro n f hf h
    have h0 : f = 0 := by simpa using h
    subst h0
    rw [away_mk_zero, map_zero]
  have hadd : ∀ (p q : MvPolynomial (Fin (N + 1)) K),
      (∀ (n : ℕ) (f : MvPolynomial (Fin (N + 1)) K) (hf : f ∈ grK K N (n • 1)),
        f = (DirectSum.decompose (grK K N) p n : MvPolynomial (Fin (N + 1)) K) →
          φ (Away.mk (grK K N) hx n f hf) = 0) →
      (∀ (n : ℕ) (f : MvPolynomial (Fin (N + 1)) K) (hf : f ∈ grK K N (n • 1)),
        f = (DirectSum.decompose (grK K N) q n : MvPolynomial (Fin (N + 1)) K) →
          φ (Away.mk (grK K N) hx n f hf) = 0) →
      ∀ (n : ℕ) (f : MvPolynomial (Fin (N + 1)) K) (hf : f ∈ grK K N (n • 1)),
        f = (DirectSum.decompose (grK K N) (p + q) n : MvPolynomial (Fin (N + 1)) K) →
          φ (Away.mk (grK K N) hx n f hf) = 0 := by
    intro p q ihp ihq n f hf h
    have h' : f = (DirectSum.decompose (grK K N) p n : MvPolynomial (Fin (N + 1)) K) +
        (DirectSum.decompose (grK K N) q n : MvPolynomial (Fin (N + 1)) K) := by
      rw [h, DirectSum.decompose_add, DirectSum.add_apply, AddMemClass.coe_add]
    subst h'
    rw [away_mk_add hx n (hmem p n) (hmem q n), map_add (f := _), ihp n _ _ rfl, ihq n _ _ rfl, add_zero]
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨d, hd, h0⟩ := hS p hp
    intro n f hf h
    have hd' : p ∈ grK K N d := by simpa using hd
    by_cases hnd : n = d
    · subst hnd
      have : f = p := h.trans (DirectSum.decompose_of_mem_same _ hd')
      subst this
      exact h0
    · have h1 : f = 0 := h.trans (DirectSum.decompose_of_mem_ne _ hd' (Ne.symm hnd))
      subst h1
      rw [away_mk_zero, map_zero]
  | zero => exact hzero
  | add p q _ _ ihp ihq => exact hadd p q ihp ihq
  | smul a p _ ih =>
    induction a using DirectSum.Decomposition.inductionOn (grK K N) with
    | zero => simpa using hzero
    | @homogeneous k m =>
      intro n f hf h
      rw [smul_eq_mul] at h
      by_cases hk : k ≤ n
      · rw [DirectSum.coe_decompose_mul_of_left_mem_of_le _ m.2 hk] at h
        subst h
        have hm1 : (m : MvPolynomial (Fin (N + 1)) K) ∈ grK K N (k • 1) := by simpa using m.2
        rw [away_mk_mul hx (by omega : k + (n - k) = n) hm1 (hmem p (n - k)), map_mul,
          ih (n - k) _ _ rfl, mul_zero]
      · rw [DirectSum.coe_decompose_mul_of_left_mem_of_not_le _ m.2 hk] at h
        subst h
        rw [away_mk_zero, map_zero]
    | add a b iha ihb =>
      rw [add_smul]
      exact hadd _ _ iha ihb

theorem evV_res {X : Scheme.{0}} (i : X ⟶ PSpace K N) (g : MvPolynomial (Fin (N + 1)) K) {V W : X.Opens}
    (hV : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) g) (h : W ≤ V) (y : Away (grK K N) g) :
    resO h (evV i g V hV y) = evV i g W (h.trans hV) y := by
  have := Scheme.Hom.appLE_map i hV (homOfLE h).op
  simp only [evV]
  exact congr($(this).hom ((Proj.awayToSection (grK K N) g).hom y))

theorem evV_awayMap {X : Scheme.{0}} (i : X ⟶ PSpace K N) {a b c : MvPolynomial (Fin (N + 1)) K} {m : ℕ}
    (hb : b ∈ grK K N m) (hc : c = a * b) {W : X.Opens} (hW : W ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) c)
    (hW' : W ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) a) (y : Away (grK K N) a) :
    evV i c W hW (HomogeneousLocalization.awayMap (grK K N) hb hc y) = evV i a W hW' y := by
  have h1 := Proj.awayMap_awayToSection (grK K N) hb hc
  have h2 := Scheme.Hom.map_appLE i hW (homOfLE (Proj.basicOpen_mono (grK K N) a c ⟨_, hc⟩)).op
  have h3 : (Proj.awayToSection (grK K N) c).hom (HomogeneousLocalization.awayMap (grK K N) hb hc y) =
      ((PSpace K N).presheaf.map (homOfLE (Proj.basicOpen_mono (grK K N) a c ⟨_, hc⟩)).op).hom
        ((Proj.awayToSection (grK K N) a).hom y) := congr($(h1).hom y)
  simp only [evV, RingHom.comp_apply]
  rw [h3]
  exact congr($(h2).hom ((Proj.awayToSection (grK K N) a).hom y))

theorem exists_chart (p : PSpace K N) : ∃ j, p ∈ Proj.basicOpen (grK K N) (X j : MvPolynomial (Fin (N + 1)) K) := by
  have h : ⨆ j, Proj.basicOpen (grK K N) (X j : MvPolynomial (Fin (N + 1)) K) = ⊤ := by
    refine Proj.iSup_basicOpen_eq_top _ _ ((HomogeneousIdeal.toIdeal_irrelevant_le _).2 fun n hn f hf => ?_)
    change f ∈ Ideal.span _
    rw [← Set.image_univ, mem_ideal_span_X_image]
    intro m hm
    by_contra! H
    obtain rfl : m = 0 := Finsupp.ext fun i => H i (Set.mem_univ i)
    have hf' : f ∈ grK K N n := hf
    have := ((mem_homogeneousSubmodule _ _).1 hf') (mem_support_iff.1 hm)
    simp only [map_zero] at this
    omega
  exact TopologicalSpace.Opens.mem_iSup.1 (h.ge (Set.mem_univ p))

theorem ratio_eq {g x f : MvPolynomial (Fin (N + 1)) K} {e s : ℕ} (hg : g ∈ grK K N e) (hx : x ∈ grK K N 1)
    (hf : f ∈ grK K N (s • e)) (hf1 : f ∈ grK K N ((s • e) • 1)) (hxs : x ^ (s • e) ∈ grK K N (s • e)) :
    HomogeneousLocalization.awayMap (grK K N) hx (rfl : g * x = g * x) (Away.mk (grK K N) hg s f hf) =
      HomogeneousLocalization.awayMap (grK K N) hx (rfl : g * x = g * x) (Away.mk (grK K N) hg s (x ^ (s • e)) hxs) *
        HomogeneousLocalization.awayMap (grK K N) hg (mul_comm g x) (Away.mk (grK K N) hx (s • e) f hf1) := by
  apply HomogeneousLocalization.val_injective
  simp only [awayMap_mk, Away.val_mk, HomogeneousLocalization.val_mul, Localization.mk_mul]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_mul, smul_eq_mul]
  ring

end GlobalTheory.CompanionTheory.GeoVanish


open GlobalTheory.CompanionTheory.GeoVanish in
theorem GlobalTheory.CompanionTheory.GeoVanish.homIdeal_vanish : ∀ {K : Type} [Field K] {X : Scheme.{0}} {N : ℕ} (i : X ⟶ PSpace K N), ∀ {g : MvPolynomial (Fin (N + 1)) K} {e : ℕ} (he : 0 < e) (hg : g ∈ grK K N e) {s : ℕ} {f : MvPolynomial (Fin (N + 1)) K} (hf : f ∈ grK K N (s • e)), f ∈ homIdeal i → ∀ (V : X.Opens) (hV : V ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) g), evV i g V hV (HomogeneousLocalization.Away.mk (grK K N) hg s f hf) = 0 := by
  intro K _ X N i g e he hg s f hf hfI V hV
  have hf1 : f ∈ grK K N ((s • e) • 1) := by simpa using hf
  have key : ∀ j : Fin (N + 1), evV i (MvPolynomial.X j) (i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j)) le_rfl
      (HomogeneousLocalization.Away.mk (grK K N) (xv_mem K N j) (s • e) f hf1) = 0 := by
    intro j
    refine chart_zero (xv_mem K N j) (evV i (MvPolynomial.X j) _ le_rfl) _ ?_ hfI (s • e) f hf1
      (DirectSum.decompose_of_mem_same _ hf).symm
    rintro p ⟨d, hp, h⟩
    exact ⟨d, hp, h j⟩
  refine TopCat.Sheaf.eq_of_locally_eq' X.sheaf
    (fun j : Fin (N + 1) => V ⊓ i ⁻¹ᵁ Proj.basicOpen (grK K N) (MvPolynomial.X j)) V
    (fun j => homOfLE inf_le_left) ?_ _ _ ?_
  · intro p hp
    obtain ⟨j, hj⟩ := exists_chart (i p)
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨j, ?_⟩
    exact And.intro hp hj
  · intro j
    set x : MvPolynomial (Fin (N + 1)) K := MvPolynomial.X j with hxdef
    have hx : x ∈ grK K N 1 := xv_mem K N j
    set W := V ⊓ i ⁻¹ᵁ Proj.basicOpen (grK K N) x with hWdef
    have hWg : W ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) g := inf_le_left.trans hV
    have hWx : W ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) x := inf_le_right
    have hWgx : W ≤ i ⁻¹ᵁ Proj.basicOpen (grK K N) (g * x) := by
      rw [Proj.basicOpen_mul]
      exact fun p hp => And.intro (hWg hp) (hWx hp)
    have hxs : x ^ (s • e) ∈ grK K N (s • e) := by
      simpa using SetLike.pow_mem_graded (s • e) hx
    have h0 : evV i x W hWx (HomogeneousLocalization.Away.mk (grK K N) hx (s • e) f hf1) = 0 := by
      rw [← evV_res i x le_rfl hWx, key j, map_zero]
    have h1 : evV i g W hWg (HomogeneousLocalization.Away.mk (grK K N) hg s f hf) = 0 := by
      rw [← evV_awayMap i hx rfl hWgx hWg, ratio_eq hg hx hf hf1 hxs, map_mul,
        evV_awayMap i hg (mul_comm g x) hWgx hWx, h0, mul_zero]
    change resO (inf_le_left : W ≤ V) (evV i g V hV _) = resO (inf_le_left : W ≤ V) 0
    rw [map_zero, evV_res i g hV inf_le_left]
    exact h1
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CubeResApply
set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite Limits Simplicial

namespace GlobalTheory.CompanionTheory.Hodge.Nerve

variable {R : Type} [CommRing R]

section Cochains

variable {C : Type} [Category.{0} C]

abbrev NC (G : C ⥤ ModuleCat.{0} R) (n : ℕ) : Type :=
  ∀ c : Fin (n + 1) ⥤ C, G.obj (c.obj (Fin.last n))

def pullNC (G : C ⥤ ModuleCat.{0} R) {m n : ℕ} (θ : Fin (m + 1) →o Fin (n + 1)) : NC G m →ₗ[R] NC G n :=
  LinearMap.pi fun c ↦ (G.map (c.map (homOfLE (Fin.le_last (θ (Fin.last m)))))).hom ∘ₗ
    LinearMap.proj (R := R) (φ := fun c : Fin (m + 1) ⥤ C ↦ (G.obj (c.obj (Fin.last m)) : Type))
      (θ.monotone.functor ⋙ c)

theorem pullNC_apply (G : C ⥤ ModuleCat.{0} R) {m n : ℕ} (θ : Fin (m + 1) →o Fin (n + 1)) (f : NC G m)
    (c : Fin (n + 1) ⥤ C) :
    pullNC G θ f c = (G.map (c.map (homOfLE (Fin.le_last (θ (Fin.last m)))))).hom (f (θ.monotone.functor ⋙ c)) :=
  rfl

theorem map_map_chain (G : C ⥤ ModuleCat.{0} R) {n : ℕ} (c : Fin (n + 1) ⥤ C) {x y z : Fin (n + 1)} (a : x ≤ y)
    (b : y ≤ z) (v : G.obj (c.obj x)) :
    (G.map (c.map (homOfLE b))).hom ((G.map (c.map (homOfLE a))).hom v) =
      (G.map (c.map (homOfLE (a.trans b)))).hom v := by
  rw [← ModuleCat.comp_apply, ← G.map_comp, ← c.map_comp]
  rfl

def cosimp (G : C ⥤ ModuleCat.{0} R) : CosimplicialObject (ModuleCat.{0} R) where
  obj n := ModuleCat.of R (NC G n.len)
  map θ := ModuleCat.ofHom (pullNC G θ.toOrderHom)
  map_id n := by
    refine ModuleCat.hom_ext (LinearMap.ext fun f ↦ funext fun c ↦ ?_)
    have e : c.map (homOfLE (Fin.le_last (Fin.last n.len))) = 𝟙 _ := c.map_id _
    change (G.map (c.map (homOfLE (Fin.le_last (Fin.last n.len))))).hom (f c) = f c
    rw [e, G.map_id]
    rfl
  map_comp {a b d} θ ψ := by
    refine ModuleCat.hom_ext (LinearMap.ext fun f ↦ funext fun c ↦ ?_)
    change (G.map (c.map _)).hom (f ((θ ≫ ψ).toOrderHom.monotone.functor ⋙ c)) =
      (G.map (c.map _)).hom ((G.map (c.map (homOfLE (ψ.toOrderHom.monotone (Fin.le_last (θ.toOrderHom (Fin.last a.len))))))).hom
        (f (θ.toOrderHom.monotone.functor ⋙ ψ.toOrderHom.monotone.functor ⋙ c)))
    exact (map_map_chain G c _ _ _).symm

def cosimpMap {G G' : C ⥤ ModuleCat.{0} R} (φ : G ⟶ G') : cosimp G ⟶ cosimp G' where
  app n := ModuleCat.ofHom (LinearMap.pi fun c ↦ (φ.app _).hom ∘ₗ
    LinearMap.proj (R := R) (φ := fun c : Fin (n.len + 1) ⥤ C ↦ (G.obj (c.obj (Fin.last n.len)) : Type)) c)
  naturality a b θ := by
    refine ModuleCat.hom_ext (LinearMap.ext fun f ↦ funext fun c ↦ ?_)
    exact congr(($(φ.naturality (c.map (homOfLE (Fin.le_last (θ.toOrderHom (Fin.last a.len)))))).hom _))

def cosimpFunctor : (C ⥤ ModuleCat.{0} R) ⥤ CosimplicialObject (ModuleCat.{0} R) where
  obj := cosimp
  map := cosimpMap
  map_id _ := rfl
  map_comp _ _ := rfl

def nerveCx : (C ⥤ ModuleCat.{0} R) ⥤ CochainComplex (ModuleCat.{0} R) ℕ :=
  cosimpFunctor ⋙ AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat.{0} R)

instance : (nerveCx (R := R) (C := C)).PreservesZeroMorphisms where
  map_zero G G' := by
    refine HomologicalComplex.hom_ext _ _ fun n ↦ ModuleCat.hom_ext (LinearMap.ext fun f ↦ funext fun c ↦ ?_)
    change (0 : G.obj _ ⟶ G'.obj _).hom (f c) = 0
    rfl

def dNC (G : C ⥤ ModuleCat.{0} R) (n : ℕ) : NC G n →ₗ[R] NC G (n + 1) :=
  ∑ i : Fin (n + 2), ((-1 : R) ^ (i : ℕ)) • pullNC G (Fin.succAboveOrderEmb i).toOrderHom

theorem nerveCx_d (G : C ⥤ ModuleCat.{0} R) (n : ℕ) :
    (nerveCx.obj G).d n (n + 1) = ModuleCat.ofHom (dNC G n) := by
  have h0 : (nerveCx.obj G).d n (n + 1) = AlgebraicTopology.AlternatingCofaceMapComplex.objD (cosimp G) n :=
    CochainComplex.of_d (fun n ↦ (cosimp G).obj ⦋n⦌) (AlgebraicTopology.AlternatingCofaceMapComplex.objD (cosimp G)) n
  refine h0.trans ?_
  change (∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • (ModuleCat.ofHom (pullNC G (Fin.succAboveOrderEmb i).toOrderHom) :
    ModuleCat.of R (NC G n) ⟶ ModuleCat.of R (NC G (n + 1)))) = _
  refine ModuleCat.hom_ext ?_
  rw [ModuleCat.hom_ofHom, ModuleCat.hom_sum]
  unfold dNC
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have h : ((-1 : R) ^ (i : ℕ)) = (((-1 : ℤ) ^ (i : ℕ) : ℤ) : R) := by push_cast; rfl
  rw [h, Int.cast_smul_eq_zsmul, ModuleCat.hom_zsmul, ModuleCat.hom_ofHom]

@[simps] def toMod (F : C ⥤ CommAlgCat.{0} R) : C ⥤ ModuleCat.{0} R where
  obj T := ModuleCat.of R (F.obj T)
  map φ := ModuleCat.ofHom (GlobalTheory.CatCoh.mp F φ).toLinearMap
  map_id T := ModuleCat.hom_ext (LinearMap.ext fun b ↦ GlobalTheory.CatCoh.mp_id F T b)
  map_comp φ ψ := ModuleCat.hom_ext (LinearMap.ext fun b ↦ GlobalTheory.CatCoh.mp_comp F φ ψ b)

end Cochains

section Cube

variable {P : Type} [SemilatticeInf P] {κ : Type} (e : κ → P)

def cubeRes (G : Pᵒᵖ ⥤ ModuleCat.{0} R) {s t : Finset κ} (h : s ⊆ t) :
    (∀ hs : PLift s.Nonempty, G.obj (op (s.inf' hs.down e))) →ₗ[R]
      ∀ ht : PLift t.Nonempty, G.obj (op (t.inf' ht.down e)) :=
  LinearMap.pi fun _ ↦ if hs : s.Nonempty then
    (G.map (homOfLE (Finset.inf'_mono e h hs)).op).hom ∘ₗ
      LinearMap.proj (R := R) (φ := fun hs : PLift s.Nonempty ↦ (G.obj (op (s.inf' hs.down e)) : Type)) ⟨hs⟩
  else 0

theorem cubeRes_apply (G : Pᵒᵖ ⥤ ModuleCat.{0} R) {s t : Finset κ} (h : s ⊆ t)
    (x : ∀ hs : PLift s.Nonempty, G.obj (op (s.inf' hs.down e))) (hs : s.Nonempty) (ht : PLift t.Nonempty) :
    cubeRes e G h x ht = (G.map (homOfLE (Finset.inf'_mono e h hs)).op).hom (x ⟨hs⟩) := by
  simp [cubeRes, hs]

theorem cubeRes_empty (G : Pᵒᵖ ⥤ ModuleCat.{0} R) {s t : Finset κ} (h : s ⊆ t)
    (x : ∀ hs : PLift s.Nonempty, G.obj (op (s.inf' hs.down e))) (hs : ¬ s.Nonempty) (ht : PLift t.Nonempty) :
    cubeRes e G h x ht = 0 := by
  simp [cubeRes, hs]

def cubeOf (G : Pᵒᵖ ⥤ ModuleCat.{0} R) : Cube.{0} κ R :=
  Cube.mk (fun s ↦ ModuleCat.of R (∀ hs : PLift s.Nonempty, G.obj (op (s.inf' hs.down e))))
    (fun h ↦ cubeRes e G h)
    (fun s x ↦ funext fun hs ↦ by
      rw [cubeRes_apply e G _ x hs.down hs]
      exact congr(($(G.map_id (op (s.inf' hs.down e)))).hom (x hs)))
    (fun {s t w} h h' x ↦ funext fun hw ↦ by
      by_cases hs : s.Nonempty
      · rw [cubeRes_apply e G h' _ (hs.mono h) hw, cubeRes_apply e G h x hs ⟨hs.mono h⟩,
          cubeRes_apply e G (h.trans h') x hs hw, ← ModuleCat.comp_apply, ← G.map_comp]
        rfl
      · rw [cubeRes_empty e G (h.trans h') x hs hw]
        by_cases ht : t.Nonempty
        · rw [cubeRes_apply e G h' _ ht hw, cubeRes_empty e G h x hs ⟨ht⟩, map_zero]
        · rw [cubeRes_empty e G h' _ ht hw])

def cubeOfMap {G G' : Pᵒᵖ ⥤ ModuleCat.{0} R} (φ : G ⟶ G') : cubeOf e G ⟶ cubeOf e G' :=
  Cube.homMk κ R (fun s ↦ LinearMap.pi fun hs ↦ (φ.app _).hom ∘ₗ
      LinearMap.proj (R := R) (φ := fun hs : PLift s.Nonempty ↦ (G.obj (op (s.inf' hs.down e)) : Type)) hs)
    (fun {s t} h x ↦ funext fun ht ↦ by
      by_cases hs : s.Nonempty
      · refine ((congrArg (φ.app _).hom (cubeRes_apply e G h x hs ht)).trans ?_).trans
          (cubeRes_apply e G' h _ hs ht).symm
        exact congr(($(φ.naturality (homOfLE (Finset.inf'_mono e h hs)).op)).hom (x ⟨hs⟩))
      · exact ((congrArg (φ.app _).hom (cubeRes_empty e G h x hs ht)).trans (map_zero _)).trans
          (cubeRes_empty e G' h _ hs ht).symm)

def cubeOfFunctor : (Pᵒᵖ ⥤ ModuleCat.{0} R) ⥤ Cube.{0} κ R where
  obj := cubeOf e
  map := cubeOfMap e
  map_id G := by
    ext s
    rfl
  map_comp φ ψ := by
    ext s
    rfl

def cechOf [LinearOrder κ] : (Pᵒᵖ ⥤ ModuleCat.{0} R) ⥤ CochainComplex (ModuleCat.{0} R) ℕ :=
  cubeOfFunctor e ⋙ cechFunctor κ R

instance : (cubeOfFunctor (R := R) e).PreservesZeroMorphisms := ⟨fun G G' ↦ by ext s; rfl⟩

instance [LinearOrder κ] : (cechOf (R := R) e).PreservesZeroMorphisms := by
  unfold cechOf
  infer_instance

end Cube

section Coinduced

variable {P : Type} [SemilatticeInf P]

def coind (M : P → ModuleCat.{0} R) : Pᵒᵖ ⥤ ModuleCat.{0} R where
  obj a := ModuleCat.of R (∀ b : {b : P // b ≤ a.unop}, M b.1)
  map {a a'} φ := ModuleCat.ofHom
    { toFun := fun f b ↦ f ⟨b.1, b.2.trans (leOfHom φ.unop)⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  map_id _ := rfl
  map_comp _ _ := rfl

def toCoind (G : Pᵒᵖ ⥤ ModuleCat.{0} R) : G ⟶ coind fun b ↦ G.obj (op b) where
  app a := ModuleCat.ofHom
    { toFun := fun x b ↦ (G.map (homOfLE b.2).op).hom x
      map_add' := fun x y ↦ funext fun b ↦ map_add _ x y
      map_smul' := fun r x ↦ funext fun b ↦ map_smul _ r x }
  naturality a a' φ := by
    refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ funext fun b ↦ ?_)
    change (G.map (homOfLE b.2).op).hom ((G.map φ).hom x) = (G.map (homOfLE (b.2.trans (leOfHom φ.unop))).op).hom x
    rw [← ModuleCat.comp_apply, ← G.map_comp]
    rfl

end Coinduced

end GlobalTheory.CompanionTheory.Hodge.Nerve
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullbackZeroCochainsAlgebraMap
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.HodgeLow

theorem qIsoAt_transport {R A₀ A₁ A₂ B₀ B₁ B₂ A₀' A₁' A₂' B₀' B₁' B₂' : Type} [CommRing R]
    [AddCommGroup A₀] [AddCommGroup A₁] [AddCommGroup A₂]
    [AddCommGroup B₀] [AddCommGroup B₁] [AddCommGroup B₂]
    [AddCommGroup A₀'] [AddCommGroup A₁'] [AddCommGroup A₂']
    [AddCommGroup B₀'] [AddCommGroup B₁'] [AddCommGroup B₂']
    [Module R A₀] [Module R A₁] [Module R A₂] [Module R B₀] [Module R B₁] [Module R B₂]
    [Module R A₀'] [Module R A₁'] [Module R A₂'] [Module R B₀'] [Module R B₁'] [Module R B₂']
    {a₀ : A₀ →ₗ[R] A₁} {a₁ : A₁ →ₗ[R] A₂} {b₀ : B₀ →ₗ[R] B₁} {b₁ : B₁ →ₗ[R] B₂} {f : A₁ →ₗ[R] B₁}
    {a₀' : A₀' →ₗ[R] A₁'} {a₁' : A₁' →ₗ[R] A₂'} {b₀' : B₀' →ₗ[R] B₁'} {b₁' : B₁' →ₗ[R] B₂'}
    {f' : A₁' →ₗ[R] B₁'}
    (ea₀ : A₀ ≃ₗ[R] A₀') (ea₁ : A₁ ≃ₗ[R] A₁') (ea₂ : A₂ ≃ₗ[R] A₂')
    (eb₀ : B₀ ≃ₗ[R] B₀') (eb₁ : B₁ ≃ₗ[R] B₁') (eb₂ : B₂ ≃ₗ[R] B₂')
    (ha₀ : ∀ x, ea₁ (a₀ x) = a₀' (ea₀ x)) (ha₁ : ∀ x, ea₂ (a₁ x) = a₁' (ea₁ x))
    (hb₀ : ∀ x, eb₁ (b₀ x) = b₀' (eb₀ x)) (hb₁ : ∀ x, eb₂ (b₁ x) = b₁' (eb₁ x))
    (hf : ∀ x, eb₁ (f x) = f' (ea₁ x)) (h : QIsoAt a₀ a₁ b₀ b₁ f) :
    QIsoAt a₀' a₁' b₀' b₁' f' := by
  refine ⟨fun x' hx' ⟨y', hy'⟩ ↦ ?_, fun z' hz' ↦ ?_⟩
  · obtain ⟨x, rfl⟩ := ea₁.surjective x'
    obtain ⟨y, rfl⟩ := eb₀.surjective y'
    have h1 : a₁ x = 0 := ea₂.injective (by rw [ha₁, hx', map_zero])
    have h2 : b₀ y = f x := eb₁.injective (by rw [hb₀, hy', hf])
    obtain ⟨w, rfl⟩ := h.1 x h1 ⟨y, h2⟩
    exact ⟨ea₀ w, (ha₀ w).symm⟩
  · obtain ⟨z, rfl⟩ := eb₁.surjective z'
    have h1 : b₁ z = 0 := eb₂.injective (by rw [hb₁, hz', map_zero])
    obtain ⟨x, y, hx, hy⟩ := h.2 z h1
    refine ⟨ea₁ x, eb₀ y, by rw [← ha₁, hx, map_zero], ?_⟩
    rw [← hf, ← map_sub, hy, hb₀]

section

variable {R : Type} [CommRing R] {C C' : Type} [Category.{0} C] [Category.{0} C']
  {F : C ⥤ CommAlgCat.{0} R} {F' : C' ⥤ CommAlgCat.{0} R}

theorem d2_apply (z : C2 F) {T T' T'' T''' : C} (φ : T ⟶ T') (ψ : T' ⟶ T'') (χ : T'' ⟶ T''') :
    d2 F z T T' T'' T''' φ ψ χ = z T' T'' T''' ψ χ - z T T'' T''' (φ ≫ ψ) χ +
      z T T' T''' φ (ψ ≫ χ) - mp F χ (z T T' T'' φ ψ) := rfl

theorem mem_Z2_iff (z : C2 F) : z ∈ Z2 F ↔ d2 F z = 0 := by
  refine ⟨fun h ↦ ?_, fun h T T' T'' T''' φ ψ χ ↦ ?_⟩
  · funext T T' T'' T''' φ ψ χ
    rw [d2_apply]
    have := h φ ψ χ
    simp only [Pi.zero_apply]
    linear_combination -this
  · have : d2 F z T T' T'' T''' φ ψ χ = 0 := by rw [h]; rfl
    rw [d2_apply] at this
    linear_combination -this

def pullbackZeroCochains (m : CoefMap (RingHom.id R) F F') : C0 F →ₗ[R] C0 F' where
  toFun g T := m.α T (g (m.G.obj T))
  map_add' _ _ := funext fun _ ↦ map_add _ _ _
  map_smul' _ _ := funext fun _ ↦ m.smul _ _ _

def pullbackOneCochains (m : CoefMap (RingHom.id R) F F') : C1 F →ₗ[R] C1 F' where
  toFun f T T' φ := m.α T' (f _ _ (m.G.map φ))
  map_add' _ _ := by funext T T' φ; exact map_add _ _ _
  map_smul' _ _ := by funext T T' φ; exact m.smul _ _ _

def pullbackTwoCochains (m : CoefMap (RingHom.id R) F F') : C2 F →ₗ[R] C2 F' where
  toFun z T T' T'' φ ψ := m.α T'' (z _ _ _ (m.G.map φ) (m.G.map ψ))
  map_add' _ _ := by funext T T' T'' φ ψ; exact map_add _ _ _
  map_smul' _ _ := by funext T T' T'' φ ψ; exact m.smul _ _ _

theorem cn_heq {n : ℕ} (f : Cn F n) {c c' : Fin (n + 1) ⥤ C} (h : c = c') : HEq (f c) (f c') := by
  subst h; rfl

theorem mk₀_comp (G : C' ⥤ C) (T : C') :
    ComposableArrows.mk₀ T ⋙ G = ComposableArrows.mk₀ (G.obj T) :=
  ComposableArrows.ext (fun i ↦ by fin_cases i; rfl) (fun i hi ↦ by omega)

theorem mk₁_comp (G : C' ⥤ C) {T T' : C'} (φ : T ⟶ T') :
    ComposableArrows.mk₁ φ ⋙ G = ComposableArrows.mk₁ (G.map φ) :=
  ComposableArrows.ext₁ rfl rfl (by
    change G.map φ = 𝟙 _ ≫ G.map φ ≫ 𝟙 _
    simp)

theorem mk₂_comp (G : C' ⥤ C) {T T' T'' : C'} (φ : T ⟶ T') (ψ : T' ⟶ T'') :
    ComposableArrows.mk₂ φ ψ ⋙ G = ComposableArrows.mk₂ (G.map φ) (G.map ψ) :=
  ComposableArrows.ext (fun i ↦ by fin_cases i <;> rfl) (fun i hi ↦ by
    obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
    · change G.map φ = 𝟙 _ ≫ G.map φ ≫ 𝟙 _
      simp
    · change G.map ψ = 𝟙 _ ≫ G.map ψ ≫ 𝟙 _
      simp)

theorem pull1_bijective (m : CoefMap (RingHom.id R) F F')
    (h : QIsoAt (d0 F) (d1 F) (d0 F') (d1 F') (pullbackOneCochains m)) : Function.Bijective m.pull1 := by
  refine ⟨(injective_iff_map_eq_zero m.pull1).2 fun c hc ↦ ?_, fun c' ↦ ?_⟩
  · obtain ⟨f, rfl⟩ := H1.mk_surjective F c
    rw [CoefMap.pullCohomologyOne_class] at hc
    obtain ⟨g, hg⟩ := H1.mk_eq_zero.1 hc
    have hf : d1 F f.1 = 0 := LinearMap.mem_ker.1 (commAlgFunctorCocyclesOne_eq_ker F ▸ f.2)
    obtain ⟨y, hy⟩ := h.1 f.1 hf ⟨g, hg⟩
    exact H1.mk_eq_zero.2 ⟨y, hy⟩
  · obtain ⟨f', rfl⟩ := H1.mk_surjective F' c'
    have hf : d1 F' f'.1 = 0 := LinearMap.mem_ker.1 (commAlgFunctorCocyclesOne_eq_ker F' ▸ f'.2)
    obtain ⟨x, y, hx, hy⟩ := h.2 f'.1 hf
    have hxm : x ∈ Z1 F := by rw [commAlgFunctorCocyclesOne_eq_ker]; exact hx
    refine ⟨H1.mk F ⟨x, hxm⟩, ?_⟩
    rw [CoefMap.pullCohomologyOne_class, H1.mk_eq_mk]
    exact ⟨y, hy.symm⟩

theorem pull2_bijective (m : CoefMap (RingHom.id R) F F')
    (h : QIsoAt (d1 F) (d2 F) (d1 F') (d2 F') (pullbackTwoCochains m)) : Function.Bijective m.pull2 := by
  refine ⟨(injective_iff_map_eq_zero m.pull2).2 fun c hc ↦ ?_, fun c' ↦ ?_⟩
  · obtain ⟨f, rfl⟩ := H2.mk_surjective F c
    rw [CoefMap.pullCohomologyTwo_class] at hc
    obtain ⟨g, hg⟩ := H2.mk_eq_zero.1 hc
    obtain ⟨y, hy⟩ := h.1 f.1 ((mem_Z2_iff _).1 f.2) ⟨g, hg⟩
    exact H2.mk_eq_zero.2 ⟨y, hy⟩
  · obtain ⟨f', rfl⟩ := H2.mk_surjective F' c'
    obtain ⟨x, y, hx, hy⟩ := h.2 f'.1 ((mem_Z2_iff _).1 f'.2)
    refine ⟨H2.mk F ⟨x, (mem_Z2_iff _).2 hx⟩, ?_⟩
    rw [CoefMap.pullCohomologyTwo_class, H2.mk_eq_mk]
    exact ⟨y, hy.symm⟩

theorem pullbackZeroCochains_algebraMap (m : CoefMap (RingHom.id R) F F') (r : R) :
    pullbackZeroCochains m (algebraMap R (C0 F) r) = algebraMap R (C0 F') r := by
  funext T
  change m.α T (algebraMap R _ r) = algebraMap R _ r
  rw [Algebra.algebraMap_eq_smul_one, m.smul, map_one, Algebra.algebraMap_eq_smul_one]
  rfl

theorem d0_algebraMap (r : R) : d0 F (algebraMap R (C0 F) r) = 0 := by
  funext T T' φ
  rw [amitsur_d0_apply]
  change algebraMap R _ r - mp F φ (algebraMap R _ r) = 0
  rw [AlgHom.commutes, sub_self]

theorem d0_pullbackZeroCochains (m : CoefMap (RingHom.id R) F F') (g : C0 F) :
    d0 F' (pullbackZeroCochains m g) = pullbackOneCochains m (d0 F g) := by
  funext T T' φ
  change m.α T' (g _) - mp F' φ (m.α T (g _)) = m.α T' (g _ - mp F (m.G.map φ) (g _))
  rw [map_sub, m.naturality]

theorem stein_iff (m : CoefMap (RingHom.id R) F F')
    (h : QIsoAt (0 : R →ₗ[R] C0 F) (d0 F) (0 : R →ₗ[R] C0 F') (d0 F') (pullbackZeroCochains m)) :
    Stein F ↔ Stein F' := by
  have hk : ∀ x, d0 F x = 0 → pullbackZeroCochains m x = 0 → x = 0 := fun x hx hp ↦ by
    obtain ⟨y, hy⟩ := h.1 x hx ⟨0, by rw [hp]; rfl⟩
    exact hy.symm
  have hs : ∀ z, d0 F' z = 0 → ∃ x, d0 F x = 0 ∧ pullbackZeroCochains m x = z := fun z hz ↦ by
    obtain ⟨x, y, hx, hy⟩ := h.2 z hz
    exact ⟨x, hx, sub_eq_zero.1 hy⟩
  constructor
  · rintro ⟨he, hi⟩
    refine ⟨fun y ↦ ⟨fun hy ↦ ?_, ?_⟩, fun r r' hr ↦ hi ?_⟩
    · obtain ⟨x, hx, rfl⟩ := hs y hy
      obtain ⟨r, rfl⟩ := (he x).1 hx
      exact ⟨r, (pullbackZeroCochains_algebraMap m r).symm⟩
    · rintro ⟨r, rfl⟩
      exact d0_algebraMap r
    · rw [← sub_eq_zero, ← map_sub]
      refine hk _ (d0_algebraMap _) ?_
      rw [pullbackZeroCochains_algebraMap, map_sub, hr, sub_self]
  · rintro ⟨he, hi⟩
    refine ⟨fun y ↦ ⟨fun hy ↦ ?_, ?_⟩, fun r r' hr ↦ hi ?_⟩
    · have h0 : d0 F' (pullbackZeroCochains m y) = 0 := by rw [d0_pullbackZeroCochains, hy, map_zero]
      obtain ⟨r, hr⟩ := (he _).1 h0
      refine ⟨r, ?_⟩
      have hr' : algebraMap R (C0 F') r = pullbackZeroCochains m y := hr
      have e : y - algebraMap R (C0 F) r = 0 := hk _ (by rw [map_sub, hy, d0_algebraMap, sub_self])
        (by rw [map_sub, pullbackZeroCochains_algebraMap, hr', sub_self])
      exact (sub_eq_zero.1 e).symm
    · rintro ⟨r, rfl⟩
      exact d0_algebraMap r
    · rw [← pullbackZeroCochains_algebraMap m, ← pullbackZeroCochains_algebraMap m, hr]

end

theorem lowSt_of_dictSt : DictSt → LowSt := by
  intro hD R _ C C' _ _ F F' m hQ
  obtain ⟨e₀, e₁, e₂, e₃, v₀, v₁, v₂, v₃, c₀, c₁, c₂⟩ := hD R C F
  obtain ⟨e₀', e₁', e₂', e₃', v₀', v₁', v₂', v₃', c₀', c₁', c₂'⟩ := hD R C' F'
  have p0 : ∀ f, e₀' (pulln m 0 f) = pullbackZeroCochains m (e₀ f) := fun f ↦ by
    funext T
    rw [v₀']
    change m.α T (f (ComposableArrows.mk₀ T ⋙ m.G)) = m.α T (e₀ f (m.G.obj T))
    rw [v₀]
    exact congrArg (m.α T) (eq_of_heq (cn_heq f (mk₀_comp m.G T)))
  have p1 : ∀ f, e₁' (pulln m 1 f) = pullbackOneCochains m (e₁ f) := fun f ↦ by
    funext T T' φ
    rw [v₁']
    change m.α T' (f (ComposableArrows.mk₁ φ ⋙ m.G)) = m.α T' (e₁ f _ _ (m.G.map φ))
    rw [v₁]
    exact congrArg (m.α T') (eq_of_heq (cn_heq f (mk₁_comp m.G φ)))
  have p2 : ∀ f, e₂' (pulln m 2 f) = pullbackTwoCochains m (e₂ f) := fun f ↦ by
    funext T T' T'' φ ψ
    rw [v₂']
    change m.α T'' (f (ComposableArrows.mk₂ φ ψ ⋙ m.G)) = m.α T'' (e₂ f _ _ _ (m.G.map φ) (m.G.map ψ))
    rw [v₂]
    exact congrArg (m.α T'') (eq_of_heq (cn_heq f (mk₂_comp m.G φ ψ)))
  refine ⟨pull1_bijective m ?_, pull2_bijective m ?_, stein_iff m ?_⟩
  · exact qIsoAt_transport e₀ e₁ e₂ e₀' e₁' e₂' c₀ c₁ c₀' c₁' p1 (hQ.2 0)
  · exact qIsoAt_transport e₁ e₂ e₃ e₁' e₂' e₃' c₁ c₂ c₁' c₂' p2 (hQ.2 1)
  · exact qIsoAt_transport (LinearEquiv.refl R R) e₀ e₁ (LinearEquiv.refl R R) e₀' e₁'
      (fun _ ↦ map_zero _) c₀ (fun _ ↦ map_zero _) c₀' p0 hQ.1

end GlobalTheory.CompanionTheory.HodgeLow
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.D2Apply
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.PerfExt

section Gen

variable (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R']

def Ext {N Q : Type} [AddCommGroup N] [Module R N] [AddCommGroup Q] [Module R' Q] (c : N → Q) : Prop :=
  ∃ e : R' ⊗[R] N ≃ₗ[R'] Q, ∀ b, e (1 ⊗ₜ b) = c b

variable {R R'}

theorem Ext.pi {J : Type} [Finite J] {N Q : J → Type} [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
    [∀ i, AddCommGroup (Q i)] [∀ i, Module R' (Q i)] (c : ∀ i, N i → Q i) (h : ∀ i, Ext R R' (c i)) :
    Ext R R' (fun (f : ∀ i, N i) i ↦ c i (f i)) := by
  classical
  have := Fintype.ofFinite J
  choose e he using h
  refine ⟨(TensorProduct.piRight R R' R' N).trans (LinearEquiv.piCongrRight e), fun b ↦ funext fun i ↦ ?_⟩
  simp [he]

variable {N N₂ Q Q₂ M : Type} [AddCommGroup N] [Module R N] [AddCommGroup N₂] [Module R N₂]
  [AddCommGroup Q] [Module R' Q] [AddCommGroup Q₂] [Module R' Q₂]
  [AddCommGroup M] [Module R' M] [Module R M] [IsScalarTower R R' M]


variable (M) in
def tw (E : R' ⊗[R] N ≃ₗ[R'] Q) : M ⊗[R] N ≃+ M ⊗[R'] Q :=
  ((AlgebraTensorModule.cancelBaseChange R R' R' M N).symm.trans (LinearEquiv.lTensor M E)).toAddEquiv

theorem tw_tmul (E : R' ⊗[R] N ≃ₗ[R'] Q) (x : M) (n : N) : tw M E (x ⊗ₜ n) = x ⊗ₜ E (1 ⊗ₜ n) := by
  simp [tw]

theorem tw_nat (E : R' ⊗[R] N ≃ₗ[R'] Q) (E₂ : R' ⊗[R] N₂ ≃ₗ[R'] Q₂) (g : N →ₗ[R] N₂) (h : Q →ₗ[R'] Q₂)
    (H : ∀ n, h (E (1 ⊗ₜ n)) = E₂ (1 ⊗ₜ g n)) (t : M ⊗[R] N) :
    tw M E₂ (g.lTensor M t) = h.lTensor M (tw M E t) := by
  induction t with
  | tmul x n => simp [tw_tmul, H]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

end Gen

theorem QIsoAt.transport {R R' A₀ A₁ A₂ B₀ B₁ B₂ A₀' A₁' A₂' B₀' B₁' B₂' : Type} [CommRing R] [CommRing R']
    [AddCommGroup A₀] [AddCommGroup A₁] [AddCommGroup A₂] [AddCommGroup B₀] [AddCommGroup B₁] [AddCommGroup B₂]
    [Module R A₀] [Module R A₁] [Module R A₂] [Module R B₀] [Module R B₁] [Module R B₂]
    [AddCommGroup A₀'] [AddCommGroup A₁'] [AddCommGroup A₂'] [AddCommGroup B₀'] [AddCommGroup B₁'] [AddCommGroup B₂']
    [Module R' A₀'] [Module R' A₁'] [Module R' A₂'] [Module R' B₀'] [Module R' B₁'] [Module R' B₂']
    {a₀ : A₀ →ₗ[R] A₁} {a₁ : A₁ →ₗ[R] A₂} {b₀ : B₀ →ₗ[R] B₁} {b₁ : B₁ →ₗ[R] B₂} {f : A₁ →ₗ[R] B₁}
    {a₀' : A₀' →ₗ[R'] A₁'} {a₁' : A₁' →ₗ[R'] A₂'} {b₀' : B₀' →ₗ[R'] B₁'} {b₁' : B₁' →ₗ[R'] B₂'} {f' : A₁' →ₗ[R'] B₁'}
    (u₁ : A₁ ≃+ A₁') (u₂ : A₂ ≃+ A₂') (v₁ : B₁ ≃+ B₁') (v₂ : B₂ ≃+ B₂')
    (h₁ : ∀ x, u₂ (a₁ x) = a₁' (u₁ x)) (h₂ : ∀ z, v₂ (b₁ z) = b₁' (v₁ z)) (hf : ∀ x, v₁ (f x) = f' (u₁ x))
    (ha : ∀ y, ∃ y', a₀' y' = u₁ (a₀ y)) (hb : ∀ y, ∃ y', b₀' y' = v₁ (b₀ y)) (hb' : ∀ y', ∃ y, v₁ (b₀ y) = b₀' y')
    (q : QIsoAt a₀ a₁ b₀ b₁ f) : QIsoAt a₀' a₁' b₀' b₁' f' := by
  obtain ⟨q₁, q₂⟩ := q
  refine ⟨fun x' hx ⟨y', hy⟩ ↦ ?_, fun z' hz ↦ ?_⟩
  · obtain ⟨x, rfl⟩ := u₁.surjective x'
    obtain ⟨y, hy'⟩ := hb' y'
    obtain ⟨w, hw⟩ := q₁ x (u₂.injective (by rw [h₁, hx, map_zero]))
      ⟨y, v₁.injective (by rw [hy', hy, hf])⟩
    obtain ⟨w', hw'⟩ := ha w
    exact ⟨w', by rw [hw', hw]⟩
  · obtain ⟨z, rfl⟩ := v₁.surjective z'
    obtain ⟨x, y, hx, hy⟩ := q₂ z (v₂.injective (by rw [h₂, hz, map_zero]))
    obtain ⟨y', hy'⟩ := hb y
    exact ⟨u₁ x, y', by rw [← h₁, hx, map_zero], by rw [hy', ← hy, map_sub, hf]⟩

section Main

theorem bc_ext {R R' N Q : Type} [CommRing R] [CommRing R'] [Algebra R R'] [AddCommGroup N] [Module R N]
    [AddCommGroup Q] [Module R' Q] (g h : R' ⊗[R] N →ₗ[R'] Q) (H : ∀ n, g (1 ⊗ₜ n) = h (1 ⊗ₜ n)) : g = h := by
  refine LinearMap.ext fun t ↦ ?_
  induction t with
  | tmul r n =>
    have e : r ⊗ₜ[R] n = r • ((1 : R') ⊗ₜ[R] n) := by simp [TensorProduct.smul_tmul']
    rw [e, map_smul, map_smul, H]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

theorem d2_apply {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R) (z : C2 F)
    {T T' T'' T''' : C} (φ : T ⟶ T') (ψ : T' ⟶ T'') (χ : T'' ⟶ T''') :
    d2 F z T T' T'' T''' φ ψ χ = z T' T'' T''' ψ χ - z T T'' T''' (φ ≫ ψ) χ + z T T' T''' φ (ψ ≫ χ) -
      mp F χ (z T T' T'' φ ψ) := rfl

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {C : Type} [Category.{0} C]
  {F : C ⥤ CommAlgCat.{0} R} {F' : C ⥤ CommAlgCat.{0} R'} [Finite C] [∀ T T' : C, Finite (T ⟶ T')]

theorem ext0 (m : BC F F') : Ext R R' (fun (f : C0 F) T ↦ m.α T (f T) : C0 F → C0 F') :=
  Ext.pi (fun T b ↦ m.α T b) fun T ↦ m.bij T

theorem ext1 (m : BC F F') : Ext R R' (fun (f : C1 F) T T' φ ↦ m.α T' (f T T' φ) : C1 F → C1 F') :=
  Ext.pi (Q := fun T ↦ ∀ (T' : C) (_ : T ⟶ T'), F'.obj T')
    (fun T (g : ∀ (T' : C) (_ : T ⟶ T'), F.obj T') T' φ ↦ m.α T' (g T' φ)) fun T ↦
  Ext.pi (Q := fun T' ↦ ∀ (_ : T ⟶ T'), F'.obj T')
    (fun T' (g : ∀ (_ : T ⟶ T'), F.obj T') φ ↦ m.α T' (g φ)) fun T' ↦
  Ext.pi (fun _ b ↦ m.α T' b) fun _ ↦ m.bij T'

theorem ext2 (m : BC F F') :
    Ext R R' (fun (f : C2 F) T T' T'' φ ψ ↦ m.α T'' (f T T' T'' φ ψ) : C2 F → C2 F') :=
  Ext.pi (Q := fun T ↦ ∀ (T' T'' : C) (_ : T ⟶ T') (_ : T' ⟶ T''), F'.obj T'')
    (fun T (g : ∀ (T' T'' : C) (_ : T ⟶ T') (_ : T' ⟶ T''), F.obj T'') T' T'' φ ψ ↦
      m.α T'' (g T' T'' φ ψ)) fun T ↦
  Ext.pi (Q := fun T' ↦ ∀ (T'' : C) (_ : T ⟶ T') (_ : T' ⟶ T''), F'.obj T'')
    (fun T' (g : ∀ (T'' : C) (_ : T ⟶ T') (_ : T' ⟶ T''), F.obj T'') T'' φ ψ ↦
      m.α T'' (g T'' φ ψ)) fun T' ↦
  Ext.pi (Q := fun T'' ↦ ∀ (_ : T ⟶ T') (_ : T' ⟶ T''), F'.obj T'')
    (fun T'' (g : ∀ (_ : T ⟶ T') (_ : T' ⟶ T''), F.obj T'') φ ψ ↦ m.α T'' (g φ ψ)) fun T'' ↦
  Ext.pi (Q := fun _ ↦ ∀ (_ : T' ⟶ T''), F'.obj T'')
    (fun φ (g : ∀ (_ : T' ⟶ T''), F.obj T'') ψ ↦ m.α T'' (g ψ)) fun _ ↦
  Ext.pi (fun _ b ↦ m.α T'' b) fun _ ↦ m.bij T''

theorem ext3 (m : BC F F') :
    Ext R R' (fun (f : C3 F) T T' T'' T''' φ ψ χ ↦ m.α T''' (f T T' T'' T''' φ ψ χ) : C3 F → C3 F') :=
  Ext.pi (Q := fun T ↦ ∀ (T' T'' T''' : C) (_ : T ⟶ T') (_ : T' ⟶ T'') (_ : T'' ⟶ T'''), F'.obj T''')
    (fun T (g : ∀ (T' T'' T''' : C) (_ : T ⟶ T') (_ : T' ⟶ T'') (_ : T'' ⟶ T'''), F.obj T''')
      T' T'' T''' φ ψ χ ↦ m.α T''' (g T' T'' T''' φ ψ χ)) fun T ↦
  Ext.pi (Q := fun T' ↦ ∀ (T'' T''' : C) (_ : T ⟶ T') (_ : T' ⟶ T'') (_ : T'' ⟶ T'''), F'.obj T''')
    (fun T' (g : ∀ (T'' T''' : C) (_ : T ⟶ T') (_ : T' ⟶ T'') (_ : T'' ⟶ T'''), F.obj T''')
      T'' T''' φ ψ χ ↦ m.α T''' (g T'' T''' φ ψ χ)) fun T' ↦
  Ext.pi (Q := fun T'' ↦ ∀ (T''' : C) (_ : T ⟶ T') (_ : T' ⟶ T'') (_ : T'' ⟶ T'''), F'.obj T''')
    (fun T'' (g : ∀ (T''' : C) (_ : T ⟶ T') (_ : T' ⟶ T'') (_ : T'' ⟶ T'''), F.obj T''')
      T''' φ ψ χ ↦ m.α T''' (g T''' φ ψ χ)) fun T'' ↦
  Ext.pi (Q := fun T''' ↦ ∀ (_ : T ⟶ T') (_ : T' ⟶ T'') (_ : T'' ⟶ T'''), F'.obj T''')
    (fun T''' (g : ∀ (_ : T ⟶ T') (_ : T' ⟶ T'') (_ : T'' ⟶ T'''), F.obj T''') φ ψ χ ↦
      m.α T''' (g φ ψ χ)) fun T''' ↦
  Ext.pi (Q := fun _ ↦ ∀ (_ : T' ⟶ T'') (_ : T'' ⟶ T'''), F'.obj T''')
    (fun φ (g : ∀ (_ : T' ⟶ T'') (_ : T'' ⟶ T'''), F.obj T''') ψ χ ↦ m.α T''' (g ψ χ)) fun _ ↦
  Ext.pi (Q := fun _ ↦ ∀ (_ : T'' ⟶ T'''), F'.obj T''')
    (fun ψ (g : ∀ (_ : T'' ⟶ T'''), F.obj T''') χ ↦ m.α T''' (g χ)) fun _ ↦
  Ext.pi (fun _ b ↦ m.α T''' b) fun _ ↦ m.bij T'''

theorem perf_ext (m : BC F F') (h : Perf F) : Perf F' := by
  obtain ⟨P₀, P₁, P₂, P₃, a₀, a₁, a₂, ψ₀, ψ₁, ψ₂, ⟨f₀, p₀⟩, ⟨f₁, p₁⟩, ⟨f₂, p₂⟩, ⟨f₃, p₃⟩, h₁₀, h₂₁, s₀, s₁,
    ⟨ψ₃, s₂⟩, hM⟩ := h
  obtain ⟨E₀, e₀⟩ := ext0 m
  obtain ⟨E₁, e₁⟩ := ext1 m
  obtain ⟨E₂, e₂⟩ := ext2 m
  obtain ⟨E₃, e₃⟩ := ext3 m
  have t₀ : ∀ x, d0 F' (E₀ (1 ⊗ₜ x)) = E₁ (1 ⊗ₜ d0 F x) := fun x ↦ by
    rw [e₀, e₁]
    funext T T' φ
    simp only [amitsur_d0_apply, map_sub, m.naturality]
  have t₁ : ∀ x, d1 F' (E₁ (1 ⊗ₜ x)) = E₂ (1 ⊗ₜ d1 F x) := fun x ↦ by
    rw [e₁, e₂]
    funext T T' T'' φ ψ
    simp only [d1_apply, map_sub, map_add (f := _), m.naturality]
  have t₂ : ∀ x, d2 F' (E₂ (1 ⊗ₜ x)) = E₃ (1 ⊗ₜ d2 F x) := fun x ↦ by
    rw [e₂, e₃]
    funext T T' T'' T''' φ ψ χ
    simp only [d2_apply, map_sub, map_add (f := _), m.naturality]
  refine ⟨.of R' (R' ⊗[R] P₀), .of R' (R' ⊗[R] P₁), .of R' (R' ⊗[R] P₂), .of R' (R' ⊗[R] P₃),
    a₀.baseChange R', a₁.baseChange R', a₂.baseChange R',
    E₀.toLinearMap ∘ₗ ψ₀.baseChange R', E₁.toLinearMap ∘ₗ ψ₁.baseChange R', E₂.toLinearMap ∘ₗ ψ₂.baseChange R',
    ⟨inferInstanceAs (Module.Finite R' (R' ⊗[R] P₀)), inferInstanceAs (Module.Projective R' (R' ⊗[R] P₀))⟩,
    ⟨inferInstanceAs (Module.Finite R' (R' ⊗[R] P₁)), inferInstanceAs (Module.Projective R' (R' ⊗[R] P₁))⟩,
    ⟨inferInstanceAs (Module.Finite R' (R' ⊗[R] P₂)), inferInstanceAs (Module.Projective R' (R' ⊗[R] P₂))⟩,
    ⟨inferInstanceAs (Module.Finite R' (R' ⊗[R] P₃)), inferInstanceAs (Module.Projective R' (R' ⊗[R] P₃))⟩,
    ?_, ?_, ?_, ?_, ⟨E₃.toLinearMap ∘ₗ ψ₃.baseChange R', ?_⟩, fun M ↦ ?_⟩
  · refine bc_ext _ _ fun n ↦ ?_
    have := LinearMap.congr_fun h₁₀ n
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at this
    simp [LinearMap.baseChange_tmul, this]
  · refine bc_ext _ _ fun n ↦ ?_
    have := LinearMap.congr_fun h₂₁ n
    simp only [LinearMap.comp_apply, LinearMap.zero_apply] at this
    simp [LinearMap.baseChange_tmul, this]
  · refine bc_ext _ _ fun n ↦ ?_
    have := LinearMap.congr_fun s₀ n
    simp only [LinearMap.comp_apply] at this
    simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul, LinearEquiv.coe_coe, this, t₀]
  · refine bc_ext _ _ fun n ↦ ?_
    have := LinearMap.congr_fun s₁ n
    simp only [LinearMap.comp_apply] at this
    simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul, LinearEquiv.coe_coe, this, t₁]
  · refine bc_ext _ _ fun n ↦ ?_
    have := LinearMap.congr_fun s₂ n
    simp only [LinearMap.comp_apply] at this
    simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul, LinearEquiv.coe_coe, this, t₂]
  · letI : Module R M := Module.compHom M (algebraMap R R')
    haveI : IsScalarTower R R' M := ⟨fun r s x ↦ by
      change (r • s) • x = (algebraMap R R' r) • (s • x)
      rw [Algebra.smul_def, mul_smul]⟩
    obtain ⟨q₀, q₁, q₂⟩ := hM (ModuleCat.of R M)
    let r₀ : R' ⊗[R] P₀ ≃ₗ[R'] R' ⊗[R] P₀ := .refl _ _
    let r₁ : R' ⊗[R] P₁ ≃ₗ[R'] R' ⊗[R] P₁ := .refl _ _
    let r₂ : R' ⊗[R] P₂ ≃ₗ[R'] R' ⊗[R] P₂ := .refl _ _
    let r₃ : R' ⊗[R] P₃ ≃ₗ[R'] R' ⊗[R] P₃ := .refl _ _
    have nA₀ : ∀ t, tw M r₁ (a₀.lTensor M t) = (a₀.baseChange R').lTensor M (tw M r₀ t) :=
      tw_nat r₀ r₁ a₀ _ fun n ↦ by simp [r₀, r₁, LinearMap.baseChange_tmul]
    have nA₁ : ∀ t, tw M r₂ (a₁.lTensor M t) = (a₁.baseChange R').lTensor M (tw M r₁ t) :=
      tw_nat r₁ r₂ a₁ _ fun n ↦ by simp [r₁, r₂, LinearMap.baseChange_tmul]
    have nA₂ : ∀ t, tw M r₃ (a₂.lTensor M t) = (a₂.baseChange R').lTensor M (tw M r₂ t) :=
      tw_nat r₂ r₃ a₂ _ fun n ↦ by simp [r₂, r₃, LinearMap.baseChange_tmul]
    have nD₀ : ∀ t, tw M E₁ ((d0 F).lTensor M t) = (d0 F').lTensor M (tw M E₀ t) := tw_nat E₀ E₁ _ _ t₀
    have nD₁ : ∀ t, tw M E₂ ((d1 F).lTensor M t) = (d1 F').lTensor M (tw M E₁ t) := tw_nat E₁ E₂ _ _ t₁
    have nD₂ : ∀ t, tw M E₃ ((d2 F).lTensor M t) = (d2 F').lTensor M (tw M E₂ t) := tw_nat E₂ E₃ _ _ t₂
    have nP₀ : ∀ t, tw M E₀ (ψ₀.lTensor M t) =
        (E₀.toLinearMap ∘ₗ ψ₀.baseChange R').lTensor M (tw M r₀ t) :=
      tw_nat r₀ E₀ ψ₀ _ fun n ↦ by simp [r₀, LinearMap.baseChange_tmul]
    have nP₁ : ∀ t, tw M E₁ (ψ₁.lTensor M t) =
        (E₁.toLinearMap ∘ₗ ψ₁.baseChange R').lTensor M (tw M r₁ t) :=
      tw_nat r₁ E₁ ψ₁ _ fun n ↦ by simp [r₁, LinearMap.baseChange_tmul]
    have nP₂ : ∀ t, tw M E₂ (ψ₂.lTensor M t) =
        (E₂.toLinearMap ∘ₗ ψ₂.baseChange R').lTensor M (tw M r₂ t) :=
      tw_nat r₂ E₂ ψ₂ _ fun n ↦ by simp [r₂, LinearMap.baseChange_tmul]
    exact ⟨QIsoAt.transport (tw M r₀) (tw M r₁) (tw M E₀) (tw M E₁) nA₀ nD₀ nP₀
        (fun _ ↦ ⟨0, by simp⟩) (fun _ ↦ ⟨0, by simp⟩) (fun _ ↦ ⟨0, by simp⟩) q₀,
      QIsoAt.transport (tw M r₁) (tw M r₂) (tw M E₁) (tw M E₂) nA₁ nD₁ nP₁
        (fun y ↦ ⟨tw M r₀ y, (nA₀ y).symm⟩) (fun y ↦ ⟨tw M E₀ y, (nD₀ y).symm⟩)
        (fun y ↦ ⟨(tw M E₀).symm y, by rw [nD₀, AddEquiv.apply_symm_apply]⟩) q₁,
      QIsoAt.transport (tw M r₂) (tw M r₃) (tw M E₂) (tw M E₃) nA₂ nD₂ nP₂
        (fun y ↦ ⟨tw M r₁ y, (nA₁ y).symm⟩) (fun y ↦ ⟨tw M E₁ y, (nD₁ y).symm⟩)
        (fun y ↦ ⟨(tw M E₁).symm y, by rw [nD₁, AddEquiv.apply_symm_apply]⟩) q₂⟩

end Main

theorem main : PerfBaseSt := by
  intro R _ P _ _ F h R' _ _ F' m
  haveI : Finite Pᵒᵖ := Finite.of_injective unop unop_injective
  haveI : ∀ T T' : Pᵒᵖ, Finite (T ⟶ T') := fun _ _ ↦ Finite.of_subsingleton
  exact perf_ext m h

end GlobalTheory.CompanionTheory.PerfExt
end
end
