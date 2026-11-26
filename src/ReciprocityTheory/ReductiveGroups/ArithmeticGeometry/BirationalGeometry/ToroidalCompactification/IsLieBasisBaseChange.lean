module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLawPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.GtPtsVal

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasisBaseChange
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Chart

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding spMap spMap_comp
open scoped CategoryTheory.Obj

variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G]

theorem chart_of_basis [IsLocalRing R] [Smooth G.hom] {d : ℕ} {v : Fin d → (epsR R ⟶ G)} (hv : IsLieBasis v) :
    ∃ x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G, IsUnivChart G d x ∧
      ∀ j, v j = spMap (dualLift (Pi.single j 1)) ≫ x 1 := by
  obtain ⟨n, x, hx⟩ := univChartLoc G
  have htan : ∀ i, IsTan (v i) := fun i => (isTan_iff _).mpr (hv.1 i)
  let M : Fin d → Fin n → R := fun i => tcoord hx (v i) (htan i)
  let L : (Fin d → R) →ₗ[R] (Fin n → R) := Fintype.linearCombination R M
  have hL : ∀ c, L c = ∑ i, c i • M i := fun c => Fintype.linearCombination_apply R M c
  have hprod : ∀ c, ∃ h : IsTan (prodPts c v), tcoord hx _ h = L c := fun c => by
    obtain ⟨h, e⟩ := prodPts_tan hx c v htan
    exact ⟨h, e.trans (hL c).symm⟩
  have hbij : Function.Bijective L := by
    constructor
    · intro c c' hcc
      obtain ⟨h, e⟩ := hprod c
      obtain ⟨h', e'⟩ := hprod c'
      have hw : prodPts c v = prodPts c' v := tan_ext hx h h' (by rw [e, e', hcc])
      have ht : IsTangent (prodPts c v) := (isTan_iff _).mp h
      exact (hv.2 _ ht).unique ((isLieComb_iff c v _).mpr rfl) ((isLieComb_iff c' v _).mpr hw)
    · intro t
      have hw := isTan_dualLift hx t
      obtain ⟨c, hc, -⟩ := hv.2 _ ((isTan_iff _).mp hw)
      refine ⟨c, ?_⟩
      obtain ⟨h, e⟩ := hprod c
      rw [← e, ← tcoord_congr hx ((isLieComb_iff c v _).mp hc) hw h, tcoord_eq hx _ hw t rfl]
  let Le := LinearEquiv.ofBijective L hbij
  let sub {a b : ℕ} (T : (Fin a → R) →ₗ[R] (Fin b → R)) (m : ℕ) :
      JetR R (Fin b) m →ₐ[R] JetR R (Fin a) m :=
    jetLift (R := R) (RingHom.ker (jetAug R (Fin a) m)) (ker_jetAug_pow (Fin a) m)
      (fun k => ∑ i, T (Pi.single i 1) k • zR m i) (fun k => sum_smul_zR_mem m _)
  have sub_zR {a b : ℕ} (T : (Fin a → R) →ₗ[R] (Fin b → R)) (m : ℕ) (k : Fin b) :
      sub T m (zR m k) = ∑ i, T (Pi.single i 1) k • zR m i := by
    exact jetLift_zR _ _ _ _ k
  have sub_id {a : ℕ} (m : ℕ) :
      sub (LinearMap.id : (Fin a → R) →ₗ[R] (Fin a → R)) m = AlgHom.id R _ := by
    apply jet_ext
    intro k
    rw [sub_zR]
    simp [Pi.single_apply]
  have sub_comp {a b c : ℕ} (T : (Fin a → R) →ₗ[R] (Fin b → R))
      (S : (Fin c → R) →ₗ[R] (Fin a → R)) (m : ℕ) :
      (sub S m).comp (sub T m) = sub (T.comp S) m := by
    apply jet_ext
    intro k
    rw [AlgHom.comp_apply, sub_zR, sub_zR, map_sum]
    simp_rw [map_smul, sub_zR, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← Finset.sum_smul]
    congr 1
    conv_rhs => rw [LinearMap.comp_apply, ← sum_single (S (Pi.single j 1))]
    simp [map_sum, map_smul, Finset.sum_apply, mul_comm]
  have sub_aug {a b : ℕ} (T : (Fin a → R) →ₗ[R] (Fin b → R)) (m : ℕ) :
      (jetAug R (Fin a) m).comp (sub T m) = jetAug R (Fin b) m := by
    apply jet_ext
    intro k
    rw [AlgHom.comp_apply, sub_zR, jetAug_zR]
    exact RingHom.mem_ker.mp (sum_smul_zR_mem m _)
  let y (m : ℕ) := spMap (sub Le.toLinearMap m) ≫ x m
  refine ⟨y, ⟨fun m => ?_, fun m => ?_, ?_⟩, fun j => Eq.symm ?_⟩
  · have trunc_zR {k : ℕ} (j : Fin k) : jetTruncR R (Fin k) m (zR (m + 1) j) = zR m j := rfl
    have ht : (jetTruncR R (Fin d) m).comp (sub Le.toLinearMap (m + 1)) =
        (sub Le.toLinearMap m).comp (jetTruncR R (Fin n) m) := by
      apply jet_ext
      intro k
      simp only [AlgHom.comp_apply, sub_zR, trunc_zR, map_sum, map_smul]
    dsimp only [y]
    rw [← Category.assoc, spMap_comp, ht, ← spMap_comp, Category.assoc, hx.1 m]
  · have zero_zR {k : ℕ} (j : Fin k) : jetZeroR R (Fin k) m (zR m j) = zR 0 j := rfl
    have hz : (jetZeroR R (Fin d) m).comp (sub Le.toLinearMap m) =
        (sub Le.toLinearMap 0).comp (jetZeroR R (Fin n) m) := by
      apply jet_ext
      intro k
      simp only [AlgHom.comp_apply, sub_zR, zero_zR, map_sum, map_smul]
    dsimp only [y]
    rw [← Category.assoc, spMap_comp, hz, ← spMap_comp, Category.assoc, hx.2.1 m, comp_one']
  · intro A _ _ aug m hA w hw
    obtain ⟨ψ, ⟨hψaug, hψw⟩, hψunique⟩ := hx.2.2 A aug m hA w hw
    have hforward : (sub Le.symm.toLinearMap m).comp (sub Le.toLinearMap m) = AlgHom.id R _ := by
      rw [sub_comp, LinearEquiv.comp_symm, sub_id]
    have hinverse : (sub Le.toLinearMap m).comp (sub Le.symm.toLinearMap m) = AlgHom.id R _ := by
      rw [sub_comp, LinearEquiv.symm_comp, sub_id]
    refine ⟨ψ.comp (sub Le.symm.toLinearMap m), ⟨?_, ?_⟩, ?_⟩
    · rw [← AlgHom.comp_assoc, hψaug, sub_aug]
    · dsimp only [y]
      rw [← Category.assoc, spMap_comp, AlgHom.comp_assoc, hforward, AlgHom.comp_id]
      exact hψw
    · rintro φ ⟨hφaug, hφw⟩
      have hφ : φ.comp (sub Le.toLinearMap m) = ψ := by
        apply hψunique
        refine ⟨?_, ?_⟩
        · rw [← AlgHom.comp_assoc, hφaug, sub_aug]
        · dsimp only [y] at hφw
          rw [hφw, ← Category.assoc, spMap_comp]
      rw [← hφ, AlgHom.comp_assoc, hinverse, AlgHom.comp_id]
  · have hLj : Le.toLinearMap (Pi.single j 1) = M j := by
      show L (Pi.single j 1) = M j
      rw [hL]
      simp [Pi.single_apply]
    have hdual : (dualLift (Pi.single j 1)).comp (sub Le.toLinearMap 1) = dualLift (M j) := by
      apply jet_ext
      intro k
      rw [AlgHom.comp_apply, sub_zR, dualLift_zR, map_sum]
      simp_rw [map_smul, dualLift_zR]
      simp [Pi.single_apply, ← hLj]
    dsimp only [y]
    rw [← Category.assoc, spMap_comp, hdual]
    exact (tcoord_spec hx (v j) (htan j)).symm

theorem basis_of_chart {n : ℕ} {x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin n) m) ⟶ G} (hx : IsUnivChart G n x) :
    IsLieBasis (G := G) (fun i : Fin n => (spMap (dualLift (Pi.single i 1)) ≫ x 1 : epsR R ⟶ G)) := by
  let v : Fin n → (epsR R ⟶ G) := fun i => spMap (dualLift (Pi.single i 1)) ≫ x 1
  have htan : ∀ i, IsTan (v i) := fun i => isTan_dualLift hx _
  have hM : ∀ i, tcoord hx (v i) (htan i) = Pi.single i 1 := fun i => tcoord_eq hx _ _ _ rfl
  refine ⟨fun i => (isTan_iff _).mp (htan i), fun w hw => ?_⟩
  have hw' : IsTan w := (isTan_iff _).mpr hw
  have key : ∀ c, IsLieComb c v w ↔ tcoord hx w hw' = c := by
    intro c
    obtain ⟨h, e⟩ := prodPts_tan hx c v htan
    have e2 : tcoord hx _ h = c := by
      rw [e]
      simp only [hM]
      exact sum_single c
    rw [isLieComb_iff]
    constructor
    · intro hwc
      rw [tcoord_congr hx hwc hw' h, e2]
    · intro hc
      exact tan_ext hx hw' h (hc.trans e2.symm)
  exact ⟨tcoord hx w hw', (key _).mpr rfl, fun c hc => ((key c).mp hc).symm⟩

theorem isLieBasis_iso {G' : Over (Spec (CommRingCat.of R))} [GrpObj G'] (e : G' ≅ G) [IsMonHom e.hom] {n : ℕ}
    {v : Fin n → (epsR R ⟶ G')} (hv : IsLieBasis fun i => v i ≫ e.hom) : IsLieBasis v := by
  have tan : ∀ w : epsR R ⟶ G', IsTangent (w ≫ e.hom) ↔ IsTangent w := fun w => by
    have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
    rw [IsTangent, IsTangent, ← IsMonHom.one_hom e.hom, Over.comp_left, Over.comp_left, ← Category.assoc, cancel_mono]
  have pr : ∀ u : Fin n → (epsR R ⟶ G'), (List.ofFn u).prod ≫ e.hom = (List.ofFn fun i => u i ≫ e.hom).prod := fun u =>
    (map_list_prod (IsMonHom.monoidHom e.hom (epsR R)) _).trans (by rw [List.map_ofFn]; rfl)
  have comb : ∀ c w, IsLieComb c (fun i => v i ≫ e.hom) (w ≫ e.hom) ↔ IsLieComb c v w := fun c w => by
    constructor
    · rintro ⟨u, hu, hw⟩
      refine ⟨fun i => u i ≫ e.inv, fun i => ?_, ?_⟩
      · rw [Over.comp_left, hu, Category.assoc, ← Over.comp_left, Category.assoc, e.hom_inv_id, Category.comp_id]
      · rw [← cancel_mono e.hom, pr, hw]; simp
    · rintro ⟨u, hu, rfl⟩
      exact ⟨fun i => u i ≫ e.hom, fun i => by rw [Over.comp_left, hu, Category.assoc]; rfl, pr u⟩
  refine ⟨fun i => (tan _).1 (hv.1 i), fun w hw => ?_⟩
  simpa only [comb] using hv.2 _ ((tan w).2 hw)

theorem isLieBasis_baseChange [IsLocalRing R] [Smooth G.hom] {R' : Type} [CommRing R'] (f : R →+* R')
    {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G'] {φ : G'.left ⟶ G.left}
    (h : IsGrpPullback G' G (Geo.Tor.spMap f) φ) {d : ℕ} {v : Fin d → (epsR R ⟶ G)} (hv : IsLieBasis v)
    {v' : Fin d → (epsR R' ⟶ G')} (hv' : ∀ j, (v' j).left ≫ φ = Geo.Tor.spMap (dualMapR f) ≫ (v j).left) :
    IsLieBasis v' := by
  let _ := f.toAlgebra
  obtain ⟨x, hx, hxv⟩ := chart_of_basis hv
  obtain ⟨x', hx', e'⟩ := tanBC_alg (R' := R') G d x hx
  obtain ⟨e, he, heφ⟩ := grpPullback_iso h (isGrpPullback_pullback G (fB R R'))
  refine isLieBasis_iso e ?_
  convert basis_of_chart hx' using 2 with j
  refine Over.OverMorphism.ext (pullback.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
  have s : (algebraMap R R' ∘ Pi.single j (1 : R) : Fin d → R') = Pi.single j 1 := by
    funext i; by_cases hij : i = j <;> simp [hij, Pi.single_apply]
  have := e' (Pi.single j 1)
  rw [s] at this
  rw [Over.comp_left, Category.assoc, heφ, hv', hxv]
  exact this.symm

end ReciprocityTheory.ChartRestriction.G.Chart
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RankPf
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj

namespace ReciprocityTheory.ChartRestriction.G.Chart

attribute [local instance] Over.cartesianMonoidalCategory

section Chart

variable {R : Type} [CommRing R] {Gx : Over (Spec (CommRingCat.of R))} [GrpObj Gx] {n : ℕ}
  {x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin n) m) ⟶ Gx} (hx : IsUnivChart Gx n x)

include hx in
theorem tvec_inj {c c' : Fin n → R} (h : tvec (x := x) c = tvec (x := x) c') : c = c' := by
  rw [← tcoord_tvec hx c, ← tcoord_tvec hx c']
  exact tcoord_congr hx h _ _

theorem list_prod_tan' : ∀ {M : ℕ} (u : Fin M → (sp (R₀ := R) (DualNumber R) ⟶ Gx)) (hu : ∀ i, IsTan (u i)),
    ∃ h : IsTan (List.ofFn u).prod, tcoord hx _ h = ∑ i, tcoord hx (u i) (hu i) := by
  intro M
  induction M with
  | zero =>
    intro u hu
    have e0 : (List.ofFn u).prod = 1 := by simp
    refine ⟨e0 ▸ isTan_one, ?_⟩
    rw [tcoord_congr hx e0 _ isTan_one, tcoord_one]
    simp
  | succ M ih =>
    intro u hu
    obtain ⟨h, e⟩ := ih (fun i => u i.succ) (fun i => hu i.succ)
    have e0 : (List.ofFn u).prod = u 0 * (List.ofFn fun i => u i.succ).prod := by
      rw [List.ofFn_succ, List.prod_cons]
    refine ⟨e0 ▸ isTan_mul (hu 0) h, ?_⟩
    rw [tcoord_congr hx e0 _ (isTan_mul (hu 0) h), tcoord_mul hx (hu 0) h, e, Fin.sum_univ_succ]

theorem mem_eigLat_iff {O : Type} (act : O → (Gx ⟶ Gx)) [∀ a, IsMonHom (act a)] (χ : O → R) (c : Fin n → R) :
    c ∈ eigLat hx act χ ↔ ∀ a, tmap hx (act a) c = χ a • c := by
  simp only [eigLat, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero]

theorem tvec_eig_iff (e : Gx ⟶ Gx) [IsMonHom e] (c : Fin n → R) (s : R) :
    tvec (x := x) c ≫ e = spMap (scaleD s) ≫ tvec (x := x) c ↔ tmap hx e c = s • c := by
  rw [← tvec_tmap hx, ← tvec_smul hx]
  exact ⟨fun h => tvec_inj hx h, fun h => by rw [h]⟩

end Chart

section Count

variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G'] {f : S' ⟶ S} {F : G'.left ⟶ G.left}
  (hc : Geo.Tor.IsGrpPullback G' G f F) {k : Type} [Field k] {tk : Spec (CommRingCat.of k) ⟶ S'}
  {g : Spec (CommRingCat.of k) ⟶ S} (hg : tk ≫ f = g)

include hc in
theorem rel_eq_iff {X : Over (Spec (CommRingCat.of k))} {w₁ w₂ : viaT tk X ⟶ G'} {v₁ v₂ : X ⟶ (Over.pullback g).obj G}
    (h₁ : Rel (F := F) tk g w₁ v₁) (h₂ : Rel (F := F) tk g w₂ v₂) : w₁ = w₂ ↔ v₁ = v₂ := by
  constructor
  · rintro rfl
    exact rel_uniq_v h₁ h₂
  · rintro rfl
    exact rel_uniq_w hc h₁ h₂

include hc hg in
theorem tan_iff {w : viaT tk (sp (R₀ := k) (DualNumber k)) ⟶ G'} {v : sp (R₀ := k) (DualNumber k) ⟶ (Over.pullback g).obj G}
    (h : Rel (F := F) tk g w v) :
    Geo.Tor.spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ w.left = (1 : Over.mk tk ⟶ G').left ↔ IsTan v := by
  have h1 := rel_pre (spMap (fstD k)) h
  have h2 := rel_one hc hg (X := sp (R₀ := k) k)
  have hid : (sp (R₀ := k) k).hom = 𝟙 _ := by
    show Spec.map (CommRingCat.ofHom (algebraMap k k)) = _
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
    rfl
  have e1 : (1 : viaT tk (sp (R₀ := k) k) ⟶ G').left = (1 : Over.mk tk ⟶ G').left := by
    rw [one_left', one_left']
    show ((sp (R₀ := k) k).hom ≫ tk) ≫ _ = tk ≫ _
    rw [hid, Category.id_comp]
  rw [IsTan, ← rel_eq_iff hc h1 h2]
  constructor
  · intro e
    apply Over.OverMorphism.ext
    exact e.trans e1.symm
  · intro e
    exact (congrArg (fun q => q.left) e).trans e1

include hc in
theorem eig_iff (a : G' ⟶ G') (b : G ⟶ G) (hab : a.left ≫ F = F ≫ b.left) (s : k)
    {w : viaT tk (sp (R₀ := k) (DualNumber k)) ⟶ G'} {v : sp (R₀ := k) (DualNumber k) ⟶ (Over.pullback g).obj G}
    (h : Rel (F := F) tk g w v) :
    (w ≫ a).left = Geo.Tor.spMap (Geo.Tor.epsScale s) ≫ w.left ↔ v ≫ (Over.pullback g).map b = spMap (scaleD s) ≫ v := by
  rw [← rel_eq_iff hc (rel_act a b hab h) (rel_pre (spMap (scaleD s)) h)]
  constructor
  · intro e
    exact Over.OverMorphism.ext e
  · intro e
    exact congrArg (fun q => q.left) e

variable {n : ℕ} {x : ∀ m : ℕ, sp (R₀ := k) (JetR k (Fin n) m) ⟶ (Over.pullback g).obj G} (hx : IsUnivChart _ n x)
  {O : Type} [CommRing O] (act : Geo.Tor.OAct O G') (b : O → (G ⟶ G))
  (hab : ∀ a, (act.act a).left ≫ F = F ≫ (b a).left)
  (act' : O → ((Over.pullback g).obj G ⟶ (Over.pullback g).obj G)) [∀ a, IsMonHom (act' a)]
  (hact' : ∀ a, act' a = (Over.pullback g).map (b a)) (τ : O →+* k)


include hc hg hab hact' in
theorem finrank_of_lieMult {N : ℕ} (hL : Geo.Tor.LieMult act tk τ N) :
    Module.finrank k (eigLat hx act' (fun a => τ a)) = N := by
  obtain ⟨vB, hvB, huq⟩ := hL
  have hT : ∀ (w : viaT tk (sp (R₀ := k) (DualNumber k)) ⟶ G') v, Rel (F := F) tk g w v →
      (Geo.Tor.IsLieEigen act tk τ w ↔ IsTan v ∧ ∀ a, v ≫ act' a = spMap (scaleD (τ a)) ≫ v) := by
    intro w v h
    refine and_congr (tan_iff hc hg h) (forall_congr' fun a => ?_)
    rw [hact']
    exact eig_iff hc (act.act a) (b a) (hab a) (τ a) h
  choose v' hv' using fun i => rel_exists_v hc hg (X := sp (R₀ := k) (DualNumber k)) (vB i)
  have hv'e : ∀ i, IsTan (v' i) ∧ ∀ a, v' i ≫ act' a = spMap (scaleD (τ a)) ≫ v' i :=
    fun i => (hT _ _ (hv' i)).mp (hvB i)
  let bb : Fin N → Fin n → k := fun i => tcoord hx (v' i) (hv'e i).1
  have htv : ∀ i, tvec (x := x) (bb i) = v' i := fun i => (tcoord_spec hx _ _).symm
  have hmem : ∀ c, c ∈ eigLat hx act' (fun a => τ a) ↔ ∀ a, tvec (x := x) c ≫ act' a = spMap (scaleD (τ a)) ≫ tvec (x := x) c := by
    intro c
    rw [mem_eigLat_iff]
    exact forall_congr' fun a => (tvec_eig_iff hx (act' a) c (τ a)).symm
  have hbW : ∀ i, bb i ∈ eigLat hx act' (fun a => τ a) := fun i => (hmem _).mpr fun a => by
    rw [htv]
    exact (hv'e i).2 a
  let P : (Fin N → k) → (sp (R₀ := k) (DualNumber k) ⟶ (Over.pullback g).obj G) :=
    fun d => (List.ofFn fun i => spMap (scaleD (d i)) ≫ v' i).prod
  let Wd : (Fin N → k) → (viaT tk (sp (R₀ := k) (DualNumber k)) ⟶ G') :=
    fun d => (List.ofFn fun i => liftT tk (spMap (scaleD (d i))) ≫ vB i).prod
  have hPW : ∀ d, Rel (F := F) tk g (Wd d) (P d) := fun d => rel_prod hc hg _ _ fun i => rel_pre _ (hv' i)
  have hPeq : ∀ d, P d = tvec (x := x) (∑ i, d i • bb i) := by
    intro d
    obtain ⟨h, e⟩ := list_prod_tan' hx (fun i => spMap (scaleD (d i)) ≫ v' i) (fun i => isTan_scale (d i) (hv'e i).1)
    refine (tcoord_spec hx (P d) h).trans ?_
    show tvec (x := x) (tcoord hx (P d) h) = _
    rw [e]
    congr 1
    exact Finset.sum_congr rfl fun i _ => tcoord_scale hx (d i) (hv'e i).1
  have hsum : ∀ d : Fin N → k, (∑ i, d i • bb i) ∈ eigLat hx act' (fun a => τ a) := fun d =>
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hbW i)
  have hWeig : ∀ d : Fin N → k, Geo.Tor.IsLieEigen act tk τ (Wd d) := fun d => (hT _ _ (hPW d)).mpr
    ⟨by rw [hPeq]; exact isTan_tvec hx _, by rw [hPeq]; exact (hmem _).mp (hsum d)⟩
  have hsat : ∀ d : Fin N → k, ∃ u : Fin N → (Geo.Tor.epsPt tk ⟶ G'),
      (∀ i, (u i).left = Geo.Tor.spMap (Geo.Tor.epsScale (d i)) ≫ (vB i).left) ∧ Wd d = (List.ofFn u).prod :=
    fun d => ⟨fun i => liftT tk (spMap (scaleD (d i))) ≫ vB i, fun i => rfl, rfl⟩
  have hli : LinearIndependent k bb := by
    rw [Fintype.linearIndependent_iff]
    intro d hd
    have e1 : P d = P 0 := by
      rw [hPeq, hPeq, hd]
      simp
    have e2 : Wd d = Wd 0 := (rel_eq_iff hc (hPW d) (hPW 0)).mpr e1
    have := (huq (Wd 0) (hWeig 0)).unique (e2 ▸ hsat d) (hsat 0)
    exact fun i => congrFun this i
  have hspan : eigLat hx act' (fun a => τ a) = Submodule.span k (Set.range bb) := by
    apply le_antisymm
    · intro c hc'
      obtain ⟨w, hw⟩ := rel_exists_w hc hg (tvec (x := x) c)
      obtain ⟨d, ⟨u, hu, hwu⟩, -⟩ := huq w ((hT _ _ hw).mpr ⟨isTan_tvec hx c, (hmem c).mp hc'⟩)
      have hu' : u = fun i => liftT tk (spMap (scaleD (d i))) ≫ vB i :=
        funext fun i => Over.OverMorphism.ext (hu i)
      have e1 : w = Wd d := by rw [hwu, hu']
      have e2 : tvec (x := x) c = P d := rel_uniq_v (e1 ▸ hw) (hPW d)
      rw [hPeq] at e2
      rw [tvec_inj hx e2]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact hbW i
  rw [hspan, finrank_span_eq_card hli, Fintype.card_fin]

end Count

section Assembly

theorem pushR_map {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (G : Over (Spec (CommRingCat.of R)))
    [GrpObj G] {P : Type} [CommRing P] [Algebra R' P] [Algebra R P] [IsScalarTower R R' P]
    (y : sp (R₀ := R') P ⟶ (Over.pullback (fB R R')).obj G) (e : G ⟶ G) :
    pushR G (y ≫ (Over.pullback (fB R R')).map e) = pushR G y ≫ e := by
  apply Over.OverMorphism.ext
  rw [pushR_left, Over.comp_left, Over.comp_left, pushR_left, Category.assoc, Category.assoc]
  congr 1
  exact pullback.lift_fst _ _ _

end Assembly

end ReciprocityTheory.ChartRestriction.G.Chart
end
end
