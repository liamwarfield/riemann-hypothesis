module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitalIntegralsTermsOneDoubleCoset
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeIntegralStabiliserNormalisedHaar
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MovedTermLatticeIsGlobalTermPhase
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianAmplitudeMassProductStructure
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalizedBesselMapsAnyScalePieriConstants

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutomorphismCovolumeEqLatticeMass
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPointsTermAutomorphismsEqMovedStabilizer
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPointsTermAutomorphismsEqMovedStabilizer
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.RoEq

section Places

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} (A : Places F E sig) {n : ℕ}

private theorem bc_single' (p : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) (i : Fin n) :
    A.bc p (Pi.single i 1 : Fin n → E) = Pi.single i 1 := by
  funext j
  by_cases h : j = i
  · subst h
    simp [Places.bc]
  · simp [Places.bc, h]

theorem ext_unique (p : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) {g : (Fin n → E) ≃ₗ[E] (Fin n → E)}
    {g₁ g₂ : (Fin n → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin n → (A.loc p).Ep)}
    (h₁ : A.Ext p g g₁) (h₂ : A.Ext p g g₂) : g₁ = g₂ := by
  apply LinearEquiv.toLinearMap_injective
  refine LinearMap.pi_ext' fun i => LinearMap.ext_ring ?_
  have e₁ := h₁ (Pi.single i 1)
  have e₂ := h₂ (Pi.single i 1)
  rw [bc_single'] at e₁ e₂
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_single, LinearEquiv.coe_coe]
  rw [e₁, e₂]

private theorem mem_rat_iff_forall_exists_ext (K : ∀ p, Subgroup ((Fin n → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin n → (A.loc p).Ep)))
    (g : (Fin n → E) ≃ₗ[E] (Fin n → E)) : g ∈ A.rat K ↔ ∀ p, ∃ g' ∈ K p, A.Ext p g g' :=
  Iff.rfl

theorem mem_rat_inf {K₁ K₂ : ∀ p, Subgroup ((Fin n → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin n → (A.loc p).Ep))}
    (g : (Fin n → E) ≃ₗ[E] (Fin n → E)) :
    g ∈ A.rat (fun p => K₁ p ⊓ K₂ p) ↔ g ∈ A.rat K₁ ∧ g ∈ A.rat K₂ := by
  rw [mem_rat_iff_forall_exists_ext, mem_rat_iff_forall_exists_ext, mem_rat_iff_forall_exists_ext]
  constructor
  · intro h
    exact ⟨fun p => by
        obtain ⟨g', hg', he⟩ := h p
        exact ⟨g', (Subgroup.mem_inf.1 hg').1, he⟩,
      fun p => by
        obtain ⟨g', hg', he⟩ := h p
        exact ⟨g', (Subgroup.mem_inf.1 hg').2, he⟩⟩
  · rintro ⟨h₁, h₂⟩ p
    obtain ⟨g₁, hg₁, he₁⟩ := h₁ p
    obtain ⟨g₂, hg₂, he₂⟩ := h₂ p
    have hg : g₁ = g₂ := ext_unique A p he₁ he₂
    subst hg
    exact ⟨g₁, Subgroup.mem_inf.2 ⟨hg₁, hg₂⟩, he₁⟩

theorem lat_map (p : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) {g : (Fin n → E) ≃ₗ[E] (Fin n → E)}
    {g' : (Fin n → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin n → (A.loc p).Ep)} (h : A.Ext p g g')
    (Λ : Submodule (𝓞 E) (Fin n → E)) :
    A.lat p (Λ.map ((g : (Fin n → E) →ₗ[E] (Fin n → E)).restrictScalars (𝓞 E))) = g' • A.lat p Λ := by
  unfold Places.lat
  rw [Submodule.smul_span]
  congr 1
  have h' : ∀ x, g' (A.bc p x) = A.bc p (g x) := h
  ext v
  simp [Set.mem_smul_set, h']

theorem ext_symm (p : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) {g : (Fin n → E) ≃ₗ[E] (Fin n → E)}
    {g' : (Fin n → (A.loc p).Ep) ≃ₗ[(A.loc p).Ep] (Fin n → (A.loc p).Ep)} (h : A.Ext p g g') :
    A.Ext p g.symm g'.symm := by
  intro x
  apply g'.injective
  rw [LinearEquiv.apply_symm_apply, h, LinearEquiv.apply_symm_apply]

private theorem mem_iff_forall_bc_mem_lat_and_finite (Λ : Submodule (𝓞 E) (Fin n → E)) (hΛ : Submodule.IsFullLattice E Λ) :
    (∀ x, x ∈ Λ ↔ ∀ p, A.bc p x ∈ A.lat p Λ) ∧ (∀ p, IsLat (A.L p) (A.lat p Λ)) ∧
      {p | A.lat p Λ ≠ Submodule.span (A.L p).O
        (Set.range fun i => (Pi.single i 1 : Fin n → (A.loc p).Ep))}.Finite := by
  exact PlacesRec.lattice_local A n Λ hΛ

theorem map_le_of_local (Λ : Submodule (𝓞 E) (Fin n → E)) (hΛ : Submodule.IsFullLattice E Λ)
    (g : (Fin n → E) ≃ₗ[E] (Fin n → E))
    (hg : ∀ p, ∃ g', A.Ext p g g' ∧ g' • A.lat p Λ = A.lat p Λ) :
    Λ.map ((g : (Fin n → E) →ₗ[E] (Fin n → E)).restrictScalars (𝓞 E)) ≤ Λ := by
  rintro _ ⟨y, hy, rfl⟩
  refine ((mem_iff_forall_bc_mem_lat_and_finite A Λ hΛ).1 _).2 fun p => ?_
  obtain ⟨g', he, hs⟩ := hg p
  have hy' : A.bc p y ∈ A.lat p Λ := Submodule.subset_span ⟨y, hy, rfl⟩
  have := Submodule.smul_mem_pointwise_smul (A.bc p y) g' (A.lat p Λ) hy'
  rw [hs, LinearEquiv.smul_def, he] at this
  exact this

theorem map_eq_of_local (Λ : Submodule (𝓞 E) (Fin n → E)) (hΛ : Submodule.IsFullLattice E Λ)
    (g : (Fin n → E) ≃ₗ[E] (Fin n → E))
    (hg : ∀ p, ∃ g', A.Ext p g g' ∧ g' • A.lat p Λ = A.lat p Λ) :
    Λ.map ((g : (Fin n → E) →ₗ[E] (Fin n → E)).restrictScalars (𝓞 E)) = Λ := by
  refine le_antisymm (map_le_of_local A Λ hΛ g hg) ?_
  have hs : Λ.map ((g.symm : (Fin n → E) →ₗ[E] (Fin n → E)).restrictScalars (𝓞 E)) ≤ Λ := by
    refine map_le_of_local A Λ hΛ g.symm fun p => ?_
    obtain ⟨g', he, hl⟩ := hg p
    refine ⟨g'.symm, ext_symm A p he, ?_⟩
    conv_lhs => rw [← hl]
    exact inv_smul_smul g' (A.lat p Λ)
  intro x hx
  refine ⟨g.symm x, hs ⟨x, hx, rfl⟩, ?_⟩
  simp

end Places

end GlobalTheory.RoEq

noncomputable section

namespace GlobalTheory.RoEq

section Glob

variable {D : D7}

theorem nlam_iff (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T)
    (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) :
    n ∈ NLam Λ F ↔ n ∈ NRat F ∧ Formalism.HermitianLatticesTheory.gmap n Λ = Λ := by
  simp only [NLam, NRat, IsAutLam, Set.mem_ofPred_eq]
  tauto

theorem gmap_mul (a b : (VS D).V ≃ₗ[D.host.E] (VS D).V) (Λ : Submodule (𝓞 D.host.E) (VS D).V) :
    Formalism.HermitianLatticesTheory.gmap (a * b) Λ = Formalism.HermitianLatticesTheory.gmap a (Formalism.HermitianLatticesTheory.gmap b Λ) := by
  ext x
  simp only [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨b y, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, rfl⟩

theorem gmap_inv_of (a : (VS D).V ≃ₗ[D.host.E] (VS D).V) {Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V}
    (h : Formalism.HermitianLatticesTheory.gmap a Λ' = Λ) : Formalism.HermitianLatticesTheory.gmap a⁻¹ Λ = Λ' := by
  subst h
  rw [← gmap_mul, inv_mul_cancel]
  ext x
  simp [Formalism.HermitianLatticesTheory.gmap]

variable {Z : LocDat D} {T T' : D.host.E} {F0 : LFlag (D.sp.Y 0) D.R.rS T} {F0' : LFlag (D.sp.Y 0) D.R.rS T'}
  {FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS} {G : GFrames (placesOf Z) D.R.rS D.R.k}
  (c : GCoord Z F0 F0' FP G)

theorem grp_conj (ρ l n : (VS D).V ≃ₗ[D.host.E] (VS D).V) :
    c.grp (ρ * l) (l⁻¹ * n * l) = c.grp ρ n := by
  have hs : ∀ y, l ((ρ * l).symm y) = ρ.symm y := fun y => by
    apply ρ.injective
    rw [← LinearEquiv.mul_apply, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  ext x
  simp [GCoord.grp, LinearEquiv.mul_apply, hs]

theorem lat_map_grp (ρ n : (VS D).V ≃ₗ[D.host.E] (VS D).V) (Λ : Submodule (𝓞 D.host.E) (VS D).V) :
    (c.lat ρ Λ).map (((c.grp ρ n : G.GLV) : G.V →ₗ[D.host.E] G.V).restrictScalars (𝓞 D.host.E)) =
      c.lat ρ (Formalism.HermitianLatticesTheory.gmap n Λ) := by
  ext x
  simp only [GCoord.lat, Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨n y, ⟨y, hy, rfl⟩, by simp [GCoord.grp]⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨_, ⟨y, hy, rfl⟩, by simp [GCoord.grp]⟩

theorem lat_inj (ρ : (VS D).V ≃ₗ[D.host.E] (VS D).V) {Λ₁ Λ₂ : Submodule (𝓞 D.host.E) (VS D).V}
    (h : c.lat ρ Λ₁ = c.lat ρ Λ₂) : Λ₁ = Λ₂ := by
  unfold GCoord.lat at h
  refine Submodule.map_injective_of_injective ?_ h
  exact (ρ.trans c.e).injective

end Glob

end GlobalTheory.RoEq

noncomputable section

namespace GlobalTheory.RoEq

section Key

variable {D : D7} {Z : LocDat D} {T T' : D.host.E} {F0 : LFlag (D.sp.Y 0) D.R.rS T} {F0' : LFlag (D.sp.Y 0) D.R.rS T'}
  {FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS} {G : GFrames (placesOf Z) D.R.rS D.R.k}
  (c : GCoord Z F0 F0' FP G)

set_option maxHeartbeats 1000000 in
theorem mem_rat_stab_iff (L : G.Lt) (hL : Submodule.IsFullLattice D.host.E L) (σ : G.GLV)
    (hx : ∀ p, ∃ g', (placesOf Z).Ext p σ g') :
    σ ∈ (placesOf Z).rat (fun p => MulAction.stabilizer (G.S p).GLV ((placesOf Z).lat p L)) ↔
      L.map ((σ : G.V →ₗ[D.host.E] G.V).restrictScalars (𝓞 D.host.E)) = L := by
  constructor
  · intro h
    refine map_eq_of_local (placesOf Z) L hL σ fun p => ?_
    obtain ⟨g', hg', he⟩ := (show ∀ p, ∃ g' ∈ MulAction.stabilizer (G.S p).GLV ((placesOf Z).lat p L),
      (placesOf Z).Ext p σ g' from h) p
    exact ⟨g', he, hg'⟩
  · intro h
    show ∀ p, ∃ g' ∈ MulAction.stabilizer (G.S p).GLV ((placesOf Z).lat p L), (placesOf Z).Ext p σ g'
    intro p
    obtain ⟨g', he⟩ := hx p
    refine ⟨g', ?_, he⟩
    rw [MulAction.mem_stabilizer_iff, ← lat_map (placesOf Z) p he L, h]

private theorem exists_ext' {F₁ E₁ : Type} [Field F₁] [NumberField F₁] [Field E₁] [NumberField E₁] [Algebra F₁ E₁]
    {sig : E₁ →ₐ[F₁] E₁} (A : Places F₁ E₁ sig) {m : ℕ} (p : IsDedekindDomain.HeightOneSpectrum (𝓞 F₁))
    (g : (Fin m → E₁) ≃ₗ[E₁] (Fin m → E₁)) : ∃ g', A.Ext p g g' := by
  have hM : LinearMap.toMatrix' (g : (Fin m → E₁) →ₗ[E₁] (Fin m → E₁)) *
      LinearMap.toMatrix' (g.symm : (Fin m → E₁) →ₗ[E₁] (Fin m → E₁)) = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    have : (g : (Fin m → E₁) →ₗ[E₁] (Fin m → E₁)).comp (g.symm : (Fin m → E₁) →ₗ[E₁] (Fin m → E₁)) =
        LinearMap.id := LinearMap.ext fun x => by simp
    rw [this, LinearMap.toMatrix'_id]
  have hM' : LinearMap.toMatrix' (g.symm : (Fin m → E₁) →ₗ[E₁] (Fin m → E₁)) *
      LinearMap.toMatrix' (g : (Fin m → E₁) →ₗ[E₁] (Fin m → E₁)) = 1 := by
    rw [← LinearMap.toMatrix'_comp]
    have : (g.symm : (Fin m → E₁) →ₗ[E₁] (Fin m → E₁)).comp (g : (Fin m → E₁) →ₗ[E₁] (Fin m → E₁)) =
        LinearMap.id := LinearMap.ext fun x => by simp
    rw [this, LinearMap.toMatrix'_id]
  let ι := (A.loc p).ιE
  refine ⟨LinearEquiv.ofLinearMap
    (Matrix.toLin' (ι.mapMatrix (LinearMap.toMatrix' (g : (Fin m → E₁) →ₗ[E₁] (Fin m → E₁)))))
    (Matrix.toLin' (ι.mapMatrix (LinearMap.toMatrix' (g.symm : (Fin m → E₁) →ₗ[E₁] (Fin m → E₁)))))
    ?_ ?_, ?_⟩
  · rw [← Matrix.toLin'_mul, ← map_mul, hM, map_one, Matrix.toLin'_one]
  · rw [← Matrix.toLin'_mul, ← map_mul, hM', map_one, Matrix.toLin'_one]
  · intro x
    funext i
    simp only [LinearEquiv.coe_ofLinearMap, Matrix.toLin'_apply, Places.bc]
    rw [show g x = Matrix.mulVec (LinearMap.toMatrix' (g : (Fin m → E₁) →ₗ[E₁] (Fin m → E₁))) x from
      (LinearMap.toMatrix'_mulVec (g : (Fin m → E₁) →ₗ[E₁] (Fin m → E₁)) x).symm, RingHom.map_mulVec]
    rfl

theorem key {Tu Tu' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS Tu) (F' : LFlag (D.sp.Y 0) D.R.rS Tu')
    (ρ l : (VS D).V ≃ₗ[D.host.E] (VS D).V) (Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V)
    (hl : Formalism.HermitianLatticesTheory.gmap l Λ' = Λ) (hL : Submodule.IsFullLattice D.host.E (c.lat ρ Λ))
    (hN : ∀ n, n ∈ NRat F ↔ c.grp ρ n ∈ G.N) (hN' : ∀ m, m ∈ NRat F' ↔ c.grp (ρ * l) m ∈ G.N')
    (n : (VS D).V ≃ₗ[D.host.E] (VS D).V) :
    (n ∈ NLam Λ F ∧ l⁻¹ * n * l ∈ NLam Λ' F') ↔ c.grp ρ n ∈ G.stabL (c.lat ρ Λ) := by
  have hx : ∀ p, ∃ g', (placesOf Z).Ext p (c.grp ρ n) g' := fun p => exists_ext' _ p _
  have hS : c.grp ρ n ∈ G.stabL (c.lat ρ Λ) ↔
      (c.grp ρ n ∈ G.N ∧ c.grp ρ n ∈ G.N') ∧ Formalism.HermitianLatticesTheory.gmap n Λ = Λ := by
    refine (mem_rat_inf (placesOf Z) (K₁ := fun p => (G.S p).St)
      (K₂ := fun p => MulAction.stabilizer (G.S p).GLV ((placesOf Z).lat p (c.lat ρ Λ))) (c.grp ρ n)).trans ?_
    refine and_congr (mem_rat_inf (placesOf Z) (K₁ := fun p => (G.S p).N) (K₂ := fun p => (G.S p).N')
      (c.grp ρ n)) ?_
    rw [mem_rat_stab_iff (c.lat ρ Λ) hL (c.grp ρ n) hx, lat_map_grp]
    exact ⟨lat_inj c ρ, fun h => by rw [h]⟩
  rw [hS, nlam_iff Λ F n, nlam_iff Λ' F' (l⁻¹ * n * l), ← hN, ← grp_conj c ρ l n, ← hN']
  have hl' : Formalism.HermitianLatticesTheory.gmap l⁻¹ Λ = Λ' := gmap_inv_of l hl
  have e : Formalism.HermitianLatticesTheory.gmap (l⁻¹ * n * l) Λ' = Formalism.HermitianLatticesTheory.gmap l⁻¹ (Formalism.HermitianLatticesTheory.gmap n Λ) := by
    rw [gmap_mul, gmap_mul, hl]
  rw [e]
  constructor
  · rintro ⟨⟨h₁, h₂⟩, h₃, -⟩
    exact ⟨⟨h₁, h₃⟩, h₂⟩
  · rintro ⟨⟨h₁, h₃⟩, h₂⟩
    exact ⟨⟨h₁, h₂⟩, h₃, by rw [h₂, hl']⟩

end Key

end GlobalTheory.RoEq

theorem GlobalTheory.RoEq.roinf_eq_realPts : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → Formalism.L2.SG.TermOp.ROinf t₀ = realPts X {σ | c.grp ρ σ ∈ G.stabL (c.lat ρ t₀.lam)} := by
  intro D X Y u u' hst hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hmv
  obtain ⟨hN, hN', -⟩ := GlobalTheory.T.rational_unipotent_groups_lattices_global_coordinates D X Y u u' hst hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hmv
  have hrow : Submodule.IsFullLattice D.host.E t₀.lam := ((Y.rowsOK u).1 t₀.lam t₀.mem).1.1
  have hT : Submodule.IsFullLattice D.host.E (c.lat ρ t₀.lam) := by
    haveI : Submodule.IsLattice D.host.E (c.lat ρ t₀.lam) :=
      Submodule.IsLattice.of_fg _ (hrow.fg.map _)
    refine ⟨?_⟩
    change Submodule.span D.host.E (((ρ.trans c.e : (VS D).V ≃ₗ[D.host.E] G.V) : (VS D).V →ₗ[D.host.E] G.V) '' (t₀.lam : Set (VS D).V)) = ⊤
    rw [← Submodule.map_span, hrow.span_eq_top, Submodule.map_top, LinearEquiv.range]
  have hkey := fun n => GlobalTheory.RoEq.key c (lf D (X.Fu u)) (lf D (X.Fu u')) ρ t₀.lin t₀.lam t₀.lam'
    t₀.rep.2.2.2.1 hT hN hN' n
  ext y
  simp only [Formalism.L2.SG.TermOp.ROinf, Formalism.L2.SG.TermOp.ROset, realPts, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x, n, h₁, h₂, h₃, h₄⟩
    exact ⟨x, n, h₁, h₂, (hkey n).1 ⟨h₃, h₄⟩⟩
  · rintro ⟨x, n, h₁, h₂, h₃⟩
    obtain ⟨h₄, h₅⟩ := (hkey n).2 h₃
    exact ⟨x, n, h₁, h₂, h₄, h₅⟩
end
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPointsTermAutomorphismsEqMovedStabilizerStatement
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realPoints_termAutomorphisms_eq_movedStabilizer : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → Formalism.L2.SG.TermOp.ROinf t₀ = realPts X {σ | c.grp ρ σ ∈ G.stabL (c.lat ρ t₀.lam)} := by
  first | exact @GlobalTheory.RoEq.roinf_eq_realPts | exact GlobalTheory.RoEq.roinf_eq_realPts | (intros; apply GlobalTheory.RoEq.roinf_eq_realPts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeStabiliserCommensurableIntegralPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeStabiliserCommensurableIntegralPoints
open NumberField GlobalTheory.HL
open scoped Pointwise Classical

namespace GlobalTheory.HL.CommInt

theorem stabL_relIndex_K0_ne_zero_of_four_mul_add_seven_le : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig) (r k : ℕ) (G : GFrames A r k), 4 * r + 7 ≤ k → ∀ Λ : G.Lt, Submodule.IsFullLattice E Λ → (G.stabL Λ).relIndex G.K0 ≠ 0 ∧ G.K0.relIndex (G.stabL Λ) ≠ 0 := by
  intro F E _ _ _ _ _ sig A r k G hk Λ hΛ
  obtain ⟨-, hlat, -⟩ := GlobalTheory.T.numberField_lattice_determined_by_local_lattices A (k + 2 * r + 1) Λ hΛ
  obtain ⟨hfin, -⟩ := GlobalTheory.HL.MassProduct.mass_eq_finprod A r k G hk Λ (by first | exact hΛ | exact hΛ.toIsLattice)
  let U : ∀ p, Subgroup (G.S p).GLV :=
    fun p => (G.S p).St ⊓ MulAction.stabilizer (G.S p).GLV (A.lat p Λ)
  let K : ∀ p, Subgroup (G.S p).GLV := fun p => (G.S p).K0
  have hidx : ∀ p, (K p).relIndex (U p) ≠ 0 ∧ (U p).relIndex (K p) ≠ 0 := by
    intro p
    haveI := (A.loc p).lf
    haveI := (A.loc p).char0
    obtain ⟨a, b, -⟩ := (GlobalTheory.HL.volSt (A.L p) r k (G.S p)).1 (A.lat p Λ) (hlat p)
    exact ⟨a, b⟩
  have hKU : {p | K p ≠ U p}.Finite := hfin.subset fun p hp h => hp h.symm
  obtain ⟨h1, h2, -⟩ := GlobalTheory.T.haarInvVolumeRelIndex_pi_univ_eq_finprod K U hKU hidx
  let φ := GlobalTheory.HL.MassProduct.extHom A (k + 2 * r + 1)
  have e1 : G.K0 = (Subgroup.pi Set.univ K).comap φ := (GlobalTheory.HL.MassProduct.comap_pi A _ K).symm
  have e2 : G.stabL Λ = (Subgroup.pi Set.univ U).comap φ := (GlobalTheory.HL.MassProduct.comap_pi A _ U).symm
  rw [e1, e2, Subgroup.relIndex_comap, Subgroup.relIndex_comap]
  exact ⟨fun h0 => h2 (Subgroup.relIndex_eq_zero_of_le_right (Subgroup.map_comap_le _ _) h0),
    fun h0 => h1 (Subgroup.relIndex_eq_zero_of_le_right (Subgroup.map_comap_le _ _) h0)⟩

end GlobalTheory.HL.CommInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeStabiliserCommensurableIntegralPointsStatement
open NumberField GlobalTheory.HL
open scoped Pointwise Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeStabiliser_commensurable_integralPoints : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E} (A : Places F E sig) (r k : ℕ) (G : GFrames A r k), 4 * r + 7 ≤ k → ∀ Λ : G.Lt, Submodule.IsFullLattice E Λ → (G.stabL Λ).relIndex G.K0 ≠ 0 ∧ G.K0.relIndex (G.stabL Λ) ≠ 0 := by
  exact @_root_.GlobalTheory.HL.CommInt.stabL_relIndex_K0_ne_zero_of_four_mul_add_seven_le
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutomorphismCovolumeEqLatticeMass
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovMass

variable {D : D7} (X : HidaSetting D)

noncomputable def realPt (γ : Formalism.HermitianLatticesTheory.isom (VS D).hT) : X.B.I.Ginf :=
  (Classical.choose ((GlobalTheory.RatIsomPoint.ratLink_points D X).1 γ.1 γ.2)).1

theorem realPt_spec {γ : Formalism.HermitianLatticesTheory.isom (VS D).hT} {x : X.B.I.GA} (h : RatLink X x γ.1) : realPt X γ = x.1 := by
  have hs := Classical.choose_spec ((GlobalTheory.RatIsomPoint.ratLink_points D X).1 γ.1 γ.2)
  unfold realPt
  rw [hs.2 x h]

theorem realPt_link (γ : Formalism.HermitianLatticesTheory.isom (VS D).hT) : ∃ x : X.B.I.GA, RatLink X x γ.1 ∧ realPt X γ = x.1 :=
  ⟨_, (Classical.choose_spec ((GlobalTheory.RatIsomPoint.ratLink_points D X).1 γ.1 γ.2)).1, rfl⟩

noncomputable def realPtHom : Formalism.HermitianLatticesTheory.isom (VS D).hT →* X.B.I.Ginf where
  toFun := realPt X
  map_one' := by
    obtain ⟨x, hx, e⟩ := realPt_link X 1
    have h := ((GlobalTheory.RatIsomPoint.ratLink_points D X).2.1 x x _ _ hx hx)
    have h2 := ((GlobalTheory.RatIsomPoint.ratLink_points D X).2.1 x (x⁻¹) _ _ hx h.2.1).1
    have h3 : RatLink X (x * x⁻¹) (1 : Formalism.HermitianLatticesTheory.isom (VS D).hT).1 := by simpa using h2
    rw [realPt_spec X h3]; simp
  map_mul' := by
    intro γ δ
    obtain ⟨x, hx, ex⟩ := realPt_link X γ
    obtain ⟨y, hy, ey⟩ := realPt_link X δ
    have h := ((GlobalTheory.RatIsomPoint.ratLink_points D X).2.1 x y _ _ hx hy).1
    rw [realPt_spec X (γ := γ * δ) h, ex, ey]; rfl

theorem realPtHom_injective : Function.Injective (realPtHom X) := by
  intro γ δ h
  obtain ⟨x, hx, ex⟩ := realPt_link X γ
  obtain ⟨y, hy, ey⟩ := realPt_link X δ
  have h' : x.1 = y.1 := by rw [← ex, ← ey]; exact h
  exact Subtype.ext (((GlobalTheory.RatIsomPoint.ratLink_points D X).2.1 x y _ _ hx hy).2.2 h')

theorem realPts_eq_map (H : Subgroup ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (hH : H ≤ Formalism.HermitianLatticesTheory.isom (VS D).hT) :
    realPts X (H : Set ((VS D).V ≃ₗ[D.host.E] (VS D).V)) = ((H.subgroupOf (Formalism.HermitianLatticesTheory.isom (VS D).hT)).map (realPtHom X) : Set X.B.I.Ginf) := by
  ext y
  constructor
  · rintro ⟨x, n, hx, rfl, hn⟩
    exact ⟨⟨n, hH hn⟩, hn, realPt_spec X (γ := ⟨n, hH hn⟩) hx⟩
  · rintro ⟨γ, hγ, rfl⟩
    obtain ⟨x, hx, ex⟩ := realPt_link X γ
    exact ⟨x, γ.1, hx, ex, hγ⟩

theorem realPts_countable (S : Set ((VS D).V ≃ₗ[D.host.E] (VS D).V)) : (realPts X S).Countable := by
  have := Formalism.L2.SG.TermOp.Vanish.countable_nf X.B.I.E
  have hsub : realPts X S ⊆ ⋃ M : Fin X.B.I.n → Fin X.B.I.n → X.B.I.E,
      {y : X.B.I.Ginf | ∀ v, uMat (y v) = (X.B.I.P v)⁻¹ * (Matrix.of M).map (X.B.I.φ v) * X.B.I.P v} := by
    rintro _ ⟨x, n, ⟨M, -, h1, -⟩, rfl, -⟩
    exact Set.mem_iUnion.2 ⟨fun i j => (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) i j, h1⟩
  refine Set.Countable.mono hsub (Set.countable_iUnion fun M => Set.Subsingleton.countable ?_)
  intro y hy y' hy'
  funext v
  exact Subtype.ext (Units.ext ((hy v).trans (hy' v).symm))

end GlobalTheory.CovMass

theorem GlobalTheory.CovMass.covol_eq_mass : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → t₀.relevant → ∀ μR, Formalism.L2.SG.VolPin.IsPinnedR t₀ w μR → ∀ K : Set X.B.I.Ginf, (MeasurableSet K ∧ ∀ y ∈ Formalism.L2.SG.TermOp.Vanish.Rset t₀, ∃! s, s ∈ ROinf t₀ ∧ s * y ∈ K) → (μR K).toReal = (((X.B.g : ℝ) ^ (D.R.f * Fintype.card (Formalism.L2.SG.RealObj.FreeE w)))⁻¹) * G.mu (c.lat ρ t₀.lam) := by
  intro D X Y u u' hSt hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv hrel μR hPin K hK
  obtain ⟨hKm, hKu⟩ := hK
  have hlink := GlobalTheory.RatIsomPoint.ratLink_points D X
  have hgrp := GlobalTheory.T.rational_unipotent_groups_lattices_global_coordinates D X Y u u' hSt hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv
  have hterm := (GlobalTheory.T.movedTermLattice_isGlobalTerm_phase D X Y u u' hSt hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv).1
  obtain ⟨KA, ⟨hKAm, hKAu⟩, hKA⟩ :=
    GlobalTheory.T.covolume_integralStabiliser_normalisedHaar D X Y u u' hSt hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv hrel μR hPin
  have hRO := GlobalTheory.T.realPoints_termAutomorphisms_eq_movedStabilizer D X Y u u' hSt hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv
  obtain ⟨hfin1, hfin2⟩ := GlobalTheory.T.latticeStabiliser_commensurable_integralPoints (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) _ _ G hk (c.lat ρ t₀.lam) (by first | exact GlobalTheory.HL.ProdStruct.full_lattice_of_term G hterm | exact hterm.1)

  let cj : ((VS D).V ≃ₗ[D.host.E] (VS D).V) →* G.GLV :=
    { toFun := c.grp ρ
      map_one' := by ext x; simp [GlobalTheory.HL.GCoord.grp]
      map_mul' := by intro m n; ext x; simp [GlobalTheory.HL.GCoord.grp] }
  have hcj : ∀ n, cj n = c.grp ρ n := fun _ => rfl
  have hcjs : Function.Surjective cj := fun x => hgrp.2.2.2.1 ρ x
  have hconj : ∀ n, c.grp (ρ * t₀.lin) (t₀.lin⁻¹ * n * t₀.lin) = c.grp ρ n := by
    intro n
    have h1 : ∀ y, t₀.lin (t₀.lin⁻¹ y) = y := fun y => by
      show (t₀.lin * t₀.lin⁻¹) y = y
      rw [mul_inv_cancel]; rfl
    have h2 : ∀ z, t₀.lin ((ρ * t₀.lin).symm z) = ρ.symm z := fun z => by
      rw [LinearEquiv.eq_symm_apply]; exact (ρ * t₀.lin).apply_symm_apply z
    ext x
    simp only [GlobalTheory.HL.GCoord.grp, LinearEquiv.trans_apply, LinearEquiv.mul_apply, LinearEquiv.symm_trans_apply, h1, h2]

  have hStN : ∀ g, g ∈ G.St → g ∈ G.N := fun g hg p => by
    obtain ⟨g', hg', he⟩ := hg p; exact ⟨g', (Subgroup.mem_inf.1 hg').1, he⟩
  have hStN' : ∀ g, g ∈ G.St → g ∈ G.N' := fun g hg p => by
    obtain ⟨g', hg', he⟩ := hg p; exact ⟨g', (Subgroup.mem_inf.1 hg').2, he⟩
  have hK0St : G.K0 ≤ G.St := fun g hg p => by
    obtain ⟨g', hg', he⟩ := hg p; exact ⟨g', hg'.1.1, he⟩
  have hLSt : G.stabL (c.lat ρ t₀.lam) ≤ G.St := fun g hg p => by
    obtain ⟨g', hg', he⟩ := hg p; exact ⟨g', hg'.1, he⟩
  have hStI : G.St.comap cj ≤ Formalism.HermitianLatticesTheory.isom (VS D).hT := fun n hn =>
    ((hgrp.1 n).2 (hStN _ hn)).1
  set P := G.K0.comap cj with hP
  set Q := (G.stabL (c.lat ρ t₀.lam)).comap cj with hQ
  have hPI : P ≤ Formalism.HermitianLatticesTheory.isom (VS D).hT := fun n hn => hStI (hK0St hn)
  have hQI : Q ≤ Formalism.HermitianLatticesTheory.isom (VS D).hT := fun n hn => hStI (hLSt hn)
  set A := (P.subgroupOf (Formalism.HermitianLatticesTheory.isom (VS D).hT)).map (GlobalTheory.CovMass.realPtHom X) with hA
  set B := (Q.subgroupOf (Formalism.HermitianLatticesTheory.isom (VS D).hT)).map (GlobalTheory.CovMass.realPtHom X) with hB
  have hAset : (A : Set X.B.I.Ginf) = realPts X {σ | c.grp ρ σ ∈ G.K0} :=
    (GlobalTheory.CovMass.realPts_eq_map X P hPI).symm
  have hBset : (B : Set X.B.I.Ginf) = Formalism.L2.SG.TermOp.ROinf t₀ := by
    rw [hRO]; exact (GlobalTheory.CovMass.realPts_eq_map X Q hQI).symm
  have hAmem : ∀ y, y ∈ A ↔ y ∈ realPts X {σ | c.grp ρ σ ∈ G.K0} := fun y => by
    rw [← hAset]; rfl
  have hBmem : ∀ y, y ∈ B ↔ y ∈ Formalism.L2.SG.TermOp.ROinf t₀ := fun y => by
    rw [← hBset]; rfl

  obtain ⟨γw, s, s', μw, hγw, hs, hs', hdec, hμwH, hμwS, hμR⟩ := hPin
  have hH := Formalism.L2.SG.Pf.VolPinAsm.pinned_haar t₀ w γw s s' μw hs hs' hdec hμwH
  rw [← hμR] at hH
  have hAR : ∀ y ∈ A, y ∈ Formalism.L2.SG.TermOp.Vanish.Rset t₀ := by
    intro y hy
    obtain ⟨x, n, hx, rfl, hn⟩ := (hAmem y).1 hy
    have hnS : c.grp ρ n ∈ G.St := hK0St hn
    refine ⟨((hlink.2.2 u x n hx).1).1 ((hgrp.1 n).2 (hStN _ hnS)), ?_⟩
    have hm : t₀.lin⁻¹ * n * t₀.lin ∈ NRat (lf D (X.Fu u')) :=
      (hgrp.2.1 _).2 (by rw [hconj]; exact hStN' _ hnS)
    have hl : RatLink X (t₀.pt⁻¹ * x * t₀.pt) (t₀.lin⁻¹ * n * t₀.lin) :=
      (hlink.2.1 _ _ _ _ (hlink.2.1 _ _ _ _ (hlink.2.1 _ _ _ _ t₀.rep.2.1 t₀.rep.2.1).2.1 hx).1 t₀.rep.2.1).1
    have h2 := ((hlink.2.2 u' _ _ hl).1).1 hm
    simpa [Prod.fst_mul, Prod.fst_inv] using h2
  have hBR : ∀ y ∈ B, y ∈ Formalism.L2.SG.TermOp.Vanish.Rset t₀ := fun y hy =>
    Formalism.L2.SG.Pf.LoopBPin.roinf_sub_rset t₀ ((hBmem y).1 hy)
  haveI hCA : Countable A := by
    have := (GlobalTheory.CovMass.realPts_countable X {σ | c.grp ρ σ ∈ G.K0}).to_subtype
    rw [← hAset] at this; exact this
  haveI hCB : Countable B := by
    have := (GlobalTheory.CovMass.realPts_countable X {σ | c.grp ρ σ ∈ G.stabL (c.lat ρ t₀.lam)}).to_subtype
    rw [← hRO, ← hBset] at this; exact this

  have hiA : B.relIndex A = (G.stabL (c.lat ρ t₀.lam)).relIndex G.K0 := by
    rw [hA, hB, Subgroup.relIndex_map_map_of_injective _ _ (GlobalTheory.CovMass.realPtHom_injective X),
      Subgroup.relIndex_subgroupOf hPI, hQ, hP, Subgroup.relIndex_comap,
      Subgroup.map_comap_eq_self_of_surjective hcjs]
  have hiB : A.relIndex B = G.K0.relIndex (G.stabL (c.lat ρ t₀.lam)) := by
    rw [hA, hB, Subgroup.relIndex_map_map_of_injective _ _ (GlobalTheory.CovMass.realPtHom_injective X),
      Subgroup.relIndex_subgroupOf hQI, hQ, hP, Subgroup.relIndex_comap,
      Subgroup.map_comap_eq_self_of_surjective hcjs]
  have hcov := Formalism.L2.SG.Pf.CovolIdx.covol_commens μR (Formalism.L2.SG.TermOp.Vanish.Rset t₀) hH.2.2.1 A B
    (fun x hx => hH.2.2.2 x (hAR x hx)) (fun x hx => hH.2.2.2 x (hBR x hx))
    (fun x hx y hy => Formalism.L2.SG.Pf.VolPinAsm.rset_mul t₀ (hAR x hx) hy)
    (fun x hx y hy => Formalism.L2.SG.Pf.VolPinAsm.rset_mul t₀ (hBR x hx) hy) KA K hKAm hKm
    (fun y hy => by simpa only [hAmem] using hKAu y hy) (fun y hy => by simpa only [hBmem] using hKu y hy)
    (by rw [hiA]; exact hfin1) (by rw [hiB]; exact hfin2)
  rw [hiA, hiB, hKA] at hcov
  set a := (G.stabL (c.lat ρ t₀.lam)).relIndex G.K0 with ha
  set b := G.K0.relIndex (G.stabL (c.lat ρ t₀.lam)) with hb
  set gi : ℝ := ((X.B.g : ℝ) ^ (D.R.f * Fintype.card (Formalism.L2.SG.RealObj.FreeE w)))⁻¹ with hgi
  have hgi0 : 0 ≤ gi := by rw [hgi]; positivity
  have hbne : (b : ℝ≥0∞) ≠ 0 := by exact_mod_cast hfin2
  have hKeq : μR K = ENNReal.ofReal gi * (a : ℝ≥0∞) / (b : ℝ≥0∞) := by
    rw [hcov, ENNReal.mul_div_cancel_right hbne (by simp)]
  rw [hKeq, ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_ofReal hgi0]
  simp only [ENNReal.toReal_natCast]
  unfold GlobalTheory.HL.GFrames.mu GlobalTheory.HL.invVol
  rw [← ha, ← hb]
  ring
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutomorphismCovolumeEqLatticeMassStatement
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.automorphismCovolume_eq_latticeMass : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → t₀.relevant → ∀ μR, Formalism.L2.SG.VolPin.IsPinnedR t₀ w μR → ∀ K : Set X.B.I.Ginf, (MeasurableSet K ∧ ∀ y ∈ Formalism.L2.SG.TermOp.Vanish.Rset t₀, ∃! s, s ∈ ROinf t₀ ∧ s * y ∈ K) → (μR K).toReal = (((X.B.g : ℝ) ^ (D.R.f * Fintype.card (Formalism.L2.SG.RealObj.FreeE w)))⁻¹) * G.mu (c.lat ρ t₀.lam) := by
  first | exact @GlobalTheory.CovMass.covol_eq_mass | exact GlobalTheory.CovMass.covol_eq_mass | (intros; apply GlobalTheory.CovMass.covol_eq_mass <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LevelCharacterUnipotentPartOfAdmissibilityWitnes
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LevelCharacterUnipotentPartOfAdmissibilityWitnes
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdmWitChar

open Formalism.L2.SG.Pf.unitaryCongruence Matrix
open scoped TensorProduct

private theorem coprime_absNorm_of_isCoprime_span {K : Type} [Field K] [NumberField K] (J : Ideal (𝓞 K)) (g : ℕ)
    (hJ : J ⊔ Ideal.span {((g : ℕ) : 𝓞 K)} = ⊤) : Nat.Coprime (Ideal.absNorm J) g := by
  have h1mem : (1 : 𝓞 K) ∈ J ⊔ Ideal.span {((g : ℕ) : 𝓞 K)} := by rw [hJ]; exact Submodule.mem_top
  obtain ⟨j, hj, y, hy, hjy⟩ := Submodule.mem_sup.1 h1mem
  obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 hy
  apply Nat.coprime_of_dvd
  intro p hp hpc hpg
  obtain ⟨k, rfl⟩ := hpg
  by_cases hJb : J = ⊥
  · have hj0 : j = 0 := (Submodule.mem_bot _).1 (hJb ▸ hj)
    have h1 : ((p * k : ℕ) : 𝓞 K) * r = 1 := by rw [← hjy, hj0, zero_add, mul_comm]
    have h2 := congrArg (Algebra.norm ℤ) h1
    rw [map_mul, map_one, ← map_natCast (algebraMap ℤ (𝓞 K)), Algebra.norm_algebraMap] at h2
    have hd : 0 < Module.finrank ℤ (𝓞 K) := Module.finrank_pos
    have h3 : ((p : ℤ)) ∣ 1 := by
      rw [← h2]
      apply Dvd.dvd.mul_right
      apply Dvd.dvd.pow _ hd.ne'
      push_cast
      exact dvd_mul_right _ _
    have h4 := Int.eq_one_of_dvd_one (by positivity) h3
    norm_cast at h4
    exact hp.one_lt.ne' h4
  · haveI : Finite (𝓞 K ⧸ J) := J.finiteQuotientOfFreeOfNeBot hJb
    haveI : Fintype (𝓞 K ⧸ J) := Fintype.ofFinite _
    haveI := Fact.mk hp
    have hcard : p ∣ Fintype.card (𝓞 K ⧸ J) := by
      rw [← Nat.card_eq_fintype_card, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply]
      exact hpc
    obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card p hcard
    have hpx : ((p : ℕ) : 𝓞 K ⧸ J) * x = 0 := by
      rw [← nsmul_eq_mul, ← hx, addOrderOf_nsmul_eq_zero]
    have hunit : ((p : ℕ) : 𝓞 K ⧸ J) * Ideal.Quotient.mk J ((k : 𝓞 K) * r) = 1 := by
      rw [← map_natCast (Ideal.Quotient.mk J), ← map_mul, ← map_one (Ideal.Quotient.mk J), Ideal.Quotient.eq]
      have : ((p : ℕ) : 𝓞 K) * ((k : 𝓞 K) * r) - 1 = -j := by
        rw [← hjy]; push_cast; ring
      rw [this]
      exact J.neg_mem hj
    have hx0 : x = 0 := by
      calc x = (((p : ℕ) : 𝓞 K ⧸ J) * Ideal.Quotient.mk J ((k : 𝓞 K) * r)) * x := by rw [hunit, one_mul]
        _ = Ideal.Quotient.mk J ((k : 𝓞 K) * r) * (((p : ℕ) : 𝓞 K ⧸ J) * x) := by ring
        _ = 0 := by rw [hpx, mul_zero]
    rw [hx0, addOrderOf_zero] at hx
    exact hp.one_lt.ne hx

private theorem hidaSetting_modGAt {D : D7} (X : HidaSetting D) : Formalism.L2.SG.NormCut.ModGAt X := by
  intro g1 Λ hΛ v hv
  have hgg : X.B.g = gS D := X.g_eq
  have hg0 : ((gS D : ℕ) : 𝓞 D.host.E) ≠ 0 := by
    have : (gS D) ≠ 0 := hgg ▸ Formalism.L2.SG.Pf.modulus_g_ne_zero X
    exact_mod_cast this
  let J : Ideal (𝓞 D.host.E) :=
    Submodule.comap (LinearMap.toSpanSingleton (𝓞 D.host.E) (VS D).V v) (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ)
  have hJ : J ⊔ Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    have hgM : ((gS D : ℕ) : 𝓞 D.host.E) ∈ M := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    have hMb : M ≠ ⊥ := fun h => hg0 (by rw [h] at hgM; exact (Submodule.mem_bot _).1 hgM)
    obtain ⟨s, hs, hsv⟩ := hv ⟨M, hM.isPrime, hMb⟩ hgM
    exact hs (hle (Ideal.mem_sup_left (show s ∈ J from hsv)))
  have hcop : Nat.Coprime (Ideal.absNorm J) (gS D) := coprime_absNorm_of_isCoprime_span J (gS D) hJ
  have hcJ : ((Ideal.absNorm J : ℕ) : 𝓞 D.host.E) ∈ J := Ideal.absNorm_mem J
  have hcv : ((Ideal.absNorm J : ℕ) : 𝓞 D.host.E) • v ∈ Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ := hcJ
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at hcv
  obtain ⟨w, hw, hwv⟩ := hcv
  have hlin : ∀ (n : ℕ) (y : (VS D).V), X.B.I.fmat g1⁻¹ *ᵥ incl X.B.I (X.crd (((n : 𝓞 D.host.E)) • y)) =
      (n : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (X.B.I.fmat g1⁻¹ *ᵥ incl X.B.I (X.crd y)) := by
    intro n y
    have h1 : ((n : 𝓞 D.host.E)) • y = ((n : D.host.E)) • y := by
      rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
    rw [h1, Formalism.L2.SG.NormCut.crd_smul' X, map_natCast, Formalism.L2.SG.NormCut.incl_smul' X, map_natCast,
      Matrix.mulVec_smul]
  refine ⟨Ideal.absNorm J, hgg ▸ hcop, ?_⟩
  rw [← hlin, ← hwv, hlin]
  exact Submodule.subset_span ⟨_, (hΛ w).1 hw, by rw [hgg]⟩

private theorem psiEf_divN_eq {D : D7} (X : HidaSetting D) (y : X.B.I.E) :
    X.psiEf (Formalism.L2.SG.HidaSetting.divN X.B.I X.B.g (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) y)) =
      (Formalism.L2.SG.PairVal.psiInf (gS D) (X.ιE y))⁻¹ := by
  have hg : X.B.g = gS D := X.g_eq
  have hdiv : Formalism.L2.SG.HidaSetting.divN X.B.I X.B.g (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) y) =
      Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (algebraMap X.B.I.F X.B.I.E ((X.B.g : X.B.I.F)⁻¹) * y) := by
    unfold Formalism.L2.SG.HidaSetting.divN
    simp [Formalism.UG.inclE, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
  rw [hdiv]
  have h1 := X.psiEf_rat (algebraMap X.B.I.F X.B.I.E ((X.B.g : X.B.I.F)⁻¹) * y)
  have h2 := Formalism.L2.SG.RealObj.PlaceEmbeddingTraceSums.TraceSum_holds D X X.B.g y
  have h3 : Formalism.L2.SG.HidaSetting.psiEinf X.B.I (algebraMap X.B.I.F X.B.I.E ((X.B.g : X.B.I.F)⁻¹) * y) =
      Formalism.L2.SG.PairVal.psiInf X.B.g (X.ιE y) := by
    rw [← h2]
    unfold Formalism.L2.SG.HidaSetting.psiEinf
    refine Finset.prod_congr rfl (fun v _ => ?_)
    congr 1
    have hφ : X.B.I.φ v (algebraMap X.B.I.F X.B.I.E ((X.B.g : X.B.I.F)⁻¹)) = ((X.B.g : ℂ))⁻¹ := by
      rw [map_inv₀, map_natCast, map_inv₀, map_natCast]
    rw [map_mul, hφ]
    simp [star_mul', div_eq_mul_inv]
    ring
  rw [h3] at h1
  rw [← hg]
  exact eq_inv_of_mul_eq_one_left h1

private theorem chiN_eq_of_fmat_mulVec_snoc {D : D7} (X : HidaSetting D) (κ : X.B.I.Gf)
    (ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E))
    (key : ∀ c, X.B.I.fmat κ *ᵥ Fin.snoc (α := fun _ => VA X.B.I) X.e0 X.z0 c -
        ∑ a, Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm ((ξ a c : 𝓞 D.host.E) : D.host.E)) •
          Fin.snoc (α := fun _ => VA X.B.I) X.e0 X.z0 a ∈ mL X.B.I X.B.g) :
    chiN X κ = X.psiEf (Formalism.L2.SG.HidaSetting.divN X.B.I X.B.g (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)
      (X.ιE.symm (∑ a : Fin D.R.rS, ((ξ a.castSucc a.succ : 𝓞 D.host.E) : D.host.E))))) := by
  have hg : X.B.g ≠ 0 := Formalism.L2.SG.Pf.modulus_g_ne_zero X
  obtain ⟨hfe, hfz, -, -⟩ := Formalism.L2.SG.Pf.reference_frame_congruences X
  have hf0 : ∀ a, X.f0 a ∈ X.B.I.Lf := fun a => (X.vectorsInLattice.1 a).2
  have hint : ∀ x : 𝓞 D.host.E,
      Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm (x : D.host.E)) ∈ IntAf X.B.I.F X.B.I.E :=
    fun x => Formalism.L2.SG.NormCut.inclE_int X x
  have hZ : ZMod' X.B.I X.B.g ((∑ a, hA X.B.I (X.f0 a) (X.B.I.fmat κ *ᵥ nxt X.e0 X.z0 a)) -
      Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)
        (X.ιE.symm (∑ a : Fin D.R.rS, ((ξ a.castSucc a.succ : 𝓞 D.host.E) : D.host.E))) - 0) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [sub_zero, map_sum, map_sum, ← Finset.sum_sub_distrib]
    refine Z_sum X.B.I X.B.g _ _ (fun a _ => ?_)
    have hnxt : nxt X.e0 X.z0 a = Fin.snoc (α := fun _ => VA X.B.I) X.e0 X.z0 a.succ := by
      unfold nxt
      split_ifs with h
      · have hs : (a.succ : Fin (D.R.rS + 1)) = Fin.castSucc ⟨a.1 + 1, h⟩ :=
          Fin.ext (by simp only [Fin.val_succ, Fin.val_castSucc])
        rw [hs, Fin.snoc_castSucc]
      · have hs : (a.succ : Fin (D.R.rS + 1)) = Fin.last _ :=
          Fin.ext (by simp only [Fin.val_succ, Fin.val_last]; omega)
        rw [hs, Fin.snoc_last]
    rw [hnxt]
    have hw : ZMod' X.B.I X.B.g (hA X.B.I (X.f0 a) (X.B.I.fmat κ *ᵥ Fin.snoc (α := fun _ => VA X.B.I) X.e0 X.z0 a.succ -
        ∑ c, Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm ((ξ c a.succ : 𝓞 D.host.E) : D.host.E)) •
          Fin.snoc (α := fun _ => VA X.B.I) X.e0 X.z0 c)) :=
      mL_Qs X.B.I X.B.g (hf0 a) (key a.succ)
    rw [hA_sub_right] at hw
    have hsum : hA X.B.I (X.f0 a) (∑ c, Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm ((ξ c a.succ : 𝓞 D.host.E) : D.host.E)) •
          Fin.snoc (α := fun _ => VA X.B.I) X.e0 X.z0 c) =
        ∑ c, Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm ((ξ c a.succ : 𝓞 D.host.E) : D.host.E)) *
          hA X.B.I (X.f0 a) (Fin.snoc (α := fun _ => VA X.B.I) X.e0 X.z0 c) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hL_apply, map_sum]
      simp [hL_apply]
    rw [hsum] at hw
    have hrest : ZMod' X.B.I X.B.g ((∑ c, Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm ((ξ c a.succ : 𝓞 D.host.E) : D.host.E)) *
          hA X.B.I (X.f0 a) (Fin.snoc (α := fun _ => VA X.B.I) X.e0 X.z0 c)) -
        Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm ((ξ a.castSucc a.succ : 𝓞 D.host.E) : D.host.E))) := by
      have he : (∑ c, Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm ((ξ c a.succ : 𝓞 D.host.E) : D.host.E)) *
          hA X.B.I (X.f0 a) (Fin.snoc (α := fun _ => VA X.B.I) X.e0 X.z0 c)) -
        Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm ((ξ a.castSucc a.succ : 𝓞 D.host.E) : D.host.E)) =
          ∑ c, Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm ((ξ c a.succ : 𝓞 D.host.E) : D.host.E)) *
            (hA X.B.I (X.f0 a) (Fin.snoc (α := fun _ => VA X.B.I) X.e0 X.z0 c) - if c = a.castSucc then 1 else 0) := by
        simp [mul_sub, Finset.sum_sub_distrib]
      rw [he]
      refine Z_sum X.B.I X.B.g _ _ (fun c _ => Z_smul X.B.I X.B.g (hint _) ?_)
      refine Fin.lastCases ?_ (fun b => ?_) c
      · have hne : (Fin.last D.R.rS) ≠ a.castSucc := (Fin.castSucc_lt_last a).ne'
        simpa [hne] using hfz a
      · by_cases hb : b = a
        · subst hb
          have h1 := (X.gramIntegral b b).2.2
          simp only at h1
          have h2 := Z_sig X.B.I X.B.g h1
          simpa [hA_symm X.B.I (X.e0 b) (X.f0 b), map_sub, map_one] using h2
        · have hne : b.castSucc ≠ a.castSucc := fun h => hb (Fin.castSucc_injective _ h)
          simpa [hne] using hfe a b (Ne.symm hb)
    have := Z_add X.B.I X.B.g hw hrest
    convert this using 1
    ring
  have hmul := psi_mul_of_Z X.B.I X.B.g X.psiEf_add X.psiEf_int hg hZ
  unfold chiN
  rw [hmul, psi_Z X.B.I X.B.g X.psiEf_add X.psiEf_int hg (Z_zero X.B.I X.B.g), mul_one]

theorem chiN_kOf_eq_inv_psiInf_sgUp : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → ∀ (t : TauC Y u u') (ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E)), AdmWit t.lam (gS D) (lf D (X.Fu u)) t.frame ξ → chiN X (kOf X u u' ((Y.cs u).h ((Y.cs u).base t.lam) : X.B.I.Gf) ((Y.cs u').h ((Y.cs u').base t.lam') : X.B.I.Gf) t.pt) = (Formalism.L2.SG.PairVal.psiInf (gS D) (Formalism.L2.SG.PairVal.sgUp (ξ.map (algebraMap (𝓞 D.host.E) D.host.E))))⁻¹ := by
  intro D X Y u u' hS t ξ hξ
  have hK := Formalism.L2.SG.NormCut.termK_car (Y.cs u) (Y.cs u') t.mem t.mem' t.rep
  have hRL : Formalism.L2.SG.TermOp.RatLink X t.pt t.lin := t.rep.2.1
  have hiso : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
  have hM : Formalism.L2.SG.NormCut.ModGAt X := hidaSetting_modGAt X
  have hξm : ∀ c, ModG (VS D) t.lam (gS D) (t.lin (frame (lf D (X.Fu u')) c) - Formalism.MainNotions.S.Lat.frameAct (frame (lf D (X.Fu u))) ξ c) := by
    intro c
    have h3 := hξ.2.2 c
    have h4 := Formalism.L2.SG.NormCut.frame_mapLF hiso (lf D (X.Fu u')) c
    unfold GTerm.frame at h3
    exact h4 ▸ h3
  have key := Formalism.L2.SG.NormCut.key_gen (Y.cs u) (Y.cs u') (Formalism.L2.SG.Full.Full.frameTie (X := X) u u') hM t.mem t.pt t.lin hRL ξ hξm hK
  rw [chiN_eq_of_fmat_mulVec_snoc X _ ξ key, psiEf_divN_eq, RingEquiv.apply_symm_apply]
  congr 2
  rw [GlobalTheory.RatIsomPoint.sgUp_eq]
  simp [Matrix.map_apply]

end GlobalTheory.AdmWitChar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LevelCharacterUnipotentPartOfAdmissibilityWitnesStatement
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelCharacter_unipotentPart_of_admissibilityWitness : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → ∀ (t : TauC Y u u') (ξ : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) (𝓞 D.host.E)), AdmWit t.lam (gS D) (lf D (X.Fu u)) t.frame ξ → chiN X (kOf X u u' ((Y.cs u).h ((Y.cs u).base t.lam) : X.B.I.Gf) ((Y.cs u').h ((Y.cs u').base t.lam') : X.B.I.Gf) t.pt) = (Formalism.L2.SG.PairVal.psiInf (gS D) (Formalism.L2.SG.PairVal.sgUp (ξ.map (algebraMap (𝓞 D.host.E) D.host.E))))⁻¹ := by
  first | exact @GlobalTheory.AdmWitChar.chiN_kOf_eq_inv_psiInf_sgUp | exact GlobalTheory.AdmWitChar.chiN_kOf_eq_inv_psiInf_sgUp | (intros; apply GlobalTheory.AdmWitChar.chiN_kOf_eq_inv_psiInf_sgUp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowTermAmplitudeEqMassMulPhase
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AmpTerm

theorem gval_of_movesTo {D : D7} {T T' : D.host.E} {F00 F : LFlag (D.sp.Y 0) D.R.rS T}
    {F'0 F' : LFlag (D.sp.Y 0) D.R.rS T'} {ρ : (VS D).V ≃ₗ[D.host.E] (VS D).V}
    {U U' : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E}
    (h : MovesTo F00 F'0 F F' ρ U U') : Gval F F' = Gval F00 F'0 := by
  obtain ⟨hρ, hU, hU', hF, hF'⟩ := h
  have hZ : ZhatL F F' = U.conjTranspose * ZhatL F00 F'0 * U' := by
    ext a b
    have e1 : ZhatL F F' a b = (VS D).hT (ρ (frame F a)) (ρ (frame F' b)) := by
      rw [hρ]; rfl
    have hz : ∀ c d, ZhatL F00 F'0 c d = (VS D).hT (frame F00 c) (frame F'0 d) := fun _ _ => rfl
    rw [e1, hF a, hF' b]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mul_apply, hz, map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply,
      smul_eq_mul, Matrix.conjTranspose_apply, starRingEnd_apply, Finset.sum_mul, Finset.mul_sum]
    simp only [RingHom.id_apply]
    refine Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => ?_))
    ring
  have hD : ∀ l, Dl F.fl F'.fl l = Dl F00.fl F'0.fl l := by
    intro l
    have := Formalism.L2.SG.Pf.leadMinor_uni U.conjTranspose (ZhatL F00 F'0) U'
      (fun a c hac => by simp [Matrix.conjTranspose_apply, (hU c a).1 hac])
      (fun a => by simp [Matrix.conjTranspose_apply, (hU a a).2 rfl])
      (fun d b hbd => (hU' d b).1 hbd) (fun b => (hU' b b).2 rfl) l
    rw [← hZ] at this
    exact this
  simp only [Gval, Gflag, hD]

theorem G_eq_gval {D : D7} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word} (t : TauC Y u u') :
    t.G = Gval (lf D (X.Fu u)) t.frame :=
  Formalism.L2.SG.TermDef.Gt_mk (Formalism.L2.SG.Pf.g_value_function _ _ _) ⟨t.frame, t.rep.2.2.2.2⟩

theorem lam_eq_of_row {D : D7} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word} {t t₀ : TauC Y u u'}
    (h : (Y.tO u u').rowOf t = (Y.tO u u').rowOf t₀) : t.lam = t₀.lam ∧ t.lam' = t₀.lam' :=
  ⟨congrArg (fun r => r.1.1) h, congrArg (fun r => r.2.1.1) h⟩

theorem exists_admissibleWitness_rowTerm {D : D7} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word} (t : TauC Y u u') :
    ∃ ξ, AdmWit t.lam (gS D) (lf D (X.Fu u)) t.frame ξ :=
  t.rep.2.2.2.2.2.1

end GlobalTheory.AmpTerm

namespace GlobalTheory.AmpTerm


open Formalism.L2.SG.PairVal in
theorem amp_eq_mass_phase : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ ν, Formalism.L2.SG.RealObj.NuQPin X u u' ν → ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → t₀.relevant → Formalism.L2.SG.PairVal.ptOf t₀.toTerm = w → ∃ T : X.Vpi u' →L[ℂ] X.Vpi u, ‖Formalism.L2.SG.PackageTie.hsEmb T‖ = ‖Formalism.L2.SG.PackageTie.hsEmb (Jw Y u u' ν w)‖ ∧ ∀ (t : TauC Y u u') (n m : ((VS D).V ≃ₗ[D.host.E] (VS D).V)), (Y.tO u u').rowOf t = (Y.tO u u').rowOf t₀ → n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m → ampN (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') t = ((((((X.B.g : ℝ) ^ (D.R.f * Fintype.card (Formalism.L2.SG.RealObj.FreeE w)))⁻¹) * G.mu (c.lat (ρ * n) t.lam) : ℝ) : ℂ) * G.om (G.datOf (c.lat ρ t₀.lam)) (c.lat (ρ * n) t.lam)) • T := by
  intro D X Y u u' hS hk w F00 F'0 FP hZ hG hAt G c ν hν t₀ ρ U U' hmv hrel hpt
  have hG0 : t₀.G ≠ 0 := by
    rw [G_eq_gval]; exact fun h => hG ((gval_of_movesTo hmv).symm.trans h)
  obtain ⟨-, T0, hT0, hform⟩ := GlobalTheory.T.orbital_integrals_terms_one_doubleCoset D X Y u u' hS ν hν t₀ hrel hG0 w hpt.symm
  have hpU : psiInf (gS D) (sgUp U) ≠ 0 := by
    intro h; have := norm_psiInf (gS D) (sgUp U); rw [h, norm_zero] at this; exact zero_ne_one this
  have hpU' : psiInf (gS D) (sgUp U') ≠ 0 := by
    intro h; have := norm_psiInf (gS D) (sgUp U'); rw [h, norm_zero] at this; exact zero_ne_one this
  refine ⟨(((scl (Y.FN u) (Y.FN u') (X := X) (u := u) (u' := u') * X.volK2 : ℝ) : ℂ) *
      psiInf (gS D) (sgUp U) * (psiInf (gS D) (sgUp U'))⁻¹) • T0, ?_, ?_⟩
  · rw [map_smul, norm_smul, hT0]
    unfold Jw
    rw [map_smul, norm_smul, norm_mul, norm_mul, norm_inv, norm_psiInf, norm_psiInf]
    simp
  · rintro t n m hrow ⟨hn, hm, hlin⟩
    obtain ⟨hlam, hlam'⟩ := lam_eq_of_row hrow
    have hL := GlobalTheory.RatIsomPoint.ratLink_points D X
    obtain ⟨xn, hxn, -⟩ := hL.1 n hn.1
    obtain ⟨xm, hxm, -⟩ := hL.1 m hm.1
    obtain ⟨μR, K, hpin, hK, hOO⟩ := hform t n m xn xm ⟨hn, hm, hlin⟩ hxn hxm
    obtain ⟨-, -, -, -, -, hgrp⟩ :=
      GlobalTheory.T.rational_unipotent_groups_lattices_global_coordinates D X Y u u' hS hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hmv
    obtain ⟨A, A', hA, hA', hnA, hmA', hmv'⟩ := hgrp t n m ⟨hn, hm, hlin⟩
    have hcos := GlobalTheory.T.flagTerm_invariants_const_on_rationalDoubleCoset D X Y u u' hS t₀ t n m hrel hG0 ⟨hn, hm, hlin⟩
    have hvol := GlobalTheory.T.automorphismCovolume_eq_latticeMass D X Y u u' hS hk w F00 F'0 FP hZ hG hAt G c t (ρ * n) (U * A) (U' * A')
      hmv' hcos.1 μR hpin K hK
    obtain ⟨ξ, hξ⟩ := exists_admissibleWitness_rowTerm t
    have hchi := GlobalTheory.T.levelCharacter_unipotentPart_of_admissibilityWitness D X Y u u' hS t ξ hξ
    have hterm := (GlobalTheory.T.movedTermLattice_isGlobalTerm_phase D X Y u u' hS hk w F00 F'0 FP hZ hG hAt G c t (ρ * n) (U * A) (U' * A')
      hmv').2 ξ hξ
    have hdat := (GlobalTheory.T.termRow_eq_iff_movedLatticeInnerData_eq D X Y u u' hS hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hmv t n m hlam hlam'
      ⟨hn, hm, hlin⟩).1 hrow
    rw [hdat] at hterm
    have hpn := (hL.2.2 u xn n hxn).2 hn A hnA
    have hpm := (hL.2.2 u' xm m hxm).2 hm A' hmA'
    have hU := hmv.2.1
    have hU' := hmv.2.2.1
    unfold ampN
    rw [hchi, hOO, hpn, hpm, hvol, hterm, Formalism.L2.SG.Pf.sgUp_mul hU hA, Formalism.L2.SG.Pf.sgUp_mul hU' hA',
      Formalism.L2.SG.Pf.psiInf_add, Formalism.L2.SG.Pf.psiInf_add, smul_smul, smul_smul, smul_smul]
    congr 1
    field_simp

end GlobalTheory.AmpTerm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowTermAmplitudeEqMassMulPhaseStatement
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowTerm_amplitude_eq_mass_mul_phase : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ ν, Formalism.L2.SG.RealObj.NuQPin X u u' ν → ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → t₀.relevant → Formalism.L2.SG.PairVal.ptOf t₀.toTerm = w → ∃ T : X.Vpi u' →L[ℂ] X.Vpi u, ‖Formalism.L2.SG.PackageTie.hsEmb T‖ = ‖Formalism.L2.SG.PackageTie.hsEmb (Jw Y u u' ν w)‖ ∧ ∀ (t : TauC Y u u') (n m : ((VS D).V ≃ₗ[D.host.E] (VS D).V)), (Y.tO u u').rowOf t = (Y.tO u u').rowOf t₀ → n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m → ampN (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') t = ((((((X.B.g : ℝ) ^ (D.R.f * Fintype.card (Formalism.L2.SG.RealObj.FreeE w)))⁻¹) * G.mu (c.lat (ρ * n) t.lam) : ℝ) : ℂ) * G.om (G.datOf (c.lat ρ t₀.lam)) (c.lat (ρ * n) t.lam)) • T := by
  first | exact @GlobalTheory.AmpTerm.amp_eq_mass_phase | exact GlobalTheory.AmpTerm.amp_eq_mass_phase | (intros; apply GlobalTheory.AmpTerm.amp_eq_mass_phase <;> assumption)
end
