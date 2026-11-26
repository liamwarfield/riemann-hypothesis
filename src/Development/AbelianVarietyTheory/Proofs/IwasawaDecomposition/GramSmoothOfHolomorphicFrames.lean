module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocalization
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProperOfCompleteDVRLiftGenericPoint
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsTanBasisOfUniqueCombination
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentialKernelsIsHolomorphicLatticeFamily

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramSmoothOfHolomorphicFrames
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix
open Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo Formalism.L2.PjFree
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.PullbackSections
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.HodgeDomain GlobalTheory.LieMet GlobalTheory.CxPts GlobalTheory.TrueCx GlobalTheory.Toroidal GlobalTheory.ShFam
open GlobalTheory.TrueCx.TorHolo GlobalTheory.TrueCx.TorFrHolo
open ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows (isDerivAt0_comp_hom isDerivAt0_unique)
open Filter Topology
open scoped ContDiff CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GramFamily

section Pull

variable {K : Type} [CommRing K] {Y : Scheme.{0}} {p : Y ⟶ Sp K} {σ : K →+* ℂ} {D : ℕ}

end Pull

section LocalBasis

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X Y : Scheme.{0}}

variable {K : Type} [CommRing K] {p : Y ⟶ Sp K} {σ : K →+* ℂ}

end LocalBasis

section Family

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
  {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {O : Type} [CommRing O] {β : O →+* c.F} (Z : Model Xo c β) {σ : c.F →+* ℂ}

theorem isHolTo_cxPt {U : Formalism.L2.PjFree.Unf Xo c σ r} (hU : Formalism.L2.PjFree.IsUnf U) (k : U.Comp) {n : ℕ} {B : Set (Fin n → ℂ)} (hB : IsOpen B)
    (x : (Fin n → ℂ) → (U.X k).dom) (hd : ∀ τ a c, DifferentiableOn ℂ (fun b => mat (x b).1 τ a c) B) :
    IsHolTo B fun b => (cxPt Z (U.un k (x b))).1 := by
  obtain ⟨-, -, -, -, -, g, e, F, ik, φ, -, hun⟩ := hU
  choose P hP hP' hx _ using hun k
  have h1 := (F.hol (ik k) n B (fun b => P (x b)) hB ⟨fun b _ => hP' _, fun a => differentiableOn_pi.2 fun i => by
    simp only [hP]
    exact differentiableOn_perFr _ (fun b _ => (x b).2) hd _ _ _⟩).1
  refine isHolTo_comp (isHolTo_of_fst _ _ hB _ (fun b => ptC_snd _) ?_) Z.jQ
  simp only [ptC_fst]
  exact LocLift.isHolTo_congr h1 fun b _ => hx _

end Family

end GlobalTheory.GramFamily
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PunctPolydiscUniversalCoverOpenConvexExpAnalytic
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PunctPolydiscUniversalCoverOpenConvexExpAnalytic
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.logDom_chart_props : ∀ (n a : ℕ), IsOpen (GlobalTheory.ShFam.Hor.logDom n a) ∧ Convex ℝ (GlobalTheory.ShFam.Hor.logDom n a) ∧ (∀ s, AnalyticAt ℂ (GlobalTheory.ShFam.Hor.logExp a : (Fin n → ℂ) → Fin n → ℂ) s) ∧ Set.MapsTo (GlobalTheory.ShFam.Hor.logExp a) (GlobalTheory.ShFam.Hor.logDom n a) (Metric.ball (0 : Fin n → ℂ) 1) := by
  intro n a
  have hEq : GlobalTheory.ShFam.Hor.logDom n a = ⋂ k : Fin n, (fun s : Fin n → ℂ => s k) ⁻¹' (if (k : ℕ) < a then {z : ℂ | z.re < 0} else Metric.ball (0 : ℂ) 1) := by
    ext s
    simp only [GlobalTheory.ShFam.Hor.logDom, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
    refine forall_congr' fun k => ?_
    split_ifs <;> simp [Metric.mem_ball, dist_zero_right]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hEq]
    refine isOpen_iInter_of_finite fun k => ?_
    refine IsOpen.preimage (continuous_apply k) ?_
    split_ifs
    · exact isOpen_lt Complex.continuous_re continuous_const
    · exact Metric.isOpen_ball
  · rw [hEq]
    refine convex_iInter fun k => ?_
    have hc : Convex ℝ (if (k : ℕ) < a then {z : ℂ | z.re < 0} else Metric.ball (0 : ℂ) 1) := by
      split_ifs
      · exact convex_halfSpace_lt (f := Complex.re) Complex.reLm.isLinear 0
      · exact convex_ball 0 1
    exact hc.linear_preimage (LinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) k)
  · intro s
    rw [analyticAt_pi_iff]
    intro k
    show AnalyticAt ℂ (fun s : Fin n → ℂ => if (k : ℕ) < a then Complex.exp (s k) else s k) s
    have hp : AnalyticAt ℂ (fun s : Fin n → ℂ => s k) s :=
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) k).analyticAt s
    split_ifs
    · exact analyticAt_cexp.comp hp
    · exact hp
  · intro s hs
    rw [Metric.mem_ball, dist_zero_right, pi_norm_lt_iff one_pos]
    intro k
    have hk := hs k
    simp only [GlobalTheory.ShFam.Hor.logExp]
    split_ifs at hk ⊢ with h
    · rw [Complex.norm_exp]
      exact Real.exp_lt_one_iff.mpr hk
    · exact hk
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PunctPolydiscUniversalCoverOpenConvexExpAnalyticStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.punctPolydiscUniversalCover_open_convex_exp_analytic : ∀ (n a : ℕ), IsOpen (GlobalTheory.ShFam.Hor.logDom n a) ∧ Convex ℝ (GlobalTheory.ShFam.Hor.logDom n a) ∧ (∀ s, AnalyticAt ℂ (GlobalTheory.ShFam.Hor.logExp a : (Fin n → ℂ) → Fin n → ℂ) s) ∧ Set.MapsTo (GlobalTheory.ShFam.Hor.logExp a) (GlobalTheory.ShFam.Hor.logDom n a) (Metric.ball (0 : Fin n → ℂ) 1) := by
  first | exact @GlobalTheory.logDom_chart_props | exact GlobalTheory.logDom_chart_props | (intros; apply GlobalTheory.logDom_chart_props <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsStrictIff
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolCell

variable {X : Type} [AddCommGroup X] {m : ℕ}

def linW (w : (X × X) →₀ ℤ) : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ where
  toFun β := w.sum fun p k => k * β p.1 p.2
  map_add' β γ := by
    simp only [LinearMap.add_apply, mul_add]
    exact Finsupp.sum_add
  map_smul' c β := by
    simp only [LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, Finsupp.mul_sum]
    exact Finsupp.sum_congr fun _ _ => by ring

def evalW (w : (X × X) →₀ ℤ) (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) : ℝ := w.sum fun p k => (k : ℝ) * B p.1 p.2

theorem linW_apply (w : (X × X) →₀ ℤ) (β : LinearMap.BilinForm ℤ X) : linW w β = w.sum fun p k => k * β p.1 p.2 := rfl

theorem evalW_toReal (w : (X × X) →₀ ℤ) (β : LinearMap.BilinForm ℤ X) : evalW w (toReal β) = linW w β := by
  simp [evalW, linW_apply, Finsupp.sum]

theorem evalW_add (w : (X × X) →₀ ℤ) (B B' : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) : evalW w (B + B') = evalW w B + evalW w B' := by
  simp only [evalW, LinearMap.add_apply, mul_add]
  exact Finsupp.sum_add

theorem evalW_smul (w : (X × X) →₀ ℤ) (t : ℝ) (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) : evalW w (t • B) = t * evalW w B := by
  simp only [evalW, LinearMap.smul_apply, smul_eq_mul, Finsupp.mul_sum]
  exact Finsupp.sum_congr fun _ _ => by ring

def evalWL (w : (X × X) →₀ ℤ) : (X →ₗ[ℤ] X →ₗ[ℤ] ℝ) →ₗ[ℝ] ℝ where
  toFun := evalW w
  map_add' := evalW_add w
  map_smul' t B := evalW_smul w t B

theorem evalW_sum (w : (X × X) →₀ ℤ) (t : Fin m → ℝ) (u : Fin m → LinearMap.BilinForm ℤ X) :
    evalW w (∑ i, t i • toReal (u i)) = ∑ i, t i * linW w (u i) := by
  have := map_sum (evalWL w) (fun i => t i • toReal (u i)) Finset.univ
  simp only [evalWL, LinearMap.coe_mk, AddHom.coe_mk] at this
  rw [this]
  exact Finset.sum_congr rfl fun i _ => by rw [evalW_smul, evalW_toReal]

def rcone (u : Fin m → LinearMap.BilinForm ℤ X) : Set (X →ₗ[ℤ] X →ₗ[ℤ] ℝ) :=
  {B | ∃ t : Fin m → ℝ, (∀ i, 0 ≤ t i) ∧ B = ∑ i, t i • toReal (u i)}

def StrictWith {O : Type} [CommRing O] (bar : O → O) (φ : InvFun O) [Module O X] [Module.Finite O X] (N : ℕ)
    (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) (u : Fin m → LinearMap.BilinForm ℤ X) : Prop :=
  (∀ i, (ℓ (u i) : ℝ) = N * φ.evalZ (u i)) ∧ (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → N * φ.evalZ β ≤ ℓ β) ∧
    ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → N * φ.evalZ β = ℓ β →
      ∃ (k : ℕ) (c : Fin m → ℕ), 0 < k ∧ k • β = ∑ i, c i • u i

theorem isStrict_iff {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} [Module O X] [Module.Finite O X]
    {u : Fin m → LinearMap.BilinForm ℤ X} : IsStrict bar φ u ↔ ∃ (N : ℕ) (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), 0 < N ∧
      StrictWith bar φ N ℓ u := Iff.rfl

def kDen (N n : ℕ) (𝓜 : Finset ℕ) : ℕ := N * ∏ M ∈ 𝓜, (M + 1) ^ n

def lamW (D N n : ℕ) (𝓜 : Finset ℕ) (r : (Fin n → ℤ) →ₗ[ℤ] X) (w : (X × X) →₀ ℤ)
    (a : ∀ M : ℕ, (Fin n → ZMod (M + 1)) → Fin n → ℤ) : (X × X) →₀ ℤ :=
  (D : ℤ) • ((∏ M ∈ 𝓜, ((M : ℤ) + 1) ^ n) • w +
    ∑ M ∈ 𝓜, ((N : ℤ) * ∏ M' ∈ 𝓜.erase M, ((M' : ℤ) + 1) ^ n) • ∑ y, Finsupp.single (r (a M y), r (a M y)) 1)

end GlobalTheory.PolCell
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenAbelianLocus
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbLocusOpenGlobal

theorem exists_unit (S : Scheme.{0}) (s : S) :
    ∃ n : ℕ, 2 ≤ n ∧ s ∈ S.basicOpen (n : Γ(S, ⊤)) := by
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add (R := S.presheaf.stalk s) (a := (3 : S.presheaf.stalk s)) (b := -2)
      (by norm_num) with h | h
  · refine ⟨3, by norm_num, (S.mem_basicOpen_top _ s).2 ?_⟩
    rw [map_natCast]; exact_mod_cast h
  · refine ⟨2, le_rfl, (S.mem_basicOpen_top _ s).2 ?_⟩
    rw [map_natCast]; exact_mod_cast (IsUnit.neg_iff _).1 h

theorem isOpen_connectedComponent_of_noetherian {X : Type} [TopologicalSpace X] [NoetherianSpace X] (x : X) :
    IsOpen (connectedComponent x) := by
  rw [← isClosed_compl_iff, show (connectedComponent x)ᶜ = ⋃ Z ∈ {Z ∈ irreducibleComponents X | ¬ Z ⊆ connectedComponent x}, Z from
    Set.ext fun y => ⟨fun h => Set.mem_biUnion ⟨irreducibleComponent_mem_irreducibleComponents y, fun k => h (k mem_irreducibleComponent)⟩
      mem_irreducibleComponent, fun h k => by
      obtain ⟨Z, ⟨a, b⟩, c⟩ := Set.mem_iUnion₂.1 h
      exact b ((a.1.isConnected.isPreconnected.subset_connectedComponent c).trans (connectedComponent_eq k).ge)⟩]
  exact (NoetherianSpace.finite_irreducibleComponents.subset (by exact fun _ h => h.1)).isClosed_biUnion fun Z h =>
    isClosed_of_mem_irreducibleComponents Z h.1

theorem exists_connected_open {S : Scheme.{0}} [IsLocallyNoetherian S] (N : S.Opens) (s : S) (hs : s ∈ N) :
    ∃ (V : Scheme.{0}) (w : V ⟶ S), IsOpenImmersion w ∧ ConnectedSpace V ∧ s ∈ Set.range w ∧
      Set.range w ⊆ (N : Set S) := by
  obtain ⟨U, hU, hsU, hUN⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := N) (x := s) hs
  have : IsAffine U := hU
  have : IsNoetherian U.toScheme := {}
  have : NoetherianSpace U.toScheme := inferInstance
  let V : U.toScheme.Opens := ⟨_, isOpen_connectedComponent_of_noetherian (X := U.toScheme) ⟨s, hsU⟩⟩
  have : ConnectedSpace V.toScheme := isConnected_iff_connectedSpace.1 isConnected_connectedComponent
  refine ⟨V.toScheme, V.ι ≫ U.ι, inferInstance, this, ⟨⟨⟨s, hsU⟩, mem_connectedComponent⟩, rfl⟩, ?_⟩
  rintro _ ⟨v, rfl⟩
  exact hUN (V.ι v).2

theorem isOpen_abLocus_of_locallyNoetherian {S : Scheme.{0}} [IsLocallyNoetherian S] (G : Over S) [GrpObj G]
    (hG : IsSemiAbelian G) : IsOpen (abLocus G) := by
  refine isOpen_iff_forall_mem_open.2 fun s hs => ?_
  obtain ⟨n, h2, hn⟩ := exists_unit S s
  obtain ⟨V, w, hw, hV, ⟨v, rfl⟩, hle⟩ := exists_connected_open _ s hn
  have hG' : IsSemiAbelian ((Over.pullback w).obj G) := IsSemiAbelian.pullback w G hG
  have := hG'.smooth
  have := hG'.geomConnected
  have : ConnectedSpace ((Over.pullback w).obj G).left := GeometricallyConnected.connectedSpace ((Over.pullback w).obj G).hom ((Over.pullback w).obj G).hom.isOpenMap
  obtain ⟨x₀⟩ : Nonempty ((Over.pullback w).obj G).left := inferInstance
  obtain ⟨g, hg⟩ := exists_dim_of_preconnected ((Over.pullback w).obj G).hom x₀
  have hu : IsUnit ((n : ℕ) : Γ(V, ⊤)) := by
    have h₀ := RingedSpace.isUnit_res_basicOpen S.toRingedSpace ((n : ℕ) : Γ(S, ⊤))
    have h₁ : (⊤ : V.Opens) ≤ w ⁻¹ᵁ S.basicOpen ((n : ℕ) : Γ(S, ⊤)) := fun y _ => hle ⟨y, rfl⟩
    have h₀' : IsUnit ((n : ℕ) : Γ(S, S.basicOpen ((n : ℕ) : Γ(S, ⊤)))) := by
      simp only [map_natCast] at h₀
      exact h₀
    have := h₀'.map (w.appLE _ ⊤ h₁).hom
    rwa [map_natCast] at this
  have hU := AbLocusOpen.isOpen_abLocus ((Over.pullback w).obj G) hG' hg h2 hu
  have key : ∀ y : V, w y ∈ abLocus G ↔ y ∈ abLocus ((Over.pullback w).obj G) := fun y =>
    abLocus_pullback abLocusOne hG (isGrpPullback_pullback G w).1 y
  refine ⟨w '' abLocus ((Over.pullback w).obj G), ?_, w.isOpenEmbedding.isOpenMap _ hU, ⟨v, (key v).1 hs, rfl⟩⟩
  rintro _ ⟨y, hy, rfl⟩
  exact (key y).2 hy

end GlobalTheory.AbLocusOpenGlobal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorsionCharExtendsDivisibleLevel
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsCharExt

section Ring

variable (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C]

end Ring

theorem sp_id (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := Spec.map_id _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X)

def pull {S S' : Scheme.{0}} {a : S ⟶ X} {a' : S' ⟶ X} (g : S' ⟶ S) (h : g ≫ a = a') :
    (Over.mk a ⟶ t.G) →* (Over.mk a' ⟶ t.G) where
  toFun w := (Over.homMk g h : Over.mk a' ⟶ Over.mk a) ≫ w
  map_one' := MonObj.comp_one _
  map_mul' _ _ := MonObj.comp_mul _ _ _

end GlobalTheory.TorsCharExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProperOfAbelianEverywhere
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.RayEv
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ProperOfAbelianFibres
open IsLocalRing

theorem apply_genericPoint_of_flat {X Y : Scheme.{0}} [IrreducibleSpace X] [IrreducibleSpace Y] (f : X ⟶ Y)
    [Flat f] : f (genericPoint X) = genericPoint Y := by
  obtain ⟨x', hx', hfx'⟩ := Flat.generalizingMap f (genericPoint_specializes (f (genericPoint X)))
  refine (Specializes.antisymm ?_ ?_).eq
  · rw [← hfx']
    exact (genericPoint_specializes x').map f.continuous
  · exact genericPoint_specializes _

theorem isProper_dvr {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (V : Type) [CommRing V]
    [IsDomain V] [IsLocalRing V] (hW : GlobalTheory.LN.CDvr V) (t : SAB H (Sp V)) (hP : GlobalTheory.LN.PolAt t (jK V))
    (hab : abLocus t.G = Set.univ) : IsProper t.G.hom := by
  haveI := hW.1
  haveI := hW.2.2
  obtain ⟨l₁, l₂, -⟩ := GlobalTheory.firstFiveLaws
  have ht : ∀ z, z ∈ abLocus t.G := fun z => hab ▸ Set.mem_univ z
  obtain ⟨P, -⟩ := GlobalTheory.LN.uDvrSt_holds E H V hW t hP (GlobalTheory.GoodTrait.splitOver_of_abLocus t.G t.semi ht)
  have hmax : (maximalIdeal V ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one]; infer_instance
  have hF : IsField (V ⧸ maximalIdeal V ^ (0 + 1)) := (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 hmax
  have p : Spec (CommRingCat.of (V ⧸ maximalIdeal V ^ (0 + 1))) := by
    letI := hF.toField
    exact (default : PrimeSpectrum (V ⧸ maximalIdeal V ^ (0 + 1)))
  let g := P.U.gt 0
  have : Mono g.i := ⟨fun a b h => g.isKernel.hom_ext h (toUnit_unique _ _)⟩
  have hs := GlobalTheory.ArcNotAbelian.subsingleton_of_mem_abLocus t.G t.semi _ hF (thick V (maximalIdeal V) 0) p (ht _)
    P.D.toPre.X g.i g.i_hom
  exact (GlobalTheory.isAbelianScheme_of_unif_of_subsingleton l₁ l₂ V hW.2.1 P.D P.A t.G t.semi P.U hs).proper

theorem isProper_of_polAt_of_abLocus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type)
    [CommRing R] [IsDomain R] [IsNoetherianRing R] [CharZero R] (t : SAB H (Sp R)), GlobalTheory.LN.PolAt t (jK R) →
    abLocus t.G = Set.univ → IsProper t.G.hom := by
  intro E _ _ _ H R _ _ _ _ t hP hab
  haveI : IsSemiAbelian t.G := t.semi
  haveI := t.semi.separated
  haveI := t.semi.quasiCompact
  haveI := t.semi.smooth
  haveI : IsIntegral t.G.left := GlobalTheory.isIntegral_left_of_isSemiAbelian t.G
  refine GlobalTheory.T.isProper_of_completeDVR_lift_genericPoint R t.G.left t.G.hom ?_
  intro V K _ _ _ _ _ _ _ x y hx hxy
  obtain ⟨φ, rfl⟩ : ∃ φ : R →+* V, spMap φ = y := ⟨(Spec.preimage y).hom, by simp [spMap]⟩

  let p₀ : Sp K := (⊥ : PrimeSpectrum K)
  have h₁ : x p₀ = genericPoint t.G.left := hx ⟨p₀, rfl⟩
  have h₂ : (x ≫ t.G.hom) p₀ = (⊥ : PrimeSpectrum R) := by
    rw [Scheme.Hom.comp_apply, h₁, apply_genericPoint_of_flat]
    exact genericPoint_eq_bot_of_affine (CommRingCat.of R)
  rw [hxy] at h₂
  have h₃ : Ideal.comap φ (Ideal.comap (algebraMap V K) (⊥ : Ideal K)) = ⊥ := congrArg PrimeSpectrum.asIdeal h₂
  have hinj : Function.Injective φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    have : a ∈ Ideal.comap φ (Ideal.comap (algebraMap V K) (⊥ : Ideal K)) := by simp [ha]
    rw [h₃] at this
    simpa using this
  haveI : CharZero V := charZero_of_injective_ringHom hinj

  obtain ⟨tV, ⟨m⟩⟩ := exists_sab (spMap φ) t
  have hinj' : Function.Injective ((algebraMap V (FractionRing V)).comp φ) :=
    (IsFractionRing.injective V (FractionRing V)).comp hinj
  let ψ : FractionRing R →+* FractionRing V := IsFractionRing.lift hinj'
  have hg : spMap ψ ≫ jK R = jK V ≫ spMap φ := by
    simp only [spMap, jK, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext r
    simp [ψ, IsFractionRing.lift_algebraMap]
  have hPV : GlobalTheory.LN.PolAt tV (jK V) := GlobalTheory.DatUniq.polAt_pull m hP (jK V) (spMap ψ) hg
  have habV : abLocus tV.G = Set.univ := Set.eq_univ_of_forall fun z =>
    (abLocus_pullback abLocusOne t.semi m.cart.1 z).1 (hab ▸ Set.mem_univ _)
  have hpV : IsProper tV.G.hom := isProper_dvr V ⟨inferInstance, inferInstance, inferInstance⟩ tV hPV habV

  let xV : Sp K ⟶ tV.G.left := m.cart.1.lift x (spMap (algebraMap V K)) hxy
  have hE : ValuativeCriterion.Existence tV.G.hom := by
    have h : UniversallyClosed tV.G.hom := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  let S : ValuativeCommSq tV.G.hom :=
    { R := V, K := K, i₁ := xV, i₂ := 𝟙 _, commSq := ⟨by simp [xV, spMap]⟩ }
  obtain ⟨l⟩ := (hE S).exists_lift
  refine ⟨l.l ≫ m.cm.F, ?_⟩
  rw [← Category.assoc]
  have := l.fac_left
  change spMap (algebraMap V K) ≫ l.l = xV at this
  rw [this]
  exact m.cart.1.lift_fst _ _ _

end GlobalTheory.ProperOfAbelianFibres
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTangentPresentationPrime
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm MonObj

namespace GlobalTheory.HTMap

attribute [local instance] Over.cartesianMonoidalCategory

section Pull

variable {X : Scheme.{0}} {G : Over X} [GrpObj G] {T T' : Scheme.{0}} {y : T ⟶ X} {y' : T' ⟶ X}

theorem spc {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by rw [← Spec.map_comp]; rfl

theorem spc_assoc {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) {Z : Scheme.{0}}
    (h : Sp A ⟶ Z) : spMap g ≫ spMap f ≫ h = spMap (g.comp f) ≫ h := by rw [← Category.assoc, spc]

def pull (g : T' ⟶ T) (h : g ≫ y = y') : (Over.mk y ⟶ G) →* (Over.mk y' ⟶ G) := Formalism.L2.Pj.preHom (Over.homMk g h)

omit [GrpObj G] in
theorem over_w (w : Over.mk y ⟶ G) : w.left ≫ G.hom = y := Over.w w


omit [GrpObj G] in
def mkPt (w : T ⟶ G.left) (h : w ≫ G.hom = y) : Over.mk y ⟶ G := Over.homMk w h

omit [GrpObj G] in
theorem mkPt_left (w : T ⟶ G.left) (h : w ≫ G.hom = y) : (mkPt w h).left = w := rfl

theorem eq_pull {g : T' ⟶ T} (w : Over.mk y ⟶ G) (w' : Over.mk y' ⟶ G) (e : w'.left = g ≫ w.left) :
    ∃ h : g ≫ y = y', w' = pull g h w :=
  ⟨by rw [← over_w w, ← over_w w', e, Category.assoc], Over.OverMorphism.ext e⟩

theorem tors_of {g : T' ⟶ T} {w : Over.mk y ⟶ G} {w' : Over.mk y' ⟶ G} (e : w'.left = g ≫ w.left) {q : ℕ}
    (hw : w ^ q = 1) : w' ^ q = 1 := by
  obtain ⟨h, rfl⟩ := eq_pull w w' e
  rw [← map_pow, hw, map_one]

theorem one_of {g : T' ⟶ T} (h : g ≫ y = y') : (1 : Over.mk y' ⟶ G).left = g ≫ (1 : Over.mk y ⟶ G).left := by
  rw [← map_one (pull (G := G) g h)]; rfl

end Pull

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X} {A : Type} [CommRing A] {x₀ : Sp A ⟶ X} {q : ℕ}


variable (t x₀ q) in
structure FP : Type 1 where
  f : A
  B : Type
  [ring : CommRing B]
  [alg : Algebra (Localization.Away f) B]
  u : Over.mk (spMap (algebraMap (Localization.Away f) B) ≫ spMap (algebraMap A (Localization.Away f)) ≫ x₀) ⟶ t.G
  ne : f ≠ 0
  fin : IsFinPart t (spMap (algebraMap A (Localization.Away f)) ≫ x₀) q u

attribute [instance] FP.ring FP.alg

namespace FP

variable (P : FP t x₀ q) {S S' : Type} [CommRing S] [CommRing S']

def str : A →+* P.B := (algebraMap (Localization.Away P.f) P.B).comp (algebraMap A (Localization.Away P.f))

def At (φ : A →+* S) (w : Sp S ⟶ t.G.left) (β : P.B →+* S) : Prop := β.comp P.str = φ ∧ spMap β ≫ P.u.left = w

variable {P}

theorem alg_ext {β β' : P.B →+* S} (h : β.comp P.str = β'.comp P.str) :
    β.comp (algebraMap (Localization.Away P.f) P.B) = β'.comp (algebraMap (Localization.Away P.f) P.B) :=
  IsLocalization.ringHom_ext (Submonoid.powers P.f) h

theorem At.map {φ : A →+* S} {w : Sp S ⟶ t.G.left} {β : P.B →+* S} (h : P.At φ w β) (ψ : S →+* S') :
    P.At (ψ.comp φ) (spMap ψ ≫ w) (ψ.comp β) :=
  ⟨by rw [← h.1]; rfl, by rw [← h.2]; exact (spc_assoc _ _ _).symm⟩

theorem At.over {φ : A →+* S} {w : Sp S ⟶ t.G.left} {β : P.B →+* S} (h : P.At φ w β) :
    w ≫ t.G.hom = spMap φ ≫ x₀ := by
  rw [← h.2, ← h.1, Category.assoc, over_w P.u, spc_assoc, spc_assoc]; rfl

theorem At.tors {φ : A →+* S} {y : Sp S ⟶ X} {w : Over.mk y ⟶ t.G} {β : P.B →+* S} (h : P.At φ w.left β) :
    w ^ q = 1 := tors_of h.2.symm P.fin.tors

theorem At.unit {φ : A →+* S} {w : Sp S ⟶ t.G.left} {β : P.B →+* S} (h : P.At φ w β) : IsUnit (φ P.f) := by
  rw [← h.1]
  exact ((IsLocalization.Away.algebraMap_isUnit (S := Localization.Away P.f) P.f).map
    (algebraMap (Localization.Away P.f) P.B)).map β

theorem at_iff (φ : Localization.Away P.f →+* S) (w : Sp S ⟶ t.G.left) :
    (∃ β, P.At (φ.comp (algebraMap A _)) w β) ↔ Thru t P.u.left φ w :=
  exists_congr fun _ => and_congr_left fun _ =>
    ⟨fun h => IsLocalization.ringHom_ext (Submonoid.powers P.f) h, fun h => by rw [← h]; rfl⟩

theorem ex_lift {φ : A →+* S} (hu : IsUnit (φ P.f)) :
    ∃ φ' : Localization.Away P.f →+* S, φ'.comp (algebraMap A _) = φ :=
  ⟨IsLocalization.Away.lift P.f hu, IsLocalization.Away.lift_comp _ _⟩

theorem at_open {φ : A →+* S} (hu : IsUnit (φ P.f)) {y : Sp S ⟶ X} (hy : y = spMap φ ≫ x₀) (w : Over.mk y ⟶ t.G)
    (hw : w ^ q = 1) (h : ∀ 𝔪 : Ideal S, 𝔪.IsMaximal →
      ∃ β, P.At ((Ideal.Quotient.mk 𝔪).comp φ) (spMap (Ideal.Quotient.mk 𝔪) ≫ w.left) β) :
    ∃ β, P.At φ w.left β := by
  obtain ⟨φ', rfl⟩ := ex_lift hu
  rw [← spc_assoc] at hy
  subst hy
  exact (at_iff _ _).2 (P.fin.isOpen S φ' w hw fun 𝔪 h𝔪 => (at_iff _ _).1 (h 𝔪 h𝔪))

theorem at_one {φ : A →+* S} (hu : IsUnit (φ P.f)) {y : Sp S ⟶ X} (hy : y = spMap φ ≫ x₀) :
    ∃ β, P.At φ (1 : Over.mk y ⟶ t.G).left β := by
  obtain ⟨φ', rfl⟩ := ex_lift hu
  rw [← spc_assoc] at hy
  subst hy
  exact (at_iff _ _).2 (P.fin.one S φ')

theorem At.mul {φ : A →+* S} {y : Sp S ⟶ X} {w w' : Over.mk y ⟶ t.G} {β β' : P.B →+* S} (h : P.At φ w.left β)
    (h' : P.At φ w'.left β') : ∃ β'', P.At φ (w * w').left β'' := by
  have hy : y = spMap φ ≫ x₀ := (over_w w).symm.trans h.over
  obtain ⟨φ', rfl⟩ := ex_lift h.unit
  rw [← spc_assoc] at hy
  subst hy
  exact (at_iff _ _).2 (P.fin.mul S φ' w w' ((at_iff _ _).1 ⟨_, h⟩) ((at_iff _ _).1 ⟨_, h'⟩))


end FP



section Dom

variable [IsDomain A]

namespace FP

variable (P : FP t x₀ q)

variable {P}



end FP

variable [IsIntegrallyClosed A] {κ : (Sp (FractionRing A) ⟶ t.G.left) → Aˣ}

end Dom

section Tan

variable {S : Type} [CommRing S] {x : Sp S ⟶ X}

theorem tan_tors {v : Sp (DualNumber S) ⟶ t.G.left} (hv : IsTanAtG t x v) (hq : (q : S) = 0)
    {y : Sp (DualNumber S) ⟶ X} (w : Over.mk y ⟶ t.G) (e : w.left = v) : w ^ q = 1 := by
  have key : ∀ n : ℕ, smT x (n : S) (ovT hv) = ovT hv ^ n := fun n => by
    induction n with
    | zero => rw [Nat.cast_zero, pow_zero, smT_zero_ovT]
    | succ n ih => rw [Nat.cast_succ, smT_add x _ (smT_zero_ovT hv), ih, smT_unit, pow_succ]
  have h : ovT hv ^ q = 1 := by rw [← key, hq, smT_zero_ovT]
  exact tors_of (w := ovT hv) (g := 𝟙 _) (e.trans (Category.id_comp _).symm) h

theorem comb_single {g : ℕ} {e : Fin g → (Sp (DualNumber S) ⟶ t.G.left)} (he : ∀ i, IsTanAtG t x (e i)) (i : Fin g) :
    IsCombAtG t x e (Pi.single i 1) (e i) :=
  (isCombAtG_iff t x (fun j => ovT (he j)) _ _).2 (by rw [combT_single _ _ fun j => smT_zero_ovT _]; rfl)

theorem tan_at (P : FP t x₀ q) {φ : A →+* S} {v : Sp (DualNumber S) ⟶ t.G.left} (hv : IsTanAtG t (spMap φ ≫ x₀) v)
    (hq : (q : S) = 0) {S' : Type} [CommRing S'] (ψ : DualNumber S →+* S')
    (hu : IsUnit (ψ (((algebraMap S (DualNumber S)).comp φ) P.f))) :
    ∃ β, P.At (ψ.comp ((algebraMap S (DualNumber S)).comp φ)) (spMap ψ ≫ v) β := by
  refine FP.at_open (φ := ψ.comp ((algebraMap S (DualNumber S)).comp φ)) hu ?_ (mkPt (spMap ψ ≫ v) rfl)
    (tors_of (g := spMap ψ) (w := ovT hv) rfl (tan_tors hv hq _ rfl)) fun 𝔪 h𝔪 => ?_
  · rw [Category.assoc, hv.1, spc_assoc, spc_assoc]
  let ρ := (Ideal.Quotient.mk 𝔪).comp ψ
  have hρ : ρ = (ρ.comp (algebraMap S (DualNumber S))).comp (TrivSqZeroExt.fstHom S S S).toRingHom := by
    refine RingHom.ext fun z => ?_
    have h0 : ρ (TrivSqZeroExt.inr z.snd) = 0 :=
      mul_self_eq_zero.1 (by rw [← map_mul, TrivSqZeroExt.inr_mul_inr, map_zero])
    conv_lhs => rw [← TrivSqZeroExt.inl_fst_add_inr_snd_eq z, map_add (f := _), h0, add_zero]
    rfl
  have e : spMap (Ideal.Quotient.mk 𝔪) ≫ spMap ψ ≫ v =
      (1 : Over.mk (spMap (ρ.comp (algebraMap S (DualNumber S))) ≫ spMap φ ≫ x₀) ⟶ t.G).left := by
    rw [one_of rfl, ← hv.2]
    exact (spc_assoc _ _ _).trans ((congrArg (fun z => spMap z ≫ v) hρ).trans (spc_assoc _ _ _).symm)
  rw [mkPt_left, e]
  exact FP.at_one (hu.map (Ideal.Quotient.mk 𝔪)) (spc_assoc _ _ _)

end Tan

section Char

variable {O : Type} [CommRing O] [IsLocalRing O] {x : A →+* O} {P : FP t x₀ q}

end Char


theorem cast_quot (R : Type) [CommRing R] (p n : ℕ) : ((p ^ n : ℕ) : R ⧸ Ideal.span {(p : R) ^ n}) = 0 := by
  rw [← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem, Nat.cast_pow]
  exact Ideal.mem_span_singleton_self _

end GlobalTheory.HTMap
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SimpLabMinValOne
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.PolFan

section Sub

variable {O : Type} [CommRing O] (bar : O → O) (q : ℕ)

def LinOnCells (φ χ : InvFun O) : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q →
    ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar φ γ → χ.LinearOn γ

def Subordinate (φ' φ : InvFun O) : Prop :=
  ∀ χ : InvFun O, LinOnCells bar q φ χ → LinOnCells bar q φ' χ

def SimpLab (φ lab : InvFun O) : Prop :=
  (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q →
    ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → ∀ k : ℕ, 0 < k → lab.evalZ ((k : ℤ) • β) = lab.evalZ β) ∧
  ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q →
    ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar φ γ →
      ∃ (m' : ℕ) (δ : Fin m' → LinearMap.BilinForm ℤ X), IsCell bar φ δ ∧ LinearIndependent ℤ δ ∧
        Function.Injective (fun i => lab.evalZ (δ i)) ∧
        ∀ j, ∃ a : Fin m' → ℝ, (∀ i, 0 ≤ a i) ∧ toReal (γ j) = ∑ i, a i • toReal (δ i)

variable {bar q}

theorem linOnCells_self (φ : InvFun O) : LinOnCells bar q φ φ := fun _ _ _ _ _ _ _ _ h => h.linear

theorem Subordinate.refl (φ : InvFun O) : Subordinate bar q φ φ := fun _ h => h

theorem Subordinate.trans {φ'' φ' φ : InvFun O} (h₁ : Subordinate bar q φ'' φ') (h₂ : Subordinate bar q φ' φ) :
    Subordinate bar q φ'' φ := fun χ h => h₁ χ (h₂ χ h)

theorem Subordinate.linearOn {φ' φ : InvFun O} (h : Subordinate bar q φ' φ) {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] [Module.Projective O X] (hX : Module.finrank O X ≤ q) {m : ℕ}
    {γ : Fin m → LinearMap.BilinForm ℤ X} (hγ : IsCell bar φ' γ) : φ.LinearOn γ :=
  h φ (linOnCells_self φ) X hX m γ hγ

end Sub

section Inhab

def zeroFun (O : Type) [CommRing O] : InvFun O where
  toFun _ _ := 0
  inv _ _ _ _ _ := rfl
  zero _ := rfl

@[simp] theorem zeroFun_evalZ {O : Type} [CommRing O] {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X]
    (β : LinearMap.BilinForm ℤ X) : (zeroFun O).evalZ β = 0 := by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' O X
  simp only [InvFun.evalZ, (zeroFun O).eval_eq hr]
  rfl

end Inhab

end GlobalTheory.PolFan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PluckerNonzeroIffIndependent
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)

noncomputable section

namespace GlobalTheory.FlagEmb.PlkSpan

theorem indep_of_plk_ne_zero (K : Type) [Field K] (N k : ℕ) (u : Fin k → Fin (N + 1) → K)
    (h : plk u id ≠ 0) : LinearIndependent K u := by
  obtain ⟨q, hq⟩ := Function.ne_iff.1 h
  set r := GlobalTheory.FlagEmb.plE N k q
  have hdet : (Matrix.of fun l l' => u l (r l')).det ≠ 0 := hq
  have hA := Matrix.linearIndependent_rows_of_det_ne_zero hdet
  refine LinearIndependent.of_comp (LinearMap.funLeft K K r) ?_
  exact hA

theorem plk_ne_zero_of_indep (K : Type) [Field K] (N k : ℕ) (u : Fin k → Fin (N + 1) → K)
    (h : LinearIndependent K u) : plk u id ≠ 0 := by
  let Q : Matrix (Fin (N + 1)) (Fin k) K := (Matrix.of u).transpose
  have hinj : Function.Injective Q.mulVec := by
    intro x y hxy
    have h0 : Q.mulVec (x - y) = 0 := by rw [Matrix.mulVec_sub, hxy, sub_self]
    have h1 : ∑ l, (x - y) l • u l = 0 := by
      funext r
      have := congrFun h0 r
      simp only [Q, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.of_apply, Pi.zero_apply] at this
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      rw [← this]
      exact Finset.sum_congr rfl fun l _ => mul_comm _ _
    have h2 := (Fintype.linearIndependent_iff.1 h) _ h1
    funext l
    exact sub_eq_zero.1 (h2 l)
  obtain ⟨Q', hQ'⟩ := GlobalTheory.matrix_exists_left_inverse_of_field Q hinj
  have hCB := GlobalTheory.FlagEmb.CauchyBinet.lform_plk K N k (Fin k) (Fin k) (fun l => Q' l) u id id
  have hM : (Matrix.of fun l l' => ∑ r, (fun l => Q' l) (id l') r * u (id l) r) = (Q' * Q).transpose := by
    ext l l'
    simp [Q, Matrix.mul_apply, mul_comm]
  rw [hM, hQ', Matrix.transpose_one, Matrix.det_one] at hCB
  intro h0
  rw [h0] at hCB
  simp at hCB

theorem plk_comb (K : Type) [Field K] (N k : ℕ) (u : Fin k → Fin (N + 1) → K) (T : Matrix (Fin k) (Fin k) K) :
    plk (fun l => ∑ j, T l j • u j) id = T.det • plk u id := by
  funext q
  simp only [plk, id, Pi.smul_apply, smul_eq_mul]
  rw [← Matrix.det_mul]
  congr 1
  ext l l'
  simp [Matrix.mul_apply, Finset.sum_apply]

theorem main : ∀ (K : Type) [Field K] (N k : ℕ) (u u' : Fin k → Fin (N + 1) → K), (plk u id ≠ 0 ↔ LinearIndependent K u) ∧ (LinearIndependent K u → ((LinearIndependent K u' ∧ Submodule.span K (Set.range u') = Submodule.span K (Set.range u)) ↔ ∃ r : Kˣ, plk u' id = (r : K) • plk u id)) := by
  intro K _ N k u u'
  refine ⟨⟨indep_of_plk_ne_zero K N k u, plk_ne_zero_of_indep K N k u⟩, fun hu => ⟨?_, ?_⟩⟩
  · rintro ⟨hu', hs⟩
    choose c hc using fun l => (Submodule.mem_span_range_iff_exists_fun K).1
      (hs ▸ Submodule.subset_span ⟨l, rfl⟩ : u' l ∈ Submodule.span K (Set.range u))
    have h1 := plk_comb K N k u (Matrix.of c)
    have h2 : (fun l => ∑ j, (Matrix.of c) l j • u j) = u' := funext hc
    rw [h2] at h1
    have hd : (Matrix.of c).det ≠ 0 := by
      intro h0
      exact plk_ne_zero_of_indep K N k u' hu' (by rw [h1, h0, zero_smul])
    exact ⟨Units.mk0 _ hd, h1⟩
  · rintro ⟨r, hr⟩
    have h0 := plk_ne_zero_of_indep K N k u hu
    have h0' : plk u' id ≠ 0 := by
      rw [hr]
      exact smul_ne_zero r.ne_zero h0
    have hr' : plk u id = (r : K)⁻¹ • plk u' id := by
      rw [hr, smul_smul, inv_mul_cancel₀ r.ne_zero, one_smul]
    refine ⟨indep_of_plk_ne_zero K N k u' h0', le_antisymm ?_ ?_⟩
    · rw [Submodule.span_le]
      rintro _ ⟨l, rfl⟩
      exact mem_span_of_plk_eq_smul K N k u u' _ h0' hr l
    · rw [Submodule.span_le]
      rintro _ ⟨l, rfl⟩
      exact mem_span_of_plk_eq_smul K N k u' u _ h0 hr' l

end GlobalTheory.FlagEmb.PlkSpan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EtaleCompletionOfDimOneNormal
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier

namespace GlobalTheory.CdvrExt

theorem isDVR_of_ringKrullDim_eq_one {A : Type} [CommRing A] [IsLocalRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] (hA : ringKrullDim A = 1) : IsDiscreteValuationRing A := by
  obtain ⟨hf, hrad⟩ := ringKrullDim_eq_one_iff_of_isLocalRing_isDomain.1 hA
  have key := (IsDiscreteValuationRing.TFAE A hf).out 1 4
  try simp only [List.length_cons, List.getElem_cons_succ, List.getElem_cons_zero] at key
  refine key.2 ⟨inferInstance, maximalIdeal A, ⟨?_, ?_⟩, ?_⟩
  · exact (isField_iff_maximalIdeal_eq).not.1 hf
  · exact (maximalIdeal.isMaximal A).isPrime
  · rintro P ⟨hP, hPp⟩
    obtain ⟨x, hxP, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP
    refine le_antisymm (le_maximalIdeal hPp.ne_top) ?_
    refine (hrad x hx0).trans ?_
    rw [hPp.radical_le_iff, Ideal.span_singleton_le_iff_mem]
    exact hxP

end GlobalTheory.CdvrExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSemiAbelianPolarized
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.GenFan.Tri

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l}

theorem isOpenImmersion_j_id (Y : Model Xo c (RingHom.id c.F)) : IsOpenImmersion Y.j := by
  unfold Model.j
  have : IsIso (pullback.fst Y.s (spMap (RingHom.id c.F))) := by
    have : IsIso (spMap (RingHom.id c.F)) := by
      show IsIso (Spec.map (CommRingCat.ofHom (RingHom.id c.F)))
      rw [show CommRingCat.ofHom (RingHom.id c.F) = 𝟙 (CommRingCat.of c.F) from rfl, Spec.map_id]
      infer_instance
    infer_instance
  have := Y.jQ_open
  infer_instance

theorem range_j_subset_abLocus {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) :
    Set.range Y.j ⊆ abLocus Y.t.G := by
  rintro _ ⟨w, rfl⟩
  have h : Y.jQ w ∈ pullback.fst Y.s (spMap β) ⁻¹' abLocus Y.t.G := by rw [Y.ab_gen]; exact ⟨w, rfl⟩
  exact h

end GlobalTheory.GenFan.Tri
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LineBundleIsoOfGenericIsoNormalLocalBase
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LineBundleIsoOfGenericIsoNormalLocalBase
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj

theorem GlobalTheory.lbIso_of_generic_normal_local : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsNoetherianRing R → IsIntegrallyClosed R → ∀ (H : Scheme.{0}) (p : H ⟶ Sp R) (e : Sp R ⟶ H), Smooth p → QuasiCompact p → GeometricallyIntegral p → e ≫ p = 𝟙 _ → ∀ L M : LB H, L.IsLB → M.IsLB → LBIso (L.pull (pullback.fst p (jK R))) (M.pull (pullback.fst p (jK R))) → LBIso L M := by
  intro R _ _ _ hN hI H p e hs _ hg he L M hL hM h
  haveI : IsNoetherianRing R := hN
  haveI : IsIntegrallyClosed R := hI
  have hD := LB.isLB_div hM hL
  have h₁ : IsPreimmersion (jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have h₂ : Flat (jK R) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat _ (nonZeroDivisors R))
  obtain ⟨t, ht⟩ := GenericExtend.exists_isGen_of_densePart (Sp R) _ (jK R) (ZJ.isNormalScheme_sp R) h₁ h₂
    DVR.isDominant_jK inferInstance (Over.mk p) e (LB.div M L) he hs hg hD
    (DVR.exists_gen_of_isLB_local _ (LB.isLB_pull hD _)) ((IsoExtend.lbIso_pull_iff_gen L M _).1 h)
  exact ⟨t, ht⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LineBundleIsoOfGenericIsoNormalLocalBaseStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleIso_of_generic_iso_normal_local_base : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsNoetherianRing R → IsIntegrallyClosed R → ∀ (H : Scheme.{0}) (p : H ⟶ Sp R) (e : Sp R ⟶ H), Smooth p → QuasiCompact p → GeometricallyIntegral p → e ≫ p = 𝟙 _ → ∀ L M : LB H, L.IsLB → M.IsLB → LBIso (L.pull (pullback.fst p (jK R))) (M.pull (pullback.fst p (jK R))) → LBIso L M := by
  first | exact @GlobalTheory.lbIso_of_generic_normal_local | exact GlobalTheory.lbIso_of_generic_normal_local | (intros; apply GlobalTheory.lbIso_of_generic_normal_local <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentialKernelsIsHolomorphicLatticeFamilyStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exponentialKernels_isHolomorphicLatticeFamily : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (m g : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)) (ex : ∀ b, (Fin g → ℂ) → (Over.mk (y b) ⟶ t.G)), IsOpen B → IsHolTo (B ×ˢ Set.univ) (fun q : (Fin m → ℂ) × (Fin g → ℂ) => (ex q.1 q.2).left) → (∀ b ∈ B, IsExpAt t (y b) (ex b)) → IsLatFam B (fun b => {w | ex b w = 1}) := by
  first | exact @GlobalTheory.ShFam.Hor.LogCh.isLatFam_ker | exact GlobalTheory.ShFam.Hor.LogCh.isLatFam_ker | (intros; apply GlobalTheory.ShFam.Hor.LogCh.isLatFam_ker <;> assumption)
end
