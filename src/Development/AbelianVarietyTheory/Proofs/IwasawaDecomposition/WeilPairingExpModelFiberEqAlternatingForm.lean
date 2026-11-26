module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemModelMap
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocalization
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsTanBasisOfUniqueCombination
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsArcDataOfBadReductionFiniteExtension
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProperOfCompleteDVRLiftGenericPoint

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilPairingExpModelFiberEqAlternatingForm
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilPairingExpModelFiberEqAlternatingForm
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ShFam.Hor.LogCh

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Hor.LogCh

theorem pow_eq_one_of_toBase {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {F : G'.left ⟶ G.left} (h : IsGrpPullback G' G f F) {T : Over S'} (x : T ⟶ G') (N : ℕ)
    (hx : Out.toBase h.1.w x ^ N = 1) : x ^ N = 1 := by
  let β := GlobalTheory.UU.toBaseHom (hw := h.1.w) (GlobalTheory.TowerAlg.toBase_mul h) T
  have hinj : Function.Injective β := fun a b e => Over.OverMorphism.ext
    (h.1.hom_ext (congrArg (fun q => q.left) e) ((Over.w a).trans (Over.w b).symm))
  exact hinj ((map_pow β x N).trans (hx.trans (map_one β).symm))

theorem pushEx_cubWeil (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (g : ℕ)
    (ty : Fin g → (E →+* ℂ)) (σ₀ : KA l →+* ℂ) (Fu : FamilyUnif Xo σ₀ ty) (y : Sp ℂ ⟶ Xo.XF c) (i : Fin Fu.n)
    (P : (Fu.Di i).La →+ (Fin g → ℂ)) (p : Sp ℂ ⟶ Z.X)
    (hu : Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
    (hp : y ≫ Z.jQ ≫ pullback.fst Z.s (spMap β) = p) (hP : IsPeriod (Fu.Di i) ty P) (k : ℕ) (a b : (Fu.Di i).La) (ζ : ℂˣ)
    (hk : 0 < k) (hζ : (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((Fu.Di i).EF a b : ℂ) / k)) :
    GlobalTheory.UU.CubWeil Z.t.cub k (pushEx Z Fu y i P p hu hp ((k : ℂ)⁻¹ • P a)) (pushEx Z Fu y i P p hu hp ((k : ℂ)⁻¹ • P b))
      (unitOn ζ) := by
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'

  have tors : ∀ d : (Fu.Di i).La, Fu.ex i P ((k : ℂ)⁻¹ • P d) ^ k = 1 := fun d => by
    have hpow : ∀ (n : ℕ) (z : Fin g → ℂ), Fu.ex i P z ^ n = Fu.ex i P (n • z) := fun n z => by
      induction n with
      | zero => simpa using ((Fu.ex_ker i P hP 0).2 (zero_mem _)).symm
      | succ n ih => rw [pow_succ, ih, ← Fu.ex_add i P hP, succ_nsmul]
    rw [hpow, Fu.ex_ker i P hP]
    exact ⟨d, by
      ext j
      simp [hk']⟩
  have h₀ : GlobalTheory.UU.CubWeil Xo.univ.t.cub k (Fu.ex i P ((k : ℂ)⁻¹ • P a)) (Fu.ex i P ((k : ℂ)⁻¹ • P b)) (unitOn ζ) :=
    (GlobalTheory.UU.cubWeil_iff_weilIs GlobalTheory.SemiRigid.globalFns (GlobalTheory.ObjDim.isAbelianScheme Xo.univ) (tors a) (tors b) _).2
      (by exact_mod_cast Fu.ex_weil i P hP k a b ζ hk hζ)
  let f₀ := pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)
  let m₀ := Z.m0.toSABMap

  let σ : Over.mk (y ≫ f₀) ⟶ Over.mk (Fu.u i P) := Over.homMk (𝟙 _) ((Category.id_comp _).trans hu)
  have h₁ := h₀.comp σ
  have e₁ : Units.map σ.left.appTop.hom.toMonoidHom (unitOn ζ) = unitOn ζ := by
    ext
    simp [σ]
  rw [e₁] at h₁

  let lf : (Fin g → ℂ) → (Over.mk y ⟶ Z.oF.t.G) := fun z =>
    Over.homMk (liftEx Z Fu y i P hu z) (liftEx_snd Z Fu y i P hu z)
  have eb : ∀ z, Out.toBase m₀.cart.1.w (lf z) = σ ≫ Fu.ex i P z := fun z =>
    Over.OverMorphism.ext ((liftEx_fst Z Fu y i P hu z).trans (by simp [σ]))
  have tl : ∀ d : (Fu.Di i).La, lf ((k : ℂ)⁻¹ • P d) ^ k = 1 := fun d =>
    pow_eq_one_of_toBase m₀.cart _ k (by
      rw [eb, ← MonObj.comp_pow, tors, MonObj.comp_one])
  obtain ⟨ζ', hζ', -⟩ := GlobalTheory.UU.existsUnique_cubWeil Z.oF.t.cub (tl a) (tl b)
  have h₂ := GlobalTheory.UU.cubWeil_of_isPullCubical _ _ f₀ _ _ m₀.cm m₀.cart.1.w (GlobalTheory.TowerAlg.toBase_mul m₀.cart) _ _ _ _ m₀.lin
    k _ _ _ ζ' hζ'
  rw [eb, eb] at h₂
  obtain rfl : ζ' = unitOn ζ := h₂.unique h₁
  have h₃ := GlobalTheory.UU.cubWeil_of_isPullCubical _ _ _ _ _ Z.m.cm Z.m.cart.1.w (GlobalTheory.TowerAlg.toBase_mul Z.m.cart) _ _ _ _ Z.m.lin
    k _ _ _ _ hζ'

  let τ : Over.mk p ⟶ Over.mk ((Over.mk y).hom ≫ Z.jQ ≫ pullback.fst Z.s (spMap β)) :=
    Over.homMk (𝟙 _) ((Category.id_comp _).trans hp)
  have h₄ := h₃.comp τ
  have e₂ : Units.map τ.left.appTop.hom.toMonoidHom (unitOn ζ) = unitOn ζ := by
    ext
    simp [τ]
  rw [e₂] at h₄
  have e₃ : ∀ z, τ ≫ Out.toBase Z.m.cart.1.w (lf z) = pushEx Z Fu y i P p hu hp z := fun z =>
    Over.OverMorphism.ext (Category.id_comp _)
  rwa [e₃, e₃] at h₄

end GlobalTheory.ShFam.Hor.LogCh
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilPairingExpModelFiberEqAlternatingFormStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ShFam.Hor.LogCh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilPairing_expModelFiber_eq_alternatingForm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (σ₀ : KA l →+* ℂ) (Fu : FamilyUnif Xo σ₀ ty) (y : Sp ℂ ⟶ Xo.XF c) (i : Fin Fu.n) (P : (Fu.Di i).La →+ (Fin g → ℂ)) (p : Sp ℂ ⟶ Z.X) (hu : Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) (hp : y ≫ Z.jQ ≫ pullback.fst Z.s (spMap β) = p), IsPeriod (Fu.Di i) ty P → ∀ (k : ℕ) (a b : (Fu.Di i).La) (ζ : ℂˣ), 0 < k → (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((Fu.Di i).EF a b : ℂ) / k) → GlobalTheory.UU.CubWeil Z.t.cub k (pushEx Z Fu y i P p hu hp ((k : ℂ)⁻¹ • P a)) (pushEx Z Fu y i P p hu hp ((k : ℂ)⁻¹ • P b)) (unitOn ζ) := by
  first | exact @GlobalTheory.ShFam.Hor.LogCh.pushEx_cubWeil | exact GlobalTheory.ShFam.Hor.LogCh.pushEx_cubWeil | (intros; apply GlobalTheory.ShFam.Hor.LogCh.pushEx_cubWeil <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProperRelAmpleOfSystem
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KeyAtFam

open GlobalTheory.CechPic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem relAmple_iff_of_cls {S : Scheme.{0}} {A : Over S} [IsProper A.hom] {L M : LB A.left} (hL : L.IsLB)
    (hM : M.IsLB) {d : ℕ} (hd : 1 ≤ d) (e : cls M hM = d • cls L hL) : Out.RelAmple A M ↔ Out.RelAmple A L := by
  rw [relAmple_iff_isAmpleLB A hL, relAmple_iff_isAmpleLB A hM]
  refine forall_congr' fun U => forall_congr' fun hU => ?_
  refine Iff.trans (isAmpleLB_congr (pull_isLB hM _) (isLB_lbPow (pull_isLB hL _) d)
    ((cls_eq_iff (pull_isLB hM _) (isLB_lbPow (pull_isLB hL _) d)).1 ?_)) (isAmpleLB_pow_iff (pull_isLB hL _) hd)
  rw [cls_lbPow (pull_isLB hL _), cls_pull hL, cls_pull hM, e, map_nsmul]

section OneModel

variable {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Y : Model Xo c β}

theorem exists_keyAt (M : GChart Y) {R : Type} [CommRing R] {z : Sp R ⟶ Y.X} (hz : ⊤ ≤ z ⁻¹ᵁ M.U)
    {t : SAB H (Sp R)} (m : SABMap t Y.t z) (hp : IsProper t.G.hom) (hA : Out.RelAmple t.G t.PP.L)
    (hK : Out.KTriv t.G t.PP.L) (hd : SmoothOfRelativeDimension M.n t.G.hom) (hn : 1 ≤ M.n) :
    ∃ x : KeyIn R, x.P.g = M.n ∧ KeyAt M z hz x := by
  obtain ⟨w, θ, ⟨hw, hr⟩, hθ, hne⟩ :=
    exists_sec_pull_nonzero_on_fibres E H _ _ Y.t t z m M.U hz M.θ M.θ_mem M.θ_ne
  have cast : ∀ (p q : Sp R ⟶ Y.X) (_ : p = q) (n : SABMap t Y.t p), ∃ n' : SABMap t Y.t q, n'.φ = n.φ := by
    rintro p q rfl n
    exact ⟨n, rfl⟩
  obtain ⟨m', hm'⟩ := cast _ _ (FlagMod.spMap_ev z M.hU hz).symm m
  obtain ⟨v, hv, hb, -⟩ := M.lie R (ev z M.U hz) t m'
  obtain ⟨-, ws, gs', -⟩ := t.sym
  let P : Out.PolAV (Sp R) :=
    { A := t.G, g := M.n, smoothDim := hd, L := t.PP.L, isLB := t.PP.isLB, ample := hA, ktriv := hK
      isAb := ⟨inferInstance, t.semi.smooth, hp, t.semi.geomConnected⟩
      rigid := ⟨t.PP.rig, t.PP.rigGen⟩
      sym := fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff ws).1 gs') _⟩ }
  have he : eSec t.G ≫ m.φ = z ≫ eSec Y.t.G := m.cm.e_comm.trans (congrArg (· ≫ _) m.base)
  have hrig : ∀ (e : Sp R ⟶ Y.X) (_ : m.cm.e = e) (he : eSec t.G ≫ m.φ = e ≫ eSec Y.t.G),
      rigPullOf m.φ e he Y.t.PP.L Y.t.PP.rig = m.cm.rigPull Y.t.PP.L Y.t.PP.rig := by
    rintro _ rfl _
    rfl
  refine ⟨⟨P, hn, t.PP.rig, t.PP.rigGen, θ, fun s => ?_, v, hb⟩, rfl, m.φ, he, w, rfl, m.cart, hw, ?_,
    fun j i h => ?_, fun i => ?_⟩
  · obtain ⟨g, i, hg, hi⟩ := hne s
    exact ⟨g, hg, Opens.mem_iSup.2 ⟨i, hi⟩⟩
  · rw [hrig z m.base he]
    exact hr
  · exact (hθ (j PUnit.unit) i _ h le_rfl).trans (congrArg (· * _) (GlobalTheory.LB.resG_self _ _))
  · rw [← hm']
    exact hv i

theorem exists_keyAt_of_point (M : GChart Y) {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    {z : Sp R ⟶ Y.X} (hz : ⊤ ≤ z ⁻¹ᵁ M.U) {t : SAB H (Sp R)} (m : SABMap t Y.t z) (hp : IsProper t.G.hom)
    (hA : Out.RelAmple t.G t.PP.L) {K : Type} [Field K] [CharZero K] (f : R →+* K) {x₀ : KeyIn K}
    (h₀ : KeyAt M (spMap f ≫ z) (le_preimage_comp _ hz) x₀) :
    ∃ x : KeyIn R, x.P.g = x₀.P.g ∧ KeyAt M z hz x := by
  obtain ⟨φ, -, w, hg, hc, hw, -⟩ := h₀
  obtain ⟨ψ, h₁, h₂⟩ : ∃ ψ : x₀.P.A.left ⟶ t.G.left, ψ ≫ m.φ = φ ∧ ψ ≫ t.G.hom = x₀.P.A.hom ≫ spMap f :=
    ⟨m.cart.1.lift φ (x₀.P.A.hom ≫ spMap f) (by rw [hc.1.w, Category.assoc]), m.cart.1.lift_fst _ _ _,
      m.cart.1.lift_snd _ _ _⟩
  subst h₁
  have g : IsGrpPullback x₀.P.A t.G (spMap f) ψ := m.cart.cancel hc h₂
  have e : LBIso x₀.P.L (t.PP.L.pull ψ) :=
    LBIso.trans x₀.P.isLB (pull_isLB Y.t.PP.isLB _) (pull_isLB t.PP.isLB _) ⟨w, hw⟩
      (GlobalTheory.LN.GenericPoint.lbIso_pull (GlobalTheory.LN.GenericPoint.lbIso_of_sabMap m) _ rfl).symm
  have hG : IsAbelianScheme t.G := ⟨inferInstance, t.semi.smooth, hp, t.semi.geomConnected⟩
  have q : Sp K := (default : PrimeSpectrum K)
  obtain ⟨U, hU, hK⟩ := KTrivGlob.exists_open t.PP.isLB x₀.P.isLB hG hA g e x₀.P.ktriv q
  have : CharZero R := f.charZero
  have : CharZero Γ(Sp R, ⊤) := charZero_of_injective_ringHom
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).1
  have kt := KTrivSpread.kTriv_of_open_integral GlobalTheory.firstFiveLaws.1 (Sp R) (fun n hn => Nat.cast_ne_zero.2 hn) U
    ⟨_, hU⟩ t.G t.PP t.cub hG hA hK
  have := t.semi.smooth
  have := t.semi.geomConnected
  have : ConnectedSpace t.G.left := GeometricallyConnected.connectedSpace t.G.hom t.G.hom.isOpenMap
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected t.G.hom (eSec t.G (spMap f q))
  obtain rfl : d = M.n := (H1.dim_unique _ ((smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback g.1 hd)
    x₀.P.smoothDim (eSec x₀.P.A q)).trans hg
  obtain ⟨x, hx, h⟩ := exists_keyAt M hz m hp hA kt hd (hg ▸ x₀.g_pos)
  exact ⟨x, hx.trans hg.symm, h⟩

end OneModel

end GlobalTheory.KeyAtFam
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpMapClosedPointOfSurjective
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

namespace GlobalTheory.ArcIntegral

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : B →+* C) (g : A →+* B) :
    spMap f ≫ spMap g = spMap (f.comp g) := (Spec.map_comp _ _).symm

theorem ev_factor {Z : Scheme.{0}} {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (z₁ : Sp A ⟶ Z) (z₂ : Sp B ⟶ Z)
    (e : z₂ = spMap φ ≫ z₁) (W : Z.Opens) (h₁ : ⊤ ≤ z₁ ⁻¹ᵁ W) (h₂ : ⊤ ≤ z₂ ⁻¹ᵁ W) (f : Γ(Z, W)) :
    ev z₂ W h₂ f = φ (ev z₁ W h₁ f) := by
  subst e
  rw [GlobalTheory.FlagMod.ev_spMap φ z₁ W h₁]
  rfl

theorem point_cases (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (x : Sp R) :
    (∃ p : Sp K, spMap (algebraMap R K) p = x) ∨ x = IsLocalRing.closedPoint R := by
  by_cases h : x.asIdeal = ⊥
  · refine Or.inl ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K), PrimeSpectrum.ext ?_⟩
    rw [h]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R K)
  · refine Or.inr (PrimeSpectrum.ext ?_)
    exact IsLocalRing.eq_maximalIdeal (x.isPrime.isMaximal h)

theorem spMap_closedPoint {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] (f : A →+* B)
    [IsLocalHom f] : spMap f (IsLocalRing.closedPoint B) = IsLocalRing.closedPoint A :=
  IsLocalRing.comap_closedPoint f

theorem spMap_closedPoint_of_surjective {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (f : A →+* B) (hf : Function.Surjective f) :
    spMap f (IsLocalRing.closedPoint B) = IsLocalRing.closedPoint A :=
  haveI : (IsLocalRing.closedPoint B).asIdeal.IsMaximal := IsLocalRing.maximalIdeal.isMaximal B
  PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective f hf))

theorem mk_le_continuum_of_finite {A B : Type} [CommRing A] [CommRing B] (g : A →+* B) (hg : g.Finite)
    (hA : Cardinal.mk A ≤ Cardinal.continuum) : Cardinal.mk B ≤ Cardinal.continuum := by
  letI := g.toAlgebra
  haveI : Module.Finite A B := hg
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' A B
  refine (Cardinal.mk_le_of_surjective hf).trans ?_
  rw [show Cardinal.mk (Fin n → A) = Cardinal.mk A ^ n by simp]
  exact (pow_le_pow_left' hA n).trans (Cardinal.power_nat_le Cardinal.aleph0_le_continuum)

theorem mem_range_of_map {R K A B : Type} [CommRing R] [IsDomain R] [ValuationRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] [CommRing A] [IsDomain A] [Field B] [Algebra A B] [IsFractionRing A B] (e : R →+* A)
    [IsLocalHom e] (la : K →+* B) (hla : ∀ r, la (algebraMap R K r) = algebraMap A B (e r)) (x : K)
    (hx : la x ∈ (algebraMap A B).range) : x ∈ (algebraMap R K).range := by
  rcases ValuationRing.isInteger_or_isInteger R x with ⟨r, hr⟩ | ⟨r, hr⟩
  · exact ⟨r, hr⟩
  by_cases h0 : x = 0
  · exact ⟨0, by simp [h0]⟩
  obtain ⟨t, ht⟩ := hx
  have h1 : algebraMap A B (e r * t) = 1 := by
    rw [map_mul, ht, ← hla, show algebraMap R K r = x⁻¹ from hr, ← map_mul, inv_mul_cancel₀ h0, map_one]
  have h2 : e r * t = 1 := IsFractionRing.injective A B (h1.trans (map_one _).symm)
  have hu : IsUnit r := isUnit_of_map_unit e r (IsUnit.of_mul_eq_one _ h2)
  obtain ⟨u, rfl⟩ := hu
  refine ⟨(u⁻¹ : Rˣ), ?_⟩
  have h3 : algebraMap R K ((u⁻¹ : Rˣ) : R) * x⁻¹ = 1 := by
    rw [← show algebraMap R K u = x⁻¹ from hr, ← map_mul, Units.inv_mul, map_one]
  exact (mul_inv_eq_one₀ (inv_ne_zero h0 |> fun h => by simpa using h)).1 h3

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

theorem range_j_subset {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β) :
    Set.range Y.j ⊆ abLocus Y.t.G := by
  rintro _ ⟨x, rfl⟩
  have h : Y.jQ x ∈ pullback.fst Y.s (spMap β) ⁻¹' abLocus Y.t.G := by
    rw [Y.ab_gen]; exact ⟨x, rfl⟩
  rw [Model.j, Scheme.Hom.comp_apply]
  exact h

theorem exists_frac_lift {A K L : Type} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K] [Field L]
    (f : A →+* L) (hf : Function.Injective f) : ∃ fK : K →+* L, fK.comp (algebraMap A K) = f :=
  ⟨IsFractionRing.lift hf, RingHom.ext fun x => by rw [RingHom.comp_apply, IsFractionRing.lift_algebraMap hf x]⟩

theorem exists_away_lift {A S L : Type} [CommRing A] [CommRing S] [Algebra A S] (x : A) [IsLocalization.Away x S]
    [CommRing L] (f : A →+* L) (hf : IsUnit (f x)) : ∃ F : S →+* L, ∀ a, F (algebraMap A S a) = f a :=
  ⟨IsLocalization.Away.lift x hf, IsLocalization.Away.lift_eq x hf⟩

theorem isUnit_map_X {A : Type} [CommRing A] (κ : A →+* ℂ) :
    IsUnit ((HahnSeries.ofPowerSeries ℤ ℂ).comp (PowerSeries.map κ) PowerSeries.X) := by
  rw [RingHom.comp_apply, PowerSeries.map_X, HahnSeries.ofPowerSeries_X]
  exact isUnit_iff_ne_zero.2 (HahnSeries.single_ne_zero one_ne_zero)

end GlobalTheory.ArcIntegral
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDvrLiftFiniteCover
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFieldExtension
open TensorProduct
namespace GlobalTheory.FieldExtensionExists

theorem exists_field_extension {R R' K : Type} [CommRing R] [CommRing R'] [Field K]
    (ρ : R →+* R') (hinj : Function.Injective ρ) (hfin : ρ.Finite) (φ : R →+* K) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L) (χ : R' →+* L),
      χ.comp ρ = (algebraMap K L).comp φ := by
  letI : Algebra R R' := ρ.toAlgebra
  haveI : Algebra.IsIntegral R R' := ⟨fun x => hfin.to_isIntegral x⟩
  haveI : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  obtain ⟨q, -, hq, hqc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (RingHom.ker φ) (⊥ : Ideal R') (by
    intro x hx
    have : ρ x = 0 := hx
    have h0 : x = 0 := hinj (this.trans (map_zero ρ).symm)
    rw [h0]; exact Ideal.zero_mem _)
  have hqc' : q.comap ρ = RingHom.ker φ := hqc
  let j : (R ⧸ RingHom.ker φ) →+* (R' ⧸ q) := Ideal.quotientMap q ρ hqc'.ge
  have hj : Function.Injective j := Ideal.quotientMap_injective' hqc'.le
  have hjf : j.Finite := by
    apply RingHom.Finite.of_comp_finite (f := Ideal.Quotient.mk (RingHom.ker φ))
    have : j.comp (Ideal.Quotient.mk (RingHom.ker φ)) = (Ideal.Quotient.mk q).comp ρ := by
      ext x; simp [j]
    rw [this]
    exact (RingHom.Finite.of_surjective _ Ideal.Quotient.mk_surjective).comp hfin
  letI : Algebra (R ⧸ RingHom.ker φ) (R' ⧸ q) := j.toAlgebra
  letI : Algebra (R ⧸ RingHom.ker φ) K := (RingHom.kerLift φ).toAlgebra
  haveI : Module.Finite (R ⧸ RingHom.ker φ) (R' ⧸ q) := hjf
  haveI : Nontrivial (K ⊗[R ⧸ RingHom.ker φ] (R' ⧸ q)) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain _ _ _
      (RingHom.kerLift_injective φ) hj
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (K ⊗[R ⧸ RingHom.ker φ] (R' ⧸ q))
  refine ⟨(K ⊗[R ⧸ RingHom.ker φ] (R' ⧸ q)) ⧸ M, Ideal.Quotient.field M, inferInstance,
    (inferInstance : Module.Finite K ((K ⊗[R ⧸ RingHom.ker φ] (R' ⧸ q)) ⧸ M)),
    (Ideal.Quotient.mk M).comp ((Algebra.TensorProduct.includeRight (R := R ⧸ RingHom.ker φ) (A := K)
      (B := R' ⧸ q)).toRingHom.comp (Ideal.Quotient.mk q)), ?_⟩
  ext r
  change Ideal.Quotient.mk M (Algebra.TensorProduct.includeRight (R := R ⧸ RingHom.ker φ) (A := K)
      (B := R' ⧸ q) (algebraMap (R ⧸ RingHom.ker φ) (R' ⧸ q) (Ideal.Quotient.mk _ r))) =
    Ideal.Quotient.mk M ((φ r) ⊗ₜ 1)
  rw [AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply]
  rfl

theorem exists_extension : ∀ (R R' : Type) [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] (ρ : R →+* R'),
    Function.Injective ρ → ρ.Finite → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V →
    ∀ (ψ : R →+* V), IsLocalHom ψ → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V')
      (f : V →+* V') (ψ' : R' →+* V'), GlobalTheory.LN.CDvr V' ∧ Function.Injective f ∧ IsLocalHom f ∧ IsLocalHom ψ' ∧
      ψ'.comp ρ = f.comp ψ := by
  intro R R' _ _ _ _ ρ hinj hfin V _ _ _ hV ψ hψ
  obtain ⟨h1, h2, h3⟩ := hV
  haveI : CharZero (FractionRing V) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective V (FractionRing V))
  obtain ⟨L, _, _, _, χ, hχ⟩ := exists_field_extension ρ hinj hfin ((algebraMap V (FractionRing V)).comp ψ)
  obtain ⟨W, _, _, hW1, hW2, _, _, _, hc, -, hf, hl, hint, -⟩ :=
    GlobalTheory.SS.exists_complete_dvr_finite_extension V (FractionRing V) L
  have hWL : Function.Injective (algebraMap W L) := IsFractionRing.injective W L
  have hmem : ∀ x : R', ∃ w : W, algebraMap W L w = χ x := by
    intro x
    obtain ⟨P, hP, hPx⟩ := hfin.to_isIntegral x
    refine hint (χ x) ⟨P.map ψ, hP.map ψ, ?_⟩
    rw [Polynomial.eval₂_map, RingHom.comp_assoc, ← hχ, ← Polynomial.hom_eval₂, hPx, map_zero]
  choose g hg using hmem
  let ψ' : R' →+* W :=
    { toFun := g
      map_one' := hWL (by simp [hg])
      map_mul' := fun x y => hWL (by simp [hg])
      map_zero' := hWL (by simp [hg])
      map_add' := fun x y => hWL (by simp [hg]) }
  have hcomp : ψ'.comp ρ = (algebraMap V W).comp ψ := by
    ext r
    apply hWL
    have e1 := RingHom.congr_fun hχ r
    have e2 := RingHom.congr_fun hc (ψ r)
    simp only [RingHom.comp_apply] at e1 e2 ⊢
    rw [e2, ← e1]
    exact hg _
  have hloc : IsLocalHom (ψ'.comp ρ) := by rw [hcomp]; infer_instance
  have hmax : ((IsLocalRing.maximalIdeal W).comap ψ').IsMaximal := by
    apply Ideal.isMaximal_of_isIntegral_of_isMaximal_comap' ρ hfin.to_isIntegral
    have e : (IsLocalRing.maximalIdeal W).comap (ψ'.comp ρ) = IsLocalRing.maximalIdeal R :=
      ((IsLocalRing.local_hom_tfae (ψ'.comp ρ)).out 1 5).1 hloc
    rw [Ideal.comap_comap, e]
    infer_instance
  refine ⟨W, inferInstance, inferInstance, inferInstance, algebraMap V W, ψ',
    ⟨hW1, hW2, charZero_of_injective_algebraMap hf⟩, hf, hl, ?_, hcomp⟩
  exact ((IsLocalRing.local_hom_tfae ψ').out 1 5).2 (IsLocalRing.eq_maximalIdeal hmax)

end GlobalTheory.FieldExtensionExists
end

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.LocExt

theorem exists_cDvr_ext_of_finite : ∀ (R R' : Type) [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] (ρ : R →+* R'), Function.Injective ρ → ρ.Finite → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V → ∀ ψ : R →+* V, IsLocalHom ψ → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V') (f : V →+* V') (ψ' : R' →+* V'), CDvr V' ∧ Function.Injective f ∧ IsLocalHom f ∧ IsLocalHom ψ' ∧ ψ'.comp ρ = f.comp ψ := by
  first
  | exact @_root_.GlobalTheory.FieldExtensionExists.exists_extension
  | exact _root_.GlobalTheory.FieldExtensionExists.exists_extension
  | (apply _root_.GlobalTheory.FieldExtensionExists.exists_extension <;> assumption)
  | (intros; apply _root_.GlobalTheory.FieldExtensionExists.exists_extension <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FieldExtensionExists.exists_extension <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FieldExtensionExists.exists_extension ..)

end GlobalTheory.LocExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorsionCountThroughExponentialLatticeKernel
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorsionCountThroughExponentialLatticeKernel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Hor.LogCh

theorem exp_lattice_torsion_count : ∀ (Q : Type) [Group Q] (g r N : ℕ) (e : (Fin g → ℂ) → Q) (b : Fin r → Fin g → ℂ) (T : Set Q), 0 < N → (∀ v w, e (v + w) = e v * e w) → Function.Surjective e → IsLatBasis {w | e w = 1} b → (∀ τ ∈ T, τ ^ N = 1) → Nat.card {p : Q // p ^ N = 1} * Nat.card T = N ^ (2 * g) → ∃ S : Set (Fin r → ZMod N), N ^ r * Nat.card S = N ^ (2 * g) ∧ ∀ a : Fin r → ℤ, (fun j => (a j : ZMod N)) ∈ S → e ((N : ℂ)⁻¹ • ∑ j, a j • b j) ∈ T := by
  intro Q _ g r N e b T hN he _hs hb hT hcard
  haveI : NeZero N := ⟨hN.ne'⟩
  have e0 : e 0 = 1 := by
    have h := he 0 0
    rw [add_zero] at h
    exact mul_left_cancel (a := e 0) (h.symm.trans (_root_.mul_one _).symm)
  have esub : ∀ v w, e (v - w) = e v * (e w)⁻¹ := by
    intro v w
    have h := he (v - w) w
    rw [sub_add_cancel] at h
    exact eq_mul_inv_of_mul_eq h.symm
  have ensmul : ∀ (n : ℕ) v, e (n • v) = e v ^ n := by
    intro n v
    induction n with
    | zero => simp [e0]
    | succ n ih => rw [succ_nsmul, he, ih, pow_succ]
  set ψ : (Fin r → ℤ) → Q := fun a => e ((N : ℂ)⁻¹ • ∑ j, a j • b j) with hψ
  have hdiff : ∀ a a' : Fin r → ℤ, (N : ℂ)⁻¹ • ∑ j, a j • b j - (N : ℂ)⁻¹ • ∑ j, a' j • b j
      = (N : ℂ)⁻¹ • ∑ j, (a j - a' j) • b j := by
    intro a a'
    rw [← smul_sub, ← Finset.sum_sub_distrib]
    simp [sub_smul]
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'

  have hdvd : ∀ (c m : Fin r → ℤ), (N : ℂ)⁻¹ • ∑ j, c j • b j = ∑ j, m j • b j → ∀ j, c j = N * m j := by
    intro c m h
    have h2 : ∑ j, c j • b j = (N : ℂ) • ∑ j, m j • b j := by
      rw [← h, smul_smul, mul_inv_cancel₀ hN0, one_smul]
    have h3 : ∑ j, ((c j : ℝ) - (N : ℝ) * (m j : ℝ)) • b j = 0 := by
      simp only [sub_smul, mul_smul, Finset.sum_sub_distrib, ← Finset.smul_sum, Int.cast_smul_eq_zsmul]
      rw [h2, Nat.cast_smul_eq_nsmul ℂ, Nat.cast_smul_eq_nsmul ℝ, sub_self]
    have h4 := Fintype.linearIndependent_iff.1 hb.1 _ h3
    intro j
    have := h4 j
    rw [sub_eq_zero] at this
    exact_mod_cast this
  have key : ∀ a a' : Fin r → ℤ, ψ a = ψ a' ↔ ∀ j, (a j : ZMod N) = a' j := by
    intro a a'
    constructor
    · intro h
      have h1 : e ((N : ℂ)⁻¹ • ∑ j, (a j - a' j) • b j) = 1 := by
        rw [← hdiff, esub]
        exact mul_inv_eq_one.2 h
      obtain ⟨m, hm⟩ := (hb.2 _).1 h1
      have := hdvd (fun j => a j - a' j) m hm
      intro j
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
      exact ⟨-m j, by have := this j; push_cast at this ⊢; linarith⟩
    · intro h
      have hk : ∀ j, ∃ k : ℤ, a j - a' j = N * k := fun j =>
        (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 (h j).symm |>.imp fun k hk => by linarith
      choose k hk using hk
      have h1 : e (∑ j, k j • b j) = 1 := (hb.2 _).2 ⟨k, rfl⟩
      have h2 : (N : ℂ)⁻¹ • ∑ j, (a j - a' j) • b j = ∑ j, k j • b j := by
        simp_rw [hk, mul_smul, ← Finset.smul_sum]
        rw [Nat.cast_smul_eq_nsmul ℤ]
        rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hN0, one_smul]
      have h3 := hdiff a a'
      rw [h2] at h3
      have h4 : (N : ℂ)⁻¹ • ∑ j, a j • b j = (N : ℂ)⁻¹ • ∑ j, a' j • b j + ∑ j, k j • b j := by
        rw [← h3]; abel
      simp only [hψ, h4, he, h1, _root_.mul_one]
  have hpow : ∀ a, ψ a ^ N = 1 := by
    intro a
    show e _ ^ N = 1
    rw [← ensmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hN0, one_smul]
    exact (hb.2 _).2 ⟨a, rfl⟩
  have hsurj : ∀ p : Q, p ^ N = 1 → ∃ a, ψ a = p := by
    intro p hp
    obtain ⟨u, rfl⟩ := _hs p
    have h1 : e (N • u) = 1 := by rw [ensmul, hp]
    obtain ⟨m, hm⟩ := (hb.2 _).1 h1
    refine ⟨m, ?_⟩
    show e _ = e u
    rw [← hm, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hN0, one_smul]
  let F : (Fin r → ZMod N) → Q := fun s => ψ (fun j => ((s j).val : ℤ))
  have hFval : ∀ a : Fin r → ℤ, F (fun j => (a j : ZMod N)) = ψ a := by
    intro a
    exact (key _ _).2 fun j => by simp
  have hFinj : Function.Injective F := by
    intro s s' h
    funext j
    have h1 := (key _ _).1 h j
    simpa using h1
  have hR : Nat.card {p : Q // p ^ N = 1} = N ^ r := by
    have hbij : Function.Bijective (fun s => (⟨F s, hpow _⟩ : {p : Q // p ^ N = 1})) := by
      refine ⟨fun s s' h => hFinj (congrArg Subtype.val h), fun p => ?_⟩
      obtain ⟨a, ha⟩ := hsurj p.1 p.2
      exact ⟨fun j => (a j : ZMod N), Subtype.ext (by show F _ = _; rw [hFval, ha])⟩
    rw [← Nat.card_eq_of_bijective _ hbij]
    simp [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card]
  refine ⟨{s | F s ∈ T}, ?_, ?_⟩
  · have hS : Nat.card {s | F s ∈ T} = Nat.card T := by
      have hbij : Function.Bijective (fun s : {s | F s ∈ T} => (⟨F s.1, s.2⟩ : T)) := by
        refine ⟨fun s s' h => Subtype.ext (hFinj (congrArg Subtype.val h)), fun τ => ?_⟩
        obtain ⟨a, ha⟩ := hsurj τ.1 (hT _ τ.2)
        refine ⟨⟨fun j => (a j : ZMod N), ?_⟩, Subtype.ext ?_⟩
        · show F _ ∈ T
          rw [hFval, ha]
          exact τ.2
        · show F _ = _
          rw [hFval, ha]
      exact Nat.card_eq_of_bijective _ hbij
    rw [hS, ← hR, hcard]
  · intro a ha
    show ψ a ∈ T
    rw [← hFval]
    exact ha

end GlobalTheory.ShFam.Hor.LogCh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorsionCountThroughExponentialLatticeKernelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_count_through_exponential_lattice_kernel : ∀ (Q : Type) [Group Q] (g r N : ℕ) (e : (Fin g → ℂ) → Q) (b : Fin r → Fin g → ℂ) (T : Set Q), 0 < N → (∀ v w, e (v + w) = e v * e w) → Function.Surjective e → IsLatBasis {w | e w = 1} b → (∀ τ ∈ T, τ ^ N = 1) → Nat.card {p : Q // p ^ N = 1} * Nat.card T = N ^ (2 * g) → ∃ S : Set (Fin r → ZMod N), N ^ r * Nat.card S = N ^ (2 * g) ∧ ∀ a : Fin r → ℤ, (fun j => (a j : ZMod N)) ∈ S → e ((N : ℂ)⁻¹ • ∑ j, a j • b j) ∈ T := by
  first | exact @GlobalTheory.ShFam.Hor.LogCh.exp_lattice_torsion_count | exact GlobalTheory.ShFam.Hor.LogCh.exp_lattice_torsion_count | (intros; apply GlobalTheory.ShFam.Hor.LogCh.exp_lattice_torsion_count <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLagrangianDualPairInCoisotropic
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLagrangianDualPairInCoisotropic
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open Module

theorem exists_lagrangian_dual_in_coisotropic : ∀ (r : ℕ) (M : Matrix (Fin r) (Fin r) ℝ) (W : Submodule ℝ (Fin r → ℝ)), Mᵀ = -M → M.det ≠ 0 → (∀ v : Fin r → ℝ, (∀ w ∈ W, v ⬝ᵥ M *ᵥ w = 0) → v ∈ W) → ∃ (d : ℕ) (e f : Fin d → Fin r → ℝ), (∀ i, e i ∈ W) ∧ (∀ i j, e i ⬝ᵥ M *ᵥ e j = 0) ∧ (∀ i j, f i ⬝ᵥ M *ᵥ e j = if i = j then 1 else 0) ∧ Submodule.span ℝ (Set.range (Sum.elim e f)) = ⊤ := by
  classical
  intro r M W hskew hdet hW
  set B : LinearMap.BilinForm ℝ (Fin r → ℝ) := Matrix.toBilin' M with hBdef
  have hB : ∀ v w, B v w = v ⬝ᵥ M *ᵥ w := fun v w => by
    simp [hBdef, Matrix.toBilin'_apply']
  have hskewB : ∀ v w, B v w = - B w v := by
    intro v w
    rw [hB, hB, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hskew, Matrix.neg_mulVec,
      neg_dotProduct, dotProduct_comm]
  have hBalt : ∀ v, B v v = 0 := fun v => by have := hskewB v v; linarith
  have hrefl : B.IsRefl := fun x y h => by rw [hskewB, h, neg_zero]
  have hnd : B.Nondegenerate := LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero' M hdet
  let P : ℕ → Prop := fun n => ∃ L : Submodule ℝ (Fin r → ℝ), L ≤ W ∧
    (∀ x ∈ L, ∀ y ∈ L, B x y = 0) ∧ finrank ℝ L = n
  have P0 : P 0 := ⟨⊥, bot_le, by simp, finrank_bot ℝ _⟩
  obtain ⟨L, hLW, hLiso, hLdim⟩ : P (Nat.findGreatest P r) := Nat.findGreatest_spec (Nat.zero_le _) P0
  have hmax : ∀ v ∈ W, (∀ l ∈ L, B v l = 0) → v ∈ L := by
    intro v hvW hvL
    by_contra hv
    have hlt : L < L ⊔ Submodule.span ℝ {v} := lt_of_le_of_ne le_sup_left (fun h => hv (by
      rw [h]; exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self v)))
    have hiso : ∀ x ∈ L ⊔ Submodule.span ℝ {v}, ∀ y ∈ L ⊔ Submodule.span ℝ {v}, B x y = 0 := by
      intro x hx y hy
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
      obtain ⟨a', ha', b', hb', rfl⟩ := Submodule.mem_sup.mp hy
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hb
      obtain ⟨c', rfl⟩ := Submodule.mem_span_singleton.mp hb'
      have h1 := hLiso a ha a' ha'
      have h2 := hvL a' ha'
      have h3 : B a v = 0 := by rw [hskewB, hvL a ha, neg_zero]
      have h4 := hBalt v
      simp [map_add (f := _), map_smul, h1, h2, h3, h4]
    have hle : L ⊔ Submodule.span ℝ {v} ≤ W :=
      sup_le hLW (by rw [Submodule.span_le]; simpa using hvW)
    have hP : P (finrank ℝ ↥(L ⊔ Submodule.span ℝ {v})) := ⟨_, hle, hiso, rfl⟩
    have h5 := Nat.le_findGreatest (by simpa using Submodule.finrank_le (L ⊔ Submodule.span ℝ {v})) hP
    have h6 := Submodule.finrank_lt_finrank_of_lt hlt
    omega
  have hWo : B.orthogonal W ≤ L := by
    intro x hx
    have hxW : x ∈ W := hW x (fun w hw => by rw [← hB, hskewB, hx w hw, neg_zero])
    exact hmax x hxW (fun l hl => by rw [hskewB, hx l (hLW hl), neg_zero])
  let b := Module.finBasis ℝ L
  let e : Fin (finrank ℝ L) → Fin r → ℝ := fun i => ((b i : L) : Fin r → ℝ)
  have heL : ∀ i, e i ∈ L := fun i => (b i).2
  have hext : ∀ (φ : (Fin r → ℝ) →ₗ[ℝ] ℝ), (∀ j, φ (e j) = 0) → ∀ l ∈ L, φ l = 0 := by
    intro φ hφ l hl
    have : φ ∘ₗ L.subtype = 0 := b.ext (fun j => by simpa using hφ j)
    simpa using LinearMap.congr_fun this ⟨l, hl⟩
  let φ : (Fin r → ℝ) →ₗ[ℝ] (Fin (finrank ℝ L) → ℝ) := LinearMap.pi (fun j => B.flip (e j))
  have hφ : ∀ v j, φ v j = B v (e j) := fun v j => rfl
  have hker : LinearMap.ker φ = B.orthogonal L := by
    ext v
    simp only [LinearMap.mem_ker, LinearMap.BilinForm.mem_orthogonal_iff]
    constructor
    · intro h l hl
      have h' := hext (B v) (fun j => by rw [← hφ, h]; rfl) l hl
      rw [hskewB, h', neg_zero]
    · intro h
      funext j
      rw [Pi.zero_apply, hφ, hskewB, h _ (heL j), neg_zero]
  have hrange : LinearMap.range φ = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have h1 := LinearMap.finrank_range_add_finrank_ker φ
    rw [hker, LinearMap.BilinForm.finrank_orthogonal hnd] at h1
    have h2 : finrank ℝ L ≤ r := by simpa using Submodule.finrank_le L
    simp only [Module.finrank_fin_fun] at h1 ⊢
    omega
  have hsurj : ∀ y, ∃ x, φ x = y := fun y => by
    have : y ∈ LinearMap.range φ := by rw [hrange]; trivial
    exact this
  choose f hf using fun i : Fin (finrank ℝ L) => hsurj (Pi.single i 1)
  have hfe : ∀ i j, B (f i) (e j) = if i = j then 1 else 0 := by
    intro i j
    rw [← hφ, hf i, Pi.single_apply]
    rcases eq_or_ne i j with h | h
    · subst h; simp
    · simp [h, Ne.symm h]
  refine ⟨finrank ℝ L, e, f, fun i => hLW (heL i),
    fun i j => by rw [← hB]; exact hLiso _ (heL i) _ (heL j),
    fun i j => by rw [← hB]; exact hfe i j, ?_⟩
  set U := Submodule.span ℝ (Set.range (Sum.elim e f)) with hU
  have hUo : B.orthogonal U = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    have hve : ∀ j, B (e j) v = 0 := fun j => hv _ (Submodule.subset_span ⟨Sum.inl j, rfl⟩)
    have hvf : ∀ i, B (f i) v = 0 := fun i => hv _ (Submodule.subset_span ⟨Sum.inr i, rfl⟩)
    have hvL : ∀ l ∈ L, B v l = 0 := hext (B v) (fun j => by rw [hskewB, hve j, neg_zero])
    have hvW : v ∈ W := by
      rw [← LinearMap.BilinForm.orthogonal_orthogonal hnd hrefl W]
      intro x hx
      rw [hskewB, hvL x (hWo hx), neg_zero]
    have hvL' : v ∈ L := hmax v hvW hvL
    have hv' : v = ∑ j, b.repr ⟨v, hvL'⟩ j • e j := by
      have := congrArg Subtype.val (b.sum_repr ⟨v, hvL'⟩)
      rw [Submodule.coe_sum] at this
      simp only [Submodule.coe_smul] at this
      exact this.symm
    have hc : ∀ i, b.repr ⟨v, hvL'⟩ i = 0 := by
      intro i
      have h := hvf i
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hv', map_sum] at h
      simpa [map_smul, hfe] using h
    have h0 : (⟨v, hvL'⟩ : L) = 0 := b.repr.injective (by ext i; simp [hc])
    simpa using congrArg Subtype.val h0
  have hdimU := LinearMap.BilinForm.finrank_orthogonal hnd U
  rw [hUo, finrank_bot] at hdimU
  apply Submodule.eq_top_of_finrank_eq
  have := Submodule.finrank_le U
  simp only [Module.finrank_fin_fun] at hdimU this ⊢
  omega

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLagrangianDualPairInCoisotropicStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lagrangian_dual_pair_in_coisotropic : ∀ (r : ℕ) (M : Matrix (Fin r) (Fin r) ℝ) (W : Submodule ℝ (Fin r → ℝ)), Mᵀ = -M → M.det ≠ 0 → (∀ v : Fin r → ℝ, (∀ w ∈ W, v ⬝ᵥ M *ᵥ w = 0) → v ∈ W) → ∃ (d : ℕ) (e f : Fin d → Fin r → ℝ), (∀ i, e i ∈ W) ∧ (∀ i j, e i ⬝ᵥ M *ᵥ e j = 0) ∧ (∀ i j, f i ⬝ᵥ M *ᵥ e j = if i = j then 1 else 0) ∧ Submodule.span ℝ (Set.range (Sum.elim e f)) = ⊤ := by
  first | exact @GlobalTheory.exists_lagrangian_dual_in_coisotropic | exact GlobalTheory.exists_lagrangian_dual_in_coisotropic | (intros; apply GlobalTheory.exists_lagrangian_dual_in_coisotropic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NumbersEqConcreteNumbersAtBaseLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NumbersEqConcreteNumbersAtBaseLevel
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.ReadIndexNumerics

theorem ijIdx_eq (D : D7) {G : Type} [Group G] [Fintype G] {Pl0 T : Type} (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (tup : T → D.what₂.Tup)
    (eMt : ∀ (i : Fin D.R.m) (t : T), (Fin (lDim D A P0 ψ0 i t) → D.what₂.LL) ≃ₗ[D.what₂.LL] D.what₂.MtL (tup t) ((i : ℕ) + 1))
    (S0 : IndefData (A.side P0 ψ0 Zs)) (Xd : DivX D)
    (jW : ∀ i : Fin D.R.m, (Fin (S0.dW i) → D.what₂.LL) →ₛₗ[D.what₂.embLL] D.what₂.Mj ((i : ℕ) + 1))
    (i : Fin D.R.m) (t : T) (eW : (Fin (S0.dW i) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Xd.MjH ((i : ℕ) + 1)).V)
    (hP : Formalism.DivisionValues.IsOrthProj (lH D A P0 ψ0 i t) (lZ0 D A P0 ψ0 Zs i t) (lPrj D A P0 ψ0 Zs i t))
    (hθ : ∀ x, D.what₂.thetaP (tup t) ((i : ℕ) + 1) (D.what₂.jMt (tup t) ((i : ℕ) + 1) (eMt i t x)) =
      jW i ((S0.θ i t).mulVec ((lPrj D A P0 ψ0 Zs i t).mulVec x)))
    (hj : ∀ x, Xd.jM ((i : ℕ) + 1) (eW x) = jW i x)
    (hl : (Xd.MjH ((i : ℕ) + 1)).L = (S0.M i).map ((eW : (Fin (S0.dW i) → D.what₂.LL) →ₗ[D.what₂.LL] (Xd.MjH ((i : ℕ) + 1)).V).restrictScalars (𝓞 D.what₂.LL)))
    (hT : Idx.TjL D (tup t) ((i : ℕ) + 1) = (Formalism.DivisionValues.matLat (lZ0 D A P0 ψ0 Zs i t) ((A.side P0 ψ0 Zs).Tl i t)).map
      ((eMt i t).toLinearMap.restrictScalars (𝓞 D.what₂.LL)))
    (w : D.what₂.places.Pl) :
    Idx.IjIdx Xd (tup t) ((i : ℕ) + 1) w = S0.Iw i t (D.plEq w) := by
  have hPE : ∀ z, lPrj D A P0 ψ0 Zs i t *ᵥ (lZ0 D A P0 ψ0 Zs i t *ᵥ z) = z := fun z => by
    rw [Matrix.mulVec_mulVec]; erw [hP.1]; exact Matrix.one_mulVec z
  have hth : Idx.thTj Xd (tup t) ((i : ℕ) + 1) = (Formalism.DivisionValues.matLat (S0.θ i t) ((A.side P0 ψ0 Zs).Tl i t)).map
      ((eW : (Fin (S0.dW i) → D.what₂.LL) →ₗ[D.what₂.LL] (Xd.MjH ((i : ℕ) + 1)).V).restrictScalars (𝓞 D.what₂.LL)) := by
    ext y
    have key : y ∈ Idx.thTj Xd (tup t) ((i : ℕ) + 1) ↔ ∃ x ∈ Idx.TjL D (tup t) ((i : ℕ) + 1),
        Xd.jM ((i : ℕ) + 1) y = D.what₂.thetaP (tup t) ((i : ℕ) + 1) (D.what₂.jMt (tup t) ((i : ℕ) + 1) x) := Iff.rfl
    rw [key, hT]
    constructor
    · rintro ⟨x, hx, hxy⟩
      obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.1 hx
      obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hu
      refine Submodule.mem_map.2 ⟨S0.θ i t *ᵥ z, Submodule.mem_map.2 ⟨z, hz, rfl⟩, ?_⟩
      apply Idx.jM_inj Xd
      have h1 := hθ (lZ0 D A P0 ψ0 Zs i t *ᵥ z)
      erw [hPE] at h1
      refine (hj _).trans ?_
      rw [hxy]
      exact h1.symm
    · intro hy
      obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.1 hy
      obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.1 hu
      refine ⟨eMt i t (lZ0 D A P0 ψ0 Zs i t *ᵥ z), Submodule.mem_map.2 ⟨lZ0 D A P0 ψ0 Zs i t *ᵥ z,
        Submodule.mem_map.2 ⟨z, hz, rfl⟩, rfl⟩, ?_⟩
      have h1 := hθ (lZ0 D A P0 ψ0 Zs i t *ᵥ z)
      erw [hPE] at h1
      refine (hj _).trans ?_
      exact h1.symm
  unfold Idx.IjIdx
  rw [hth, hl, SkeletonIndexLemmas.lidx_map _ _ eW.injective]
  rfl

theorem numTie_of_read : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y) (Xd : DivX D) (JM : MjHIds D A3.A Xd (A3.indefDown (s0Of R F))), Pins R F cG → Holds R F → MjHTie D A3.A Xd (A3.indefDown (s0Of R F)) Z.jW JM → IdxDefs D Xd → NumTie D A3.A (A3.indefDown (s0Of R F)) Y.tup := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z Xd JM hP hH hM hI
  obtain ⟨-, hθ⟩ := GlobalTheory.T.liftCuspFormSpace_thetaMap_eq_data D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH
  have hZ0 := GlobalTheory.T.zeroSubspace_spanned_by_dataZeroSubspace_lifts D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH
  have hok := hH.ok.ok2
  have hB : ∀ i t, BlockHyp (A3.A.fam.L i t) (A3.A.fam.lvlA F.P0 F.ψ0) A3.A.fam.v0 1 :=
    fun i t => ⟨hok.conj, hok.irr, hok.lifts i t⟩
  have hOP : ∀ i t, Formalism.DivisionValues.IsOrthProj (lH D A3.A F.P0 F.ψ0 i t) (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t)
      (lPrj D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t) :=
    fun i t => BlockDat.lf_l_proj (Z := (A3.fam3.toSub2 (zsOf R F)).Zl i t) (hB i t)
  have hT := fun i t => GlobalTheory.T.lattice_Tj_eq_image_of_coordinate_lattice D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) Y.tup Y.eMt i t (hOP i t) (Y.formsL i t) (Y.latL i t)
    (hZ0 i t) (fun x => by
      have e : ∀ v, lPrj D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ v) = v :=
        fun v => by rw [Matrix.mulVec_mulVec]; erw [(hOP i t).1]; exact Matrix.one_mulVec v
      have h2 := hθ i t (lZ0 D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ (lPrj D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) i t *ᵥ x))
      erw [e] at h2
      exact (hθ i t x).trans h2.symm)
  refine ⟨fun i t w => ?_, fun i t w => ?_, fun i w => ?_⟩
  · rw [hI.Ij_def _ _ _ (by omega) (by omega)]
    exact ijIdx_eq D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) Y.tup Y.eMt (A3.indefDown (s0Of R F)) Xd Z.jW i t (JM.eW i)
      (hOP i t) (hθ i t) (hM.j_eq i) (hM.hlat i).lat (hT i t) w
  · rw [hI.jw_def _ _ _ (by omega) (by omega)]
    refine GlobalTheory.T.lattice_jw_index_eq_concrete_lift_index D A3.A F.P0 F.ψ0 (A3.fam3.toSub2 (zsOf R F)) Y.tup Y.eMt i t (hOP i t) (Y.formsL i t)
      (BlockDat.lf_lE_form (hB i t)) ?_ (hT i t) w
    classical
    let K := D.what₂.LL
    let B := A3.A.fam.L i t
    let S := B.S
    let ℓ := A3.A.fam.lvlA F.P0 F.ψ0
    let Zl := (A3.fam3.toSub2 (zsOf R F)).Zl i t
    have hGood := (hB i t).ok.good
    change Submodule.span K (↑(B.Tl ℓ Zl) : Set (Fin (B.dZ ℓ Zl) → K)) = ⊤
    apply top_unique
    intro z _
    let x := (B.fE ℓ Zl).mulVec z
    have hdenom (c : S.Cl) : ∃ d : 𝓞 K, d ≠ 0 ∧ d • S.I x c ∈ S.Nab c := by
      obtain ⟨g, hg⟩ := (hGood.nab_lat c).fg
      obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 K)) g
        (fun y => S.pair y (S.I x c))
      refine ⟨d, nonZeroDivisors.coe_ne_zero d, ?_⟩
      have hdual : (d : 𝓞 K) • S.I x c ∈ Formalism.HermitianLatticesTheory.dual S.pair (S.Nab c) := by
        rw [Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
        intro y hy
        refine Submodule.span_induction
          (p := fun y _ => S.pair y ((d : 𝓞 K) • S.I x c) ∈ (1 : Submodule (𝓞 K) K))
          ?_ ?_ ?_ ?_ (hg.symm ▸ hy)
        · intro y hy
          rw [LinearMap.map_smul_of_tower, Submodule.mem_one]
          exact hd y hy
        · simp
        · intro y y' _ _ hy hy'
          rw [map_add, LinearMap.add_apply]
          exact add_mem hy hy'
        · intro a y _ hy
          obtain ⟨a', ha'⟩ := Formalism.DivisionValues.exponent_index_lattice.hstar (K := K) a
          rw [← algebraMap_smul K a y, LinearMap.map_smulₛₗ, LinearMap.smul_apply]
          change star (algebraMap (𝓞 K) K a) • _ ∈ (1 : Submodule (𝓞 K) K)
          rw [← ha', algebraMap_smul]
          exact Submodule.smul_mem _ _ hy
      exact hGood.del_le c (by simpa using hGood.dual_le c _ hdual)
    choose d hd0 hd using hdenom
    let a := ∏ c, d c
    have ha : a ≠ 0 := Finset.prod_ne_zero_iff.mpr fun c _ => hd0 c
    have hax : a • x ∈ S.nabLat := by
      apply (Formalism.DivisionValues.ValuationLatticeField.mem_valLatF S.I S.Nab _).2
      intro c
      rw [LinearMap.map_smul_of_tower, Pi.smul_apply]
      obtain ⟨b, hb⟩ := Finset.dvd_prod_of_mem d (Finset.mem_univ c)
      rw [show a = d c * b from hb, mul_comm, mul_smul]
      exact (S.Nab c).smul_mem b (hd c)
    have haz : a • z ∈ B.Tl ℓ Zl := by
      apply BlockDat.lf_cutZ_le (hB i t)
      change (B.fE ℓ Zl).mulVec (a • z) ∈ S.nabLat
      rwa [Matrix.mulVec_smul]
    have haK : (a : K) ≠ 0 := RingOfIntegers.coe_ne_zero_iff.mpr ha
    have hmem : (a : K) • z ∈ Submodule.span K (↑(B.Tl ℓ Zl) : Set _) := by
      rw [algebraMap_smul K a z]
      exact Submodule.subset_span haz
    exact inv_smul_smul₀ haK z ▸ (Submodule.span K _).smul_mem (a : K)⁻¹ hmem
  · rw [Z.etaJ]
    by_cases h : D.plEq w ∈ R.twPl
    · rw [if_pos h, if_pos (show D.plEq w ∈ (A3.indefDown (s0Of R F)).Tw from h)]; rfl
    · rw [if_neg h, if_neg (show D.plEq w ∉ (A3.indefDown (s0Of R F)).Tw from h)]

end GlobalTheory.Mem.ReadIndexNumerics

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NumbersEqConcreteNumbersAtBaseLevelStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.numbers_eq_concreteNumbers_at_baseLevel : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y) (Xd : DivX D) (JM : MjHIds D A3.A Xd (A3.indefDown (s0Of R F))), Pins R F cG → Holds R F → MjHTie D A3.A Xd (A3.indefDown (s0Of R F)) Z.jW JM → IdxDefs D Xd → NumTie D A3.A (A3.indefDown (s0Of R F)) Y.tup := by
  first | exact @GlobalTheory.Mem.ReadIndexNumerics.numTie_of_read | exact GlobalTheory.Mem.ReadIndexNumerics.numTie_of_read | (intros; apply GlobalTheory.Mem.ReadIndexNumerics.numTie_of_read <;> assumption)
end
end
