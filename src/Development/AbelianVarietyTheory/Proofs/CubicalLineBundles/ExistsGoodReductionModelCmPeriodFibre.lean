module

public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLetterIntegralInIntegralEigenbasis
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsNumberFieldPointOfCmPeriodLattice

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PrincipalTripleExtendsOfCurveHomomorphisms
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPrincipalTripleModelOfIsogenyDedekind
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPrincipalTripleModelOfIsogenyDedekind
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

namespace GlobalTheory.CM

theorem exists_pat_model_of_isogeny : ThetaUnifAV → Out.Laws → Out.Laws2 → HomExtDvr → Published.KernelFiniteFlatSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R K : Type) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (σ : K →+* ℂ) (P : Out.PolAV (Sp R)) (P₀ : Out.PolAV (Sp K)) (φ : P₀.A.left ⟶ P.A.left) (T₀ : PAT H (Sp K)) (ψ : P₀.A ⟶ T₀.t.G), IsPolFibre (algebraMap R K) P P₀ φ → P.g = T₀.g → IsMonHom ψ → Surjective ψ.left → ∃ (T : PAT H (Sp R)) (_ : SABMap T₀.t T.t (spMap (algebraMap R K))), T.g = T₀.g := by
  intro hU hL hL2 hX hK E _ _ _ H R K _ _ _ _ _ σ P P₀ φ T₀ ψ hP hg hψ hs
  obtain ⟨hfin, hfl, n, hn, hker⟩ := GlobalTheory.T.finite_flat_torsion_ker_of_surjective_polAV hU hL K σ P₀ T₀.pol ψ (hP.1.trans hg) hψ hs
  obtain ⟨B, _, φB, Ψ, hB, gp, -, hΨfin, hΨfl, hΨs, -⟩ :=
    GlobalTheory.exists_abelianScheme_model_of_isogeny_dedekind hL R K P P₀.A T₀.t.G φ ψ n hP.2.1 T₀.ab hψ hfin hfl hs hn hker
  obtain ⟨t, m, e, -, -⟩ := GlobalTheory.T.exists_triple_of_abelian_model_dedekind hL hX E H R K T₀.t B φB hB gp
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  have : IsIso e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map e.inv))
  have hpr : IsProper t.G.hom := by
    have := hB.proper
    rw [← Over.w e.hom]
    infer_instance
  have hA : IsAbelianScheme t.G := ⟨t.semi.comm, t.semi.smooth, hpr, t.semi.geomConnected⟩
  obtain ⟨w, hw, -⟩ := m.lin
  have i : LBIso T₀.t.PP.L (t.PP.L.pull m.φ) := ⟨w, hw⟩
  have ha : Out.RelAmple t.G t.PP.L :=
    GlobalTheory.T.relAmple_of_generic_isogenous_dedekind hL hL2 R K P t.G (Ψ ≫ e.inv) t.PP.L T₀.t.G m.φ T₀.t.PP.L hA t.PP.isLB T₀.t.PP.isLB
      (by rw [Over.comp_left]; infer_instance) (by rw [Over.comp_left]; infer_instance)
      (by rw [Over.comp_left]; infer_instance) m.cart i T₀.ample
  obtain ⟨_, w', hw', -⟩ := t.sym
  exact ⟨⟨t, hA, T₀.g,
    smoothOfRelativeDimension_of_fibre R K (algebraMap R K) t.G _ m.φ T₀.t.G.hom T₀.g hA m.cart.1 T₀.dim,
    sym_of_lbIso_neg ⟨w', hw'⟩, ha,
    hK.kTriv_of_generic hA t.PP.isLB ha m.cart T₀.t.PP.isLB i T₀.ktriv⟩, m, rfl⟩

end GlobalTheory.CM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPrincipalTripleModelOfIsogenyDedekindStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_principalTriple_model_of_isogeny_dedekind : ThetaUnifAV → Out.Laws → Out.Laws2 → HomExtDvr → Published.KernelFiniteFlatSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R K : Type) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (σ : K →+* ℂ) (P : Out.PolAV (Sp R)) (P₀ : Out.PolAV (Sp K)) (φ : P₀.A.left ⟶ P.A.left) (T₀ : PAT H (Sp K)) (ψ : P₀.A ⟶ T₀.t.G), IsPolFibre (algebraMap R K) P P₀ φ → P.g = T₀.g → IsMonHom ψ → Surjective ψ.left → ∃ (T : PAT H (Sp R)) (_ : SABMap T₀.t T.t (spMap (algebraMap R K))), T.g = T₀.g := by
  first | exact @GlobalTheory.CM.exists_pat_model_of_isogeny | exact GlobalTheory.CM.exists_pat_model_of_isogeny | (intros; apply GlobalTheory.CM.exists_pat_model_of_isogeny <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PrincipalTripleExtendsOfCurveHomomorphisms
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.CurveFamily

variable {S : Scheme.{0}}

theorem comp_prod {T B A : Over S} [GrpObj A] [IsCommMonObj A] {I : Type} (s : Finset I) (x : T ⟶ B)
    (f : I → (B ⟶ A)) : x ≫ ∏ i ∈ s, f i = ∏ i ∈ s, x ≫ f i :=
  map_prod (preHom (G := A) x) f s

theorem prod_comp {T B A : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] {I : Type} (s : Finset I)
    (x : I → (T ⟶ B)) (f : B ⟶ A) [IsMonHom f] : (∏ i ∈ s, x i) ≫ f = ∏ i ∈ s, x i ≫ f :=
  map_prod (MonoidHom.mk' (fun y : T ⟶ B => y ≫ f) fun a b => MonObj.mul_comp a b f) x s

theorem exists_hom_pow {G B A : Over S} [GrpObj G] [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] {n : ℕ}
    (p : Out.IsPowGrp G B n) (ψ : Fin n → (B ⟶ A)) (hψ : ∀ i, IsMonHom (ψ i)) {k : Type} [Field k] (t : Sp k ⟶ S)
    (h : OntoAt ψ t) : ∃ Ψ : G ⟶ A, IsMonHom Ψ ∧ ∀ y : Over.mk t ⟶ A, ∃ x : Over.mk t ⟶ G, y = x ≫ Ψ := by
  have := p.hom
  have isMonHom_of_mul_comp (f : G ⟶ A)
      (hf : ∀ (T : Over S) (x y : T ⟶ G), (x * y) ≫ f = (x ≫ f) * (y ≫ f)) : IsMonHom f := by
    refine ⟨?_, ?_⟩
    ·
      rw [MonObj.one_eq_one, MonObj.one_eq_one]
      exact map_one (MonoidHom.mk' (fun x : 𝟙_ (Over S) ⟶ G => x ≫ f) (hf _))
    ·
      rw [MonObj.mul_eq_mul G, hf, MonObj.mul_eq_mul A, MonObj.comp_mul,
        tensorHom_fst, tensorHom_snd]
  refine ⟨∏ i, p.pr i ≫ ψ i, isMonHom_of_mul_comp _ (fun T x y => ?_), fun y => ?_⟩
  · simp only [comp_prod, ← Finset.prod_mul_distrib, ← Category.assoc, MonObj.mul_comp]
  · obtain ⟨m, i, x, rfl⟩ := h y
    let c : Fin n → (Over.mk t ⟶ B) := fun j => ∏ a ∈ Finset.univ.filter (fun a => i a = j), x a
    have hc : ∀ j, p.lim.lift (Fan.mk (Over.mk t) c) ≫ p.pr j = c j := fun j => p.lim.fac (Fan.mk (Over.mk t) c) ⟨j⟩
    refine ⟨p.lim.lift (Fan.mk (Over.mk t) c), ?_⟩
    rw [List.prod_ofFn, comp_prod, ← Finset.prod_fiberwise Finset.univ i]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [← Category.assoc, hc, prod_comp]
    exact Finset.prod_congr rfl fun a ha => by rw [(Finset.mem_filter.1 ha).2]

theorem exists_extension : ThetaUnifAV → Out.Laws → Out.Laws2 → HomExtDvr → Published.KernelFiniteFlatSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R K : Type) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (σ : K →+* ℂ) (P : Out.PolAV (Sp R)) (P₀ : Out.PolAV (Sp K)) (φ : P₀.A.left ⟶ P.A.left) (T₀ : PAT H (Sp K)) (ψ : Fin T₀.g → (P₀.A ⟶ T₀.t.G)), IsPolFibre (algebraMap R K) P P₀ φ → P.g = 1 → (∀ i, IsMonHom (ψ i)) → OntoAt ψ (spMap σ) → ∃ (T : PAT H (Sp R)) (_ : SABMap T₀.t T.t (spMap (algebraMap R K))), T.g = T₀.g := by
  intro hT hL hL₂ hE hK E _ _ _ H R K _ _ _ _ _ σ P P₀ φ T₀ ψ hφ hg hψ ho
  have := P₀.isAb.comm
  have := T₀.ab.comm
  obtain ⟨Q, p, hQ⟩ := GlobalTheory.T.exists_polarisedAbelianScheme_power R P T₀.g
  obtain ⟨Q₀, Φ, hΦ⟩ := exists_isPolFibre hL.polBaseChange (algebraMap R K) Q
  let p₀ := Out.powIsPowGrp P₀.A T₀.g
  obtain ⟨Φ', hΦ', -⟩ := KeyPow.exists_isGrpPullback_pow hφ.2.1 p p₀
  obtain ⟨e, he, -⟩ := grpPullback_iso hΦ.2.1 hΦ'
  obtain ⟨Ψ, hΨ, hs⟩ := exists_hom_pow p₀ ψ hψ (spMap σ) ho
  refine GlobalTheory.T.exists_principalTriple_model_of_isogeny_dedekind hT hL hL₂ hE hK E H R K σ Q Q₀ Φ T₀ (e.hom ≫ Ψ) hΦ (by rw [hQ, hg, _root_.mul_one])
    inferInstance ?_
  refine (GlobalTheory.T.abelianScheme_surjective_of_onto_complex_points K σ σ.injective T₀.t.G Q₀.A (e.hom ≫ Ψ) T₀.ab Q₀.isAb fun y => ?_).1
  obtain ⟨x, rfl⟩ := hs y
  exact ⟨x ≫ e.inv, by simp⟩

end GlobalTheory.CM.CurveFamily
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PrincipalTripleExtendsOfCurveHomomorphismsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principal_triple_extends_of_curve_homomorphisms : ThetaUnifAV → Out.Laws → Out.Laws2 → HomExtDvr → Published.KernelFiniteFlatSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R K : Type) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (σ : K →+* ℂ) (P : Out.PolAV (Sp R)) (P₀ : Out.PolAV (Sp K)) (φ : P₀.A.left ⟶ P.A.left) (T₀ : PAT H (Sp K)) (ψ : Fin T₀.g → (P₀.A ⟶ T₀.t.G)), IsPolFibre (algebraMap R K) P P₀ φ → P.g = 1 → (∀ i, IsMonHom (ψ i)) → OntoAt ψ (spMap σ) → ∃ (T : PAT H (Sp R)) (_ : SABMap T₀.t T.t (spMap (algebraMap R K))), T.g = T₀.g := by
  first | exact @GlobalTheory.CM.CurveFamily.exists_extension | exact GlobalTheory.CM.CurveFamily.exists_extension | (intros; apply GlobalTheory.CM.CurveFamily.exists_extension <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsGoodReductionModelCmPeriodFibre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.PeriodModel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def twist {R : Type} [CommRing R] {ω : R} (C : Ell H R ω) (b : Bool) : Ell H R (cond b ω (1 - ω)) where
  P := C.P
  dim := C.dim
  act := cond b C.act (Serre.comapAct C.act (EllConj.barK H))
  v := C.v
  basis := C.basis
  eig := by
    cases b
    · exact EllConj.isLieComb_one_sub C.v (C.basis.1 0) ω (C.act.act (wK H)) _
        (by
          show C.act.act (EllConj.barK H (wK H)) * C.act.act (wK H) = _
          rw [← C.act.add, EllConj.barK_wK_add, C.act.one]) C.eig
    · exact C.eig
  adj := by
    cases b
    · exact fun x y h => C.adj _ _ (congrArg H.bar h)
    · exact C.adj
  prim := by
    cases b
    · exact LBIso.trans C.P.isLB (DVR.linComb_isLB _ C.P.isLB _ _) (DVR.linComb_isLB _ C.P.isLB _ _) C.prim
        (EllConj.lbIso_of_adj C.P.isLB
          (C.adj (EllConj.barK H (wK H)) (wK H) (GlobalTheory.HostModel.bar_bar H _).symm))
    · exact C.prim

theorem ellMap_twist {R R' : Type} [CommRing R] [CommRing R'] {ω : R} {ω' : R'} {C' : Ell H R' ω'} {C : Ell H R ω}
    {f : R →+* R'} {φ : C'.P.A.left ⟶ C.P.A.left} (h : EllMap C' C f φ) (b : Bool) :
    EllMap (twist C' b) (twist C b) f φ := by
  cases b
  · exact ⟨by simp [h.1], h.2.1, h.2.2.1, fun a => h.2.2.2 _⟩
  · exact h

theorem exists_pat_univ {D : Datum H} {l : Level H} (Xo : Moduli D l) {S : Scheme.{0}} (f : S ⟶ Xo.X) :
    ∃ (T : PAT H S) (_ : SABMap T.t Xo.univ.t f), T.g = Module.finrank ℚ E / 2 * (D.p + D.q) := by
  obtain ⟨U, hU, hg⟩ := exists_pat_of_obj E H D l _ _ _ _ Xo.univ
  obtain ⟨T, m, hT⟩ := GlobalTheory.T.exists_pat_pullback_g_eq E H _ _ f U
  exact ⟨T, hU ▸ m, hT.trans hg⟩

theorem exists_sign {ω ρ : ℂ} (h : 2 * ω - 1 = ρ) (hρ : ρ ^ 2 = -(H.d : ℂ)) :
    ∃ ε : ℤˣ, 0 < ((ε : ℤ) : ℝ) * ω.im := by
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have h0 : ω.im ≠ 0 := fun h0 => by
    have e := congrArg Complex.re hρ
    have hi : ρ.im = 0 := by rw [← h]; simp [h0]
    simp only [pow_two, Complex.mul_re, hi, Complex.neg_re, Complex.natCast_re] at e
    nlinarith [mul_self_nonneg ρ.re]
  rcases lt_or_gt_of_ne h0 with h1 | h1
  · exact ⟨-1, by simpa using h1⟩
  · exact ⟨1, by simpa using h1⟩

theorem exists_pure_span {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {Pe : D.La →+ (Fin g → ℂ)}
    {hP : IsPeriod D ty Pe} {p q : ℕ} (Z : CMLat hP p q) {N : ℕ} (hN : N = Module.finrank ℚ E / 2 * (D.p + D.q)) :
    ∃ (b : Fin N → Bool) (a : ∀ j, PureType.lat hP (if b j then H.rt0 else -H.rt0)),
      ∀ z : Fin g → ℂ, ∃ c : Fin N → ℂ, z = ∑ j, c j • Pe (a j) := by
  subst hN
  obtain ⟨ε, a, h⟩ := exists_pure_vectors_periods_span E H D g ty Pe hP p q Z
  refine ⟨fun j => decide (ε j = 1), fun j => ⟨a j, ?_⟩, h⟩
  have := (a j).2
  rcases Int.units_eq_one_or (ε j) with e | e
  · simpa [e] using this
  · simpa [e] using this

theorem ontoAt_of_exp {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [GrpObj G] [IsCommMonObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (hφ : IsGrpPullback G' G f φ) (t : Sp ℂ ⟶ S') {s : Sp ℂ ⟶ S}
    (hs : t ≫ f = s) {V : Type} [AddCommGroup V] [Module ℂ V] (e : V → (Over.mk s ⟶ G))
    (hadd : ∀ z w, e (z + w) = e z * e w) (honto : Function.Surjective e) {N : ℕ} (v : Fin N → V)
    (hv : ∀ z, ∃ c : Fin N → ℂ, z = ∑ j, c j • v j) {B : Over S'} (ψ : Fin N → (B ⟶ G'))
    (hψ : ∀ j (z : ℂ), ∃ x : Over.mk t ⟶ B, x.left ≫ (ψ j).left ≫ φ = (e (z • v j)).left) :
    OntoAt (B := fun _ => B) ψ t := by
  subst hs
  intro y
  obtain ⟨z, hz⟩ := honto (pushHom hφ (Over.mk t) y)
  obtain ⟨c, rfl⟩ := hv z
  choose x hx using hψ
  refine ⟨N, id, fun j => x j (c j), ?_⟩
  have hinj : Function.Injective (pushHom hφ (Over.mk t)) := fun a b h =>
    Over.OverMorphism.ext (hφ.1.hom_ext (congrArg (fun q => q.left) h) ((Over.w a).trans (Over.w b).symm))
  apply hinj
  let F : Multiplicative V →* (Over.mk (t ≫ f) ⟶ G) := MonoidHom.mk' (fun z => e z.toAdd) fun z w => hadd _ _
  have h1 : e (∑ j, c j • v j) = (List.ofFn fun j => e (c j • v j)).prod := by
    have := map_list_prod F (List.ofFn fun j => Multiplicative.ofAdd (c j • v j))
    rw [List.map_ofFn, List.prod_ofFn, ← ofAdd_sum] at this
    exact this
  rw [← hz, h1, map_list_prod, List.map_ofFn]
  congr 2
  funext j
  exact Over.OverMorphism.ext ((hx j (c j)).symm.trans (Category.assoc _ _ _).symm)

theorem exists_model : CMCurve → CMPoint → ThetaUnifAV → Out.Laws → Out.Laws2 → HomExtDvr → Published.KernelFiniteFlatSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Pe : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty Pe) (p q : ℕ) (_ : CMLat hP p q) (k : IntermediateField ℚ ℂ), FiniteDimensional ℚ k →
  ∃ (K₁ : IntermediateField ℚ ℂ) (_ : NumberField K₁) (hk : KA l ≤ K₁) (ω : Bool → 𝓞 K₁) (C : ∀ b, Ell H (𝓞 K₁) (ω b)) (ε : Bool → ℤˣ) (h : Bool → (FU.Di i).La → (FU.Di i).La → OK H) (B : PAT H (Sp (𝓞 K₁))) (y : Sp K₁ ⟶ Xo.X) (t₀ : SAB H (Sp K₁)) (m : SABMap t₀ Xo.univ.t y) (m' : SABMap t₀ B.t (spMap (algebraMap (𝓞 K₁) K₁)))
    (ψ : ∀ b : Bool, PureType.lat hP (if b then H.rt0 else -H.rt0) → ((C b).P.A ⟶ B.t.G)) (ω' : Bool → ℂ) (C' : ∀ b, Ell H ℂ (ω' b)) (π : ∀ b, (C' b).P.A.left ⟶ (C b).P.A.left) (u₀ : ∀ b, HolUnif (C' b).P.A (C' b).P.L (C' b).P.g) (c : Bool → ℂ),
    k ≤ K₁ ∧ y ≫ Xo.s = spMap (IntermediateField.inclusion hk).toRingHom ∧ spMap (algebraMap K₁ ℂ) ≫ y = FU.u i Pe ∧
    ∀ b : Bool, 2 * ω' b - 1 = (if b then H.rt0 else -H.rt0) ∧ 0 < ((ε b : ℤ) : ℝ) * (ω' b).im ∧ IsKForm (FU.Di i) (ε b) (h b) ∧ IsFam (C b) B (h b) _ (ψ b) ∧ EllMap (C' b) (C b) ((algebraMap K₁ ℂ).comp (algebraMap (𝓞 K₁) K₁)) (π b) ∧ c b ≠ 0 ∧ PureType.IsQuadLattice (u₀ b).Λ H.d (c b) ∧
      ∀ a (z : ℂ) (x : Sp ℂ ⟶ t₀.G.left), x ≫ t₀.G.hom = spMap (algebraMap K₁ ℂ) → x ≫ m'.φ = ((u₀ b).ex (fun _ => c b * z)).left ≫ π b ≫ (ψ b a).left → x ≫ m.φ = (FU.ex i Pe (z • Pe a)).left := by
  intro hC hPt hU hL hL₂ hX hK E _ _ _ H D l Xo g ty FU i Pe hP p q Z k hkf
  have hB := hL.polBaseChange
  have hm := H.d_mod
  have : NeZero H.d := ⟨by omega⟩
  obtain ⟨χ, hχ⟩ := exists_isKroneckerChar (d := H.d) (by omega) (by omega)
  obtain ⟨M, _, ω, C, -, hω, hpr, -⟩ := GlobalTheory.T.exists_cmEllipticCurve_integers_with_period hC hU hL hX E H χ hχ H.rt0 H.sqrt_neg_disc_sq
  obtain ⟨K₀, hK₀, y₀, _, hy₀, hy₀'⟩ := GlobalTheory.T.exists_numberField_point_of_cmPeriodLattice hC hPt hU hL E H D l Xo g ty FU i Pe hP p q ⟨Z⟩

  obtain ⟨k₀, _, e₁, e₂, e₃⟩ : ∃ k₀ : IntermediateField ℚ ℂ, FiniteDimensional ℚ k₀ ∧ K₀ ≤ k₀ ∧ M ≤ k₀ ∧ k ≤ k₀ :=
    ⟨K₀ ⊔ M ⊔ k, inferInstance, le_sup_left.trans le_sup_left, le_sup_right.trans le_sup_left, le_sup_right⟩
  obtain ⟨C₀, φ₀, c₀⟩ := exists_ellMap hB E H _ ω C k₀
    ((IntermediateField.inclusion e₂).toRingHom.comp (algebraMap (𝓞 M) M))
  obtain ⟨C', φ, c'⟩ := exists_ellMap hB E H _ _ C₀ ℂ (algebraMap k₀ ℂ)
  obtain ⟨T, mT, -⟩ := exists_pat_univ Xo (spMap (IntermediateField.inclusion e₁).toRingHom ≫ y₀)
  obtain ⟨T', n, -⟩ := exists_pat_univ Xo (FU.u i Pe)
  obtain ⟨mT', hmT'⟩ := (Factor.ellMap_cancel_and_sabMap_cancel E H k₀ k₀ ℂ (RingHom.id _) (algebraMap k₀ ℂ)).2
    _ _ _ _ _ _ mT n (by rw [← Category.assoc, spMap_comp_spMap]; exact hy₀')
  obtain ⟨u₀, hu₀⟩ := PureType.exists_isThetaUnif hU C'.P
  obtain ⟨c, hc, hΛ⟩ := hpr C'.P (φ ≫ φ₀) ((EllComp.ellMap_comp E H _ _ C _ _ C₀ _ _ c₀).1 _ _ C' _ _ c').2.1 u₀
  generalize hω' : (algebraMap k₀ ℂ) (((IntermediateField.inclusion e₂).toRingHom.comp (algebraMap (𝓞 M) M)) ω) = ω'
    at C' φ c' u₀ hu₀ hΛ
  have hρ : ∀ b : Bool, 2 * cond b ω' (1 - ω') - 1 = if b then H.rt0 else -H.rt0 := fun b => by
    have : 2 * ω' - 1 = H.rt0 := hω' ▸ hω
    cases b
    · simp only [cond_false, Bool.false_eq_true, if_false]
      linear_combination -this
    · exact this
  choose ε hε using fun b => exists_sign (H := H) (hρ b) (by split_ifs <;> simp [H.sqrt_neg_disc_sq])
  choose h hh _ using fun b => GlobalTheory.T.exists_unique_cmHermitianLatticeForm E H (FU.Di i) (ε b)
  have fam : ∀ b : Bool, ∃ ψ : PureType.lat hP (if b then H.rt0 else -H.rt0) → (C'.P.A ⟶ T'.t.G),
      IsFam (twist C' b) T' (fun x y => h b x y) _ ψ ∧
      ∀ a (z : ℂ), (u₀.ex (fun _ => c * z) ≫ ψ a).left ≫ n.φ = (FU.ex i Pe (z • Pe a)).left := fun b => by
    rw [← hρ b]
    exact GlobalTheory.T.exists_cmCurve_homFamily_to_fibre_at_period hU hL E H D l Xo g ty FU i Pe hP _ (twist C' b) u₀ c T' n (ε b) _ hu₀ hc hΛ (hε b) (hh b)
  choose ψ' hψ' hex using fam
  choose k₁ hk₁ hle hdesc using fun b => GlobalTheory.T.cmFamily_descends_to_numberField hU hL E H k₀ _ (twist C₀ b) (FU.Di i) _ T _ _ (twist C' b) φ T'
    mT' (ψ' b) (ellMap_twist c' b) (hψ' b)

  obtain ⟨K₁, _, e₄⟩ : ∃ K₁ : IntermediateField ℚ ℂ, FiniteDimensional ℚ K₁ ∧ ∀ b, k₁ b ≤ K₁ := by
    have := hk₁ true
    have := hk₁ false
    exact ⟨k₁ true ⊔ k₁ false, inferInstance, fun b => by cases b; exacts [le_sup_right, le_sup_left]⟩
  have : NumberField K₁ := ⟨⟩
  have e₅ : k₀ ≤ K₁ := (hle true).trans (e₄ true)
  obtain ⟨C₁, φ₁, c₁⟩ := exists_ellMap hB E H _ ω C (𝓞 K₁)
    (RingOfIntegers.mapRingHom (IntermediateField.inclusion (e₂.trans e₅)).toRingHom)
  obtain ⟨C₂, φ₁₂, c₁₂⟩ := exists_ellMap hB E H _ _ C₁ K₁ (algebraMap (𝓞 K₁) K₁)
  obtain ⟨φ₂, c₂, -⟩ := (Factor.ellMap_cancel_and_sabMap_cancel E H (𝓞 M) k₀ K₁ _
    (IntermediateField.inclusion e₅).toRingHom).1 _ _ _ C C₀ C₂ φ₀ _ c₀
    ((EllComp.ellMap_comp E H _ _ C _ _ C₁ _ _ c₁).1 _ _ C₂ _ _ c₁₂)
  obtain ⟨φ₃, c₃, hφ₃⟩ := (Factor.ellMap_cancel_and_sabMap_cancel E H k₀ K₁ ℂ _ (algebraMap K₁ ℂ)).1
    _ _ _ C₀ C₂ C' φ₂ φ c₂ c'
  have hy : spMap (algebraMap K₁ ℂ) ≫ spMap (IntermediateField.inclusion (e₁.trans e₅)).toRingHom ≫ y₀ = FU.u i Pe := by
    rw [← Category.assoc, spMap_comp_spMap]; exact hy₀'
  obtain ⟨T₂, m, hg⟩ := exists_pat_univ Xo (spMap (IntermediateField.inclusion (e₁.trans e₅)).toRingHom ≫ y₀)
  obtain ⟨m₂, hm₂⟩ := (Factor.ellMap_cancel_and_sabMap_cancel E H k₀ k₀ K₁ (RingHom.id _)
    (IntermediateField.inclusion e₅).toRingHom).2 _ _ _ _ _ _ mT m (by rw [← Category.assoc, spMap_comp_spMap]; rfl)
  obtain ⟨m₃, hm₃⟩ := (Factor.ellMap_cancel_and_sabMap_cancel E H K₁ K₁ ℂ (RingHom.id _)
    (algebraMap K₁ ℂ)).2 _ _ _ _ _ _ m₂ mT' (by rw [spMap_comp_spMap]; rfl)
  have hn : m₃.φ ≫ m.φ = n.φ := by rw [← hm₂, ← Category.assoc, hm₃, hmT']
  choose ψ₂ hψ₂ hsq using fun b => hdesc b K₁ e₅ (e₄ b) _ (twist C₂ b) φ₂ φ₃ T₂ m₂ m₃ (ellMap_twist c₂ b)
    (ellMap_twist c₃ b) hφ₃ hm₃
  have hex₂ : ∀ b a (z : ℂ), ((u₀.ex fun _ => c * z).left ≫ φ₃ ≫ (ψ₂ b a).left) ≫ m.φ =
      (FU.ex i Pe (z • Pe a)).left := fun b a z => by
    rw [← hex, ← hn, ← Category.assoc _ m₃.φ, Over.comp_left, Category.assoc _ _ m₃.φ]
    exact congrArg (fun q => (_ ≫ q) ≫ m.φ) (hsq b a).symm
  have hpt : ∀ z : Fin C'.P.g → ℂ, ((u₀.ex z).left ≫ φ₃) ≫ C₂.P.A.hom = spMap (algebraMap K₁ ℂ) := fun z => by
    rw [Category.assoc, c₃.2.1.2.1.1.w, ← Category.assoc, Over.w]
    exact Category.id_comp _

  obtain ⟨bb, a, hspan⟩ := exists_pure_span Z (N := T₂.g) (by rw [hg, (FU.sig i).1, (FU.sig i).2])
  obtain ⟨B, m', -⟩ := GlobalTheory.T.principal_triple_extends_of_curve_homomorphisms hU hL hL₂ hX hK E H (𝓞 K₁) K₁ (algebraMap K₁ ℂ) C₁.P C₂.P φ₁₂ T₂
    (fun j => ψ₂ (bb j) (a j)) c₁₂.2.1 C₁.dim (fun j => ((hψ₂ (bb j)).1 (a j)).1)
    (ontoAt_of_exp m.cart _ hy (FU.ex i Pe) (FU.ex_add i Pe hP) (FU.ex_onto i Pe hP) _ hspan _ fun j z =>
      ⟨Over.homMk _ (hpt fun _ => c * z), by
        rw [← hex₂]
        simp only [Category.assoc]
        exact Category.assoc _ _ _⟩)
  choose ψ hψ hsq' using fun b => GlobalTheory.T.cmFamily_extends_over_dedekindDomain hL hX E H (𝓞 K₁) K₁ _ (twist C₁ b) (FU.Di i) _ B _ _ (twist C₂ b) φ₁₂
    T₂ m' (ψ₂ b) (ellMap_twist c₁₂ b) (hψ₂ b)
  refine ⟨K₁, inferInstance, hK₀.trans (e₁.trans e₅), _, twist C₁, ε, fun b x y => h b x y, B, _, T₂.t, m, m', ψ, _,
    twist C', fun _ => φ₃ ≫ φ₁₂, fun _ => u₀, fun _ => c, e₃.trans e₅, ?_, hy, fun b =>
      ⟨hρ b, hε b, hh b, hψ b, ellMap_twist ((EllComp.ellMap_comp E H _ _ C₁ _ _ C₂ _ _ c₁₂).1 _ _ C' _ _ c₃) b, hc, hΛ,
        fun a z x hx hx' => ?_⟩⟩
  · rw [Category.assoc, hy₀, spMap_comp_spMap]
    rfl
  · rw [← hex₂ b a z]
    congr 1
    refine m'.cart.1.hom_ext ?_ ?_
    · refine hx'.trans ?_
      simp only [Category.assoc]
      exact congrArg (fun q => _ ≫ φ₃ ≫ q) (hsq' b a).symm
    · rw [hx, ← hpt fun _ => c * z]
      simp only [Category.assoc]
      exact congrArg (fun q => _ ≫ φ₃ ≫ q) (Over.w (ψ₂ b a)).symm

end GlobalTheory.CM.PeriodModel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsGoodReductionModelCmPeriodFibreStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_goodReduction_model_cmPeriod_fibre : CMCurve → CMPoint → ThetaUnifAV → Out.Laws → Out.Laws2 → HomExtDvr → Published.KernelFiniteFlatSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Pe : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty Pe) (p q : ℕ) (_ : CMLat hP p q) (k : IntermediateField ℚ ℂ), FiniteDimensional ℚ k →
  ∃ (K₁ : IntermediateField ℚ ℂ) (_ : NumberField K₁) (hk : KA l ≤ K₁) (ω : Bool → 𝓞 K₁) (C : ∀ b, Ell H (𝓞 K₁) (ω b)) (ε : Bool → ℤˣ) (h : Bool → (FU.Di i).La → (FU.Di i).La → OK H) (B : PAT H (Sp (𝓞 K₁))) (y : Sp K₁ ⟶ Xo.X) (t₀ : SAB H (Sp K₁)) (m : SABMap t₀ Xo.univ.t y) (m' : SABMap t₀ B.t (spMap (algebraMap (𝓞 K₁) K₁)))
    (ψ : ∀ b : Bool, PureType.lat hP (if b then H.rt0 else -H.rt0) → ((C b).P.A ⟶ B.t.G)) (ω' : Bool → ℂ) (C' : ∀ b, Ell H ℂ (ω' b)) (π : ∀ b, (C' b).P.A.left ⟶ (C b).P.A.left) (u₀ : ∀ b, HolUnif (C' b).P.A (C' b).P.L (C' b).P.g) (c : Bool → ℂ),
    k ≤ K₁ ∧ y ≫ Xo.s = spMap (IntermediateField.inclusion hk).toRingHom ∧ spMap (algebraMap K₁ ℂ) ≫ y = FU.u i Pe ∧
    ∀ b : Bool, 2 * ω' b - 1 = (if b then H.rt0 else -H.rt0) ∧ 0 < ((ε b : ℤ) : ℝ) * (ω' b).im ∧ IsKForm (FU.Di i) (ε b) (h b) ∧ IsFam (C b) B (h b) _ (ψ b) ∧ EllMap (C' b) (C b) ((algebraMap K₁ ℂ).comp (algebraMap (𝓞 K₁) K₁)) (π b) ∧ c b ≠ 0 ∧ PureType.IsQuadLattice (u₀ b).Λ H.d (c b) ∧
      ∀ a (z : ℂ) (x : Sp ℂ ⟶ t₀.G.left), x ≫ t₀.G.hom = spMap (algebraMap K₁ ℂ) → x ≫ m'.φ = ((u₀ b).ex (fun _ => c b * z)).left ≫ π b ≫ (ψ b a).left → x ≫ m.φ = (FU.ex i Pe (z • Pe a)).left := by
  first | exact @GlobalTheory.CM.PeriodModel.exists_model | exact GlobalTheory.CM.PeriodModel.exists_model | (intros; apply GlobalTheory.CM.PeriodModel.exists_model <;> assumption)
end
