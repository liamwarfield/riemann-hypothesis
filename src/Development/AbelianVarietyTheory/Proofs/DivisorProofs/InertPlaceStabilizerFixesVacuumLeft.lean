module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceLatticeStabilizerVacuumScalarEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdditiveSwapOfTrivAxes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheaf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleTrivialOfSamePolarization

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceStabilizerFixesVacuumLeft
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceStabilizerFixesVacuumLeft
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.InertSphLeft

open GlobalTheory.InertSph

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem hTens_eq_left {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) {α β : Type} [Fintype α]
    [Fintype β] (JA : Matrix α α A) (JB : Matrix β β A) (x y : Matrix α β A) :
    hTens c JA JB x y = ∑ j, ∑ l, JB j l * (xᵀ * JA * y.map c) j l := by
  simp only [hTens, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm, Finset.sum_comm (γ := β)]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem symp_mul_left {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
    (c : A →ₐ[R] A) {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] (ξ : A) (JA : Matrix α α A)
    (JB : Matrix β β A) (g : Matrix α α A) (hg : gᵀ * JA * g.map c = JA) (x : Matrix α β A) :
    symp c ξ JA JB (g * x) (g * x) = symp c ξ JA JB x x := by
  have e : (g * x)ᵀ * JA * (g * x).map c = xᵀ * JA * x.map c := by
    have hm : (g * x).map c = g.map c * x.map c := Matrix.map_mul (f := c.toRingHom)
    rw [hm, Matrix.transpose_mul]
    calc xᵀ * gᵀ * JA * (g.map c * x.map c) = xᵀ * (gᵀ * JA * g.map c) * x.map c := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hg]
  unfold symp
  rw [hTens_eq_left, hTens_eq_left, e]

variable {σ : E →ₐ[F] E}

theorem vecMulVec_mem_latAtV_left {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F)) {y : Fin d → E} (hy : y ∈ W.L)
    {z : Fin n → AE F E} (hz : z ∈ latAt X v) :
    Matrix.vecMulVec z (fun i => inclR (F := F) (AF F) (y i)) ∈ latAtV X W v := by
  let f : (Fin n → AE F E) →+ Matrix (Fin n) (Fin d) (AE F E) :=
    { toFun := fun z => Matrix.vecMulVec z (fun i => inclR (F := F) (AF F) (y i))
      map_zero' := by ext i j; simp [Matrix.vecMulVec_apply]
      map_add' := fun z z' => by ext i j; simp [Matrix.vecMulVec_apply, add_mul] }
  have : latAt X v ≤ (latAtV X W v).comap f := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro z ⟨a, ha, hai, x, hx, rfl⟩
    refine AddSubgroup.subset_closure ⟨a, ha, hai, x, hx, y, hy, ?_⟩
    ext i j
    simp only [f, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.vecMulVec_apply, Pi.smul_apply, Matrix.smul_apply, incM,
      Matrix.map_apply, map_mul, Algebra.smul_def, Pi.mul_apply, Pi.algebraMap_apply]
    ring
  exact this hz

theorem mul_left_inv_mem_latAtV {n d : ℕ} (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F)) {g : UA σ X.J}
    (hg : g ∈ KAt σ X v) {γ : Matrix (Fin n) (Fin d) (AE F E)} (hγ : γ ∈ latAtV X W v) :
    mat g⁻¹ * γ ∈ latAtV X W v := by
  let f : Matrix (Fin n) (Fin d) (AE F E) →+ Matrix (Fin n) (Fin d) (AE F E) :=
    { toFun := fun γ => mat g⁻¹ * γ
      map_zero' := by simp
      map_add' := fun γ γ' => by simp [Matrix.mul_add] }
  have : latAtV X W v ≤ (latAtV X W v).comap f := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro z ⟨a, ha, hai, x, hx, y, hy, rfl⟩
    show mat g⁻¹ * (a • incM F (Matrix.vecMulVec x y)) ∈ latAtV X W v
    have hz : (a • fun i => inclR (F := F) (AF F) (x i)) ∈ latAt X v :=
      AddSubgroup.subset_closure ⟨a, ha, hai, x, hx, rfl⟩
    have e : mat g⁻¹ * (a • incM F (Matrix.vecMulVec x y)) =
        Matrix.vecMulVec (mat g⁻¹ *ᵥ (a • fun i => inclR (F := F) (AF F) (x i)))
          (fun j => inclR (F := F) (AF F) (y j)) := by
      ext i j
      simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.smul_apply, Matrix.mulVec,
        dotProduct, Pi.smul_apply, incM, Matrix.map_apply, map_mul, Algebra.smul_def, Pi.mul_apply, Pi.algebraMap_apply,
        Finset.sum_mul]
      refine Finset.sum_congr rfl fun l _ => ?_
      ring
    rw [e]
    exact vecMulVec_mem_latAtV_left X W v hy (hg.2 _ hz).2
  exact this hγ

theorem acts_vacCond_of_mem_KAt_left : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (θ : 𝓞 E), (θ : E) + σ θ = 1 → ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V' v,
      ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v),
        Acts (evFin F v) (om' (k, 1)) φ φ₁ →
        (∀ γ ∈ latAtV G.V' G.W v, Acts (evFin F v) (G.M'.co.rho B.ψ γ) φ
          (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) γ γ) • φ)) →
        (∀ γ ∈ latAtV G.V' G.W v, Acts (evFin F v) (G.M'.co.rho B.ψ γ) φ₁
          (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) γ γ) • φ₁)) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v θ hθ k hk φ hφ φ₁ hφ₁ hAct hvac γ hγ r hr
  have hS := IsUWeilPair.isUSplitting hTr.weil'
  have etens : ∀ (c : ℂ) (f : (Fin a' × Fin (a + a') → Fv F v) → ℂ),
      tens (evFin F v) (c • f) r = c • tens (evFin F v) f r := fun c f => by
    funext x; simp only [tens, Pi.smul_apply, smul_eq_mul]; ring
  by_cases h0 : φ₁ = 0
  · subst h0
    have e0 : tens (evFin F v) (0 : (Fin a' × Fin (a + a') → Fv F v) → ℂ) r = 0 := by
      funext x; simp [tens]
    rw [smul_zero, e0]
    funext x
    simp [Darboux.rho, schr]
  have hrφ : Rest (evFin F v) φ r := GlobalTheory.T.complementaryAdelicSchwartz_of_nonzero_local v φ₁ φ r h0 hφ hr
  set γ' := actAB (cA σ) (k⁻¹, (1 : UA σ G.W.J)) γ
  have eγ' : γ' = mat k⁻¹ * γ := by
    simp [γ', actAB, mat]
  have hγ' : γ' ∈ latAtV G.V' G.W v := by
    rw [eγ']; exact mul_left_inv_mem_latAtV G.V' G.W v hk hγ
  have hsym : symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) γ' γ' =
      symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F G.V'.J) (incM F G.W.J) γ γ := by
    rw [eγ']
    exact symp_mul_left (cA σ) _ _ _ (mat k⁻¹) (k⁻¹).2 γ
  have e1 : actAB (cA σ) (k, (1 : UA σ G.W.J)) γ' = γ := by
    simp only [γ', actAB]
    simp [← Matrix.mul_assoc]
  have hi := hS.impl (k, (1 : UA σ G.W.J)) γ' _ hrφ.2
  rw [e1] at hi
  rw [← hAct r hrφ, ← hi, hvac γ' hγ' r hrφ, hsym, etens, map_smul, hAct r hrφ, etens]

end GlobalTheory.InertSphLeft

namespace GlobalTheory.InertSphLeft

theorem vac_fixed_left : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V' v, Acts (evFin F v) (om' (k, 1)) (G.M'.vac v) (G.M'.vac v) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v w hw hv k hk
  obtain ⟨hSB, -, θ, hθ, hvac⟩ := hTr.geo.hM'.vac v
  obtain ⟨S, hS⟩ := GlobalTheory.T.weilRepresentationLocality_unitaryGroupV' B G X om om' hTr v k hk.1
  obtain ⟨hφ₁, hact⟩ := hS _ hSB
  have h1 := acts_vacCond_of_mem_KAt_left F E σ B a a' G X om om' hTr v θ hθ k hk _ hSB _ hφ₁ hact hvac
  obtain ⟨c, hc'⟩ := GlobalTheory.T.inertPlace_schwartzBruhat_vacuumCondition_eq_smul F E σ B a a' G X om om' hTr v w hw θ hθ hvac _ hφ₁ h1
  rw [hc'] at hact
  have hc := GlobalTheory.T.inertPlace_latticeStabilizer_vacuumScalar_eq_one F E σ B a a' G X om om' hTr v w hw hv k hk c hact
  rwa [hc, one_smul] at hact

end GlobalTheory.InertSphLeft
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceStabilizerFixesVacuumLeftStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPlace_stabilizer_fixes_vacuum_left : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl (F := F)) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.V' v, Acts (evFin F v) (om' (k, 1)) (G.M'.vac v) (G.M'.vac v) := by
  first | exact @GlobalTheory.InertSphLeft.vac_fixed_left | exact GlobalTheory.InertSphLeft.vac_fixed_left | (intros; apply GlobalTheory.InertSphLeft.vac_fixed_left <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GmSpMapUnitOn
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.PsiMono
variable {V V₁ : Type} [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁]

def fracPt (ρ : V →+* V₁) (hρ : Function.Injective ρ) : (TK V₁).left ⟶ (TK V).left :=
  spMap (IsFractionRing.map (K := FractionRing V) (L := FractionRing V₁) hρ)

theorem fracPt_comp (ρ : V →+* V₁) (hρ : Function.Injective ρ) : fracPt ρ hρ ≫ jK V = jK V₁ ≫ spMap ρ := by
  simp only [fracPt, spMap, jK, TK, Over.mk_hom, ← Spec.map_comp]
  congr 1
  ext x
  simp [IsFractionRing.map, IsLocalization.map_eq]

theorem gm_spMap_unitOn {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (z : Sp R') (k : Rˣ) :
    gm (spMap f) z ⊤ (unitOn k) = gm (𝟙 _) z ⊤ (unitOn (Units.map f.toMonoidHom k)) := by
  have h := gm_pull (𝟙 _) (spMap f) z ⊤ trivial (unitOn k)
  rw [Category.id_comp] at h
  refine h.symm.trans (congrArg _ ?_)
  ext
  have e := congrArg (fun g => g.hom (k : R)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
  simp only [unitOn, pullU, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
  exact e.symm

theorem val_scaleGen {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (c : Γ(Y, ⊤)ˣ) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    val (scaleGen t c) r z J = gm r z ⊤ c * val t r z J :=
  gm_scaleGen t c r z _ (hJ.mem φ r)

theorem prod_zpow_swap {F : Type} [Field F] {I C : Type} [Fintype I] [Fintype C] (x : I → F) (e : C → I → ℤ)
    (w : C → ℤ) (h : ∀ c, ∏ i, x i ^ e c i ≠ 0) :
    ∏ c, (∏ i, x i ^ e c i) ^ w c = ∏ i, x i ^ ∑ c, w c * e c i := by
  classical
  have hz : ∀ i, x i = 0 → ∀ c, e c i = 0 := by
    intro i hi c
    by_contra hne
    exact h c (Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hi, zero_zpow _ hne]))
  set y : I → F := fun i => if x i = 0 then 1 else x i with hy
  have hy0 : ∀ i, y i ≠ 0 := fun i => by
    by_cases hi : x i = 0 <;> simp [hy, hi]
  have hxy : ∀ i (n : ℤ), (x i = 0 → n = 0) → x i ^ n = y i ^ n := by
    intro i n hn
    by_cases hi : x i = 0
    · rw [hn hi]; simp
    · simp [hy, hi]
  have l1 : ∀ c, ∏ i, x i ^ e c i = ∏ i, y i ^ e c i :=
    fun c => Finset.prod_congr rfl fun i _ => hxy i _ fun hi => hz i hi c
  have l2 : ∀ i, x i ^ ∑ c, w c * e c i = y i ^ ∑ c, w c * e c i := fun i => hxy i _ fun hi => by
    simp [hz i hi]
  simp_rw [l1, l2, ← Finset.prod_zpow, ← zpow_mul]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun i _ => ?_
  have key : ∀ (a : F), a ≠ 0 → ∀ (s : Finset C) (n : C → ℤ), ∏ c ∈ s, a ^ n c = a ^ ∑ c ∈ s, n c := by
    intro a ha s n
    induction s using Finset.induction_on with
    | empty => simp
    | insert c s hc ih => rw [Finset.prod_insert hc, Finset.sum_insert hc, ih, zpow_add₀ ha]
  rw [key _ (hy0 i)]
  exact congrArg _ (Finset.sum_congr rfl fun c _ => mul_comm _ _)

abbrev fracOver (ρ : V →+* V₁) (hρ : Function.Injective ρ) : Over (Sp V) := Over.mk (fracPt ρ hρ ≫ jK V)

theorem psi_val (W : Matrix (Fin 8) (Fin 8) ℤ) (Q : Data V) (ρ : V →+* V₁) (hρ : Function.Injective ρ) (D : DegPre V₁)
    (e : (Fin 8 → Q.X) ≃+ D.X) (pr : Fin 8 → (D.P.A ⟶ (Over.pullback (spMap ρ)).obj Q.B))
    (w : LB.Iso D.P.L (LB.LinComb Q.M.L (K := (Fin 8 × Fin 8) × Fin 4)
      (fun k => lamPts (pr k.1.1) (pr k.1.2) k.2 ≫ pullback.fst Q.B.hom (spMap ρ)) (fun k => -(W k.1.1 k.1.2 * negε k.2))))
    (hw : ∀ κ : (TK V₁).left ⟶ (TK V).left, κ ≫ jK V = jK V₁ ≫ spMap ρ → ∀ mu z J J', Good Q.M.L z J → Good D.P.L z J' →
      val (D.psi (e mu)) (𝟙 _) z J' =
        gm (D.xK (e mu)) z _ (w.s (fun k : (Fin 8 × Fin 8) × Fin 4 => J (D.xK (e mu) ≫ lamPts (pr k.1.1) (pr k.1.2) k.2 ≫
            pullback.fst Q.B.hom (spMap ρ)), J' (D.xK (e mu)))) *
          ∏ a, ∏ b, val (Q.tau (mu a) (mu b)) κ z J ^ W a b)
    (τ₀ : Gens Q) {n : ℕ} (s : Fin n → V) (ε : Fin n → LinearMap.BilinForm ℤ Q.X) (hτ : TauIn Q τ₀ s ε)
    {W₀ : Type} [CommRing W₀] (ib : W₀ →+* V) (B₀ : Over (Sp W₀)) [GrpObj B₀] [IsCommMonObj B₀] (M₀ : LB B₀.left)
    (c₀ : Q.X → (𝟙_ (Over (Sp W₀)) ⟶ B₀)) (τ₁ : ∀ a b : Q.X, LB.Gen (LB.LinComb M₀ (lamPts (c₀ a) (c₀ b)) negε))
    (β₂ : (G2 Q.B).left ⟶ (G2 B₀).left) (w₀ : LB.Iso (abelian₂ Q.B Q.M.L) ((abelian₂ B₀ M₀).pull β₂))
    (h₀ : ∀ (T : Over (Sp V)) (a b : Q.X) z J J', Good M₀ z J → Good Q.M.L z J' →
      val (τ₀ a b) (toUnit T).left z J' =
        lamVal w₀ (lift (toUnit T ≫ Q.c a) (toUnit T ≫ Q.c b)).left z J J' * val (τ₁ a b) (T.hom ≫ spMap ib) z J)
    (mu : Fin 8 → Q.X) (z : (TK V₁).left) (J : ((TK V₁).left ⟶ Q.B.left) → Q.M.L.ι)
    (J' : ((TK V₁).left ⟶ D.P.A.left) → D.P.L.ι) (J₀ : ((TK V₁).left ⟶ B₀.left) → M₀.ι)
    (hJ : Good Q.M.L z J) (hJ' : Good D.P.L z J') (hJ₀ : Good M₀ z J₀) :
    ∃ u : (FractionRing V₁)ˣ, (u : FractionRing V₁) = ∏ i, algebraMap V₁ (FractionRing V₁) (ρ (s i)) ^ qW W (ε i) mu ∧
      val (D.psi (e mu)) (𝟙 _) z J' =
        gm (D.xK (e mu)) z _ (w.s (fun k : (Fin 8 × Fin 8) × Fin 4 => J (D.xK (e mu) ≫ lamPts (pr k.1.1) (pr k.1.2) k.2 ≫
            pullback.fst Q.B.hom (spMap ρ)), J' (D.xK (e mu)))) *
          (∏ a, ∏ b, (lamVal (Z := (TK V₁).left) w₀ (lift (toUnit (fracOver ρ hρ) ≫ Q.c (mu a)) (toUnit (fracOver ρ hρ) ≫ Q.c (mu b))).left
              z J₀ J * val (τ₁ (mu a) (mu b)) ((fracPt ρ hρ ≫ jK V) ≫ spMap ib) z J₀) ^ W a b) *
          gm (𝟙 _) z ⊤ (unitOn u) := by
  classical
  have hL : Q.M.L.IsLB := Q.M.isLB
  choose k hk hkv using fun a b => (hτ a b).2
  have htau : ∀ a b, val (Q.tau a b) (fracPt ρ hρ) z J =
      gm (fracPt ρ hρ) z ⊤ (unitOn (k a b)) * val (τ₀ a b) (fracPt ρ hρ ≫ jK V) z J := by
    intro a b
    let t₁ := scaleGen (LB.pullGen Q.M.L (lamPts (Q.c a) (Q.c b)) negε (τ₀ a b) (toUnit (TK V)).left) (unitOn (k a b))
    have hc : LB.Gen.Corr Q.M.L _ _ _ _ (Q.tau a b) t₁ := corr_of_val hL fun y J₁ hJ₁ => by
      rw [val_scaleGen _ _ _ _ hJ₁, val_pull hJ₁, Category.id_comp]
      exact hkv a b y J₁ hJ₁
    rw [val_corr hJ hc (fracPt ρ hρ), val_scaleGen _ _ _ _ hJ, val_pull hJ]
    rfl
  have hunit : ∀ a b, gm (fracPt ρ hρ) z ⊤ (unitOn (k a b)) =
      gm (𝟙 _) z ⊤ (unitOn (Units.map (IsFractionRing.map (K := FractionRing V) (L := FractionRing V₁) hρ).toMonoidHom
        (k a b))) := fun a b => gm_spMap_unitOn _ z _
  have hbase : ∀ a b, val (τ₀ a b) (fracPt ρ hρ ≫ jK V) z J =
      lamVal (Z := (TK V₁).left) w₀ (lift (toUnit (fracOver ρ hρ) ≫ Q.c a) (toUnit (fracOver ρ hρ) ≫ Q.c b)).left z J₀ J *
        val (τ₁ a b) ((fracPt ρ hρ ≫ jK V) ≫ spMap ib) z J₀ := fun a b => h₀ (fracOver ρ hρ) a b z J₀ J hJ₀ hJ
  have hfk : ∀ a b, ((Units.map (IsFractionRing.map (K := FractionRing V) (L := FractionRing V₁) hρ).toMonoidHom
      (k a b) : (FractionRing V₁)ˣ) : FractionRing V₁) =
        ∏ i, algebraMap V₁ (FractionRing V₁) (ρ (s i)) ^ ε i a b := by
    intro a b
    show IsFractionRing.map (K := FractionRing V) (L := FractionRing V₁) hρ (k a b : FractionRing V) = _
    rw [hk a b, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_zpow₀]
    simp [IsFractionRing.map, IsLocalization.map_eq]
  refine ⟨∏ a, ∏ b, Units.map (IsFractionRing.map (K := FractionRing V) (L := FractionRing V₁) hρ).toMonoidHom
      (k (mu a) (mu b)) ^ W a b, ?_, ?_⟩
  · simp_rw [Units.coe_prod, Units.val_zpow_eq_zpow_val, hfk]
    have hne : ∀ c : Fin 8 × Fin 8, ∏ i, algebraMap V₁ (FractionRing V₁) (ρ (s i)) ^ ε i (mu c.1) (mu c.2) ≠ 0 :=
      fun c => by rw [← hfk]; exact Units.ne_zero _
    have e := prod_zpow_swap (fun i => algebraMap V₁ (FractionRing V₁) (ρ (s i)))
      (fun (c : Fin 8 × Fin 8) i => ε i (mu c.1) (mu c.2)) (fun (c : Fin 8 × Fin 8) => W c.1 c.2) hne
    rw [Fintype.prod_prod_type] at e
    simp only [Fintype.sum_prod_type] at e
    rw [e]
    rfl
  · rw [hw (fracPt ρ hρ) (fracPt_comp ρ hρ) mu z J J' hJ hJ', _root_.mul_assoc]
    congr 1
    clear hw h₀ hkv hk hτ hfk
    simp only [htau, hunit, hbase]
    simp only [unitOn, map_prod, map_zpow, mul_zpow, Finset.prod_mul_distrib]
    exact _root_.mul_comm _ _

theorem psi_val_of (W : Matrix (Fin 8) (Fin 8) ℤ) (Q : Data V) (ρ : V →+* V₁) (hρ : Function.Injective ρ) (D : DegPre V₁)
    (e : (Fin 8 → Q.X) ≃+ D.X) (hS : SharpRef W Q ρ D e) (τ₀ : Gens Q) {n : ℕ} (s : Fin n → V)
    (ε : Fin n → LinearMap.BilinForm ℤ Q.X) (hτ : TauIn Q τ₀ s ε) {W₀ : Type} [CommRing W₀] (ib : W₀ →+* V)
    (hB : FromBase Q τ₀ ib) :
    ∃ (pr : Fin 8 → (D.P.A ⟶ (Over.pullback (spMap ρ)).obj Q.B))
      (w : LB.Iso D.P.L (LB.LinComb Q.M.L (K := (Fin 8 × Fin 8) × Fin 4)
        (fun k => lamPts (pr k.1.1) (pr k.1.2) k.2 ≫ pullback.fst Q.B.hom (spMap ρ)) (fun k => -(W k.1.1 k.1.2 * negε k.2)))),
      (∀ a, IsMonHom (pr a)) ∧
      (∀ (T : Over (Sp V₁)) (y : Fin 8 → (T ⟶ (Over.pullback (spMap ρ)).obj Q.B)), ∃! x : T ⟶ D.P.A, ∀ a, x ≫ pr a = y a) ∧
      w.IsGen ∧ (∀ mu a, (D.c (e mu) ≫ pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) = spMap ρ ≫ (Q.c (mu a)).left) ∧
      ∃ (B₀ : Over (Sp W₀)) (_ : GrpObj B₀) (_ : IsCommMonObj B₀) (M₀ : LB B₀.left) (c₀ : Q.X → (𝟙_ (Over (Sp W₀)) ⟶ B₀))
        (τ₁ : ∀ a b : Q.X, LB.Gen (LB.LinComb M₀ (lamPts (c₀ a) (c₀ b)) negε))
        (β : Q.B.left ⟶ B₀.left) (β₂ : (G2 Q.B).left ⟶ (G2 B₀).left)
        (w₀ : LB.Iso (abelian₂ Q.B Q.M.L) ((abelian₂ B₀ M₀).pull β₂)),
        IsAbelianScheme B₀ ∧ M₀.IsLB ∧ IsGrpPullback Q.B B₀ (spMap ib) β ∧ IsSquare β β₂ ∧ w₀.IsGen ∧
        (∀ a, (Q.c a).left ≫ β = spMap ib ≫ (c₀ a).left) ∧ (∀ a b, (τ₁ a b).IsGen) ∧
        (∀ (T : Over (Sp V)) (a b : Q.X) z J J', Good M₀ z J → Good Q.M.L z J' →
          val (τ₀ a b) (toUnit T).left z J' =
            lamVal w₀ (lift (toUnit T ≫ Q.c a) (toUnit T ≫ Q.c b)).left z J J' * val (τ₁ a b) (T.hom ≫ spMap ib) z J) ∧
        ∀ (mu : Fin 8 → Q.X) (z : (TK V₁).left) (J : ((TK V₁).left ⟶ Q.B.left) → Q.M.L.ι)
          (J' : ((TK V₁).left ⟶ D.P.A.left) → D.P.L.ι) (J₀ : ((TK V₁).left ⟶ B₀.left) → M₀.ι),
          Good Q.M.L z J → Good D.P.L z J' → Good M₀ z J₀ →
          ∃ u : (FractionRing V₁)ˣ,
            (u : FractionRing V₁) = ∏ i, algebraMap V₁ (FractionRing V₁) (ρ (s i)) ^ qW W (ε i) mu ∧
            val (D.psi (e mu)) (𝟙 _) z J' =
              gm (D.xK (e mu)) z _ (w.s (fun k : (Fin 8 × Fin 8) × Fin 4 => J (D.xK (e mu) ≫ lamPts (pr k.1.1) (pr k.1.2) k.2 ≫
                  pullback.fst Q.B.hom (spMap ρ)), J' (D.xK (e mu)))) *
                (∏ a, ∏ b, (lamVal (Z := (TK V₁).left) w₀
                    (lift (toUnit (fracOver ρ hρ) ≫ Q.c (mu a)) (toUnit (fracOver ρ hρ) ≫ Q.c (mu b))).left
                    z J₀ J * val (τ₁ (mu a) (mu b)) ((fracPt ρ hρ ≫ jK V) ≫ spMap ib) z J₀) ^ W a b) *
                gm (𝟙 _) z ⊤ (unitOn u) := by
  obtain ⟨pr, w, h1, h2, h3, h4, hw⟩ := hS
  obtain ⟨B₀, _, _, M₀, c₀, τ₁, β, β₂, w₀, g1, g2, g3, g4, g5, g6, g7, h₀⟩ := hB
  exact ⟨pr, w, h1, h2, h3, h4, B₀, inferInstance, inferInstance, M₀, c₀, τ₁, β, β₂, w₀, g1, g2, g3, g4, g5, g6, g7, h₀,
    fun mu z J J' J₀ hJ hJ' hJ₀ => psi_val W Q ρ hρ D e pr w hw τ₀ s ε hτ ib B₀ M₀ c₀ τ₁ β₂ w₀ h₀ mu z J J' J₀ hJ hJ' hJ₀⟩

end GlobalTheory.Poinc.PsiMono

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSquareAffineH1Vanish
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSquareAffineH1Vanish
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Obs

theorem sq_abelian_and_affine_H1 : ∀ (R : Type) [CommRing R], (∀ (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → IsAbelianScheme (A ⊗ A) ∧ SmoothOfRelativeDimension (g + g) (A ⊗ A).hom) ∧ ∀ (X : Scheme.{0}) [IsAffine X] (s : X ⟶ Sp R) (c : HO1 s), c = 0 := by
  intro R _
  refine ⟨fun A _ g hA hg ↦ ⟨ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA, ?_⟩, fun X _ s c ↦ ?_⟩
  · haveI := hg
    haveI : SmoothOfRelativeDimension g (Limits.pullback.fst A.hom A.hom) :=
      (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
        (IsPullback.of_hasPullback _ _).flip hg
    exact inferInstanceAs (SmoothOfRelativeDimension (g + g) (Limits.pullback.fst A.hom A.hom ≫ A.hom))
  · let T₀ : AffOp X := Opposite.op ⟨⊤, isAffineOpen_top X⟩
    have h : Limits.IsInitial T₀ := Limits.IsInitial.ofUniqueHom
      (fun U ↦ (homOfLE (show U.unop ≤ ⟨⊤, isAffineOpen_top X⟩ from le_top (a := U.unop.1))).op) fun _ _ ↦ rfl
    exact H1.eq_zero_of_isInitial _ h c

end GlobalTheory.Obs
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSquareAffineH1VanishStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_square_affine_h1_vanish : ∀ (R : Type) [CommRing R], (∀ (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → IsAbelianScheme (A ⊗ A) ∧ SmoothOfRelativeDimension (g + g) (A ⊗ A).hom) ∧ ∀ (X : Scheme.{0}) [IsAffine X] (s : X ⟶ Sp R) (c : HO1 s), c = 0 := by
  first | exact @GlobalTheory.Obs.sq_abelian_and_affine_H1 | exact GlobalTheory.Obs.sq_abelian_and_affine_H1 | (intros; apply GlobalTheory.Obs.sq_abelian_and_affine_H1 <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TheoremOfSquareCechPicardTranslates
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TheoremOfSquareCechPicardTranslates
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SquareSym

theorem lam_mul_left {S : Scheme.{0}} [IsLocallyNoetherian S] {A : Over S} [GrpObj A] (hA : IsAbelianScheme A)
    (c : Pic A.left) {Y : Over S} (a a' x : Y ⟶ A) : lam c (a * a') x = lam c a x + lam c a' x := by
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  have hP : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  have e : ∀ (Y : Over S) (a b : Y ⟶ A), evc hP a b = lam (cls L hL) a b := fun Y a b ↦ by
    rw [evc, show cls _ hP = lam (cls L hL) (fst A A) (snd A A) from cls_cube_two hL _ _ hP, pull_lam, lift_fst,
      lift_snd]
  have h := GlobalTheory.CubeNoeth.isAdditive_of_triv_axes hA hA hP
    (by rw [triv_ev_iff hP, e, lam_one_left]) (by rw [triv_ev_iff hP, e, lam_one_right])
  simpa only [e] using (isAdditive_iff hP).1 h Y a a' x

theorem pull_mul_add_pull_mul_inv : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (c : Pic A.left) (Y : Over S) (x a : Y ⟶ A), GlobalTheory.CechPic.pull (x * a).left c + GlobalTheory.CechPic.pull (x * a⁻¹).left c = 2 • GlobalTheory.CechPic.pull (x).left c + GlobalTheory.CechPic.pull (a).left c + GlobalTheory.CechPic.pull (a⁻¹).left c - 2 • GlobalTheory.CechPic.pull ((1 : Y ⟶ A)).left c := by
  intro S _ A _ hA c Y x a
  haveI := hA.comm
  have h := lam_mul_left hA c a a⁻¹ x
  rw [mul_inv_cancel, lam_one_left, lam_comm c a x, lam_comm c a⁻¹ x, lam, lam] at h
  rw [← sub_eq_zero, h]
  abel

end GlobalTheory.SquareSym
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TheoremOfSquareCechPicardTranslatesStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theorem_of_square_cechPicard_translates : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (c : Pic A.left) (Y : Over S) (x a : Y ⟶ A), GlobalTheory.CechPic.pull (x * a).left c + GlobalTheory.CechPic.pull (x * a⁻¹).left c = 2 • GlobalTheory.CechPic.pull (x).left c + GlobalTheory.CechPic.pull (a).left c + GlobalTheory.CechPic.pull (a⁻¹).left c - 2 • GlobalTheory.CechPic.pull ((1 : Y ⟶ A)).left c := by
  first | exact @GlobalTheory.SquareSym.pull_mul_add_pull_mul_inv | exact GlobalTheory.SquareSym.pull_mul_add_pull_mul_inv | (intros; apply GlobalTheory.SquareSym.pull_mul_add_pull_mul_inv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasicoherentHomFromAffine
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite

namespace GlobalTheory.Glue

variable {T : Scheme.{0}} {F G : T.Modules}

theorem le_iSup_affine (U : T.Opens) :
    U ≤ ⨆ k : {W : T.Opens // IsAffineOpen W ∧ W ≤ U}, k.1 := by
  intro x hx
  obtain ⟨W, hW, hxW, hWU⟩ := (Opens.isBasis_iff_nbhd.mp T.isBasis_affineOpens) hx
  exact Opens.mem_iSup.2 ⟨⟨W, hW, hWU⟩, hxW⟩

variable (j : ∀ V : T.Opens, IsAffineOpen V → Γ(F, V) →ₗ[Γ(T, V)] Γ(G, V))
  (hj : ∀ (V V' : T.Opens) (hV : IsAffineOpen V) (hV' : IsAffineOpen V') (h : V' ≤ V)
    (s : Γ(F, V)), j V' hV' (GlobalTheory.Twist.resM F h s) = GlobalTheory.Twist.resM G h (j V hV s))


include hj in
theorem agree {U W W' V : T.Opens} (hW : IsAffineOpen W) (hW' : IsAffineOpen W') (hWU : W ≤ U)
    (hW'U : W' ≤ U) (h₁ : V ≤ W) (h₂ : V ≤ W') (s : Γ(F, U)) :
    GlobalTheory.Twist.resM G h₁ (j W hW (GlobalTheory.Twist.resM F hWU s)) =
      GlobalTheory.Twist.resM G h₂ (j W' hW' (GlobalTheory.Twist.resM F hW'U s)) := by
  refine GlobalTheory.Twist.sec_ext_of_cover (fun k : {Z : T.Opens // IsAffineOpen Z ∧ Z ≤ V} => k.1)
    (fun k => k.2.2) (le_iSup_affine V) fun k => ?_
  rw [GlobalTheory.Twist.resM_resM, GlobalTheory.Twist.resM_resM, ← hj _ _ hW k.2.1, ← hj _ _ hW' k.2.1,
    GlobalTheory.Twist.resM_resM, GlobalTheory.Twist.resM_resM]

include hj in
theorem exists_glue (U : T.Opens) (s : Γ(F, U)) :
    ∃ t : Γ(G, U), ∀ (W : T.Opens) (hW : IsAffineOpen W) (hWU : W ≤ U),
      GlobalTheory.Twist.resM G hWU t = j W hW (GlobalTheory.Twist.resM F hWU s) := by
  obtain ⟨t, ht⟩ := GlobalTheory.Twist.exists_sec_of_cover
    (fun k : {Z : T.Opens // IsAffineOpen Z ∧ Z ≤ U} => k.1) (fun k => k.2.2) (le_iSup_affine U)
    (fun k => j k.1 k.2.1 (GlobalTheory.Twist.resM F k.2.2 s))
    fun k l => agree j hj k.2.1 l.2.1 k.2.2 l.2.2 _ _ s
  exact ⟨t, fun W hW hWU => ht ⟨W, hW, hWU⟩⟩

def glue (U : T.Opens) (s : Γ(F, U)) : Γ(G, U) := Classical.choose (exists_glue j hj U s)


end GlobalTheory.Glue
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedPointOverLabelPowRNEqOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedPointOverLabelPowRNEqOne
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LabelTorsion

theorem pt_nsmul {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} (ρ : S.Real) (b : S.Gam)
    (n : ℕ) : ρ.pt (n • b) = ρ.pt b ^ n := by
  have h0 : ρ.pt 0 = 1 := by
    have h := ρ.pt_add 0 0
    rw [add_zero] at h
    exact left_eq_mul.mp h
  induction n with
  | zero => rw [zero_smul, pow_zero, h0]
  | succ n ih => rw [succ_nsmul, ρ.pt_add, ih, pow_succ]

theorem pt_pow_eq_one {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} (ρ : S.Real) (b : S.Gam) :
    ρ.pt b ^ (S.r * S.N) = 1 := by
  have h : (S.r * S.N) • b = 0 • b := by
    funext i
    rw [Pi.smul_apply, Pi.smul_apply, zero_smul, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  rw [← pt_nsmul, h, pt_nsmul, pow_zero]

theorem pow_eq_one_of_over_label : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (b : S.Gam) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), x.left ≫ u.φ = spMap y₀ ≫ (ρ.pt b).left → x ^ (S.r * S.N) = 1 := by
  intro o Ω _ _ _ S ρ p _ y₀ u b x hx
  exact GlobalTheory.FrameMove.pow_eq_one_of (T := baseOver (Sp S.R)) (x := ρ.pt b) u.cart hx (pt_pow_eq_one ρ b)

end GlobalTheory.LabelTorsion
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedPointOverLabelPowRNEqOneStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformised_point_over_label_pow_rN_eq_one : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (b : S.Gam) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), x.left ≫ u.φ = spMap y₀ ≫ (ρ.pt b).left → x ^ (S.r * S.N) = 1 := by
  first | exact @GlobalTheory.LabelTorsion.pow_eq_one_of_over_label | exact GlobalTheory.LabelTorsion.pow_eq_one_of_over_label | (intros; apply GlobalTheory.LabelTorsion.pow_eq_one_of_over_label <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiValueFractionRingOfPsiCoord
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiValueFractionRingOfPsiCoord
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

theorem valF_psi_of_psiCoord : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (χ : D.X) (r : R), Formalism.L2.Pj.PsiCoord D χ r → ∃ j : PUnit → D.P.L.ι, ⊤ ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U (j PUnit.unit) ∧ valF (𝟙 (Sp (FractionRing R))) _ ((D.psi χ).s j).val = algebraMap R (FractionRing R) r := by
  intro R _ _ D χ r h
  obtain ⟨j, hj, h, e⟩ := h
  refine ⟨j, hj, ?_⟩
  unfold valF
  rw [dite_eq_left (by exact h)]
  have e1 : ∀ (h' : ⊤ ≤ 𝟙 (Sp (FractionRing R)) ⁻¹ᵁ (D.P.L.LinComb (fun _ ↦ ptK (D.c χ)) fun _ ↦ -1).U j),
      (Scheme.Hom.appLE (𝟙 (Sp (FractionRing R)))
        ((D.P.L.LinComb (fun _ ↦ ptK (D.c χ)) fun _ ↦ -1).U j) ⊤ h').hom ((D.psi χ).s j).val
      = ((TK R).left.presheaf.map (homOfLE h).op).hom ((D.psi χ).s j).val := by
    intro h'
    rfl
  refine (congrArg (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom ((e1 h).trans e.symm)).trans ?_
  have e2 : DegPre.toOpen (R := R) ⊤ r = (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r := by
    have : (homOfLE (le_top : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ ⊤)).op = 𝟙 _ := rfl
    simp only [DegPre.toOpen, RingHom.comp_apply, this, CategoryTheory.Functor.map_id]
    rfl
  rw [e2]
  have n := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R)))
  have n' := congrArg (fun f => (f ≫ (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom).hom r) n
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at n'
  exact n'.symm

end GlobalTheory.Poinc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiValueFractionRingOfPsiCoordStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psi_value_fractionRing_of_psiCoord : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (χ : D.X) (r : R), Formalism.L2.Pj.PsiCoord D χ r → ∃ j : PUnit → D.P.L.ι, ⊤ ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U (j PUnit.unit) ∧ valF (𝟙 (Sp (FractionRing R))) _ ((D.psi χ).s j).val = algebraMap R (FractionRing R) r := by
  first | exact @GlobalTheory.Poinc.valF_psi_of_psiCoord | exact GlobalTheory.Poinc.valF_psi_of_psiCoord | (intros; apply GlobalTheory.Poinc.valF_psi_of_psiCoord <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedIntegralOfCombinedMetrics
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CxPts GlobalTheory.Mean4O.CombForm

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CombChern

section Bundle

variable {X : Scheme.{0}} [IsIntegral X]

theorem presents_zpow {D : CartierDiv X} {L : LB X} {r : L.ι → X.functionFieldˣ} (h : Presents D L r) (n : ℤ) :
    Presents (n • D) (LB.LinComb L (K := PUnit) (fun _ => 𝟙 X) fun _ => n) fun j => r (j PUnit.unit) ^ n := by
  have mem : ∀ (j : PUnit → L.ι) {x : X}, x ∈ (LB.LinComb L (K := PUnit) (fun _ => 𝟙 X) fun _ => n).U j →
      x ∈ L.U (j PUnit.unit) := fun j x hx => by simpa using Set.mem_iInter.1 hx PUnit.unit
  refine ⟨LB.isLB_linComb h.isLB _ _, fun j j' hjj => ?_, fun j x hx => (h.isEqn _ x (mem j hx)).zsmul n⟩
  have l : (LB.LinComb L (K := PUnit) (fun _ => 𝟙 X) fun _ => n).U j ⊓
      (LB.LinComb L (K := PUnit) (fun _ => 𝟙 X) fun _ => n).U j' ≤ L.U (j PUnit.unit) ⊓ L.U (j' PUnit.unit) :=
    fun x hx => ⟨mem j hx.1, mem j' hx.2⟩
  have hg : (LB.LinComb L (K := PUnit) (fun _ => 𝟙 X) fun _ => n).g j j' = res l (L.g (j PUnit.unit) (j' PUnit.unit)) ^ n := by
    change ∏ _k : PUnit, _ = _
    exact Fintype.prod_unique _
  have key : ∀ {U : X.Opens} (hU : genericPoint X ∈ U) (u : Γ(X, U)ˣ) (m : ℤ),
      fnOf U hU ((u ^ m : Γ(X, U)ˣ) : Γ(X, U)) = fnOf U hU (u : Γ(X, U)) ^ m := fun hU u m => by
    have e := congrArg Units.val (map_zpow (Units.map (fnOf _ hU).toMonoidHom) u m)
    rw [Units.val_zpow_eq_zpow_val, Units.coe_map, Units.coe_map] at e
    exact e
  rw [Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, h.isRatSec _ _ (l hjj), mul_zpow, hg, key]
  congr 2
  exact (fnOf_resG l hjj _).symm

end Bundle

section Comb

variable {X : Scheme.{0}} [IsIntegral X] {ι : Type} (T : ι → LB X) (b : ι → ℤ)

variable {k : Type} [CommRing k] {p : X ⟶ Sp k} {σ : k →+* ℂ}

end Comb

section Met

variable {F : Type} [Field F] [NumberField F] {C : CxSt F} {Y : Var F}

end Met

end GlobalTheory.CombChern
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAugmentationTensorSigmaMap
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAugmentationTensorSigmaMap
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Obs

theorem smul_mem_map_eq_zero {R B : Type} [CommRing R] [CommRing B] [Algebra R B] {I : Ideal R} (hI : I ^ 2 = 0)
    {i : R} (hi : i ∈ I) {x : B} (hx : x ∈ I.map (algebraMap R B)) : i • x = 0 := by
  rw [Algebra.smul_def]
  have h : algebraMap R B i * x ∈ I.map (algebraMap R B) * I.map (algebraMap R B) :=
    Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ hi) hx
  rw [← Ideal.map_mul, ← pow_two, hI, Ideal.zero_eq_bot, Ideal.map_bot] at h
  simpa using h

theorem exists_isSig : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (B B₀ : Type) [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀] (p : B →+* B₀) (hs : SemiHom π p) (hp : Function.Surjective p) (hker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)), ∃ σ : R₁ ⊗[R₀] B₀ →+ B, α.IsSig p σ := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α B B₀ _ _ _ _ p hs hp hker
  have key : ∀ (y : R₁) (b b' : B), p b = p b' → α.k y • b = α.k y • b' := by
    intro y b b' h
    have hm : b - b' ∈ I.map (algebraMap R B) := (hker _).1 (by rw [map_sub, h, sub_self])
    have := smul_mem_map_eq_zero hI (α.mem y) hm
    rwa [smul_sub, sub_eq_zero] at this
  let s : B₀ → B := Function.surjInv hp
  have hs' : ∀ b₀, p (s b₀) = b₀ := Function.surjInv_eq hp
  let f : R₁ →+ B₀ →+ B := AddMonoidHom.mk' (fun y ↦ AddMonoidHom.mk' (fun b₀ ↦ α.k y • s b₀) (by
      intro b₀ b₀'
      rw [← smul_add]
      exact key y _ _ (by rw [map_add (f := _), hs', hs', hs'])))
    (by
      intro y y'
      ext b₀
      simp [add_smul])
  refine ⟨TensorProduct.liftAddHom f ?_, ?_⟩
  · intro r₀ y b₀
    obtain ⟨r, rfl⟩ := hπ r₀
    change α.k (π r • y) • s b₀ = α.k y • s (π r • b₀)
    rw [α.smul, mul_comm, mul_smul]
    exact key y _ _ (by rw [hs, hs', hs'])
  · intro y b
    change α.k y • s (p b) = α.k y • b
    exact key y _ _ (hs' _)

end GlobalTheory.Obs
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAugmentationTensorSigmaMapStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_augmentation_tensor_sigma_map : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (B B₀ : Type) [CommRing B] [Algebra R B] [CommRing B₀] [Algebra R₀ B₀] (p : B →+* B₀) (hs : SemiHom π p) (hp : Function.Surjective p) (hker : ∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)), ∃ σ : R₁ ⊗[R₀] B₀ →+ B, α.IsSig p σ := by
  first | exact @GlobalTheory.Obs.exists_isSig | exact GlobalTheory.Obs.exists_isSig | (intros; apply GlobalTheory.Obs.exists_isSig <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HessianOfCombinationMetricLinear
open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.Mean4 GlobalTheory.Mean4O

open scoped ContDiff

namespace GlobalTheory.Mean4O.ReadsProj

theorem hess_comb : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {ι : Type} [Fintype ι] (L : ι → HermLB p) (n : ι → ℤ) (σ : k →+* ℂ) {D : ℕ} (c : AlgChart p σ D) {y : CxPts p σ}, y ∈ c.e.source → ∀ (i : (ArInt.comb L n).B.ι), y ∈ ptsIn p σ ((ArInt.comb L n).B.U i) → ∀ (m : ∀ l, (L l).B.ι), (∀ l, y ∈ ptsIn p σ ((L l).B.U (m l))) → c.hess ((ArInt.comb L n).φ σ) i y = ∑ l, ((n l : ℝ) : ℂ) • c.hess ((L l).φ σ) (m l) y := by
  classical
  intro k _ X p ι _ L n σ D c y hy i hi m hm
  obtain ⟨i₀, hi₀, e₀⟩ := halfWeight_comb (fun l => halfWeight_locPot (σ := σ) (L l)) n y
  choose j hj ej using fun l => halfWeight_locPot (σ := σ) (L l) y
  set F : ι → ReciprocityTheory.L2DbarEstimates.V D → ℝ := fun l v => ((L l).φ σ).φ (j l) (c.e.symm v) with hF
  have e : ∀ z, ((ArInt.comb L n).φ σ).φ i₀ z = ∑ l, (n l : ℝ) * ((L l).φ σ).φ (j l) z := by
    intro z
    have h := e₀ z
    simp only [← ej] at h
    have h2 : ∑ l, (n l : ℝ) * (((L l).φ σ).φ (j l) z / 2) =
        (∑ l, (n l : ℝ) * ((L l).φ σ).φ (j l) z) / 2 := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun _ _ => by ring
    linarith
  set Ω := c.e.target ∩ c.e.symm ⁻¹' ⋂ l, ptsIn p σ ((L l).B.U (j l)) with hΩdef
  have hΩ : IsOpen Ω := ChartGlue.isOpen_over c.e (isOpen_iInter_of_finite fun l => isOpen_ptsIn _)
  have hmem : c.e y ∈ Ω := ChartGlue.mem_over c.e hy (Set.mem_iInter.2 hj)
  have hs : ∀ l, ContDiffOn ℝ ∞ (F l) Ω := fun l =>
    (contDiffOn_chart ((L l).cInf σ (j l)) c).mono fun v hv => ⟨hv.1, Set.mem_iInter.1 hv.2 l⟩
  have key : ∀ s : Finset ι,
      ReciprocityTheory.L2DbarEstimates.cHess D (fun v => ((∑ l ∈ s, (n l : ℝ) * F l v : ℝ) : ℂ)) (c.e y) =
        ∑ l ∈ s, ((n l : ℝ) : ℂ) • ReciprocityTheory.L2DbarEstimates.cHess D (fun v => (F l v : ℂ)) (c.e y) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have h0 := ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cHess_add_smul hΩ (p := fun _ => (0 : ℝ))
        (q := fun _ => (0 : ℝ)) contDiffOn_const contDiffOn_const 1 hmem
      simp only [mul_zero, add_zero, Complex.ofReal_one, one_smul] at h0
      simp only [Finset.sum_empty]
      exact left_eq_add.1 h0
    | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      have h1 := ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cHess_add_smul hΩ
        (p := fun w => ∑ l ∈ s, (n l : ℝ) * F l w) (q := F a)
        (ContDiffOn.sum fun l _ => contDiffOn_const.mul (hs l)) (hs a) (n a) hmem
      have h3 : (fun v => ((∑ l ∈ insert a s, (n l : ℝ) * F l v : ℝ) : ℂ)) =
          fun v => ((∑ l ∈ s, (n l : ℝ) * F l v + (n a : ℝ) * F a v : ℝ) : ℂ) := by
        funext v
        rw [Finset.sum_insert ha, add_comm]
      rw [h3, h1, ih, add_comm]
  calc c.hess ((ArInt.comb L n).φ σ) i y = c.hess ((ArInt.comb L n).φ σ) i₀ y :=
        c.hess_eq ((ArInt.comb L n).cInf σ) hy hi₀ hi
    _ = ReciprocityTheory.L2DbarEstimates.cHess D (fun v => ((∑ l, (n l : ℝ) * F l v : ℝ) : ℂ)) (c.e y) := by
        simp only [AlgChart.hess, e, hF]
    _ = ∑ l, ((n l : ℝ) : ℂ) • ReciprocityTheory.L2DbarEstimates.cHess D (fun v => (F l v : ℂ)) (c.e y) := key _
    _ = ∑ l, ((n l : ℝ) : ℂ) • c.hess ((L l).φ σ) (m l) y :=
        Finset.sum_congr rfl fun l _ => by
          rw [← c.hess_eq ((L l).cInf σ) hy (hm l) (hj l)]
          rfl

end GlobalTheory.Mean4O.ReadsProj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeEqOfNatCastEqZero
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

theorem prime_eq_of_natCast_eq_zero {K : Type*} [Field K] {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h1 : (p : K) = 0) (h2 : (q : K) = 0) : p = q := by
  have a := ringChar.dvd h1
  have b := ringChar.dvd h2
  have hne : ringChar K ≠ 1 := CharP.ringChar_ne_one
  have e1 := (hp.eq_one_or_self_of_dvd _ a).resolve_left hne
  have e2 := (hq.eq_one_or_self_of_dvd _ b).resolve_left hne
  rw [← e1, ← e2]

theorem natCast_residueField_cPt {X : Scheme.{0}} {p : ℕ} [Fact p.Prime] (y : Sp (OO p) ⟶ X) :
    ((p : ℕ) : X.residueField (y (cPt p))) = 0 := by
  let φ := (Scheme.stalkClosedPointTo (R := CommRingCat.of (OO p)) y).hom
  have hinj := (IsLocalRing.ResidueField.map φ).injective
  refine hinj ((map_natCast _ p).trans ?_)
  exact (natCast_residueField_OO (p := p)).trans (map_zero _).symm

theorem eq_zero_of_val_cen_eq_zero : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M : RatModel o Ω), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → ∀ (U : M.Z.Opens), (U : Set M.Z).Nonempty → ∀ (p : ℕ) [Fact p.Prime] (y₀ : Sp (OO p) ⟶ M.Z) (b : Ω), b ∈ M.O (y₀ (cPt p)) → (∀ y : Sp (OO p) ⟶ M.Z, M.Cen U (y₀ (cPt p)) y → M.val (gPt p ≫ y) b = 0) → b = 0 := by
  intro o Ω _ _ _ hb M hN U hU p _ y₀ b hb0 hv
  by_contra hne
  obtain ⟨V, f, hzV, hf⟩ := hb0
  have hD : ((M.Z.basicOpen f : M.Z.Opens) : Set M.Z).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro h
    have h0 : f = 0 := (basicOpen_eq_bot_iff f).1 (SetLike.coe_injective h)
    apply hne
    rw [← hf, ← M.res_apply V ⟨_, hzV⟩, h0, map_zero]
  have hW : ((U ⊓ M.Z.basicOpen f : M.Z.Opens) : Set M.Z).Nonempty := M.nonempty_inf hU hD
  have := hb.ded
  have := hb.ft
  have := hb.char
  have : CharZero o := (RingHom.charZero_iff hb.inj).2 hb.char
  let π : M.Z ⟶ Spec (.of ℤ) := M.s ≫ Spec.map (CommRingCat.ofHom (Int.castRingHom o))
  have : Flat M.s := GlobalTheory.ModelOfOutput.flat_ratModel M
  have : Flat (Spec.map (CommRingCat.ofHom (Int.castRingHom o))) := by
    refine Flat.SpecMap_iff.2 ?_
    have : FaithfulSMul ℤ o := inferInstance
    exact (RingHom.flat_algebraMap_iff.2 inferInstance)
  have : Flat π := inferInstance
  have := M.lft
  have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (Int.castRingHom o))) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact (RingHom.finiteType_algebraMap (A := ℤ) (B := o)).2 hb.ft
  have : LocallyOfFiniteType π := inferInstance
  have hz : IsClosed ({y₀ (cPt p)} : Set M.Z) := isClosed_singleton_cPt y₀
  obtain ⟨p', hp', y, hy, hyW⟩ := GlobalTheory.padicAlgCl_integral_points.1 M.Z π (y₀ (cPt p)) hz _ hW
  have e : p = p' := prime_eq_of_natCast_eq_zero (Fact.out) hp'.out (natCast_residueField_cPt y₀)
    (hy ▸ natCast_residueField_cPt y)
  subst e
  have h0 := hv y ⟨hy, hyW.trans (fun _ h => h.1)⟩
  let w : Sp (PadicAlgCl p) := IsLocalRing.closedPoint _
  have hξ : (gPt p ≫ y) w ∈ M.Z.basicOpen f := (hyW ⟨w, rfl⟩).2
  have hξV : (gPt p ≫ y) w ∈ V := M.Z.basicOpen_le f hξ
  subst hf
  exact (RatModel.val_ne_zero_iff (RatModel.range_eq_singleton _ w) ⟨_, RatModel.valF_mem_O hξV f⟩).2
    ((RatModel.isUnit_valF_iff hξV f).2 hξ) h0

end GlobalTheory.Poinc

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleOfGenericPrincipal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GenericAmpleDvr

theorem triv_theta {S : Scheme.{0}} [IsLocallyNoetherian S] {A : Over S} [GrpObj A] [IsCommMonObj A]
    (hA : IsAbelianScheme A) {L : LB A.left} (hL : L.IsLB) : AbLaw.Triv (Theta A L) :=
  CubeNoeth.triv_of_faces allSixLaws.1.globalFns hA hL (thφ A (x3 A)) thε
    (fun r i b h => AbLaw.CubeGen.trivAt_of_formal hL r (AbLaw.CubeGen.prod_face r i b h))
    (fun r b h => AbLaw.CubeGen.prod_face r 0 b h)

end GlobalTheory.GenericAmpleDvr
end
