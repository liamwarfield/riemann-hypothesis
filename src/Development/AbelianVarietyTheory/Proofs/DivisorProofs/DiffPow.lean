module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefiningDegenerationDataTauCoordinateUnit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppTopBijectiveAndSurjectiveNormalDomain
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffPow
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChart.CUniq

theorem map_max {R V : Type} [CommRing R] [IsLocalRing R] [CommRing V] [IsLocalRing V] (θ : R →+* V) [IsLocalHom θ]
    {x : R} (hx : x ∈ maximalIdeal R) : θ x ∈ maximalIdeal V := by
  rw [mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
  exact fun h => hx (isUnit_of_map_unit θ x h)

theorem diff_pow {A R V : Type} [CommRing A] [CommRing R] [IsLocalRing R] [CommRing V] [IsLocalRing V]
    (ψ : A →+* R) (hψ : IsComplAt ψ) (θ₁ θ₂ : R →+* V) [IsLocalHom θ₁] [IsLocalHom θ₂]
    (h : θ₁.comp ψ = θ₂.comp ψ) (k : ℕ) : ∀ r : R, θ₁ r - θ₂ r ∈ maximalIdeal V ^ k := by
  have hc : ∀ a, θ₁ (ψ a) = θ₂ (ψ a) := fun a => congrArg (fun f => f a) h
  induction k with
  | zero => intro r; simp
  | succ k ih =>
    have hm : ∀ x ∈ maximalIdeal R, θ₁ x - θ₂ x ∈ maximalIdeal V ^ (k + 1) := by
      intro x hx
      rw [← hψ.2.2.2.1] at hx
      induction hx using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨p, -, rfl⟩ := hy
        simp [hc]
      | zero => simp
      | add y z _ _ hy hz =>
        have := add_mem hy hz
        simpa [map_add (f := _), sub_add_sub_comm] using this
      | smul a y hy' hy =>
        have hyM : y ∈ maximalIdeal R := hψ.2.2.2.1 ▸ hy'
        have e : θ₁ (a • y) - θ₂ (a • y) = θ₁ a * (θ₁ y - θ₂ y) + (θ₁ a - θ₂ a) * θ₂ y := by
          simp only [smul_eq_mul, map_mul]; ring
        rw [e]
        refine add_mem (Ideal.mul_mem_left _ _ hy) ?_
        rw [pow_succ]
        exact Ideal.mul_mem_mul (ih a) (map_max θ₂ hyM)
    intro r
    obtain ⟨a, b, hb, hx⟩ := hψ.2.2.2.2 r
    have e := hm _ hx
    have hu : IsUnit (θ₁ (ψ b)) := hb.map θ₁
    have e2 : θ₁ (r * ψ b - ψ a) - θ₂ (r * ψ b - ψ a) = (θ₁ r - θ₂ r) * θ₁ (ψ b) := by
      simp only [map_sub, map_mul, hc]; ring
    rw [e2] at e
    obtain ⟨u, hu'⟩ := hu
    have : θ₁ r - θ₂ r = (θ₁ r - θ₂ r) * θ₁ (ψ b) * ↑u⁻¹ := by
      rw [← hu', _root_.mul_assoc, Units.mul_inv, _root_.mul_one]
    rw [this]
    exact Ideal.mul_mem_right _ _ e

end GlobalTheory.TChart.CUniq

theorem GlobalTheory.TChart.cuniq : ∀ (A R V : Type) [CommRing A] [CommRing R] [IsLocalRing R] [CommRing V] [IsLocalRing V] [IsNoetherianRing V] (ψ : A →+* R), IsComplAt ψ → ∀ θ₁ θ₂ : R →+* V, IsLocalHom θ₁ → IsLocalHom θ₂ → θ₁.comp ψ = θ₂.comp ψ → θ₁ = θ₂ := by
  intro A R V _ _ _ _ _ _ ψ hψ θ₁ θ₂ h₁ h₂ h
  ext r
  have hk := fun k => GlobalTheory.TChart.CUniq.diff_pow ψ hψ θ₁ θ₂ h k r
  have hbot := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal V) (maximalIdeal.isMaximal V).ne_top
  have : θ₁ r - θ₂ r ∈ ⨅ k : ℕ, maximalIdeal V ^ k := Ideal.mem_iInf.mpr hk
  rw [hbot, Ideal.mem_bot, sub_eq_zero] at this
  exact this
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupPullbackTangentVectorsCompat
set_option autoImplicit false

noncomputable section

open NumberField GlobalTheory.ShFam.Pad AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LiePull


set_option maxHeartbeats 800000 in
theorem exists_lieBasis_of_tanBasis {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}}
    (t : SAB H X0) {K : Type} [CommRing K] (x0 : Sp K ⟶ X0) (A : Over (Sp K)) [GrpObj A] (θ : A.left ⟶ t.G.left)
    (hθ : IsGrpPullback A t.G x0 θ) {m : ℕ} (u : Fin m → (Sp (DualNumber K) ⟶ t.G.left))
    (hu : ∀ j, IsTanAtG t x0 (u j)) (hc : ∀ w, IsTanAtG t x0 w → ∃! c : Fin m → K, IsCombAtG t x0 u c w) :
    ∃ v : Fin m → (epsR K ⟶ A), IsLieBasis v ∧ ∀ j, (v j).left ≫ θ = u j := by
  classical
  let up : ∀ w : Sp (DualNumber K) ⟶ t.G.left, w ≫ t.G.hom = spMap (algebraMap K (DualNumber K)) ≫ x0 →
      (epsR K ⟶ A) := fun w h => Over.homMk (hθ.1.lift w _ h) (hθ.1.lift_snd _ _ _)
  have hup : ∀ w h, (up w h).left ≫ θ = w := fun w h => hθ.1.lift_fst _ _ _
  have inj : ∀ {T : Over (Sp K)} {a b : T ⟶ A}, a.left ≫ θ = b.left ≫ θ → a = b := fun h =>
    Over.OverMorphism.ext (hθ.1.hom_ext h ((Over.w _).trans (Over.w _).symm))
  have one : ∀ T : Over (Sp K), (1 : T ⟶ A).left ≫ θ = (1 : Over.mk (T.hom ≫ x0) ⟶ t.G).left :=
    fun T => congrArg (fun q => q.left) (map_one (pushHom hθ T))
  have tan : ∀ w : epsR K ⟶ A, IsTangent w ↔ IsTanAtG t x0 (w.left ≫ θ) := fun w => by
    have e : (1 : Chart.sp (R₀ := K) K ⟶ A).left ≫ θ = (1 : Over.mk x0 ⟶ t.G).left :=
      (one _).trans (congrArg (· ≫ (η[t.G]).left) (show Spec.map (CommRingCat.ofHom (RingHom.id K)) ≫ x0 = x0 by simp))
    rw [← Chart.isTan_iff]
    refine ⟨fun h => ⟨Over.w (pushPt hθ.1.w w), ?_⟩, fun h => inj ?_⟩
    · exact (Category.assoc _ _ _).symm.trans ((congrArg (fun q => q.left ≫ θ) h).trans e)
    · exact (Category.assoc _ _ _).trans (h.2.trans e.symm)
  have pr : ∀ {n} (a : Fin n → (epsR K ⟶ A)), (List.ofFn a).prod.left ≫ θ =
      (List.ofFn fun i => (pushPt hθ.1.w (a i) : tEpsG x0 ⟶ t.G)).prod.left := fun a =>
    congrArg (fun q => q.left) ((map_list_prod (pushHom hθ (epsR K)) _).trans (by rw [List.map_ofFn]; rfl))
  have comb : ∀ {n} (c : Fin n → K) (v : Fin n → (epsR K ⟶ A)) w,
      IsLieComb c v w ↔ IsCombAtG t x0 (fun i => (v i).left ≫ θ) c (w.left ≫ θ) := fun c v w => by
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨fun i => pushPt hθ.1.w (a i), fun i => (congrArg (· ≫ θ) (ha i)).trans (Category.assoc _ _ _), (pr a).symm⟩
    · rintro ⟨a, ha, hw⟩
      refine ⟨fun i => up (a i).left (Over.w _), fun i => hθ.1.hom_ext ?_ ?_, inj (hw.symm.trans (Eq.trans ?_ (pr _).symm))⟩
      · exact (hup _ _).trans ((ha i).trans (Category.assoc _ _ _).symm)
      · refine (Over.w (up (a i).left (Over.w _))).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
        refine Eq.trans ?_ (congrArg (spMap (epsScaleR (c i)) ≫ ·) (Over.w (v i))).symm
        exact (Over.w (Chart.spMap (Chart.scaleD (c i)))).symm
      · have : a = fun i => (pushPt hθ.1.w (up (a i).left (Over.w _)) : tEpsG x0 ⟶ t.G) :=
          funext fun i => Over.OverMorphism.ext (hup (a i).left (Over.w _)).symm
        exact congrArg (fun q : _ → (tEpsG x0 ⟶ t.G) => (List.ofFn q).prod.left) this
  let v : Fin m → (epsR K ⟶ A) := fun j => up (u j) (hu j).1
  have hv : (fun i => (v i).left ≫ θ) = u := funext fun j => hup _ _
  refine ⟨v, ⟨fun j => (tan _).2 (by rw [hup]; exact hu j), fun w hw => ?_⟩, fun j => hup _ _⟩
  have key : ∀ c, IsLieComb c v w ↔ IsCombAtG t x0 u c (w.left ≫ θ) := fun c => by
    rw [comb, hv]
  obtain ⟨c, hc1, hc2⟩ := hc _ ((tan w).1 hw)
  exact ⟨c, (key c).2 hc1, fun c' h' => hc2 c' ((key c').1 h')⟩

theorem lieBasis_of_tanBasis : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X0 : Scheme.{0}} (t : ReciprocityTheory.ChartRestriction.G.Geo.Tor.SAB H X0) {K : Type} [CommRing K] (x0 : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K ⟶ X0) (A : Over (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K)) [GrpObj A] (θ : A.left ⟶ t.G.left), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback A t.G x0 θ → ∀ {m : ℕ} (u : Fin m → (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (DualNumber K) ⟶ t.G.left)), (∀ j, Formalism.L2.Pj.IsTanAtG t x0 (u j)) → (∀ w, Formalism.L2.Pj.IsTanAtG t x0 w → ∃! c : Fin m → K, Formalism.L2.Pj.IsCombAtG t x0 u c w) → ∃ v : Fin m → (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsR K ⟶ A), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsLieBasis v ∧ ∀ j, (v j).left ≫ θ = u j :=
  by
  intro E _ _ _ H X0 t K _ x0 A _ θ hθ m u hu hc
  exact exists_lieBasis_of_tanBasis t x0 A θ hθ u hu hc

end GlobalTheory.LiePull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFreeGenWedgeFormOfFormallyEtaleMvPolynomial
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFreeGenWedgeFormOfFormallyEtaleMvPolynomial
open GlobalTheory GlobalTheory.TopForm
open scoped TensorProduct

namespace GlobalTheory.TopFrameEt

theorem isFreeGen_dForm_of_formallyEtale_mvPolynomial :
    ∀ {k A₀ A : Type} [CommRing k] [CommRing A₀] [CommRing A] (α : k →+* A₀) (β : k →+* A)
    (ρ : A₀ →+* A), ρ.comp α = β → ∀ {n r : ℕ} (z : Fin n → A₀) (b : Module.Basis (Fin n) A₀ (Omega α)),
    (∀ i, b i = dFun α (z i)) → ∀ (t : Fin r → A), (MvPolynomial.eval₂Hom ρ t).FormallyEtale →
    IsFreeGen A (dForm β (Fin.append t (fun i => ρ (z i)))) := by
  intro k A₀ A _ _ _ α β ρ hc n r z b hb t hφ
  letI := α.toAlgebra
  letI := β.toAlgebra
  letI := ρ.toAlgebra
  haveI : IsScalarTower k A₀ A := IsScalarTower.of_algebraMap_eq' hc.symm
  let φ := MvPolynomial.eval₂Hom ρ t
  letI : Algebra (MvPolynomial (Fin r) A₀) A := φ.toAlgebra
  haveI : IsScalarTower A₀ (MvPolynomial (Fin r) A₀) A :=
    IsScalarTower.of_algebraMap_eq fun a ↦ by
      change _ = φ (MvPolynomial.C a)
      simp [φ, RingHom.algebraMap_toAlgebra]
  haveI : Algebra.FormallyEtale (MvPolynomial (Fin r) A₀) A := hφ
  haveI : Algebra.FormallySmooth A₀ A :=
    Algebra.FormallySmooth.comp A₀ (MvPolynomial (Fin r) A₀) A
  haveI : Subsingleton (Algebra.H1Cotangent A₀ A) :=
    Algebra.FormallySmooth.subsingleton_h1Cotangent
  have hinj : Function.Injective (KaehlerDifferential.mapBaseChange k A₀ A) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro y hy
    obtain ⟨w, rfl⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange k A₀ A y).1 hy
    rw [Subsingleton.elim w 0, map_zero]
  let w : Module.Basis (Fin r) A (Ω[A⁄A₀]) :=
    (KaehlerDifferential.isBaseChange_of_formallyEtale A₀ (MvPolynomial (Fin r) A₀) A).basis
      (KaehlerDifferential.mvPolynomialBasis A₀ (Fin r))
  have hw : ∀ i, w i = KaehlerDifferential.D A₀ A (t i) := fun i ↦ by
    simp [w, IsBaseChange.basis_apply, KaehlerDifferential.mvPolynomialBasis_apply,
      KaehlerDifferential.map_D, RingHom.algebraMap_toAlgebra, φ]
  obtain ⟨B, hB⟩ := exists_basis_of_exact
    (KaehlerDifferential.mapBaseChange k A₀ A) (KaehlerDifferential.map k A₀ A A) hinj
    (KaehlerDifferential.exact_mapBaseChange_map k A₀ A)
    (b.baseChange A) w (fun i ↦ KaehlerDifferential.D k A (t i))
    (fun i ↦ by rw [hw, KaehlerDifferential.map_D]; rfl)
  let e : Fin (r + n) ≃ Fin n ⊕ Fin r := finSumFinEquiv.symm.trans (Equiv.sumComm _ _)
  refine isFreeGen_dForm _ (B.reindex e.symm) fun a ↦ ?_
  rw [Module.Basis.reindex_apply, Equiv.symm_symm, hB]
  refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) a
  · simp [e, Fin.append_left]
  · simp only [e, Equiv.trans_apply, finSumFinEquiv_symm_apply_natAdd, Equiv.sumComm_apply,
      Sum.swap_inr, Sum.elim_inl, Module.Basis.baseChange_apply,
      KaehlerDifferential.mapBaseChange_tmul, one_smul, hb, dFun, KaehlerDifferential.map_D,
      Fin.append_right]
    rfl

end GlobalTheory.TopFrameEt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFreeGenWedgeFormOfFormallyEtaleMvPolynomialStatement
open GlobalTheory GlobalTheory.TopForm
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFreeGen_wedgeForm_of_formallyEtale_mvPolynomial : ∀ {k A₀ A : Type} [CommRing k] [CommRing A₀] [CommRing A] (α : k →+* A₀) (β : k →+* A)
    (ρ : A₀ →+* A), ρ.comp α = β → ∀ {n r : ℕ} (z : Fin n → A₀) (b : Module.Basis (Fin n) A₀ (Omega α)),
    (∀ i, b i = dFun α (z i)) → ∀ (t : Fin r → A), (MvPolynomial.eval₂Hom ρ t).FormallyEtale →
    IsFreeGen A (dForm β (Fin.append t (fun i => ρ (z i)))) := by
  first | exact @GlobalTheory.TopFrameEt.isFreeGen_dForm_of_formallyEtale_mvPolynomial | exact GlobalTheory.TopFrameEt.isFreeGen_dForm_of_formallyEtale_mvPolynomial | (intros; apply GlobalTheory.TopFrameEt.isFreeGen_dForm_of_formallyEtale_mvPolynomial <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPermutationLeadingMinors
namespace GlobalTheory

open Matrix

theorem exists_isUnit_of_isUnit_sum_localRing {R : Type} [CommRing R] [IsLocalRing R]
    {ι : Type} (s : Finset ι) (f : ι → R) (h : IsUnit (∑ i ∈ s, f i)) :
    ∃ i ∈ s, IsUnit (f i) := by
  by_contra hne
  push_neg at hne
  apply (IsLocalRing.mem_maximalIdeal _).mp _ h
  exact Ideal.sum_mem _ fun i hi => (IsLocalRing.mem_maximalIdeal _).mpr (hne i hi)

theorem exists_perm_isUnit_leading_minors_localRing :
    ∀ {R : Type} [CommRing R] [IsLocalRing R] {m : ℕ} (M : Matrix (Fin m) (Fin m) R),
      IsUnit M.det → ∃ w : Equiv.Perm (Fin m), ∀ (k : ℕ) (hk : k ≤ m),
        IsUnit ((M.submatrix id w).submatrix (Fin.castLE hk) (Fin.castLE hk)).det := by
  intro R _ _ m
  induction m with
  | zero =>
    intro M _
    refine ⟨1, fun k hk => ?_⟩
    obtain rfl : k = 0 := Nat.le_zero.mp hk
    simp
  | succ n ih =>
    intro M hM
    rw [Matrix.det_succ_row M (Fin.last n)] at hM
    obtain ⟨j, -, hj⟩ := exists_isUnit_of_isUnit_sum_localRing _ _ hM
    have hN := isUnit_of_mul_isUnit_right hj
    rw [Fin.succAbove_last] at hN
    obtain ⟨v, hv⟩ := ih _ hN
    let f : Fin (n + 1) → Fin (n + 1) := fun i =>
      if h : i = Fin.last n then j else j.succAbove (v (i.castPred h))
    have hf : Function.Injective f := by
      intro a b hab
      simp only [f] at hab
      by_cases ha : a = Fin.last n <;> by_cases hb : b = Fin.last n
      · rw [ha, hb]
      · simp only [ha, hb, dite_true, dite_false] at hab
        exact absurd hab.symm (Fin.succAbove_ne _ _)
      · simp only [ha, hb, dite_true, dite_false] at hab
        exact absurd hab (Fin.succAbove_ne _ _)
      · simp only [ha, hb, dite_false] at hab
        have := v.injective (Fin.succAbove_right_injective hab)
        exact Fin.castPred_inj.mp this
    let w : Equiv.Perm (Fin (n + 1)) :=
      Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf)
    refine ⟨w, fun k hk => ?_⟩
    rcases Nat.lt_or_ge k (n + 1) with hlt | hge
    · have hk' : k ≤ n := Nat.lt_succ_iff.mp hlt
      have heq : (M.submatrix id w).submatrix (Fin.castLE hk) (Fin.castLE hk) =
          ((M.submatrix Fin.castSucc j.succAbove).submatrix id v).submatrix
            (Fin.castLE hk') (Fin.castLE hk') := by
        ext a b
        have hb : Fin.castLE hk b ≠ Fin.last n := by
          intro h
          have := congrArg Fin.val h
          simp at this
          omega
        simp only [submatrix_apply, id, w, Equiv.ofBijective_apply, f, hb, dite_false]
        congr 2
        all_goals (ext; simp)
      rw [heq]
      exact hv k hk'
    · obtain rfl : k = n + 1 := le_antisymm hk hge
      have : Fin.castLE hk = id := Fin.castLE_rfl _
      rw [this, Matrix.submatrix_id_id, Matrix.det_permute']
      refine IsUnit.mul ?_ ?_
      · rcases Int.units_eq_one_or (Equiv.Perm.sign w) with h | h <;> simp [h]
      · rw [Matrix.det_succ_row M (Fin.last n)]
        exact hM

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHodgeFiltrationIffPointwiseCoboundary
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

variable {R : Type} [CommRing R] {X : Over (Sp R)}

theorem existsUnique_pt_of_triv (T : Thick (dp0 R) (X.hom ≫ 𝟙 _)) (hT : T.J = ⊥) :
    ∃! y : Pt X T.B, spMap T.π ≫ y.left = T.x := by
  have hb : Function.Bijective T.π :=
    ⟨(injective_iff_map_eq_zero _).2 fun b hb ↦ by simpa [hT] using (T.ker b).1 hb, T.surj⟩
  let e := RingEquiv.ofBijective T.π hb
  let ρ : T.B₀ →+* T.B := e.symm.toRingHom
  have h1 : ρ.comp T.π = RingHom.id _ := RingHom.ext e.symm_apply_apply
  have h2 : T.π.comp ρ = RingHom.id _ := RingHom.ext e.apply_symm_apply
  have k1 : spMap ρ ≫ spMap T.π = 𝟙 _ := by rw [← Cris.spMap_comp, h1, Cris.spMap_id]
  have k2 : spMap T.π ≫ spMap ρ = 𝟙 _ := by rw [← Cris.spMap_comp, h2, Cris.spMap_id]
  have hw : (spMap ρ ≫ T.x) ≫ X.hom = spMap (algebraMap R T.B) := by
    have : T.x ≫ X.hom = spMap (T.π.comp (algebraMap R T.B)) :=
      (congrArg (T.x ≫ ·) (Category.comp_id X.hom)).symm.trans T.w
    rw [Category.assoc, this, Cris.spMap_comp, ← Category.assoc, k1, Category.id_comp]
  let point : Pt X T.B := Over.homMk (spMap ρ ≫ T.x) hw
  refine ⟨point, ?_, ?_⟩
  · change spMap T.π ≫ spMap ρ ≫ T.x = T.x
    rw [← Category.assoc, k2, Category.id_comp]
  · intro y hy
    apply Over.OverMorphism.ext
    change y.left = spMap ρ ≫ T.x
    rw [← hy, ← Category.assoc, k1]
    exact (Category.id_comp _).symm

def liftHom (T : Thick (dp0 R) (X.hom ≫ 𝟙 _)) (y : Pt X T.B) (h : spMap T.π ≫ y.left = T.x) : trivAt y ⟶ T :=
  Thick.trivHom (AlgHom.id R T.B) h

private def trivObject {D : Type} [CommRing D] [Algebra R D] (x : Pt X D) :
    (IsTriv (X.hom ≫ 𝟙 _)).FullSubcategory :=
  ⟨trivAt x, show (trivAt x).J = ⊥ from rfl⟩

theorem mem_hodgeFiltration_iff_pointwiseCoboundary (R : Type) [CommRing R] (X : Over (Sp R)) (f : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))) :
    CatCoh.H1.mk _ f ∈ F1 (X.hom ≫ 𝟙 _) ↔ ∃ k : Fn0 X, IsCob (whole X) (fv f) k := by
  rw [F1, LinearMap.mem_ker, toH1O, CoefMap.pullCohomologyOne_class, CatCoh.H1.mk_eq_zero]
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨fun D _ _ x ↦ g (trivObject x), ?_⟩
    intro D _ _ D' _ _ φ x _
    let a : trivObject x ⟶ trivObject (spOver φ ≫ x) := ObjectProperty.homMk (trivMap φ x)
    exact (congrFun (congrFun (congrFun hg (trivObject x)) (trivObject (spOver φ ≫ x))) a).symm
  · rintro ⟨k, hk⟩
    choose y hy hu using existsUnique_pt_of_triv (R := R) (X := X)
    refine ⟨fun T ↦ (k T.obj.B (y T.obj T.property) +
      ev f (liftHom T.obj _ (hy T.obj T.property)) : T.obj.B), ?_⟩
    funext ⟨T, hT⟩ ⟨T', hT'⟩ ⟨φ⟩
    have h' : spMap T'.π ≫ (spOver φ.φ ≫ y T hT).left = T'.x := by
      change spMap T'.π ≫ spMap (φ.φ : T.B →+* T'.B) ≫ (y T hT).left = T'.x
      have hπ : T'.π.comp (φ.φ : T.B →+* T'.B) = φ.φ₀.comp T.π :=
        RingHom.ext fun b ↦ (φ.comm b).symm
      rw [← Category.assoc, ← Cris.spMap_comp, hπ, Cris.spMap_comp, Category.assoc, hy T hT, φ.pt]
    have key : ∀ (z : Pt X T'.B) (hz : spMap T'.π ≫ z.left = T'.x), spOver φ.φ ≫ y T hT = z →
        k T'.B z + ev f (liftHom T' z hz) - φ.φ (k T.B (y T hT) + ev f (liftHom T _ (hy T hT))) = ev f φ := by
      rintro _ hz rfl
      have e1 := ev_sq f (trivMap φ.φ (y T hT)) (liftHom T' _ hz) (liftHom T _ (hy T hT)) φ fun _ ↦ rfl
      have e2 := hk T.B T'.B φ.φ (y T hT) (sm_whole _)
      change fv f T.B T'.B φ.φ (y T hT) + _ = _ at e1
      rw [map_add φ.φ]
      linear_combination e1 - e2
    exact key _ (hy T' hT') (hu T' hT' _ h')

end GlobalTheory.PtExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BirigidifiedLiftPullbackOneProdEndomorphism
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BirigidifiedLiftPullbackOneProdEndomorphism
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet

attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.Published

namespace GlobalTheory.BirigidLift

theorem pull_one_prod_of_lift : GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.Published.AbelianDualCrystal →
    ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (κ : DividedPowers I), IsNilDP κ →
    ∀ (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I →
    ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A : Over (Sp R)) [GrpObj A] (i : A₀.left ⟶ A.left),
      IsGrpPullback A₀ A (spMap π) i → IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ (l : (A₀ ⊗ A₀).left ⟶ (A ⊗ A).left), IsSquare i l →
    ∀ (L : LB A.left), L.IsLB → Out.RelAmple A L →
    ∀ (u₀ : A₀ ⟶ A₀) (u : A ⟶ A) [IsMonHom u₀] [IsMonHom u], u₀.left ≫ i = i ≫ u.left →
    ∀ (P₀ Q₀ : LB (A₀ ⊗ A₀).left), P₀.IsLB → Q₀.IsLB → LBIso Q₀ (P₀.pull (lift (fst A₀ A₀) (snd A₀ A₀ ≫ u₀)).left) →
    ∀ (P Q : LB (A ⊗ A).left), P.IsLB → Q.IsLB →
      HasGen (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left) → HasGen (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left) →
      HasGen (Q.pull (lift (1 : A ⟶ A) (𝟙 A)).left) → HasGen (Q.pull (lift (𝟙 A) (1 : A ⟶ A)).left) →
      LBIso (P.pull l) P₀ → LBIso (Q.pull l) Q₀ → LBIso Q (P.pull (lift (fst A A) (snd A A ≫ u)).left) := by
  intro HG HD R R₀ _ _ I κ hκ π hπ hI g A₀ _ A _ i h hA hg l hl L hL aL u₀ u _ _ hu P₀ Q₀ hP₀ hQ₀ eQ₀ P Q hP hQ
    p₁ p₂ q₁ q₂ eP eQ
  set m : (A ⊗ A).left ⟶ (A ⊗ A).left := (lift (fst A A) (snd A A ≫ u)).left with hm
  set m₀ : (A₀ ⊗ A₀).left ⟶ (A₀ ⊗ A₀).left := (lift (fst A₀ A₀) (snd A₀ A₀ ≫ u₀)).left with hm₀
  have hP' : (P.pull m).IsLB := pull_isLB hP m
  have hev : ∀ (a : A ⟶ A) (t : A ⟶ A), evc hP' a t = evc hP a (t ≫ u) := fun a t ↦ by
    have := evc_ev hP (fst A A) (snd A A ≫ u) hP' a t
    rw [this, lift_fst, lift_snd_assoc]
  have z₁ : evc hP (1 : A ⟶ A) (𝟙 A) = 0 := (triv_ev_iff hP _ _).1 p₁
  have z₂ : evc hP (𝟙 A) (1 : A ⟶ A) = 0 := (triv_ev_iff hP _ _).1 p₂
  have h₁' : Triv (ev (P.pull m) (1 : A ⟶ A) (𝟙 A)) := by
    rw [triv_ev_iff hP', hev, Category.id_comp]
    have := pull_evc hP u (1 : A ⟶ A) (𝟙 A)
    rw [z₁, map_zero, Category.comp_id, MonObj.comp_one] at this
    exact this.symm
  have h₂' : Triv (ev (P.pull m) (𝟙 A) (1 : A ⟶ A)) := by
    rw [triv_ev_iff hP', hev, MonObj.one_comp]
    exact z₂
  have sq : l ≫ m = m₀ ≫ l := by
    apply left_ext
    · rw [Category.assoc, Category.assoc, hm, hm₀, lift_left_fst, hl.1, lift_left_fst_assoc]
    · rw [Category.assoc, Category.assoc, hm, hm₀, lift_left_snd, hl.2, lift_left_snd_assoc, Over.comp_left,
        Over.comp_left, ← Category.assoc, hl.2, Category.assoc, Category.assoc, hu]
  have e' : LBIso ((P.pull m).pull l) Q₀ := by
    refine (cls_eq_iff (pull_isLB hP' l) hQ₀).1 ?_
    rw [cls_pull hP' l, cls_pull hP m, ← pull_comp, sq, pull_comp, ← cls_pull hP l (pull_isLB hP l),
      (cls_eq_iff (pull_isLB hP l) hP₀).2 eP, ← cls_pull hP₀ m₀ (pull_isLB hP₀ m₀),
      (cls_eq_iff hQ₀ (pull_isLB hP₀ m₀)).2 eQ₀]
  exact lift_unique HG HD.1 hκ hπ hI hA hg hA hg h h hl.1 hl.2 hL aL hL aL hQ₀ hQ q₁ q₂ eQ hP' h₁' h₂' e'

end GlobalTheory.BirigidLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BirigidifiedLiftPullbackOneProdEndomorphismStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.birigidified_lift_pullback_one_prod_endomorphism : GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.Published.AbelianDualCrystal →
    ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (κ : DividedPowers I), IsNilDP κ →
    ∀ (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I →
    ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A : Over (Sp R)) [GrpObj A] (i : A₀.left ⟶ A.left),
      IsGrpPullback A₀ A (spMap π) i → IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ (l : (A₀ ⊗ A₀).left ⟶ (A ⊗ A).left), IsSquare i l →
    ∀ (L : LB A.left), L.IsLB → Out.RelAmple A L →
    ∀ (u₀ : A₀ ⟶ A₀) (u : A ⟶ A) [IsMonHom u₀] [IsMonHom u], u₀.left ≫ i = i ≫ u.left →
    ∀ (P₀ Q₀ : LB (A₀ ⊗ A₀).left), P₀.IsLB → Q₀.IsLB → LBIso Q₀ (P₀.pull (lift (fst A₀ A₀) (snd A₀ A₀ ≫ u₀)).left) →
    ∀ (P Q : LB (A ⊗ A).left), P.IsLB → Q.IsLB →
      HasGen (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left) → HasGen (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left) →
      HasGen (Q.pull (lift (1 : A ⟶ A) (𝟙 A)).left) → HasGen (Q.pull (lift (𝟙 A) (1 : A ⟶ A)).left) →
      LBIso (P.pull l) P₀ → LBIso (Q.pull l) Q₀ → LBIso Q (P.pull (lift (fst A A) (snd A A ≫ u)).left) := by
  first | exact @GlobalTheory.BirigidLift.pull_one_prod_of_lift | exact GlobalTheory.BirigidLift.pull_one_prod_of_lift | (intros; apply GlobalTheory.BirigidLift.pull_one_prod_of_lift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkLiftFiniteCoverNormalLocal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkLiftFiniteCoverNormalLocal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FiniteLift

theorem exists_retraction {V B : Type} [CommRing V] [IsDomain V] [IsIntegrallyClosed V] [CommRing B]
    (φ : V →+* B) (hφ : φ.IsIntegral) (ψ : B →+* FractionRing V)
    (h : ψ.comp φ = algebraMap V (FractionRing V)) :
    ∃ s : B →+* V, s.comp φ = RingHom.id V ∧ (algebraMap V (FractionRing V)).comp s = ψ := by
  have hinj : Function.Injective (algebraMap V (FractionRing V)) := IsFractionRing.injective _ _
  have hmem : ∀ b, ψ b ∈ (algebraMap V (FractionRing V)).range := by
    intro b
    obtain ⟨p, hp, hpb⟩ := hφ b
    have : IsIntegral V (ψ b) := ⟨p, hp, by rw [← h, ← Polynomial.hom_eval₂, hpb, map_zero]⟩
    exact IsIntegrallyClosed.algebraMap_eq_of_integral this
  let e := RingEquiv.ofBijective (algebraMap V (FractionRing V)).rangeRestrict
    ⟨fun a b hab => hinj (congrArg Subtype.val hab), RingHom.rangeRestrict_surjective _⟩
  have key : ∀ b, algebraMap V (FractionRing V) (e.symm (ψ.codRestrict _ hmem b)) = ψ b := fun b =>
    congrArg Subtype.val (e.apply_symm_apply (ψ.codRestrict _ hmem b))
  refine ⟨e.symm.toRingHom.comp (ψ.codRestrict _ hmem), ?_, ?_⟩
  · ext v
    apply hinj
    exact (key (φ v)).trans (DFunLike.congr_fun h v)
  · ext b
    exact key b

theorem exists_lift {V : Type} [CommRing V] [IsDomain V] [IsIntegrallyClosed V]
    {X Z : Scheme.{0}} (π : X ⟶ Z) [IsFinite π] (f : Sp V ⟶ Z) (y : Sp (FractionRing V) ⟶ X)
    (h : y ≫ π = jK V ≫ f) : ∃ l : Sp V ⟶ X, l ≫ π = f ∧ jK V ≫ l = y := by
  have : IsAffine (pullback π f) := isAffine_of_isAffineHom (pullback.snd π f)
  let P := pullback π f
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (P.isoSpec.inv ≫ pullback.snd π f)
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (pullback.lift y (jK V) h ≫ P.isoSpec.hom)
  have hfin : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
  rw [IsFinite.SpecMap_iff] at hfin
  have hc : φ ≫ ψ = CommRingCat.ofHom (algebraMap V (FractionRing V)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ, hψ, Category.assoc, Iso.hom_inv_id_assoc]
    exact pullback.lift_snd _ _ _
  obtain ⟨s, hs1, hs2⟩ := exists_retraction φ.hom hfin.to_isIntegral ψ.hom
    (congrArg CommRingCat.Hom.hom hc)
  have h1 : Spec.map (CommRingCat.ofHom s) ≫ P.isoSpec.inv ≫ pullback.snd π f = 𝟙 _ := by
    rw [← hφ, ← Spec.map_comp, ← Spec.map_id]
    congr 1
    exact CommRingCat.hom_ext hs1
  have h2 : jK V ≫ Spec.map (CommRingCat.ofHom s) =
      pullback.lift y (jK V) h ≫ P.isoSpec.hom := by
    rw [← hψ, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext hs2
  refine ⟨Spec.map (CommRingCat.ofHom s) ≫ P.isoSpec.inv ≫ pullback.fst π f, ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% h1]
  · rw [reassoc_of% h2, Iso.hom_inv_id_assoc]
    exact pullback.lift_fst _ _ _

theorem exists_stalk_lift : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsIntegrallyClosed V₁ → ∀ (X Z : Scheme.{0}) (π : X ⟶ Z), IsFinite π → ∀ (f : Sp V₁ ⟶ Z) (yM : Sp (FractionRing V₁) ⟶ X), yM ≫ π = jK V₁ ≫ f → ∃ (z₁ : X) (ev : X.presheaf.stalk z₁ →+* V₁), IsLocalHom ev ∧ spMap ev ≫ X.fromSpecStalk z₁ ≫ π = f ∧ jK V₁ ≫ spMap ev ≫ X.fromSpecStalk z₁ = yM := by
  intro V _ _ _ hV X Z π hπ f y h
  obtain ⟨l, h1, h2⟩ := exists_lift π f y h
  have e : spMap (Scheme.stalkClosedPointTo (R := .of V) l).hom ≫ X.fromSpecStalk _ = l :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of V) l
  refine ⟨_, (Scheme.stalkClosedPointTo (R := .of V) l).hom, inferInstance, ?_, ?_⟩
  · rw [reassoc_of% e, h1]
  · rw [e, h2]

end GlobalTheory.FiniteLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkLiftFiniteCoverNormalLocalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_stalk_lift_finite_cover_normal_local : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsIntegrallyClosed V₁ → ∀ (X Z : Scheme.{0}) (π : X ⟶ Z), IsFinite π → ∀ (f : Sp V₁ ⟶ Z) (yM : Sp (FractionRing V₁) ⟶ X), yM ≫ π = jK V₁ ≫ f → ∃ (z₁ : X) (ev : X.presheaf.stalk z₁ →+* V₁), IsLocalHom ev ∧ spMap ev ≫ X.fromSpecStalk z₁ ≫ π = f ∧ jK V₁ ≫ spMap ev ≫ X.fromSpecStalk z₁ = yM := by
  first | exact @GlobalTheory.FiniteLift.exists_stalk_lift | exact GlobalTheory.FiniteLift.exists_stalk_lift | (intros; apply GlobalTheory.FiniteLift.exists_stalk_lift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackTwistedSectionIso
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.Twist

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CutPull

variable {X Y : Scheme.{0}} (f : Y ⟶ X) {L : LB X}

theorem homEquiv_pullbackZIso_hom (hL : L.IsLB) (G : X.Modules) (n : ℤ) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ (pullbackZIso G f hL n).hom =
      Twist.map (lbZPow L n) ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app G) ≫
        (projZIso f hL ((Scheme.Modules.pullback f).obj G) n).inv := by
  have e : (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (twist G (lbZPow L n)) ≫
      (Scheme.Modules.pushforward f).map (pullbackHom G (lbZPow L n) f) =
        Twist.map (lbZPow L n) ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app G) ≫
          (projIso (lbZPow L n) f _).inv :=
    ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_unit _ _ _).symm.trans
      (Equiv.apply_symm_apply _ _)
  rw [Adjunction.homEquiv_unit, pullbackZIso, Iso.trans_hom, Functor.map_comp, ← Category.assoc,
    pullbackIso_hom, e, projZIso, Iso.trans_inv, Functor.mapIso_inv, Iso.symm_hom, Category.assoc]

theorem pullback_mulSecOfEq (hL : L.IsLB) (G : X.Modules) {n m k : ℤ} (σ : LB.Sec (lbZPow L m))
    (h : n + m = k) :
    (Scheme.Modules.pullback f).map (mulSecOfEq G σ h) ≫ (pullbackZIso G f hL k).hom =
      (pullbackZIso G f hL n).hom ≫ mulSecOfEq ((Scheme.Modules.pullback f).obj G) (zpull f σ) h := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    homEquiv_pullbackZIso_hom, homEquiv_pullbackZIso_hom, Category.assoc]
  have e : (Scheme.Modules.pushforward f).map
      (mulSecOfEq ((Scheme.Modules.pullback f).obj G) (zpull f σ) h) ≫
        (projZIso f hL ((Scheme.Modules.pullback f).obj G) k).hom =
      (projZIso f hL ((Scheme.Modules.pullback f).obj G) n).hom ≫
        mulSecOfEq ((Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback f).obj G)) σ h := by
    refine zhom_ext fun V (s : Γ(twistZ ((Scheme.Modules.pullback f).obj G) (L.pull f) n, f ⁻¹ᵁ V)) i => ?_
    refine (zcoord_projZIso_hom_app f hL _ ((mulSecOfEq _ (zpull f σ) h).app _ s) i).trans ?_
    refine Eq.trans ?_ (zcoord_mulSecOfEq_app σ h ((projZIso f hL _ n).hom.app V s) i).symm
    have e : (f.app (V ⊓ L.U i)).hom (resG X inf_le_right (zfun σ i)) =
        (f.appLE (L.U i) _ (f.preimage_mono (inf_le_right : V ⊓ L.U i ≤ L.U i))).hom (zfun σ i) := by
      rw [← Scheme.Hom.appLE_eq_app, LB.appLE_resG]
    rw [zcoord_mulSecOfEq_app, resM_smul, resG_resG, zfun_zpull, LB.resG_appLE]
    refine Eq.trans (congrArg (· • resM _ (le_pidx_inf f V i) (zcoord s (pidx L f i))) e.symm) ?_
    exact congrArg (fun t : Γ((Scheme.Modules.pullback f).obj G, f ⁻¹ᵁ (V ⊓ L.U i)) =>
      (f.app (V ⊓ L.U i)).hom (resG X inf_le_right (zfun σ i)) • t)
      (zcoord_projZIso_hom_app f hL _ s i).symm
  have e' : (projZIso f hL ((Scheme.Modules.pullback f).obj G) n).inv ≫
      (Scheme.Modules.pushforward f).map (mulSecOfEq ((Scheme.Modules.pullback f).obj G) (zpull f σ) h) =
        mulSecOfEq ((Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback f).obj G)) σ h ≫
          (projZIso f hL ((Scheme.Modules.pullback f).obj G) k).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
    exact e
  rw [e', ← Category.assoc, ← Category.assoc]
  congr 1
  symm
  refine zhom_ext fun V s i => ?_
  change zcoord ((mulSecOfEq _ σ h).app V ((Twist.map (lbZPow L n) _).app V s)) i =
    zcoord ((Twist.map (lbZPow L k) _).app V ((mulSecOfEq G σ h).app V s)) i
  rw [zcoord_mulSecOfEq_app, zcoord_map_app, zcoord_map_app, zcoord_mulSecOfEq_app,
    Scheme.Modules.Hom.app_smul]

end GlobalTheory.CutPull

namespace GlobalTheory


open GlobalTheory.CutPull in
theorem cut_pullback_iso : ∀ {X Y : Scheme.{0}} (f : Y ⟶ X) (G : X.Modules) [G.IsQuasicoherent] {L : LB X} (hL : L.IsLB) (s : L.Sec) (hL' : (L.pull f).IsLB), Nonempty ((Scheme.Modules.pullback f).obj (cut G hL s) ≅ cut ((Scheme.Modules.pullback f).obj G) hL' (secPull s f)) := by
  intro X Y f G _ L hL s hL'
  have : PreservesColimits (Scheme.Modules.pullback f) :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).leftAdjoint_preservesColimits
  have hz : ∀ j, zfun (zpull f (zofSec s)) j = zfun (zofSec (secPull s f)) j := fun j => by
    rw [zfun_zpull, zfun_zofSec, zfun_zofSec]
    rfl
  have hM : mulSecOfEq ((Scheme.Modules.pullback f).obj G) (zpull f (zofSec s)) (neg_add_cancel (1 : ℤ)) =
      mulSecOfEq ((Scheme.Modules.pullback f).obj G) (zofSec (secPull s f)) (neg_add_cancel (1 : ℤ)) :=
    zhom_ext fun V t j => by rw [zcoord_mulSecOfEq_app, zcoord_mulSecOfEq_app, hz]
  have e := pullback_mulSecOfEq f hL G (zofSec s) (neg_add_cancel (1 : ℤ))
  rw [hM, ← Iso.eq_comp_inv] at e
  have key : (Scheme.Modules.pullback f).map (cutHom G hL s) =
      (pullbackZIso G f hL (-1)).hom ≫
        (mulSecOfEq ((Scheme.Modules.pullback f).obj G) (zofSec (secPull s f)) (neg_add_cancel (1 : ℤ)) ≫
          ((pullbackZIso G f hL 0).symm ≪≫ (Scheme.Modules.pullback f).mapIso (twistZZeroIso G hL).symm).hom) := by
    rw [cutHom, Functor.map_comp, e]
    simp
  exact ⟨PreservesCokernel.iso (Scheme.Modules.pullback f) (cutHom G hL s) ≪≫ cokernelIsoOfEq key ≪≫
    cokernelEpiComp _ _ ≪≫ cokernelCompIsIso _ _ ≪≫
    (cokernelCompIsIso _ (twistZZeroIso ((Scheme.Modules.pullback f).obj G) hL').inv).symm⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocycleCohomologousOfDeRhamSurjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocycleCohomologousOfDeRhamSurjective
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PtExt.Lift

variable {R : Type} [CommRing R] {X : Over (Sp R)}

def trivEquiv (T : Thick (dp0 R) (X.hom ≫ 𝟙 _)) (hT : T.J = ⊥) : T.B ≃+* T.B₀ :=
  RingEquiv.ofBijective T.π ⟨(injective_iff_map_eq_zero T.π).2 fun b hb ↦ by
      have h := (T.ker b).1 hb
      rw [hT] at h
      exact Ideal.mem_bot.1 h, T.surj⟩

theorem trivEquiv_symm_π (T : Thick (dp0 R) (X.hom ≫ 𝟙 _)) (hT : T.J = ⊥) (b : T.B) :
    (trivEquiv T hT).symm (T.π b) = b :=
  (trivEquiv T hT).symm_apply_apply b

def trivPt (T : Thick (dp0 R) (X.hom ≫ 𝟙 _)) (hT : T.J = ⊥) : Pt X T.B :=
  Over.homMk (U := SpAlg R T.B) (spMap ((trivEquiv T hT).symm.toRingHom) ≫ T.x) (by
    have h : T.x ≫ X.hom = spMap (T.π.comp (algebraMap R T.B)) :=
      ((Category.comp_id _).symm.trans (Category.assoc _ _ _)).trans T.w
    change (spMap _ ≫ T.x) ≫ X.hom = spMap (algebraMap R T.B)
    rw [Category.assoc, h, ← Cris.spMap_comp]
    congr 1
    ext r
    exact trivEquiv_symm_π T hT _)

theorem spOver_trivPt {T T' : Thick (dp0 R) (X.hom ≫ 𝟙 _)} (hT : T.J = ⊥) (hT' : T'.J = ⊥) (φ : T ⟶ T') :
    spOver φ.φ ≫ trivPt T hT = trivPt T' hT' := by
  apply Over.OverMorphism.ext
  change spMap (φ.φ : T.B →+* T'.B) ≫ spMap ((trivEquiv T hT).symm.toRingHom) ≫ T.x =
    spMap ((trivEquiv T' hT').symm.toRingHom) ≫ T'.x
  rw [← φ.pt, ← Category.assoc, ← Category.assoc, ← Cris.spMap_comp, ← Cris.spMap_comp]
  congr 2
  ext b
  obtain ⟨b, rfl⟩ := T.surj b
  change φ.φ ((trivEquiv T hT).symm (T.π b)) = (trivEquiv T' hT').symm (φ.φ₀ (T.π b))
  rw [φ.comm, trivEquiv_symm_π, trivEquiv_symm_π]

theorem trivPt_trivAt {D : Type} [CommRing D] [Algebra R D] (x : Pt X D) : trivPt (trivAt x) rfl = x := by
  apply Over.OverMorphism.ext
  change spMap ((trivEquiv (trivAt x) rfl).symm.toRingHom) ≫ x.left = x.left
  have : (trivEquiv (trivAt x) rfl).symm.toRingHom = RingHom.id D :=
    RingHom.ext fun b ↦ trivEquiv_symm_π (trivAt x) rfl b
  rw [this, Cris.spMap_id, Category.id_comp]

def trivCoc (u : Fn1 X) (hu : IsCoc (whole X) u) :
    Z1 ((IsTriv (X.hom ≫ 𝟙 _)).ι ⋙ O (dp0 R) (X.hom ≫ 𝟙 _)) :=
  ⟨fun T T' φ ↦ u T.obj.B T'.obj.B φ.hom.φ (trivPt T.obj T.property), fun T T' T'' φ ψ ↦ by
    change u _ _ (ψ.hom.φ.comp φ.hom.φ) _ = ψ.hom.φ (u _ _ φ.hom.φ _) + u _ _ ψ.hom.φ _
    rw [hu _ _ _ φ.hom.φ ψ.hom.φ _ (sm_whole _), spOver_trivPt T.property T'.property φ.hom]⟩

end GlobalTheory.PtExt.Lift


open GlobalTheory.PtExt.Lift in
theorem GlobalTheory.PtExt.cohom_fv_of_toH1O_surjective : ∀ (R : Type) [CommRing R] (X : Over (Sp R)),
    Function.Surjective (toH1O (X.hom ≫ 𝟙 _)) → ∀ u : Fn1 X, IsCoc (whole X) u →
      ∃ f : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _)), Cohom (whole X) u (fv f) := by
  intro R _ X hs u hu
  obtain ⟨c, hc⟩ := hs (H1.mk _ (trivCoc u hu))
  obtain ⟨f, rfl⟩ := H1.mk_surjective _ c
  have hc' : H1.mk _ ((CoefMap.restrict (O (dp0 R) (X.hom ≫ 𝟙 _)) (IsTriv (X.hom ≫ 𝟙 _)).ι).pullbackOneCocycle f) =
      H1.mk _ (trivCoc u hu) := hc
  obtain ⟨g, hg⟩ := H1.mk_eq_mk.1 hc'
  refine ⟨f, fun D _ _ x ↦ -g ⟨trivAt x, rfl⟩, ?_⟩
  intro D _ _ D' _ _ φ x _
  let T : (IsTriv (X.hom ≫ 𝟙 _)).FullSubcategory := ⟨trivAt x, rfl⟩
  let T' : (IsTriv (X.hom ≫ 𝟙 _)).FullSubcategory := ⟨trivAt (spOver φ ≫ x), rfl⟩
  let a : T ⟶ T' := ObjectProperty.homMk (trivMap φ x)
  let b : D := g T
  let b' : D' := g T'
  have h := congrFun (congrFun (congrFun hg T) T') a
  change b' - φ b = ev f (trivMap φ x) - u D D' φ (trivPt (trivAt x) rfl) at h
  rw [trivPt_trivAt] at h
  change u D D' φ x + -ev f (trivMap φ x) = -b' - φ (-b)
  rw [map_neg]
  linear_combination h
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocycleCohomologousOfDeRhamSurjectiveStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cocycle_cohomologous_of_de_rham_surjective : ∀ (R : Type) [CommRing R] (X : Over (Sp R)), Function.Surjective (toH1O (X.hom ≫ 𝟙 _)) → ∀ u : Fn1 X, IsCoc (whole X) u → ∃ f : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _)), Cohom (whole X) u (fv f) := by
  first | exact @GlobalTheory.PtExt.cohom_fv_of_toH1O_surjective | exact GlobalTheory.PtExt.cohom_fv_of_toH1O_surjective | (intros; apply GlobalTheory.PtExt.cohom_fv_of_toH1O_surjective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalFiniteModelOfExtension
open CategoryTheory Limits AlgebraicGeometry IsLocalRing TensorProduct
open GlobalTheory GlobalTheory.QCoh GlobalTheory.Vert GlobalTheory.PerfdLat GlobalTheory.Published

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BplusDescent

section Field

variable {X : Scheme.{0}} [IsIntegral X] {L : Type} [Field L] (φ : X.presheaf.stalk (genericPoint X) ⟶ .of L)

abbrev fieldPt : Spec (.of L) ⟶ X := Spec.map φ ≫ X.fromSpecStalk (genericPoint X)

theorem fieldPt_apply (x : Spec (.of L)) : fieldPt φ x = genericPoint X := by
  letI : Field (X.presheaf.stalk (genericPoint X)) := inferInstanceAs (Field X.functionField)
  have : Spec.map φ x = closedPoint (X.presheaf.stalk (genericPoint X)) :=
    Subsingleton.elim (α := PrimeSpectrum (X.presheaf.stalk (genericPoint X))) _ _
  change X.fromSpecStalk _ (Spec.map φ x) = _
  rw [this]
  exact Scheme.fromSpecStalk_closedPoint

theorem top_le_fieldPt {U : X.Opens} (hU : genericPoint X ∈ U) : ⊤ ≤ fieldPt φ ⁻¹ᵁ U := fun x _ => by
  change fieldPt φ x ∈ U
  rwa [fieldPt_apply]

theorem fieldPt_appLE {U : X.Opens} (hU : genericPoint X ∈ U) :
    (fieldPt φ).appLE U ⊤ (top_le_fieldPt φ hU) ≫ (Scheme.ΓSpecIso (.of L)).hom = X.presheaf.germ U _ hU ≫ φ := by
  have h1 : ⊤ ≤ X.fromSpecStalk (genericPoint X) ⁻¹ᵁ U := fun x _ => by
    letI : Field (X.presheaf.stalk (genericPoint X)) := inferInstanceAs (Field X.functionField)
    have : x = closedPoint (X.presheaf.stalk (genericPoint X)) :=
      Subsingleton.elim (α := PrimeSpectrum (X.presheaf.stalk (genericPoint X))) _ _
    change X.fromSpecStalk _ x ∈ U
    rw [this, Scheme.fromSpecStalk_closedPoint]
    exact hU
  rw [← Scheme.Hom.appLE_comp_appLE (Spec.map φ) (X.fromSpecStalk (genericPoint X)) U ⊤ ⊤ h1 le_rfl]
  have h2 : (Spec.map φ).appLE ⊤ ⊤ le_rfl = (Spec.map φ).appTop := (Scheme.Hom.app_eq_appLE _).symm
  rw [h2, Category.assoc, Scheme.ΓSpecIso_naturality, Scheme.Hom.appLE, Scheme.fromSpecStalk_app hU]
  simp only [Category.assoc, ← Functor.map_comp_assoc]
  have h3 : ∀ i : (Opposite.op ⊤ : (Spec (X.presheaf.stalk (genericPoint X))).Opensᵒᵖ) ⟶ Opposite.op ⊤,
      (Spec (X.presheaf.stalk (genericPoint X))).presheaf.map i = 𝟙 _ := fun i => by
    rw [Subsingleton.elim i (𝟙 _)]; exact CategoryTheory.Functor.map_id _ _
  rw [h3]
  simp

def normFun {U : X.Opens} (hU : genericPoint X ∈ U) :
    Γ((fieldPt φ).normalization, (fieldPt φ).fromNormalization ⁻¹ᵁ U) ⟶ .of L :=
  (fieldPt φ).toNormalization.appLE _ ⊤ (by
    rw [← Scheme.Hom.comp_preimage, Scheme.Hom.toNormalization_fromNormalization]; exact top_le_fieldPt φ hU) ≫
    (Scheme.ΓSpecIso (.of L)).hom

theorem app_normFun {U : X.Opens} (hU : genericPoint X ∈ U) :
    (fieldPt φ).fromNormalization.app U ≫ normFun φ hU = X.presheaf.germ U _ hU ≫ φ := by
  have key : ∀ (g : Spec (.of L) ⟶ X) (_ : g = fieldPt φ) (e : ⊤ ≤ g ⁻¹ᵁ U),
      g.appLE U ⊤ e = (fieldPt φ).appLE U ⊤ (top_le_fieldPt φ hU) := by
    rintro _ rfl _
    rfl
  rw [normFun, ← fieldPt_appLE, ← Category.assoc]
  congr 1
  exact (Scheme.Hom.comp_appLE _ _ _ _ _).symm.trans (key _ (fieldPt φ).toNormalization_fromNormalization (by
    rw [Scheme.Hom.toNormalization_fromNormalization]; exact top_le_fieldPt φ hU))

theorem normFun_spec {U : X.Opens} (hU : genericPoint X ∈ U) (hA : IsAffineOpen U) :
    Function.Injective (normFun φ hU).hom ∧
      ∀ x : L, x ∈ (normFun φ hU).hom.range ↔ (X.presheaf.germ U _ hU ≫ φ).hom.IsIntegralElem x := by
  let u := fieldPt φ
  letI := (u.app U).hom.toAlgebra
  let ε : Γ(Spec (.of L), u ⁻¹ᵁ U) ⟶ .of L :=
    (Spec (.of L)).presheaf.map (homOfLE (top_le_fieldPt φ hU)).op ≫ (Scheme.ΓSpecIso (.of L)).hom
  have hε : Function.Bijective ε.hom := by
    have : homOfLE (top_le_fieldPt φ hU) = eqToHom (top_le_iff.1 (top_le_fieldPt φ hU)).symm := Subsingleton.elim _ _
    haveI : IsIso ε := by
      simp only [ε, this]
      infer_instance
    exact ConcreteCategory.bijective_of_isIso ε
  have h1 : normFun φ hU = (u.normalizationObjIso hA).hom ≫
      CommRingCat.ofHom (integralClosure Γ(X, U) Γ(Spec (.of L), u ⁻¹ᵁ U)).val.toRingHom ≫ ε := by
    rw [← Category.assoc, u.normalizationObjIso_hom_val hA, normFun]
    simp only [ε]
    rw [Scheme.Hom.appLE_map_assoc]
  have h2 : X.presheaf.germ U _ hU ≫ φ = u.app U ≫ ε := by
    rw [← fieldPt_appLE, Scheme.Hom.appLE, Category.assoc]
  have hb := ConcreteCategory.bijective_of_isIso (u.normalizationObjIso hA).hom
  rw [h1, h2]
  refine ⟨hε.1.comp (Subtype.val_injective.comp hb.1), fun x => ⟨?_, ?_⟩⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨p, hp, hp0⟩ := ((u.normalizationObjIso hA).hom y).2
    refine ⟨p, hp, ?_⟩
    have := congrArg ε.hom hp0
    rw [Polynomial.hom_eval₂, map_zero] at this
    exact this
  · rintro ⟨p, hp, hp0⟩
    obtain ⟨y, rfl⟩ := hε.2 x
    have hy : IsIntegral Γ(X, U) y := ⟨p, hp, hε.1 (by rw [Polynomial.hom_eval₂, map_zero]; exact hp0)⟩
    obtain ⟨z, hz⟩ := hb.2 ⟨y, hy⟩
    exact ⟨z, congrArg (fun w : integralClosure Γ(X, U) Γ(Spec (.of L), u ⁻¹ᵁ U) => ε.hom w.1) hz⟩

end Field

end GlobalTheory.BplusDescent

end
end
