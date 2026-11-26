module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TheoremOfCubePolAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NormalisedPolarisation
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NormalisedPolarisationStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAppellHumbertFrameOfPulledBiextension
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAppellHumbertFrameOfPulledBiextension
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.PulledBiextFrame

open GlobalTheory.CubeValues GlobalTheory.SelfCube

def combUnif {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
    {K : Type} [Fintype K] (φ : K → (A.left ⟶ A.left))
    (p : K → (Fin g → ℂ) → (Fin g → ℂ)) (hd : ∀ k, Differentiable ℂ (p k)) (ε : K → ℤ)
    (hp : ∀ k z, (u.ex z).left ≫ φ k = (u.ex (p k z)).left) :
    HolUnif A (LB.LinComb L φ ε) g where
  ex := u.ex
  ex_add := u.ex_add
  ex_onto := u.ex_onto
  Λ := u.Λ
  ker := u.ker
  discrete := u.discrete
  full := u.full
  hol := u.hol
  fr := fun j z => ∏ k, u.fr (j k) (p k z) ^ ε k
  fr_hol := fun j => by
    have hD : ∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (LB.LinComb L φ ε).U j →
        ∀ k, ⊤ ≤ (u.ex (p k z)).left ⁻¹ᵁ L.U (j k) := fun z hz k => by
      rw [← hp]; exact (le_preimage_wchart (u.ex z).left L φ j).1 hz k
    refine differentiableOn_prod' _ fun k => DifferentiableOn.zpow
      ((u.fr_hol (j k)).comp (hd k).differentiableOn fun z hz => hD z hz k) ?_
    exact Or.inl fun z hz => u.fr_ne _ _ (hD z hz k)
  fr_ne := fun j z hz => by
    refine Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (u.fr_ne _ _ ?_)
    rw [← hp]; exact (le_preimage_wchart (u.ex z).left L φ j).1 hz k
  fr_compat := fun j j' z hz => by
    obtain ⟨h1, h2⟩ := (le_preimage_inf _ _ _).1 hz
    have e := val_linComb (u.ex z).left GlobalTheory.valAt'_rules L φ ε j j' h1 h2
    refine Eq.trans ?_ (congrArg (· * _) e.symm)
    simp only [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    have a1 := (le_preimage_wchart (u.ex z).left L φ j).1 h1 k
    have a2 := (le_preimage_wchart (u.ex z).left L φ j').1 h2 k
    rw [hp] at a1 a2 ⊢
    rw [u.fr_compat _ _ _ ((le_preimage_inf _ _ _).2 ⟨a1, a2⟩), mul_zpow]

theorem exists_appellHumbert_frame :
    Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (Ef : LinearMap.BilinForm ℤ u.Λ) (w : P.A ⟶ P.A) (F F' : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ)), u.IsAH Hm χ → (∀ a b : u.Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) → (∀ z, u.ex (F z) = u.ex z ≫ w) → F + F' = LinearMap.id → (∀ z z', hermForm Hm (F z) z' = hermForm Hm z (F' z')) → ∃ (u₁ : HolUnif P.A (cubeLB P.A ![𝟙 P.A, w] P.L) P.g) (χ₁ : u₁.Λ → ℂ), u₁.ex = u.ex ∧ u₁.Λ = u.Λ ∧ u₁.IsAH Hm χ₁ ∧ ∀ (l : u₁.Λ) (a b : u.Λ), (a : Fin P.g → ℂ) = l → (b : Fin P.g → ℂ) = F l → χ₁ l = (-1) ^ Ef a b := by
  intro _ _ _ _ P u Hm χ Ef w F F' ⟨hH, hpos, hχ, hfr⟩ hE hw hFF hadj
  classical
  have hv : ValueRules := GlobalTheory.valAt'_rules
  have hF : ∀ l ∈ u.Λ, F l ∈ u.Λ := fun l hl => by
    have h0 := hw 0
    rw [map_zero, ex_zero] at h0
    rw [← u.ker, hw, (u.ker l).2 hl, ← h0]
  have hsc := fun l m => semicharacter_rule hv P.isLB u hH χ hfr l m _ (hE l m)
  have hχ0 : ∀ l, χ l ≠ 0 := fun l h => by simpa [h] using hχ l
  let Y : Fin 2 → (Fin P.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ) := ![LinearMap.id, F]
  have hy : ∀ k z, u.ex z ≫ (![𝟙 P.A, w] : Fin 2 → _) k = u.ex (Y k z) := by
    intro k z
    fin_cases k
    · exact Category.comp_id _
    · exact (hw z).symm
  let p : ULift.{0} (Finset (Fin 2)) → (Fin P.g → ℂ) → (Fin P.g → ℂ) := fun I z => ∑ k ∈ I.down, Y k z
  have hpd : ∀ I, Differentiable ℂ (p I) := fun I =>
    Differentiable.fun_sum fun k _ => (LinearMap.toContinuousLinearMap (Y k)).differentiable
  have hps : ∀ (I : ULift.{0} (Finset (Fin 2))) z,
      (u.ex z).left ≫ (psum P.A ![𝟙 P.A, w] I.down).left = (u.ex (p I z)).left := fun I z => by
    rw [← Over.comp_left, comp_psum u (u.ex z) _ (fun k => Y k z) (fun k => hy k z)]
  refine ⟨combUnif u _ p hpd _ hps, fun l : u.Λ => (-1) ^ Ef l ⟨F l, hF l l.2⟩, rfl, rfl,
    ⟨hH, hpos, fun l => by simp [norm_zpow], ?_⟩, ?_⟩
  · intro (l : u.Λ) j z hz
    have hc : ∀ I, ⊤ ≤ (u.ex (p I z)).left ⁻¹ᵁ P.L.U (j I) := fun I => by
      rw [← hps]; exact (le_preimage_wchart (u.ex z).left P.L _ j).1 hz I
    change ∏ I, u.fr (j I) (p I z) ^ ((-1 : ℤ) ^ (2 - I.down.card)) =
      (-1) ^ Ef l ⟨F l, hF l l.2⟩ *
        Complex.exp (Real.pi * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l) *
        ∏ I, u.fr (j I) (p I (z + l)) ^ ((-1 : ℤ) ^ (2 - I.down.card))
    rw [prod_finset_fin_two fun I => u.fr (j ⟨I⟩) (p ⟨I⟩ z) ^ ((-1 : ℤ) ^ (2 - I.card)),
      prod_finset_fin_two fun I => u.fr (j ⟨I⟩) (p ⟨I⟩ (z + l)) ^ ((-1 : ℤ) ^ (2 - I.card))]
    have p0 : ∀ x, p ⟨∅⟩ x = 0 := fun x => by simp [p]
    have p1 : ∀ x, p ⟨{0}⟩ x = x := fun x => by simp [p, Y]
    have p2 : ∀ x, p ⟨{1}⟩ x = F x := fun x => by simp [p, Y]
    have p3 : ∀ x, p ⟨{0, 1}⟩ x = x + F x := fun x => by simp [p, Y]
    have c1 := hc ⟨{0}⟩
    have c2 := hc ⟨{1}⟩
    have c3 := hc ⟨{0, 1}⟩
    rw [p1] at c1
    rw [p2] at c2
    rw [p3] at c3
    have e1 := hfr l _ _ c1
    have e2 := hfr ⟨F l, hF l l.2⟩ _ _ c2
    have e3 := hfr (l + ⟨F l, hF l l.2⟩) _ _ c3
    rw [hsc] at e3
    have k2 : ({0, 1} : Finset (Fin 2)).card = 2 := by decide
    have s3 : z + F z + ((l + ⟨F l, hF l l.2⟩ : u.Λ) : Fin P.g → ℂ) = z + l + F (z + l) := by
      simp only [Submodule.coe_add, map_add (f := _)]; abel
    rw [s3] at e3
    have haddR : ∀ x y y', hermForm Hm x (y + y') = hermForm Hm x y + hermForm Hm x y' := fun x y y' => by
      simp [hermForm, Matrix.mulVec_add, dotProduct_add]
    have haddL : ∀ x x' y, hermForm Hm (x + x') y = hermForm Hm x y + hermForm Hm x' y := fun x x' y => by
      simp [hermForm, star_add, add_dotProduct]
    have hsum : ∀ x y, hermForm Hm x (F y) + hermForm Hm (F x) y = hermForm Hm x y := fun x y => by
      rw [hadj, ← haddR]
      exact congrArg _ (LinearMap.congr_fun hFF y)
    change _ = _ * Complex.exp (Real.pi * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l) * _ at e1
    change _ = _ * Complex.exp (Real.pi * hermForm Hm (F z) (F l) +
      Real.pi / 2 * hermForm Hm (F l) (F l)) * u.fr _ (F z + F l) at e2
    change _ = _ * Complex.exp (Real.pi * hermForm Hm (z + F z) (l + F l) +
      Real.pi / 2 * hermForm Hm (l + F l) (l + F l)) * _ at e3
    rw [← map_add (f := _)] at e2
    have hx : Real.pi * hermForm Hm (z + F z) (l + F l) +
        Real.pi / 2 * hermForm Hm (l + F l) (l + F l) =
        (Real.pi * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l) +
        (Real.pi * hermForm Hm z l + Real.pi / 2 * hermForm Hm l l) +
        (Real.pi * hermForm Hm (F z) (F l) + Real.pi / 2 * hermForm Hm (F l) (F l)) := by
      simp only [haddL, haddR]
      linear_combination (Real.pi : ℂ) * hsum z l + (Real.pi / 2 : ℂ) * hsum l l
    rw [hx, Complex.exp_add, Complex.exp_add (_ + _) (_ + _)] at e3
    simp only [p0, p1, p2, p3, k2, Finset.card_empty, Finset.card_singleton]
    rw [e1, e2, e3]
    have n1 := hχ0 l
    have n2 := hχ0 ⟨F l, hF l l.2⟩
    norm_num
    field_simp
  · intro (l : u.Λ) a b ha hb
    obtain rfl : a = l := Subtype.ext ha
    obtain rfl : b = ⟨F a, hF a a.2⟩ := Subtype.ext hb
    rfl

end GlobalTheory.PulledBiextFrame
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAppellHumbertFrameOfPulledBiextensionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.exists_appellHumbert_frame_of_pulled_biextension : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (Ef : LinearMap.BilinForm ℤ u.Λ) (w : P.A ⟶ P.A) (F F' : (Fin P.g → ℂ) →ₗ[ℂ] (Fin P.g → ℂ)), u.IsAH Hm χ → (∀ a b : u.Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) → (∀ z, u.ex (F z) = u.ex z ≫ w) → F + F' = LinearMap.id → (∀ z z', hermForm Hm (F z) z' = hermForm Hm z (F' z')) → ∃ (u₁ : HolUnif P.A (cubeLB P.A ![𝟙 P.A, w] P.L) P.g) (χ₁ : u₁.Λ → ℂ), u₁.ex = u.ex ∧ u₁.Λ = u.Λ ∧ u₁.IsAH Hm χ₁ ∧ ∀ (l : u₁.Λ) (a b : u.Λ), (a : Fin P.g → ℂ) = l → (b : Fin P.g → ℂ) = F l → χ₁ l = (-1) ^ Ef a b := by
  first | exact @GlobalTheory.PulledBiextFrame.exists_appellHumbert_frame | exact GlobalTheory.PulledBiextFrame.exists_appellHumbert_frame | (intros; apply GlobalTheory.PulledBiextFrame.exists_appellHumbert_frame <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaObjectOfPolarisedLattice
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory

theorem obbuild_hf_add_left {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (a b c : Fin g → ℂ) :
    hermForm Hm (a + b) c = hermForm Hm a c + hermForm Hm b c := by
  simp [hermForm, add_dotProduct]

theorem obbuild_hf_add_right {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (a b c : Fin g → ℂ) :
    hermForm Hm a (b + c) = hermForm Hm a b + hermForm Hm a c := by
  simp [hermForm, Matrix.mulVec_add, dotProduct_add]

theorem obbuild_hf_smul_left {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (r : ℂ) (a c : Fin g → ℂ) :
    hermForm Hm (r • a) c = r * hermForm Hm a c := by
  simp [hermForm, smul_dotProduct]

theorem obbuild_hf_smul_right {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (r : ℂ) (a c : Fin g → ℂ) :
    hermForm Hm a (r • c) = star r * hermForm Hm a c := by
  simp [hermForm, Matrix.mulVec_smul, dotProduct_smul]

theorem obbuild_adj {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (s : Set (Fin g → ℂ))
    (hs : Submodule.span ℝ s = ⊤) (F F' : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (h : ∀ a ∈ s, ∀ c ∈ s, (hermForm Hm (F a) c).im = (hermForm Hm a (F' c)).im) (z z' : Fin g → ℂ) :
    hermForm Hm (F z) z' = hermForm Hm z (F' z') := by
  have hz : ∀ z : Fin g → ℂ, hermForm Hm 0 z = 0 ∧ hermForm Hm z 0 = 0 := fun z => by simp [hermForm]
  have hr : ∀ (r : ℝ) (z : Fin g → ℂ), r • z = (r : ℂ) • z := fun r z => by
    ext i; simp
  have h1 : ∀ a ∈ s, ∀ c, (hermForm Hm (F a) c).im = (hermForm Hm a (F' c)).im := by
    intro a ha c
    have hc : c ∈ Submodule.span ℝ s := hs ▸ Submodule.mem_top
    induction hc using Submodule.span_induction with
    | mem x hx => exact h a ha x hx
    | zero => simp [hz]
    | add x y _ _ hx hy => simp [obbuild_hf_add_right, hx, hy]
    | smul r x _ hx => rw [hr, map_smul, obbuild_hf_smul_right, obbuild_hf_smul_right]; simp [hx]
  have h2 : ∀ a c, (hermForm Hm (F a) c).im = (hermForm Hm a (F' c)).im := by
    intro a c
    have ha : a ∈ Submodule.span ℝ s := hs ▸ Submodule.mem_top
    induction ha using Submodule.span_induction with
    | mem x hx => exact h1 x hx c
    | zero => simp [hz]
    | add x y _ _ hx hy => simp [obbuild_hf_add_left, hx, hy]
    | smul r x _ hx => rw [hr, map_smul, obbuild_hf_smul_left, obbuild_hf_smul_left]; simp [hx]
  apply Complex.ext
  · have := h2 (Complex.I • z) z'
    rw [map_smul, obbuild_hf_smul_left, obbuild_hf_smul_left] at this
    simpa using this
  · exact h2 z z'

theorem obbuild_ex_pow {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
    (z : Fin g → ℂ) (n : ℕ) : u.ex z ^ n = u.ex ((n : ℂ) • z) := by
  induction n with
  | zero => simp [(u.ker 0).2 u.Λ.zero_mem]
  | succ n ih => rw [pow_succ, ih, ← u.ex_add]; congr 1; push_cast; rw [add_smul, one_smul]

theorem obbuild_unitS {o : Type} [CommRing o] (em : o →+* ℂ) (u : oˣ) :
    unitS (spMap em) u = unitOn (Units.map em.toMonoidHom u) := by
  ext
  have := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom em)
  exact (congrArg (fun f => f.hom (u : o)) this).symm

theorem obbuild_unitOn_zpow {R : Type} [CommRing R] (u : Rˣ) (n : ℤ) : unitOn (u ^ n) = unitOn u ^ n := by
  simp [unitOn]

theorem thetaObject_of_lattice :
    Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (em : o →+* ℂ) (w w' : J) (La : Type) [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (lam : Fin (2 * g) → La) (ac : J → La → La) (Q : La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), Function.Bijective EF → (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm (Q x) (Q y)).im = EF x y) → (∀ j, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ x, F (Q x) = Q (ac j x)) → (∀ x, ac w x + ac w' x = x) → (∀ x y, EF (ac w x) y = EF x (ac w' y)) → (∀ i₁ i₂, Complex.exp (-(2 * Real.pi * Complex.I) * (EF (lam i₁) (lam i₂) : ℂ) / ((k : ℕ) : ℂ)) = em (b.ζ : o) ^ Out.stdSymp g i₁ i₂) → ∃ t : TObj g k J b (spMap em), t.Prim w w' ∧ (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH Hm χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ (Q).range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = Q x → χ' l = (-1) ^ EF x (ac w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((k : ℕ) : ℂ)⁻¹ • Q (lam i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q x) = Q (ac j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀) := by
  intro h1 h2 h3 h4 o _ g k J b em w w' La _ EF lam ac Q Hm hE ⟨hQ, hdisc, hspan, hH, hpos, him⟩ hac hw hadj hlam
  choose F hF using hac
  let Λ : Submodule ℤ (Fin g → ℂ) := LinearMap.range Q.toIntLinearMap
  let e : La ≃ₗ[ℤ] Λ := LinearEquiv.ofInjective Q.toIntLinearMap hQ
  have he : ∀ a : Λ, Q (e.symm a) = a := fun a => congrArg Subtype.val (e.apply_symm_apply a)
  have hbij : Function.Bijective (LinearMap.BilinForm.congr e EF) := by
    have : (LinearMap.BilinForm.congr e EF : Λ → Λ →ₗ[ℤ] ℤ) = e.symm.dualMap ∘ EF ∘ e.symm := by
      funext a; ext c; simp
    rw [this]
    exact e.symm.dualMap.bijective.comp (hE.comp e.symm.bijective)
  obtain ⟨P, u, χ, hg, hΛ, hAH, -, -⟩ := principalTorus_algebraic g Λ Hm (LinearMap.BilinForm.congr e EF) hdisc
    hspan hH hpos (fun a c => by rw [← he a, ← he c, him]; simp) hbij
  subst hg
  have hmem : ∀ z, z ∈ u.Λ ↔ z ∈ Q.range := fun z => by rw [hΛ]; rfl
  have hhom := fun j => GlobalTheory.T.existsUnique_isMonHom_of_linearMap_lattice_anyDim h1 h2 h3 h4 P P P.L P.L u u (F j) (fun z hz => by
    obtain ⟨x, rfl⟩ := (hmem z).1 hz
    exact (hmem _).2 ⟨_, (hF j x).symm⟩)
  choose act hact using fun j => (hhom j).exists
  have hFF : F w + F w' = LinearMap.id := by
    apply LinearMap.restrictScalars_injective ℝ
    refine LinearMap.ext_on hspan ?_
    rintro _ ⟨x, rfl⟩
    simp [hF, ← map_add (f := _), hw]
  have hmul : act w * act w' = 𝟙 P.A := by
    haveI := P.isAb.comm
    haveI := (hact w).1
    haveI := (hact w').1
    refine (GlobalTheory.T.existsUnique_isMonHom_of_linearMap_lattice_anyDim h1 h2 h3 h4 P P P.L P.L u u LinearMap.id (fun z hz => hz)).unique ⟨?_, fun z => ?_⟩
      ⟨inferInstance, fun z => by simp⟩
    · rw [Hom.mul_def]; infer_instance
    · rw [MonObj.comp_mul, ← (hact w).2, ← (hact w').2, ← u.ex_add, ← LinearMap.add_apply, hFF]
  have hadjH : ∀ z z', hermForm Hm (F w z) z' = hermForm Hm z (F w' z') := by
    refine obbuild_adj Hm _ hspan _ _ ?_
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [hF, hF, him, him, hadj]
  have hiso := (GlobalTheory.T.cubeLineBundle_adjoint_iff_hermForm_adjoint h1 h2 h3 h4 P u Hm χ _ _ _ _ hAH (hact w).1 (hact w').1 (hact w).2 (hact w').2).2 hadjH
  obtain ⟨m1, m2, m3, m4, m5, -, m7, m8⟩ := GlobalTheory.T.normalised_polarisation' h1 h3 ℂ P _ _ (hact w).1 (hact w').1 hmul hiso _ rfl
  obtain ⟨Ef, hEf, -⟩ := GlobalTheory.T.appellHumbert_uniformisation_riemannForm h1 h2 h3 h4 P u Hm χ hAH
  obtain ⟨u₁, χ₁, hex, hΛ₁, hAH₁, hχ₁⟩ := GlobalTheory.T.exists_appellHumbert_frame_of_pulled_biextension h1 h2 h3 h4 P u Hm χ Ef (act w) (F w) (F w') hAH hEf
    (hact w).2 hFF hadjH
  let P₁ : Out.PolAV (Sp ℂ) :=
    { A := P.A, isAb := P.isAb, g := P.g, smoothDim := P.smoothDim, L := cubeLB P.A ![𝟙 P.A, act w] P.L,
      isLB := m1, rigid := m2, sym := m3, ample := m4, ktriv := m5 }
  obtain ⟨Ef₁, hEf₁, -, -, -, -, -, -, hweil⟩ := GlobalTheory.T.appellHumbert_uniformisation_riemannForm h1 h2 h3 h4 P₁ u₁ Hm χ₁ hAH₁
  have hmem₁ : ∀ z, z ∈ u₁.Λ ↔ z ∈ Q.range := fun z => by rw [hΛ₁]; exact hmem z
  have hk : (k : ℂ) ≠ 0 := by simpa using (b.unit.map em).ne_zero
  have hk0 : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hk)
  let pt : Fin (2 * P.g) → (Out.baseOver (Sp ℂ) ⟶ P.A) := fun i => u₁.ex ((k : ℂ)⁻¹ • Q (lam i))
  have htor : ∀ i, pt i ^ k = 1 := fun i => by
    have := obbuild_ex_pow u₁ ((k : ℂ)⁻¹ • Q (lam i)) k
    rw [smul_inv_smul₀ hk, (u₁.ker _).2 ((hmem₁ _).2 ⟨_, rfl⟩)] at this
    exact this
  have hpair : ∀ i j, Out.WeilIs P.A (cubeLB P.A ![𝟙 P.A, act w] P.L) k (pt i) (pt j)
      (unitOn (Units.map em.toMonoidHom b.ζ) ^ Out.stdSymp P.g i j) := fun i j => by
    rw [← obbuild_unitOn_zpow]
    refine hweil k ⟨Q (lam i), (hmem₁ _).2 ⟨_, rfl⟩⟩ ⟨Q (lam j), (hmem₁ _).2 ⟨_, rfl⟩⟩ _ hk0 ?_
    have h5 := hEf₁ ⟨Q (lam i), (hmem₁ _).2 ⟨_, rfl⟩⟩ ⟨Q (lam j), (hmem₁ _).2 ⟨_, rfl⟩⟩
    rw [show (hermForm Hm _ _).im = _ from him (lam i) (lam j), Int.cast_inj] at h5
    rw [h5, hlam]
    simp
  have hb := GlobalTheory.T.symplectic_torsion_system_is_geometric_basis h1 ℂ P₁ k (Units.map em.toMonoidHom b.ζ) pt hk
    (IsPrimitiveRoot.coe_units_iff.1 (b.prim ℂ em)) htor hpair
  refine ⟨{ A := P.A, ab := P.isAb, dim := P.smoothDim, L := cubeLB P.A ![𝟙 P.A, act w] P.L,
            isLB := m1, rigid := m2, sym := m3, ample := m4, ktriv := m5, pt := pt, torsion := htor, bij := hb,
            pairing := fun i j => by rw [obbuild_unitS]; exact hpair i j,
            act := act, hom := fun j => (hact j).1 }, ⟨hmul, m8, m7⟩, u₁, χ₁, hAH₁, hmem₁, ?_, fun _ => rfl, ?_⟩
  · intro x l hl
    rw [hχ₁ l ⟨Q x, (hmem _).2 ⟨_, rfl⟩⟩ ⟨Q (ac w x), (hmem _).2 ⟨_, rfl⟩⟩ hl.symm (by rw [hl, hF])]
    have h5 := hEf ⟨Q x, (hmem _).2 ⟨_, rfl⟩⟩ ⟨Q (ac w x), (hmem _).2 ⟨_, rfl⟩⟩
    rw [show (hermForm Hm _ _).im = _ from him x (ac w x), Int.cast_inj] at h5
    rw [h5]
  · intro j
    refine ⟨F j, hF j, fun z => ?_⟩
    have := (hact j).2 z
    rw [← hex] at this
    exact this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaObjectOfPolarisedLatticeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaObject_of_polarisedLattice : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (em : o →+* ℂ) (w w' : J) (La : Type) [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (lam : Fin (2 * g) → La) (ac : J → La → La) (Q : La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), Function.Bijective EF → (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm (Q x) (Q y)).im = EF x y) → (∀ j, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), ∀ x, F (Q x) = Q (ac j x)) → (∀ x, ac w x + ac w' x = x) → (∀ x y, EF (ac w x) y = EF x (ac w' y)) → (∀ i₁ i₂, Complex.exp (-(2 * Real.pi * Complex.I) * (EF (lam i₁) (lam i₂) : ℂ) / ((k : ℕ) : ℂ)) = em (b.ζ : o) ^ Out.stdSymp g i₁ i₂) → ∃ t : TObj g k J b (spMap em), t.Prim w w' ∧ (∃ (u : HolUnif t.A t.L g) (χ' : u.Λ → ℂ), u.IsAH Hm χ' ∧ (∀ z, z ∈ u.Λ ↔ z ∈ (Q).range) ∧ (∀ x (l : u.Λ), (l : Fin g → ℂ) = Q x → χ' l = (-1) ^ EF x (ac w x)) ∧ (∀ i₀, (t.pt i₀).left = (u.ex (((k : ℕ) : ℂ)⁻¹ • Q (lam i₀))).left) ∧ ∀ j₀, ∃ F : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ), (∀ x, F (Q x) = Q (ac j₀ x)) ∧ ∀ z, u.ex (F z) = u.ex z ≫ t.act j₀) := by
  first | exact @GlobalTheory.thetaObject_of_lattice | exact GlobalTheory.thetaObject_of_lattice | (intros; apply GlobalTheory.thetaObject_of_lattice <;> assumption)
end
