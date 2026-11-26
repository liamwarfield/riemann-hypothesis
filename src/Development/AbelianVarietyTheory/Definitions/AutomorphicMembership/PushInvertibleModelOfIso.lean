module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.KeyFormulaAndKeyCore
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa

namespace GlobalTheory

theorem keyFormula_and_keyCore : KeyFormula ∧ Formalism.L2.LamCM.KeyCore :=
  ⟨GlobalTheory.keyFormula_of_connFam GlobalTheory.KeyFam.connFam_holds, Formalism.L2.LamCM.key_formula_link (GlobalTheory.keyFormula_of_connFam GlobalTheory.KeyFam.connFam_holds)⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ThetaSqMulSqrtEtaSq
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KeyPow GlobalTheory.KeyCl

noncomputable section
namespace GlobalTheory.LocM

structure NgC (g : ℕ) : Type where

  τ : Matrix (Fin g) (Fin g) ℂ
  symm : τ.IsSymm
  pos : (τ.map Complex.im).PosDef

  a : Fin g → ℂ

  b : Fin g → ℂ
  half : charHalf g a b

namespace NgC

variable {g : ℕ}

def base (g : ℕ) (a b : Fin g → ℂ) (h : charHalf g a b) : NgC g :=
  ⟨_, (TorusAlg.hypotheses_inhabited.1 g 0 Matrix.isSymm_zero).1,
    (TorusAlg.hypotheses_inhabited.1 g 0 Matrix.isSymm_zero).2, a, b, h⟩

instance (g : ℕ) : Nonempty (NgC g) := ⟨base g 0 0 ⟨fun _ => Or.inl rfl, fun _ => Or.inl rfl⟩⟩

def Y (z : NgC g) : Matrix (Fin g) (Fin g) ℝ := z.τ.map Complex.im

def Frame (z : NgC g) (x : KeyIn ℂ) : Prop :=
  ∃ h : x.P.g = g, NormalAt x (z.τ.submatrix (Fin.cast h) (Fin.cast h)) 1
    (fun i => z.a (i.cast h)) (fun i => z.b (i.cast h)) 1

def cubSq (z : NgC g) (w : Fin g → ℂ) : ℝ :=
  ‖thetaChar z.τ z.a z.b w‖ ^ 2 *
    Real.exp (-2 * Real.pi * ((fun i => (w i).im) ⬝ᵥ (z.Y)⁻¹.mulVec fun i => (w i).im))

def thetaSq (z : NgC g) : ℝ :=
  ∫ p in Set.pi Set.univ (fun _ : Fin g ⊕ Fin g => Set.Ico (0 : ℝ) 1),
    z.cubSq ((fun i => (p (.inl i) : ℂ)) + z.τ.mulVec (fun i => (p (.inr i) : ℂ)))

def lieGram (z : NgC g) : Matrix (Fin g) (Fin g) ℂ :=
  Matrix.of fun i j => Real.pi * hermForm ((z.Y)⁻¹.map fun x : ℝ => (x : ℂ))
    (Pi.single i (2 * Real.pi * Complex.I)⁻¹) (Pi.single j (2 * Real.pi * Complex.I)⁻¹)

def etaSq (z : NgC g) : ℝ := (z.lieGram.det.re)⁻¹

theorem lieGram_eq (z : NgC g) :
    z.lieGram = (((4 * Real.pi)⁻¹ • (z.Y)⁻¹ : Matrix (Fin g) (Fin g) ℝ)).map fun x : ℝ => (x : ℂ) := by
  ext i j
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have e : star (Pi.single j (2 * Real.pi * Complex.I : ℂ)⁻¹ : Fin g → ℂ) =
      Pi.single j (-(2 * Real.pi * Complex.I : ℂ)⁻¹) := by
    funext k
    by_cases h : k = j
    · subst h; simp
    · simp [h]
  simp only [lieGram, Matrix.of_apply, hermForm, e, single_dotProduct, Matrix.mulVec_single, Matrix.map_apply,
    Matrix.smul_apply, smul_eq_mul]
  simp
  field_simp
  simp
  ring

theorem etaSq_eq (z : NgC g) : z.etaSq = (4 * Real.pi) ^ g * z.Y.det := by
  have e : z.lieGram.det = ((((4 * Real.pi)⁻¹ • (z.Y)⁻¹ : Matrix (Fin g) (Fin g) ℝ)).det : ℝ) := by
    rw [lieGram_eq]
    exact (RingHom.map_det Complex.ofRealHom _).symm
  rw [etaSq, e, Complex.ofReal_re, Matrix.det_smul, Matrix.det_nonsing_inv, Fintype.card_fin, Ring.inverse_eq_inv',
    mul_inv, inv_inv, inv_pow, inv_inv]

end NgC

structure IsKF (g c : ℕ) (κ : Rule) : Prop where
  homog : ∀ (K : Type) [Field K] [CharZero K] (P : Out.PolAV (Sp K)) (hg rig hr th hth v hv th' hth' v' hv') (a : K)
    (M : Matrix (Fin P.g) (Fin P.g) K), P.g = g → (∀ i, LB.Sec.f th' i = constFn P.A.hom _ a * LB.Sec.f th i) →
    (∀ i, IsLieComb (M i) v (v' i)) →
    a ^ (2 * c) * (κ K ⟨P, hg, rig, hr, th', hth', v', hv'⟩ : K) = M.det ^ c * κ K ⟨P, hg, rig, hr, th, hth, v, hv⟩
  funct : Funct κ
  unitSp : UnitSp κ
  off : ∀ (K : Type) [Field K] [CharZero K] (x : KeyIn K), x.P.g ≠ g → κ K x = 1

namespace IsKF

variable {g c : ℕ} {κ κ' : Rule}

theorem value_normalAt (h : IsKF g c κ) (x : KeyIn ℂ) (hx : x.P.g = g) {τ M : Matrix (Fin x.P.g) (Fin x.P.g) ℂ}
    {a b : Fin x.P.g → ℂ} {c₀ : ℂ} (hc : c₀ ≠ 0) (hM : M.det ≠ 0) (hN : NormalAt x τ M a b c₀) (t : ℂ)
    (ht : ∀ (y : KeyIn ℂ) (e : y.P.g = x.P.g), NormalAt y (τ.submatrix (Fin.cast e) (Fin.cast e)) 1
      (fun i => a (i.cast e)) (fun i => b (i.cast e)) 1 → (κ ℂ y : ℂ) = t) :
    c₀ ^ (2 * c) * (κ ℂ x : ℂ) = M.det ^ c * t := by
  obtain ⟨P, hg, rig, hr, th, hth, v, hv⟩ := x
  obtain ⟨th₀, hth₀, v₀, hv₀, hN₀, e₁, hMv⟩ := KeyConst.exists_rescale P hg rig hr th hth v hv τ M _ _ c₀ hc hM hN
  rw [← ht ⟨P, hg, rig, hr, th₀, hth₀, v₀, hv₀⟩ rfl hN₀]
  exact h.homog ℂ P hg rig hr _ hth₀ v₀ hv₀ th hth v hv c₀ M hx e₁ hMv

theorem ext (h : IsKF g c κ) (h' : IsKF g c κ') (f : NgC g → ℂˣ)
    (hf : ∀ (z : NgC g) x, z.Frame x → κ ℂ x = f z) (hf' : ∀ (z : NgC g) x, z.Frame x → κ' ℂ x = f z) : κ = κ' := by
  funext K _ _ x
  by_cases hx : x.P.g = g
  swap
  · rw [h.off K x hx, h'.off K x hx]
  obtain ⟨K₀, x₀, hK₀, hx₀⟩ := (KeyCountableDescent.keyIn_descends_countable firstFiveLaws.1).2 K x
  obtain ⟨σ⟩ := KeyRuleUnique.nonempty_ringHom_complex K₀
  obtain ⟨y, hy⟩ := exists_keyPB_ring x₀ σ
  have hyg : y.P.g = g := (KeyGalDesc.g_eq hy).trans ((KeyGalDesc.g_eq hx₀).symm.trans hx)
  subst hyg
  obtain ⟨⟨τ, M, a, b, c₀, hab, hc, hM, hN⟩, -⟩ := KeyNormalExists.exists_normalAt thetaUnifAV_all y
  let z : NgC y.P.g := ⟨τ, hN.mem_siegelH.1, hN.mem_siegelH.2, a, b, hab⟩
  have e : (κ ℂ y : ℂ) = κ' ℂ y := by
    refine mul_left_cancel₀ (pow_ne_zero (2 * c) hc) ?_
    rw [h.value_normalAt y rfl hc hM hN (f z) fun w e hw => congrArg Units.val (hf z w ⟨e, hw⟩),
      h'.value_normalAt y rfl hc hM hN (f z) fun w e hw => congrArg Units.val (hf' z w ⟨e, hw⟩)]
  rw [h.funct K₀ ℂ σ x₀ y hy, h'.funct K₀ ℂ σ x₀ y hy] at e
  apply Units.ext
  rw [h.funct K₀ K _ x₀ x hx₀, h'.funct K₀ K _ x₀ x hx₀, σ.injective e]

end IsKF

open Classical in
def cutRule (g : ℕ) (s : ℤˣ) (κ : Rule) : Rule := fun K _ _ x =>
  if x.P.g = g then Units.map (Int.castRingHom K).toMonoidHom s * κ K x else 1

theorem isKF_cutRule {g c : ℕ} (s : ℤˣ) {κ : Rule}
    (hH : ∀ (K : Type) [Field K] [CharZero K] (P : Out.PolAV (Sp K)) (hg rig hr th hth v hv th' hth' v' hv') (a : K)
      (M : Matrix (Fin P.g) (Fin P.g) K), P.g = g → (∀ i, LB.Sec.f th' i = constFn P.A.hom _ a * LB.Sec.f th i) →
      (∀ i, IsLieComb (M i) v (v' i)) →
      a ^ (2 * c) * (κ K ⟨P, hg, rig, hr, th', hth', v', hv'⟩ : K) = M.det ^ c * κ K ⟨P, hg, rig, hr, th, hth, v, hv⟩)
    (hF : Funct κ) (hU : UnitSp κ) : IsKF g c (cutRule g s κ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro K _ _ P hg rig hr th hth v hv th' hth' v' hv' a M hP h₁ h₂
    simp only [cutRule, ite_eq_left hP, Units.val_mul]
    rw [mul_left_comm, hH K P hg rig hr th hth v hv th' hth' v' hv' a M hP h₁ h₂, mul_left_comm]
  · intro K K' _ _ _ _ f x x' h
    simp only [cutRule, KeyGalDesc.g_eq h]
    split_ifs
    · simp [hF K K' f x x' h]
    · simp
  · intro R K _ _ _ _ _ _ _ x xK h
    by_cases hx : x.P.g = g
    · obtain ⟨u, hu, hk⟩ := hU R K x xK h
      refine ⟨Units.map (Int.castRingHom R).toMonoidHom s * u, ?_, fun k _ _ r xk hr hxk => ?_⟩
      · simp [cutRule, KeyGalDesc.g_eq h, hx, hu]
      · simp [cutRule, KeyGalDesc.g_eq hxk, hx, hk k r xk hr hxk]
    · exact ⟨1, by simp [cutRule, KeyGalDesc.g_eq h, hx],
        fun k _ _ r xk hr hxk => by simp [cutRule, KeyGalDesc.g_eq hxk, hx]⟩
  · intro K _ _ x hx
    exact ite_eq_right hx

structure KF (g c : ℕ) : Type where

  val : NgC g → ℂˣ
  ex : ∃ κ : Rule, IsKF g c κ ∧ ∀ (z : NgC g) (x : KeyIn ℂ), z.Frame x → κ ℂ x = (val z)⁻¹
  zero : g = 0 → ∀ z, val z = 1 ∨ val z = -1

namespace KF

variable {g c : ℕ} (kf : KF g c)

def rule (kf : KF g c) : Rule := kf.ex.choose

def coef (K : Type) [Field K] [CharZero K] (x : KeyIn K) : Kˣ := (kf.rule K x)⁻¹

def norm (z : NgC g) : ℝ := ‖(kf.val z : ℂ)‖ / (z.thetaSq ^ c * Real.sqrt z.etaSq ^ c)

def ofRule (N : ℕ → ℕ) (κ : Rule) (hH : Homog N κ) (hF : Funct κ) (hU : UnitSp κ) (hT : ThetaOne κ) (g : ℕ) :
    KF g (4 * N g) where
  val _ := 1
  ex := ⟨cutRule g 1 κ, isKF_cutRule 1 (fun K _ _ P hg rig hr th hth v hv th' hth' v' hv' a M hP h₁ h₂ => by
      subst hP
      rw [show 2 * (4 * N P.g) = 8 * N P.g by ring]
      exact hH K P hg rig hr th hth v hv th' hth' v' hv' a M h₁ h₂) hF hU, fun z x h => by
    obtain ⟨e, h⟩ := h
    obtain ⟨u, h₁, h₂, h₃, h₄, h₅, h₆⟩ := (normalAt_one_iff x _ _ _).1 h
    rw [cutRule, ite_eq_left e, hT x u _ _ _ h₁ h₂ (fun i => z.half.1 _) (fun i => z.half.2 _) h₃ h₄ h₅ h₆]
    simp⟩
  zero _ _ := Or.inl rfl

end KF

def ngTrue : Formalism.L2.Geo.NgPkg where
  NgC := NgC
  NgC_ne _ := inferInstance
  KF := KF
  kfNorm kf z := kf.norm z

theorem exists_kf_four (g : ℕ) : ∃ kf : KF g 4, ∀ z, kf.val z = 1 := by
  obtain ⟨κ, h₁, h₂, h₃, h₄, -⟩ := keyFormula_iff.1 keyFormula_and_keyCore.1
  exact ⟨KF.ofRule (fun _ => 1) κ h₁ h₂ h₃ h₄ g, fun _ => rfl⟩

end GlobalTheory.LocM
end
end

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam
open GlobalTheory.FlagMod (GChart thUnit thRat detChg pushPP detOm detLie de ev)
open GlobalTheory.Reg (MChart)
open GlobalTheory.LB (toMod)

namespace GlobalTheory.LocM

section OneModel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

section Transport

variable (Y : Model Xo c β) {X : Scheme.{0}} (π : X ⟶ Y.X) [IsIso π]

def genInv : pullback Y.s (spMap β) ⟶ pullback (π ≫ Y.s) (spMap β) :=
  pullback.map _ _ _ _ (inv π) (𝟙 _) (𝟙 _) (by simp) (by simp)

instance isIso_genInv : IsIso (genInv Y π) := by unfold genInv; infer_instance

theorem genInv_fst : genInv Y π ≫ pullback.fst _ _ ≫ π = pullback.fst _ _ := by
  rw [genInv, pullback.lift_fst_assoc, Category.assoc, IsIso.inv_hom_id, Category.comp_id]

theorem genInv_snd : genInv Y π ≫ pullback.snd _ _ = pullback.snd _ _ := by
  rw [genInv, pullback.lift_snd, Category.comp_id]

theorem exists_sabMap_genInv {t : SAB H X} (m : SABMap t Y.t π) :
    ∃ n : SABMap Y.oF.t t ((Y.jQ ≫ genInv Y π) ≫ pullback.fst _ _), n.φ ≫ m.φ = Y.m.φ := by
  have e : ((Y.jQ ≫ genInv Y π) ≫ pullback.fst _ _) ≫ π = Y.jQ ≫ pullback.fst _ _ := by
    simp only [Category.assoc, genInv_fst]
  obtain ⟨n', hn'⟩ : ∃ n' : SABMap Y.oF.t Y.t (((Y.jQ ≫ genInv Y π) ≫ pullback.fst _ _) ≫ π), n'.φ = Y.m.φ := by
    rw [e]; exact ⟨Y.m, rfl⟩
  obtain ⟨n, hn⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m n'
  exact ⟨n, hn.symm.trans hn'⟩

@[reducible] def modelOfIso (hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) (t : SAB H X) (m : SABMap t Y.t π) :
    Model Xo c β where
  X := X
  s := π ≫ Y.s
  normal := hn
  proj := by
    obtain ⟨n, i, hi, e⟩ := Y.proj
    exact ⟨n, π ≫ i, inferInstance, by rw [Category.assoc, e]⟩
  flat := have := Y.flat; inferInstance
  jQ := Y.jQ ≫ genInv Y π
  jQ_over := by rw [Category.assoc, genInv_snd, Y.jQ_over]
  jQ_open := have := Y.jQ_open; inferInstance
  jQ_dense := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp]
    exact (genInv Y π).surjective.denseRange.comp Y.jQ_dense (genInv Y π).continuous
  t := t
  oF := Y.oF
  m0 := Y.m0
  m := (exists_sabMap_genInv Y π m).choose
  ab_gen := by
    ext y
    obtain ⟨y, rfl⟩ := (genInv Y π).surjective y
    rw [Set.mem_preimage, ← abLocus_pullback abLocusOne Y.t.semi m.cart.1, ← Scheme.Hom.comp_apply,
      ← Scheme.Hom.comp_apply, genInv_fst, ← Set.mem_preimage, Y.ab_gen]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, Scheme.Hom.comp_apply _ _ _⟩
    · rintro ⟨x, hx⟩
      exact ⟨x, (genInv Y π).homeomorph.injective ((Scheme.Hom.comp_apply _ _ _).symm.trans hx)⟩

theorem pushInvertible_modelOfIso (hn : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X) (t : SAB H X) (m : SABMap t Y.t π)
    (hD : GlobalTheory.Models.IsDedFrac β) (hY : PushInvertible Y.t.G Y.t.PP.L) : PushInvertible t.G t.PP.L := by
  obtain ⟨l₁, l₂, l₃, -, -⟩ := GlobalTheory.firstFiveLaws
  let C := modelOfIso Y π hn t m
  exact GlobalTheory.PushInv.pushInvertible_of_model l₁ l₂ l₃ E H Dw l _ _ _ _ _ _ Y.oF _ β
    ⟨C.X, C.s, C.normal, C.proj, C.flat, C.jQ, C.jQ_over, C.jQ_open, C.jQ_dense, C.t, C.m, C.ab_gen⟩ hD
    ((GlobalTheory.AbLocusPull.abLocus_sections_pull _ _ π Y.t.G t.G m.φ Y.t.semi m.cart).2 _ _ Y.t.PP.isLB t.PP.isLB
      (GlobalTheory.LN.GenericPoint.lbIso_of_sabMap m) fun x => by
        obtain ⟨V, hV, θ, hθ, -, nz⟩ := hY x
        exact ⟨V, hV, θ, hθ, nz⟩)

end Transport

variable {Y : Model Xo c β}

def pushMod {X : Scheme.{0}} (t : SAB H X) : X.Modules := (Scheme.Modules.pushforward t.G.hom).obj (toMod t.PP.L)

def keyUnit (k : ℕ) (M M' : GChart Y) : Γ(Y.X, M.U ⊓ M'.U)ˣ :=
  (thUnit M M')⁻¹ ^ (2 * k) * detChg M.toMChart M'.toMChart ^ k

theorem thRat_pow_mul_keyUnit (k : ℕ) (M M' : GChart Y) :
    thRat M M' ^ (2 * k) * (keyUnit k M M').val = (detChg M.toMChart M'.toMChart).val ^ k := by
  have : thUnit M M' ^ (2 * k) * keyUnit k M M' = detChg M.toMChart M'.toMChart ^ k := by
    simp only [keyUnit, inv_pow, mul_inv_cancel_left]
  simpa only [Units.val_mul, Units.val_pow_eq_pow_val, GlobalTheory.FlagMod.thUnit_val] using congrArg Units.val this

def keyLB (Y : Model Xo c β) (k : ℕ) : LB Y.X := ⟨GChart Y, fun M => M.U, keyUnit k⟩

theorem gm_keyUnit (k : ℕ) (M M' : GChart Y) (y : Y.X) :
    gm (𝟙 Y.X) y _ (keyUnit k M M') =
      (gm (𝟙 Y.X) y _ (thUnit M M'))⁻¹ ^ (2 * k) * gm (𝟙 Y.X) y _ (detChg M.toMChart M'.toMChart) ^ k := by
  rw [keyUnit, map_mul, map_pow, map_pow, map_inv]

section Cover

variable [IsNoetherianRing O] (hP : PushInvertible Y.t.G Y.t.PP.L)
include hP

theorem isLB_keyLB (k : ℕ) : (keyLB Y k).IsLB := by
  refine GlobalTheory.LBLimit.isLB_of_germs _ (GlobalTheory.FlagMod.exists_gChart hP) fun a b d y ha hb hd => ?_
  have e₁ : gm (𝟙 Y.X) y _ (thUnit a b) * gm (𝟙 Y.X) y _ (thUnit b d) = gm (𝟙 Y.X) y _ (thUnit a d) :=
    gm_cocycle (GlobalTheory.FlagMod.isLB_pushPP hP) (𝟙 Y.X) y ha hb hd
  have e₂ : gm (𝟙 Y.X) y _ (detChg a.toMChart b.toMChart) * gm (𝟙 Y.X) y _ (detChg b.toMChart d.toMChart) =
      gm (𝟙 Y.X) y _ (detChg a.toMChart d.toMChart) :=
    gm_cocycle (GlobalTheory.FlagMod.isLB_detLie hP) (𝟙 Y.X) y (i := a.toMChart) (j := b.toMChart) (k := d.toMChart) ha hb hd
  refine (congrArg₂ (· * ·) (gm_keyUnit k a b y) (gm_keyUnit k b d y)).trans (Eq.trans ?_ (gm_keyUnit k a d y).symm)
  rw [← e₁, ← e₂, mul_inv, mul_pow, mul_pow, _root_.mul_mul_mul_comm]

end Cover

def KeyAt (M : GChart Y) {R : Type} [CommRing R] (z : Sp R ⟶ Y.X) (hz : ⊤ ≤ z ⁻¹ᵁ M.U) (x : KeyIn R) : Prop :=
  ∃ (φ : x.P.A.left ⟶ Y.t.G.left) (he : eSec x.P.A ≫ φ = z ≫ eSec Y.t.G)
    (w : LB.Iso x.P.L (Y.t.PP.L.pull φ)) (hg : x.P.g = M.n),
    IsGrpPullback x.P.A Y.t.G z φ ∧ w.IsGen ∧
    LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec x.P.A) (fun _ => 1)) x.rig
      (rigPullOf φ z he Y.t.PP.L Y.t.PP.rig) ∧
    (∀ (j : (Y.t.PP.L.pull φ).ι) (i : x.P.L.ι)
      (h : (Y.t.PP.L.pull φ).U j ⊓ x.P.L.U i ≤ φ ⁻¹ᵁ (Y.t.G.hom ⁻¹ᵁ M.U ⊓ Y.t.PP.L.U (j PUnit.unit))),
      (φ.appLE _ _ h).hom (M.θ (j PUnit.unit)) =
        (show Γ(x.P.A.left, (Y.t.PP.L.pull φ).U j ⊓ x.P.L.U i) from (w.s (j, i)).val) *
          resG _ inf_le_right (x.th.f i)) ∧
    ∀ i, (x.v i).left ≫ φ = spMap (_root_.Formalism.L2.Pj.dualMap (ev z M.U hz)) ≫ M.v₀ (i.cast hg)

end OneModel

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ}

namespace At

variable (ct : At S κ p)

@[reducible] def base : Model (S.Xo ct.Xm.i.l) ct.Xm.i.c (ct.Xm.i.c.V ct.W).subtype :=
  haveI := ct.B.iso none
  modelOfIso (ct.Y ct.Xm.i) ct.Xm.π (@GlobalTheory.IsNormalScheme.pred _ ct.Xm.normal) ct.Xm.t ct.Xm.tMap

instance isNoetherianRing_base : IsNoetherianRing (ct.Xm.i.c.V ct.W) :=
  GlobalTheory.ModelPresentation.isNoetherianRing_place _ _ ct.hp.ne_zero ct.hW

theorem pushInvertible : PushInvertible ct.Xm.t.G ct.Xm.t.PP.L :=
  haveI := ct.B.iso none
  pushInvertible_modelOfIso (ct.Y ct.Xm.i) ct.Xm.π (@GlobalTheory.IsNormalScheme.pred _ ct.Xm.normal) ct.Xm.t ct.Xm.tMap
    ((GlobalTheory.CoeffRings.coeff_isDedFrac _ A.H _ ct.Xm.i.c).2.2.2 p ct.W ct.hp ct.hW).1
    ((S.sys.clauses p ct.W ct.hp ct.hW).1.1 ct.Xm.i).2.2.1

abbrev KeyChart : Type := GChart ct.base

def keyL (c : ℕ) : LB ct.Xm.X := keyLB ct.base c

theorem isLB_keyL (c : ℕ) : (ct.keyL c).IsLB := isLB_keyLB (Y := ct.base) ct.pushInvertible c

def ofModIso {Z : ct.Mdl} {F : Z.X.Modules} (h : GlobalTheory.VB.IsVB F 1) : (Z.ofMod F).toMod ≅ F :=
  haveI := h.isFiniteQC
  (GlobalTheory.ModelPresentation.nonempty_ofMod_toMod_iso _ _ _ _ p ct.W ct.hp ct.hW _ _ Z F).some

def piPP : ct.Sh ct.Xm := ct.Xm.ofMod (pushMod ct.Xm.t)

def keySh (c : ℕ) : ct.Sh ct.Xm := ct.Xm.ofMod (toMod (ct.keyL c))

def keyIso (c : ℕ) : (ct.keySh c).toMod ≅ toMod (ct.keyL c) := ct.ofModIso (GlobalTheory.VB.isVB_toMod (ct.isLB_keyL c))

theorem isInv_keySh (c : ℕ) : ct.IsInv (ct.keySh c) :=
  (GlobalTheory.VB.isVB_toMod (ct.isLB_keyL c)).of_iso (ct.keyIso c).symm

variable {ct}

def keyGen (c : ℕ) (M : ct.KeyChart) : Γ((ct.keySh c).toMod, M.U) :=
  (ct.keyIso c).inv.app M.U (GlobalTheory.LB.chartSec (ct.isLB_keyL c) M)

theorem isFrame_keyGen (c : ℕ) (M : ct.KeyChart) : GlobalTheory.LB.IsFrame (keyGen c M) :=
  (GlobalTheory.LB.isFrame_chartSec (ct.isLB_keyL c) M).app (ct.keyIso c).symm

def keyCoef {c : ℕ} {V : ct.Xm.X.Opens} (s : Γ((ct.keySh c).toMod, V)) (M : ct.KeyChart) : Γ(ct.Xm.X, V ⊓ M.U) :=
  GlobalTheory.LB.coord ((ct.keyIso c).hom.app V s) M

def keyMk (c : ℕ) {V : ct.Xm.X.Opens} (f : ∀ M : ct.KeyChart, Γ(ct.Xm.X, V ⊓ M.U)) (hf : f ∈ secOn (ct.keyL c) V) :
    Γ((ct.keySh c).toMod, V) :=
  (GlobalTheory.LB.appLinearEquiv (ct.keyIso c) V).symm (GlobalTheory.LB.mkSec f hf)

theorem keyCoef_keyMk (c : ℕ) {V : ct.Xm.X.Opens} (f : ∀ M : ct.KeyChart, Γ(ct.Xm.X, V ⊓ M.U))
    (hf : f ∈ secOn (ct.keyL c) V) : keyCoef (keyMk c f hf) = f :=
  congrArg GlobalTheory.LB.coord ((GlobalTheory.LB.appLinearEquiv (ct.keyIso c) V).apply_symm_apply _)

def HasKeyValues {c : ℕ} (val : GlobalTheory.KeyCl.Rule) (s : ct.Sec (ct.keySh c)) : Prop :=
  ∀ (M : ct.KeyChart) (K : Type) [Field K] [CharZero K] (z : Sp K ⟶ ct.Xm.X) (hz : ⊤ ≤ z ⁻¹ᵁ (ct.Xm.genO ⊓ M.U))
    (x : KeyIn K), KeyAt M z (GlobalTheory.FlagMod.le_preimage_mono inf_le_right hz) x → ev z _ hz (keyCoef s M) = val K x

variable (ct)


open Classical in
def pbKF {g c : ℕ} (kf : KF g c) : ct.Sec (ct.keySh c) :=
  if h : ∃ s : ct.Sec (ct.keySh c), HasKeyValues kf.coef s then h.choose else 0

end At

def keyTrue (ct : At S κ p) : KeySt ct where
  piPP := ct.piPP
  keySh := ct.keySh
  keySh_inv _ := ct.isInv_keySh

end GlobalTheory.LocM
