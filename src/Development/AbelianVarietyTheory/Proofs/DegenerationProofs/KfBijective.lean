module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLabelMapTorsionCharacters
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormVal
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleGeneratorExtendingDensePart
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorsionEqOneOfTranslationKeepsRatios

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KfBijective
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.ClassWeight
open GlobalTheory.UT

def kf (R : Type) [CommRing R] [IsDomain R] (F : Type) [Field F] [Algebra (FractionRing R) F] :
    F →+* Γ((TFK (R := R) F).left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom

theorem kf_bijective (R : Type) [CommRing R] [IsDomain R] (F : Type) [Field F] [Algebra (FractionRing R) F] :
    Function.Bijective (kf R F) :=
  ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {p : ℕ} [Fact p.Prime]
  {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀)

theorem base_eq : (show (TFK (R := u.V) (PadicAlgCl p)).left ⟶ (baseOver (Sp S.R)).left from spMap y₀) ≫
    (baseOver (Sp S.R)).hom = (TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK := by
  refine (Category.comp_id _).trans ?_
  exact (congrArg spMap u.fac.symm).trans
    (Spec.map_comp (CommRingCat.ofHom u.yK) (CommRingCat.ofHom (algebraMap (FractionRing u.V) (PadicAlgCl p))))

def Moved (w : LB.Iso u.A.L (ρ.P.L.pull u.φ)) {k : ℕ} (t : SecA u.A (PadicAlgCl p) k)
    (s : LB.Sec (LPow ρ.P.A ρ.P.L (k : ℤ) (baseOver (Sp S.R)))) : Prop :=
  ThetaPtMove.SecRel u.cart (T := TFK (R := u.V) (PadicAlgCl p)) (T₀ := baseOver (Sp S.R)) (spMap y₀) (base_eq u) w t s

theorem exists_moved {w : LB.Iso u.A.L (ρ.P.L.pull u.φ)} (hw : w.IsGen) {k : ℕ}
    (s : LB.Sec (LPow ρ.P.A ρ.P.L (k : ℤ) (baseOver (Sp S.R)))) : ∃ t, Moved u w t s :=
  ThetaPtMove.exists_secRel u.cart _ _ hw ρ.P.isLB u.A.isLB s

end GlobalTheory.ZH.ClassWeight
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TestQuadraticFormEqPsiValuationMul
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TestQuadraticFormEqPsiValuationMul
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.PsiForm

theorem q_eq_val_mul : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab), ∃ (ϖ : u.V) (Q : u.D.toPre.X → ℤ), Irreducible ϖ ∧ DVR.QForm.IsQ u.D.toPre ϖ Q ∧ ‖(u.j ϖ : PadicAlgCl p)‖ < 1 ∧ ∀ χ, l.q χ = Q χ * (-Real.log ‖(u.j ϖ : PadicAlgCl p)‖) := by
  intro o Ω _ _ _ _ S ρ p _ y₀ u l
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible u.V
  choose Q hQ using DVR.QForm.exists_QVal hϖ u.D
  have hj : (u.j ϖ : PadicAlgCl p) =
      algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V (FractionRing u.V) ϖ) := rfl
  refine ⟨ϖ, Q, hϖ, hQ, ?_, fun χ => ?_⟩
  · rw [hj]
    exact norm_lt_one_of_irreducible u.norm_le hϖ
  · have hc := u.D.toPre.P.isLB.cover
    let x : Sp u.V := IsLocalRing.closedPoint u.V
    have hx : (u.D.toPre.c χ).left x ∈ ⨆ i, u.D.toPre.P.L.U i := by rw [hc]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    have htop : ⊤ ≤ (u.D.toPre.c χ).left ⁻¹ᵁ u.D.toPre.P.L.U i :=
      ((IsLocalRing.closedPoint_mem_iff (R := u.V) _).1 hi).ge
    have h1 := l.q_eq χ (fun _ => i) htop
    have h2 := norm_of_hasVal u.norm_le hϖ
      (hasVal_valF u.D.toPre.P.L _ _ (DVR.QForm.ptK_eq u.D.toPre χ) (-1) _ (hQ χ) (fun _ => i) htop)
    have h3 := neg_injective (Real.exp_injective (h1.symm.trans h2))
    rw [hj, h3, mul_comm]

end GlobalTheory.ZH.PsiForm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TestQuadraticFormEqPsiValuationMulStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
theorem _root_.GlobalTheory.T.testQuadraticForm_eq_psi_valuation_mul : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab), ∃ (ϖ : u.V) (Q : u.D.toPre.X → ℤ), Irreducible ϖ ∧ DVR.QForm.IsQ u.D.toPre ϖ Q ∧ ‖(u.j ϖ : PadicAlgCl p)‖ < 1 ∧ ∀ χ, l.q χ = Q χ * (-Real.log ‖(u.j ϖ : PadicAlgCl p)‖) := by
  first | exact @GlobalTheory.ZH.PsiForm.q_eq_val_mul | exact GlobalTheory.ZH.PsiForm.q_eq_val_mul | (intros; apply GlobalTheory.ZH.PsiForm.q_eq_val_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsOperators
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.ThetaReal

theorem pt_nsmul {G H : Type} [AddCommGroup G] [Group H] (pt : G → H) (h : ∀ a b, pt (a + b) = pt a * pt b) :
    pt 0 = 1 ∧ ∀ (n : ℕ) a, pt (n • a) = pt a ^ n := by
  have h0 : pt 0 = 1 := by
    have := h 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  refine ⟨h0, fun n a => ?_⟩
  induction n with
  | zero => rw [zero_smul, pow_zero, h0]
  | succ n ih => rw [succ_nsmul, h, ih, pow_succ]

theorem eStd_nsmul (g M r : ℕ) (a b : Fin g ⊕ Fin g → ZMod M) : eStd g M a (r • b) = r • eStd g M a b := by
  simp only [eStd, Finset.smul_sum, Pi.smul_apply, nsmul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem nsmul_self {κ : Type} (M : ℕ) (a : κ → ZMod M) : M • a = 0 := by
  funext i
  simp

theorem exists_operators (hL : Laws) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) {g m r N : ℕ}
    (hN : N = m ^ 2) (hm : Odd m) (hu : IsUnit ((r * N : ℕ) : Γ(S, ⊤))) (ze : Γ(S, ⊤)ˣ)
    (pt : (Fin g ⊕ Fin g → ZMod (r * N)) → (baseOver S ⟶ P.A)) (hadd : ∀ a b, pt (a + b) = pt a * pt b)
    (hw : ∀ a b, WeilIs P.A P.L (r * N : ℕ) (pt a) (pt b) (ze ^ (r * N * (eStd g (r * N) a b).val)))
    (U : (Fin g ⊕ Fin g → ZMod (r * N)) → ThetaGrp P.A P.L N (baseOver S))
    (hU : ∀ a, SymLift P.A P.L N N (pt (r • a)) (U a))
    {α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(snd (baseOver S) P.A).left, (snd (baseOver S) P.A ^ m).left]
      ![(N : ℤ), -1])} (hα : α.IsGen) {th : LB.Sec (LPow P.A P.L 1 (baseOver S))}
    {s₀ : LB.Sec (LPow P.A P.L N (baseOver S))}
    (hs : IsTwistPull P.A P.L (mulT P.A _ m) (snd _ P.A ^ m) (lift_snd _ _) N 1 α th s₀) :
    ∃ u : (Fin g ⊕ Fin g → ZMod (r * N)) →
        SecM P.A P.L N (baseOver S) →ₗ[Γ((baseOver S).left, ⊤)] SecM P.A P.L N (baseOver S),
      (∀ a s s', IsActOf P.A P.L N (U a) s s' ↔ u a (SecM.ofSec P.A s) = SecM.ofSec P.A s') ∧
      (∀ a, r • a = 0 → ∀ v, u a v = v) ∧
      (∀ a b, ∃ e : ℕ, ∀ v, u a (u b v) = (show Γ((baseOver S).left, ⊤) from ze.val ^ e) • u (a + b) v) ∧
      (∀ a b, r • eStd g _ a b = 0 → ∀ v, u a (u b v) = u (a + b) v) ∧
      ∀ a, (r * m) • a = 0 → u a (SecM.ofSec P.A s₀) = SecM.ofSec P.A s₀ := by
  obtain ⟨ρ, hρ, -⟩ := GlobalTheory.thetaGrp_acts_linearly hL.globalFns S P N (baseOver S)
  obtain ⟨h0, hsm⟩ := pt_nsmul pt hadd
  have hodd : Odd N := hN ▸ hm.pow
  have tors : ∀ a, pt (r • a) ^ N = 1 := fun a => by rw [← hsm, smul_smul, mul_comm N r, nsmul_self, h0]
  have act : ∀ a v, IsActOf P.A P.L N (U a) (SecM.toSec P.A v) (SecM.toSec P.A (ρ (U a) v)) := fun a v =>
    (hρ _ _ _).2 rfl
  have weil : ∀ a b, WeilIs P.A P.L N (pt (r • a)) (pt (r • b))
      (ze ^ (r * N * (r • eStd g (r * N) a b).val)) := fun a b => by
    have h₁ := hw a (r • b)
    rw [eStd_nsmul] at h₁
    have h₂ := (hL.weil S P N (baseOver S)).2.2.2 r (pt a) (pt (r • b))
      (ze ^ (r * N * (r • eStd g (r * N) a b).val)) (by rw [mul_comm]; exact hu)
      (by rw [← hsm, mul_comm N r, nsmul_self, h0]) (tors b)
    rw [hsm r a]
    refine h₂.1 ?_
    rw [← Nat.cast_mul, mul_comm N r]
    exact h₁
  have key : ∀ a b v, ρ (U a) (ρ (U b) v) = (show Γ((baseOver S).left, ⊤) from
      ze.val ^ (r * N * (r • eStd g (r * N) a b).val * ((N + 1) / 2))) • ρ (U (a + b)) v := fun a b v => by
    have := act_act hL.globalFns P.isAb P.isLB hodd (tors b) (hU a) (hU b)
      (by rw [← hadd, ← smul_add, add_comm]; exact hU (a + b)) (weil a b) (act b v) (act a _) (act (a + b) v)
    refine this.trans (congrArg (· • _) ?_)
    rw [pow_mul ze.val]
    exact (Units.val_pow_eq_pow_val _ _).trans (congrArg (· ^ _) (Units.val_pow_eq_pow_val _ _))
  refine ⟨fun a => (ρ (U a)).toLinearMap, fun a => hρ _, fun a ha v => ?_, fun a b => ⟨_, key a b⟩,
    fun a b h v => ?_, fun a ha => (hρ _ _ _).1 ?_⟩
  · have h₁ : SymLift P.A P.L N N 1 (U a) := by
      have := hU a
      rwa [ha, h0] at this
    have := act_act hL.globalFns P.isAb P.isLB hodd (one_pow N) h₁ h₁ (by rw [_root_.mul_one]; exact h₁)
      ((hL.weil S P N (baseOver S)).2.2.1 1 (one_pow N)) (act a v) (act a _) (act a v)
    rw [one_pow, Units.val_one, one_smul] at this
    exact (ρ (U a)).injective this
  · refine (key a b v).trans ?_
    rw [h, ZMod.val_zero, mul_zero, zero_mul, pow_zero]
    exact one_smul _ _
  · obtain ⟨ν, hν⟩ := GlobalTheory.exists_gen_negLB hL.globalFns S P 1 (baseOver S)
    exact isActOf_self hL.globalFns P.isAb P.isLB hν hodd hα hs
      (by rw [← hsm, smul_smul, mul_comm m r, ha, h0]) (tors a) (hU a)

end GlobalTheory.ThetaReal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGtDatumOfTorusCoords
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGtDatumOfTorusCoords
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

noncomputable section
namespace GlobalTheory.ZH.UFib
open GlobalTheory.CoordToExt

section
variable {S : Scheme.{0}}

theorem exists_gtDatum_of_units (E : SplitExt S) {G : Over S} [GrpObj G] (q : G ⟶ E.B) (i : splitTorus S E.X ⟶ G)
    (hq : IsMonHom q) (hi : IsMonHom i) (hf : Flat q.left) (hs : Surjective q.left) (ha : IsAffineHom q.left)
    (hk : IsPullback i (toUnit _) q (η[E.B]))
    (s : ∀ (χ : E.X) (a : (E.O χ).L.ι), Γ(G.left, q.left ⁻¹ᵁ (E.O χ).L.U a)ˣ)
    (h₁ : ∀ (χ : E.X) (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (a a' : (E.O χ).L.ι), q.left (r z) ∈ (E.O χ).L.U a →
      q.left (r z) ∈ (E.O χ).L.U a' →
      gm r z _ (s χ a') = gm (r ≫ q.left) z _ ((E.O χ).L.g a a') * gm r z _ (s χ a))
    (h₂ : ∀ (χ : E.X) (a : (E.O χ).L.ι) (Z : Over S) (t : Z ⟶ splitTorus S E.X) (g : Z ⟶ G) (z : Z.left),
      q.left (g.left z) ∈ (E.O χ).L.U a →
      gm ((t ≫ i) * g).left z _ (s χ a) = gm t.left z ⊤ (charUnit S E.X χ) * gm g.left z _ (s χ a))
    (h₃ : ∀ (χ : E.X) (a : (E.O χ).L.ι) (y : (𝟙_ (Over S)).left), q.left (eSec G y) ∈ (E.O χ).L.U a →
      gm (eSec G) y _ (s χ a) * gm (𝟙 _) y _ ((E.O χ).rig.s fun _ => a) = 1) :
    ∃ d : E.GtDatum G, d.q = q ∧ d.i = i := by
  have hact : ∀ {Z : Over S} (t : Z ⟶ splitTorus S E.X) (g : Z ⟶ G) (z : Z.left),
      q.left (((t ≫ i) * g).left z) = q.left (g.left z) := by
    intro Z t g z
    have e : ((t ≫ i) * g) ≫ q = g ≫ q := by
      rw [MonObj.mul_comp, Category.assoc, hk.w, ← Category.assoc, comp_toUnit, ← Hom.one_def, _root_.one_mul]
    exact congrArg (fun f => f.left z) e
  let u : ∀ (j : E.ChartIdx) (_k : Module.Free.ChooseBasisIndex ℤ E.X), Γ(G.left, q.left ⁻¹ᵁ E.chart j)ˣ :=
    fun j k => res (Scheme.Hom.preimage_mono q.left (E.chart_le j k)) (s _ (j k))
  have hu : ∀ (j : E.ChartIdx) k {Z : Scheme.{0}} (r : Z ⟶ G.left) (z : Z), q.left (r z) ∈ E.chart j →
      gm r z (q.left ⁻¹ᵁ E.chart j) (u j k) = gm r z _ (s _ (j k)) := fun j k Z r z hz => gm_res r z _ hz _
  refine ⟨{
    q := q, i := i, q_hom := hq, i_hom := hi, q_flat := hf, q_surjective := hs, q_affine := ha, isKernel := hk
    u := u
    coord := fun j V hV h => ?_
    trans := fun j j' k => unit_ext fun y hy => ?_
    act_le := fun j y hy => (congrArg (· ∈ E.chart j) (hact (fst _ _) (snd _ _) y)).mpr hy
    equiv := fun j k => unit_ext fun y hy => ?_
    unit_norm := fun j k => unit_ext fun y hy => ?_ }, rfl, rfl⟩
  · refine bijective_of_basis E.basis q i hq hi hf hs ha hk V hV _ fun k Z t g z hz => ?_
    have hz' : q.left (((t ≫ i) * g).left z) ∈ V := by rw [hact]; exact hz
    rw [gm_res _ z (V := q.left ⁻¹ᵁ V) _ hz', gm_res _ z (V := q.left ⁻¹ᵁ V) _ hz, hu j k _ z (h hz'), hu j k _ z (h hz)]
    exact h₂ _ _ Z t g z (E.chart_le j k (h hz))
  · refine ((gm_res _ y _ hy _).trans ((hu j' k _ y hy.2).trans
      (h₁ _ _ (𝟙 _) y (j k) (j' k) (E.chart_le j k hy.1) (E.chart_le j' k hy.2)))).trans (Eq.symm ?_)
    exact (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_pull (𝟙 _) q.left y (E.chart j ⊓ E.chart j') hy _).trans
      (gm_res _ y (V := E.chart j ⊓ E.chart j') _ hy _)) ((gm_res _ y _ hy _).trans (hu j k _ y hy.1)))
  · have hy' : q.left (((fst (splitTorus S E.X) G ≫ i) * snd (splitTorus S E.X) G).left y) ∈ E.chart j :=
      (congrArg (· ∈ E.chart j) (hact (fst _ _) (snd _ _) y)).mpr hy
    have e := h₂ _ (j k) _ (fst _ _) (snd _ _) y (E.chart_le j k hy)
    rw [← hu j k _ y hy, ← hu j k _ y hy'] at e
    refine ((gm_res _ y _ hy _).trans ((gm_pull (𝟙 _) ((fst (splitTorus S E.X) G ≫ i) * snd (splitTorus S E.X) G).left y
      (q.left ⁻¹ᵁ E.chart j) hy' _).trans ?_)).trans
      ((map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res (𝟙 _) y _ hy _).trans
        (gm_pull (𝟙 _) (fst (splitTorus S E.X) G).left y ⊤ trivial _))
        (gm_pull (𝟙 _) (snd (splitTorus S E.X) G).left y (q.left ⁻¹ᵁ E.chart j) hy _))).symm
    rw [Category.id_comp, Category.id_comp, Category.id_comp]
    exact e
  · refine Eq.trans ?_ ((h₃ _ (j k) y (E.chart_le j k hy.1)).trans (map_one _).symm)
    refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res _ y _ hy _).trans
      ((gm_pull (𝟙 _) (eSec G) y (q.left ⁻¹ᵁ E.chart j) hy.1 _).trans ?_)) (gm_res _ y _ hy _))
    rw [Category.id_comp]
    exact hu j k _ y hy.1

end

theorem exists_gtDatum_of_gtCoord : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G), ∃ (E : SplitExt (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (xe : E.X ≃+ D.X) (d : E.GtDatum (thickObj R I e G)) (π : E.B.left ⟶ D.P.A.left), IsGrpPullback E.B D.P.A (thick R I e) π ∧ d.q.left ≫ π = g.pG.left ∧ (∀ χ, LBIso (E.O χ).L (LB.LinComb D.P.L (fun a => π ≫ D.Oφ (𝟙 D.P.A) (xe χ) a) Oε)) ∧ ∀ χ, UFib.GenWt (G := thickObj R I e G) d.i (g.t (xe χ)) χ := by
  intro R _ _ I D e G _ _ g
  have := g.q_hom
  have he : eSec (thickObj R I e G) ≫ g.q.left = eSec (thickObj R I e D.P.A) :=
    congrArg (fun f => f.left) (IsMonHom.one_hom g.q)
  choose ρ hρ hρ' using fun χ => exists_rig g.q.left _ _ he (bundle I D e χ) (coordUnit g χ) (coordUnit_trans g χ)
  let E : SplitExt (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) :=
    { B := thickObj R I e D.P.A
      isAbelian := isAbelianScheme_thick I D e
      X := D.X
      O := fun χ => ⟨bundle I D e χ, ρ χ, DVR.linComb_isLB _ D.P.isLB _ _, hρ χ⟩
      addIso := bundle_add I D e
      zeroTriv := bundle_zero I D e
      primitive := bundle_primitive I D e }
  obtain ⟨d, hq, hi⟩ := exists_gtDatum_of_units E g.q g.i g.q_hom g.i_hom g.q_flat g.q_surj g.q_affine g.isKernel
    (coordUnit g) (coordUnit_trans g) (coordUnit_weight g) hρ'
  refine ⟨E, AddEquiv.refl _, d, (D.prBe I e).left, isGrpPullback_pullback D.P.A (thick R I e), ?_, fun χ => ?_,
    fun χ => ?_⟩
  · rw [hq]
    rfl
  · refine exists_iso D.P.isLB (funext fun k => ?_) Oε
    refine Eq.trans ?_ (WeightPf.Oφ_comp (D.prBe I e) (𝟙 _) χ k).symm
    rw [Category.comp_id]
  · rw [hi]
    intro Z t y z J hJ
    have v := TorusCoord.val_t_act g t y χ (𝟙 _) z J hJ
    have c : splitTorusPointsEquiv _ D.X Z t (Multiplicative.ofAdd χ) = pullU t.left ⊤ (charUnit _ D.X χ) :=
      Units.ext (splitTorusPointsEquiv_val _ _ _ t χ)
    have c' := gm_pull (𝟙 _) t.left z ⊤ trivial (charUnit _ D.X χ)
    rw [Category.id_comp] at c'
    rw [Category.id_comp, Category.id_comp, c] at v
    exact v.trans (congrArg (· * _) c')

end GlobalTheory.ZH.UFib
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGtDatumOfTorusCoordsStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_gtDatum_of_torusCoords : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G), ∃ (E : SplitExt (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (xe : E.X ≃+ D.X) (d : E.GtDatum (thickObj R I e G)) (π : E.B.left ⟶ D.P.A.left), IsGrpPullback E.B D.P.A (thick R I e) π ∧ d.q.left ≫ π = g.pG.left ∧ (∀ χ, LBIso (E.O χ).L (LB.LinComb D.P.L (fun a => π ≫ D.Oφ (𝟙 D.P.A) (xe χ) a) Oε)) ∧ ∀ χ, UFib.GenWt (G := thickObj R I e G) d.i (g.t (xe χ)) χ := by
  first | exact @GlobalTheory.ZH.UFib.exists_gtDatum_of_gtCoord | exact GlobalTheory.ZH.UFib.exists_gtDatum_of_gtCoord | (intros; apply GlobalTheory.ZH.UFib.exists_gtDatum_of_gtCoord <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsoIsMonHomOfIsGtOfRangeEq
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory

theorem ker_le_ker_of_range_subset_of_isReduced {X T Y : Scheme.{0}} [IsReduced T] (f : X ⟶ Y)
    [IsClosedImmersion f] (g : T ⟶ Y) (h : Set.range g ⊆ Set.range f) : f.ker ≤ g.ker := by
  refine le_trans ?_ (ReducedSubgroup.vanishingIdeal_le_ker g
    ⟨Set.range f, f.isClosedEmbedding.isClosed_range⟩ h)
  rw [← Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal]
  exact f.range_subset_ker_support

theorem exists_iso_isMonHom_of_isGt_of_range_eq :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (Y : Over (Sp k)) (E E' : SplitExt (Sp k)) (G G' : Over (Sp k)) [GrpObj G] [GrpObj G'] [IsCommMonObj G] [IsCommMonObj G'] (f : G ⟶ Y) (f' : G' ⟶ Y), E.IsGt G → E'.IsGt G' → IsClosedImmersion f.left → IsClosedImmersion f'.left → Set.range f.left = Set.range f'.left → η[G] ≫ f = η[G'] ≫ f' → ∃ e : G ≅ G', IsMonHom e.hom ∧ e.hom ≫ f' = f := by
  intro k _ _ Y E E' G G' _ _ _ _ f f' h h' hf hf' hr h1
  have hs := (UnitRigidity.smooth_geometricallyConnected_of_isGt E G h).1
  have hs' := (UnitRigidity.smooth_geometricallyConnected_of_isGt E' G' h').1
  have : IsReduced G.left := isReduced_of_smooth_of_isReduced G.hom
  have : IsReduced G'.left := isReduced_of_smooth_of_isReduced G'.hom
  have hk : f'.left.ker = f.left.ker :=
    le_antisymm (ker_le_ker_of_range_subset_of_isReduced _ _ hr.le)
      (ker_le_ker_of_range_subset_of_isReduced _ _ hr.ge)
  have := IsClosedImmersion.isIso_lift f'.left f.left hk
  have hl := IsClosedImmersion.lift_fac f'.left f.left hk.le
  let e : G ≅ G' := Over.isoMk (asIso (IsClosedImmersion.lift f'.left f.left hk.le)) (by
    rw [asIso_hom, ← Over.w f', reassoc_of% hl, Over.w f])
  have he : e.hom ≫ f' = f := Over.OverMorphism.ext hl
  have : Mono f' := Over.mono_of_mono_left f'
  refine ⟨e, isMonHom_of_isGt_of_one k E E' G G' h h' e.hom ?_, he⟩
  rw [← cancel_mono f', Category.assoc, he, h1]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitExtendOfGeneric
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.GenericExtend

theorem eq_of_valR_eq {Y : Scheme.{0}} [IsReduced Y] {V : Y.Opens} {f g : Γ(Y, V)}
    (H : ∀ x ∈ V, ∃ (K : Type) (_ : Field K) (h : Sp K ⟶ Y), (∀ o, h o = x) ∧
      valR h V f = valR h V g) : f = g := by
  rw [← sub_eq_zero, ← basicOpen_eq_bot_iff, eq_bot_iff]
  intro x hx
  exfalso
  have hxV := Y.basicOpen_le _ hx
  obtain ⟨K, _, h, ho, hv⟩ := H x hxV
  have h₁ : ⊤ ≤ h ⁻¹ᵁ V := fun o _ ↦ show h o ∈ V from (ho o).symm ▸ hxV
  have h₂ := (Points.le_preimage_basicOpen_iff h h₁ (f - g)).1
    fun o _ ↦ show h o ∈ Y.basicOpen (f - g) from (ho o).symm ▸ hx
  rw [Points.valR_eq h V h₁, Points.valR_eq h V h₁] at hv
  rw [Points.valR_eq h V h₁, map_sub, hv, sub_self] at h₂
  exact not_isUnit_zero h₂

theorem compat_of_valF {Q Y : Scheme.{0}} [IsReduced Q] {N : LB Y} {J : Q ⟶ Y}
    {τ : ∀ a, Γ(Q, J ⁻¹ᵁ N.U a)ˣ}
    (H : ∀ (a b : N.ι) (K : Type) [Field K] (h : Sp K ⟶ Q), Set.range (h ≫ J) ⊆ N.U a →
      Set.range (h ≫ J) ⊆ N.U b →
      valF h _ (τ a).val = valF (h ≫ J) _ (N.g a b).val * valF h _ (τ b).val) :
    Compat N J τ := by
  intro Z r z a b ha hb
  have l₁ : J ⁻¹ᵁ (N.U a ⊓ N.U b) ≤ J ⁻¹ᵁ N.U a := J.preimage_mono inf_le_left
  have l₂ : J ⁻¹ᵁ (N.U a ⊓ N.U b) ≤ J ⁻¹ᵁ N.U b := J.preimage_mono inf_le_right
  have key : res l₁ (τ a) = pullU J _ (N.g a b) * res l₂ (τ b) := by
    refine Units.ext (eq_of_valR_eq fun x hx ↦ ⟨Q.residueField x, inferInstance,
      Q.fromSpecResidueField x, fun o ↦ Scheme.fromSpecResidueField_apply x o, ?_⟩)
    have ho : ∀ o, (Q.fromSpecResidueField x : Sp (Q.residueField x) ⟶ Q) o = x :=
      fun o ↦ Scheme.fromSpecResidueField_apply x o
    generalize (Q.fromSpecResidueField x : Sp (Q.residueField x) ⟶ Q) = h at ho
    have h₁ : ⊤ ≤ h ⁻¹ᵁ J ⁻¹ᵁ (N.U a ⊓ N.U b) := fun o _ ↦
      show h o ∈ J ⁻¹ᵁ (N.U a ⊓ N.U b) from (ho o).symm ▸ hx
    have := H a b _ h (by rintro _ ⟨o, rfl⟩; exact (h₁ (x := o) trivial).1)
      (by rintro _ ⟨o, rfl⟩; exact (h₁ (x := o) trivial).2)
    rw [Points.valF_eq_valR, Points.valF_eq_valR, Points.valF_eq_valR, Points.valR_comp,
      ← Points.valR_res h l₁ h₁, ← Points.valR_res h l₂ h₁, ← Points.valR_mul _ _ h₁] at this
    exact this
  have hz : r z ∈ J ⁻¹ᵁ (N.U a ⊓ N.U b) := ⟨ha, hb⟩
  have := congrArg (gm r z _) key
  rwa [map_mul, gm_res r z l₁ hz, gm_res r z l₂ hz, gm_pull r J z _ hz] at this

theorem exists_unit_extend_of_generic : ∀ (X P : Scheme.{0}) [IsLocallyNoetherian X] (Ω : Type) [Field Ω] (j : Sp Ω ⟶ X), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → IsPreimmersion j → Flat j → IsDominant j → ∀ (p : P ⟶ X) (e : X ⟶ P) (N : LB P), e ≫ p = 𝟙 X → Smooth p → GeometricallyIntegral p → N.IsLB → ∀ τ : ∀ a, Γ(pullback p j, pullback.fst p j ⁻¹ᵁ N.U a)ˣ, (∀ (a b : N.ι) (K : Type) [Field K] (h : Sp K ⟶ pullback p j), Set.range (h ≫ pullback.fst p j) ⊆ N.U a → Set.range (h ≫ pullback.fst p j) ⊆ N.U b → valF h _ (τ a).val = valF (h ≫ pullback.fst p j) _ (N.g a b).val * valF h _ (τ b).val) → (∀ a, ∃ u : Γ(X, e ⁻¹ᵁ N.U a)ˣ, ∀ h : Sp Ω ⟶ pullback p j, h ≫ pullback.fst p j = j ≫ e → Set.range (j ≫ e) ⊆ N.U a → valF h _ (τ a).val = valF j _ u.val) → ∃ σ : ∀ a, Γ(P, N.U a)ˣ, ∀ (a : N.ι) (K : Type) [Field K] (h : Sp K ⟶ pullback p j), Set.range (h ≫ pullback.fst p j) ⊆ N.U a → valF (h ≫ pullback.fst p j) _ (σ a).val = valF h _ (τ a).val := by
  intro X P _ Ω _ j hX _ _ _ p e N he _ _ hN τ H₁ H₂
  have := GlobalTheory.IsNormalScheme.of_pred hX
  have := isNormalScheme_of_smooth p
  have := LocallyOfFiniteType.isLocallyNoetherian p
  have : QuasiCompact j := ⟨fun U _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have := IsSchemeTheoreticallyDominant.of_isDominant j
  have hJ := (pullback.fst p j).app_injective
  have := DvrModel.isIntegral_of_geometricallyIntegral (IsPullback.of_hasPullback p j)
  have hτ : Compat N (pullback.fst p j) τ := compat_of_valF H₁
  choose ρ hρ using H₂
  let eU : Sp Ω ⟶ pullback p j := pullback.lift (j ≫ e) (𝟙 _) (by simp [he])
  have w : eU ≫ pullback.fst p j = j ≫ e := pullback.lift_fst _ _ _
  have hπ : eU ≫ pullback.snd p j = 𝟙 _ := pullback.lift_snd _ _ _
  have hτρ : ∀ (Z : Scheme.{0}) (κ : Z ⟶ Sp Ω) (z : Z) (a : N.ι),
      e (j (κ z)) ∈ N.U a → gm (κ ≫ eU) z (pullback.fst p j ⁻¹ᵁ N.U a) (τ a) =
        gm (κ ≫ j) z (e ⁻¹ᵁ N.U a) (ρ a) := by
    intro Z κ z a ha
    have hle : j ⁻¹ᵁ e ⁻¹ᵁ N.U a ≤ eU ⁻¹ᵁ pullback.fst p j ⁻¹ᵁ N.U a := by
      rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, w]
    have h₁ : ⊤ ≤ (𝟙 (Sp Ω) :) ⁻¹ᵁ j ⁻¹ᵁ e ⁻¹ᵁ N.U a := fun o _ ↦
      show e (j o) ∈ N.U a from Subsingleton.elim (κ z) o ▸ ha
    have key : res hle (pullU eU _ (τ a)) = pullU j _ (ρ a) := by
      refine Units.ext (eq_of_valR_eq fun x hx ↦ ⟨Ω, inferInstance, 𝟙 _,
        fun o ↦ Subsingleton.elim _ _, ?_⟩)
      have := hρ a eU w (by rintro _ ⟨o, rfl⟩; exact h₁ (x := o) trivial)
      rw [Points.valF_eq_valR, Points.valF_eq_valR] at this
      refine (Points.valR_res _ hle h₁ _).trans ?_
      refine (Points.valR_comp (𝟙 _) eU _ _).symm.trans ?_
      refine Eq.trans ?_ (Points.valR_comp (𝟙 _) j _ _)
      rwa [Category.id_comp, Category.id_comp]
    have := congrArg (gm κ z _) key
    rwa [gm_res_pullU κ eU z hle ha, gm_pull κ j z _ ha] at this
  have key : ∀ a, ∀ y ∈ N.U a, Order.coheight y ≤ 1 → y ∉ Set.range (pullback.fst p j) →
      ExtAt (pullback.fst p j) (N.U a) (τ a).val y ∧
        ExtAt (pullback.fst p j) (N.U a) ((τ a)⁻¹).val y := fun a y ha h1 hy ↦ by
    refine extAt_of_coheight_eq_one j p he hN w hπ hτ hτρ y
      (le_antisymm (coheight_apply_le_one p h1) (ENat.one_le_iff_ne_zero.2 fun h0 ↦ hy ?_)) a ha
    rw [Scheme.Pullback.range_fst]
    obtain ⟨ξ, hξ, hξy⟩ := exists_specializes_mem_range j (p y)
    exact (Flat.generalizingMap j).stableUnderGeneralization_range
      (show p y ⤳ ξ from Order.coheight_eq_zero.1 h0 hξy) hξ
  choose s hs using fun a ↦ exists_app_eq _ hJ _ _ fun y ha h1 hy ↦ (key a y ha h1 hy).1
  choose s' hs' using fun a ↦ exists_app_eq _ hJ _ _ fun y ha h1 hy ↦ (key a y ha h1 hy).2
  have hm : ∀ a, s a * s' a = 1 := fun a ↦ hJ _ (by
    change ((pullback.fst p j).app _).hom _ = ((pullback.fst p j).app _).hom _
    rw [map_mul, map_one, hs, hs', Units.mul_inv])
  refine ⟨fun a ↦ ⟨s a, s' a, hm a, (mul_comm _ _).trans (hm a)⟩, fun a K _ h _ ↦ ?_⟩
  rw [Points.valF_eq_valR, Points.valF_eq_valR, Points.valR_comp]
  exact congrArg _ (hs a)

end GlobalTheory.GenericExtend
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.BasisValueAtOrigin
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.OriginFrame

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S} {Z : Scheme.{0}}

theorem sval_valueAt {a : ℤ} {s : LB.Sec (LPow A L a T)} {x : T ⟶ A}
    {τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => a))} {v : Γ(T.left, ⊤)}
    (H : IsValueAt A L a s x τ v) (t : Z ⟶ T.left) {z : Z} {J} (hJ : Good L z J) :
    sval (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s (t ≫ (ptSecT A x).left) z J =
      gs t z ⊤ v * (val τ t z J).val := by
  have hy := hJ.mem (fun _ : Fin 1 => x.left) t
  rw [sval_of (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) s (t ≫ (ptSecT A x).left) z J
    (fun _ => J (t ≫ x.left)) (fun _ => by rw [Category.assoc, ← Over.comp_left, ptSecT, lift_snd])]
  refine Eq.trans ?_ ((congrArg (gs t z _) (H _)).trans ((gs_mul _ z _ hy _ _).trans
    (congrArg₂ (· * ·) (gs_res _ z _ hy _) (gs_unit _ z _ hy _))))
  exact ((gs_res _ z _ hy _).trans (gs_pull t (ptSecT A x).left z
    (LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => J (t ≫ x.left))) (val_le A L x _ hy) _)).symm

theorem val_rigT (rig : LB.Gen (L.pull (eSec A))) (k : ℤ) (t : Z ⟶ T.left) {z : Z} {J} (hJ : Good L z J) :
    val (rigT A L rig T k) t z J = val rig (t ≫ T.hom) z J ^ k := by
  have hy := hJ.mem (fun _ : Fin 1 => T.hom ≫ eSec A) t
  refine (map_zpow _ _ _).trans (congrArg (· ^ k) ((gm_res _ z _ hy _).trans ?_))
  exact gm_pull t T.hom z (LB.wchart L (fun _ : PUnit => eSec A) (fun _ => J (t ≫ T.hom ≫ eSec A)))
    (rigT_le A L _ hy) _

theorem torsFrame_pow_origin (P : PolAV S) {T : Over S} {m : ℕ}
    {rig : LB.Gen (P.L.pull (eSec P.A))} {x : T ⟶ P.A} (hx : x = 1) {τ} (H : IsTorsFrame P rig m x τ)
    (t : Z ⟶ T.left) {z : Z} {J} (hJ : Good P.L z J) :
    val τ t z J ^ (m ^ 2) = val rig (t ≫ T.hom) z J ^ (m ^ 2) := by
  subst hx
  obtain ⟨-, -, β, hβ, hn, hc⟩ := H
  have q₁ := val_corr hJ hn (t ≫ T.hom)
  have q₂ := val_corr hJ hc t
  rw [val_pull hJ, val_mul hJ, val_inv] at q₁
  rw [val_mul hJ, val_pull hJ, val_rigT _ _ _ hJ] at q₂
  have p₁ : val (rigPow P.A P.L rig ((m : ℤ) ^ 2)) (t ≫ T.hom) z J = val rig (t ≫ T.hom) z J ^ ((m : ℤ) ^ 2) :=
    map_zpow _ _ _
  have p₂ : val (powFrame P.A P.L 1 τ ((m : ℤ) ^ 2)) t z J = val τ t z J ^ ((m : ℤ) ^ 2) := map_zpow _ _ _
  have q₃ : val β (t ≫ (1 : T ⟶ P.A).left) z J = _ := q₁.trans (congrArg (· * _) p₁)
  rw [p₂, q₃, zpow_one] at q₂
  rw [← zpow_natCast, ← zpow_natCast, Nat.cast_pow, q₂]
  exact inv_mul_cancel_right _ _

theorem valF_spMap_fn {R K : Type} [CommRing R] [Field K] (y : R →+* K) (a : R) :
    valF (X := (baseOver (Sp R)).left) (spMap y) ⊤ (fn a) = y a := by
  rw [valF, dite_eq_left (by simp)]
  have h := congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom y))
  have h' := congrArg (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom h
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, Iso.inv_hom_id_apply] at h'
  refine Eq.trans ?_ h'.symm
  congr 1

end GlobalTheory.OriginFrame

namespace GlobalTheory


open OriginFrame ThetaScalar in
theorem basis_value_at_origin : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (K : Type) [Field K] (y₀ : S.R →+* K) (r : Sp K ⟶ (baseOver (Sp S.R) ⊗ ρ.P.A).left) (jP : ρ.P.L.ι), r ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left = spMap y₀ ≫ eSec ρ.P.A → Set.range (r ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left) ⊆ ρ.P.L.U jP → ∃ ξ : K, ξ ^ ((S.r * S.N) ^ 2) = 1 ∧ ∀ l, valF r _ ((ρ.s l).f (fun _ => jP)) = y₀ ⟨S.ev 0 l, S.ev_mem 0 l⟩ * (ξ * valF (spMap y₀) _ (ρ.rig.s (fun _ => jP)).val) ^ S.N := by
  intro o Ω _ _ _ S ρ K _ y₀ r jP hr hU
  have := ρ.P.isAb.comm
  have h0 : ρ.pt 0 = 1 := mul_left_cancel (a := ρ.pt 0) (by rw [← ρ.pt_add, add_zero, _root_.mul_one])
  let z : Sp K := IsLocalRing.closedPoint K
  let t : Sp K ⟶ (baseOver (Sp S.R)).left := spMap y₀
  have ht : t ≫ (baseOver (Sp S.R)).hom = spMap y₀ := Category.comp_id _
  have hz : (spMap y₀ ≫ eSec ρ.P.A) z ∈ ρ.P.L.U jP := hU ⟨z, by rw [hr]⟩
  obtain ⟨J, hJ, eJ⟩ := exists_good ρ.P.L ρ.P.isLB z (fun _ : PUnit => spMap y₀ ≫ eSec ρ.P.A) (fun _ => jP)
    (fun _ _ _ => rfl) (fun _ => hz)
  have hs : (t ≫ (ptSecT ρ.P.A (ρ.pt 0)).left) ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left = spMap y₀ ≫ eSec ρ.P.A := by
    rw [Category.assoc, ← Over.comp_left, ptSecT, lift_snd, h0, ← ht, Category.assoc]; rfl
  have er : r = t ≫ (ptSecT ρ.P.A (ρ.pt 0)).left := by
    haveI : Mono (snd (baseOver (Sp S.R)) ρ.P.A).left :=
      inferInstanceAs (Mono (pullback.snd (𝟙 (Sp S.R)) ρ.P.A.hom))
    rw [← cancel_mono (snd (baseOver (Sp S.R)) ρ.P.A).left, hr, hs]
  have hp := torsFrame_pow_origin ρ.P h0 (ρ.fr_tors 0) t hJ
  rw [ht] at hp
  have m₁ : r z ∈ LB.wchart ρ.P.L (fun _ : Fin 1 => (snd (baseOver (Sp S.R)) ρ.P.A).left) (fun _ => jP) :=
    Set.mem_iInter.2 fun _ => hU ⟨z, rfl⟩
  have m₂ : (spMap y₀) z ∈ LB.wchart ρ.P.L (fun _ : PUnit => eSec ρ.P.A) (fun _ => jP) :=
    Set.mem_iInter.2 fun _ => hz
  have m₃ := hJ.mem (fun _ : Fin 1 => (ρ.pt 0).left) t
  have a₂ : toStk z (valF (spMap y₀) _ (ρ.rig.s (fun _ => jP)).val) = (val ρ.rig (spMap y₀) z J).val :=
    (toStk_valF_gs (spMap y₀) _ z m₂ _).trans ((gs_unit _ z _ m₂ _).trans
      (congrArg Units.val (val_of ρ.rig (spMap y₀) z J (fun _ => jP) (fun _ => eJ PUnit.unit)).symm))
  obtain ⟨a, ha⟩ : ∃ a : K, toStk z a = (val (ρ.fr 0) t z J).val :=
    ⟨_, (toStk_valF_gs t _ z m₃ _).trans (gs_unit _ z _ m₃ _)⟩
  generalize valF (spMap y₀) _ (ρ.rig.s (fun _ => jP)).val = b at a₂ ⊢
  have hb : b ≠ 0 := fun e => (val ρ.rig (spMap y₀) z J).ne_zero (by rw [← a₂, e, map_zero])
  have hab : a ^ ((S.r * S.N) ^ 2) = b ^ ((S.r * S.N) ^ 2) := (toStk z).injective (by
    rw [map_pow, map_pow, ha, a₂, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val]
    exact congrArg Units.val hp)
  refine ⟨a / b, by rw [div_pow, hab, div_self (pow_ne_zero _ hb)], fun l => (toStk z).injective ?_⟩
  have hv := sval_valueAt (ρ.ev_val l 0) t hJ
  have p : val (powFrame ρ.P.A ρ.P.L (ρ.pt 0) (ρ.fr 0) S.N) t z J = val (ρ.fr 0) t z J ^ (S.N : ℤ) :=
    map_zpow _ _ _
  rw [← er, p, zpow_natCast] at hv
  replace hv := (sval_of (φ := fun _ : Fin 1 => (snd (baseOver (Sp S.R)) ρ.P.A).left) (ε := fun _ => (S.N : ℤ))
    (ρ.s l) r z J (fun _ => jP) (fun _ => by rw [hr]; exact eJ PUnit.unit)).symm.trans hv
  have a₁ := toStk_valF_gs r _ z m₁ ((ρ.s l).f (fun _ => jP))
  have a₃ := toStk_valF_gs t ⊤ z trivial (fn (⟨S.ev 0 l, S.ev_mem 0 l⟩ : S.R))
  rw [valF_spMap_fn] at a₃
  refine a₁.trans (hv.trans ?_)
  rw [div_mul_cancel₀ _ hb, map_mul, map_pow, a₃, ha, Units.val_pow_eq_pow_val]

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGtDatumBaseChangeMaps
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGtDatumBaseChangeMaps
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

noncomputable section

namespace GlobalTheory


open GtBaseChange in
theorem exists_gtDatum_baseChange_maps :
    ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (E : SplitExt S) (G : Over S) [GrpObj G] (d : E.GtDatum G), ∃ (E' : SplitExt S') (xe : E'.X ≃+ E.X) (d' : E'.GtDatum ((Over.pullback f).obj G)) (π : E'.B.left ⟶ E.B.left), IsGrpPullback E'.B E.B f π ∧ d'.q.left ≫ π = pullback.fst G.hom f ≫ d.q.left ∧ (∀ χ, LBIso (E'.O χ).L ((E.O (xe χ)).L.pull π)) ∧ ∀ (Z : Over S') (τ : Z ⟶ splitTorus S' E'.X), ∃ τ₀ : Over.mk (Z.hom ≫ f) ⟶ splitTorus S E.X, (τ₀ ≫ d.i).left = (τ ≫ d'.i).left ≫ pullback.fst G.hom f ∧ ∀ (χ : E'.X) (z : Z.left), gm (Y := Z.left) τ₀.left z ⊤ (charUnit S E.X (xe χ)) = gm τ.left z ⊤ (charUnit S' E'.X χ) := by
  intro S S' f E G _ d
  have := d.q_hom
  have := d.i_hom
  have : IsMonHom (Iso.refl ((Over.pullback f).obj G)).hom := inferInstanceAs (IsMonHom (𝟙 _))
  have : IsMonHom (Iso.refl ((Over.pullback f).obj E.B)).hom := inferInstanceAs (IsMonHom (𝟙 _))
  obtain ⟨eT, mT, hT⟩ := splitTorus_baseChange S S' f E.X
  obtain ⟨q, i, h1, h2, h3, h4, h5, h6, h7, h8⟩ := TorusExtBaseChange.exists_extension f eT
    (Iso.refl ((Over.pullback f).obj G)) (Iso.refl ((Over.pullback f).obj E.B)) d.i d.q d.q_flat d.q_surjective
    d.q_affine d.isKernel
  have hq : q.left ≫ pullback.fst E.B.hom f = pullback.fst G.hom f ≫ d.q.left := by simpa using h7
  have hi : i.left ≫ pullback.fst G.hom f = (eT.hom.left ≫ pullback.fst _ f) ≫ d.i.left := by simpa using h8
  have le : ∀ j : (extBC f E).ChartIdx, q.left ⁻¹ᵁ (extBC f E).chart j ≤
      pullback.fst G.hom f ⁻¹ᵁ (d.q.left ⁻¹ᵁ E.chart (fun k => j k PUnit.unit)) := fun j y hy => by
    change (pullback.fst G.hom f ≫ d.q.left) y ∈ E.chart (fun k => j k PUnit.unit)
    rw [← hq]
    exact chart_le_preimage f E j hy
  let u : ∀ (j : (extBC f E).ChartIdx) (_ : Module.Free.ChooseBasisIndex ℤ E.X),
      Γ(((Over.pullback f).obj G).left, q.left ⁻¹ᵁ (extBC f E).chart j)ˣ := fun j k =>
    res (le j) (pullU (pullback.fst G.hom f) _ (d.u (fun k => j k PUnit.unit) k))
  have hw : ∀ j k, HasWeight i _ (u j k) (E.basis k) := fun j k =>
    HasWeight.baseChange f ((hasWeight_iff d.i _ _ _ (d.act_le _) _).2 (d.equiv _ k)) i _ (by
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      exact congrArg (· ≫ f) (Over.w eT.hom)) hi (hT _) (le j)
      fun Z t g z hz => translate_mem q i h6 t g _ z hz
  refine ⟨extBC f E, AddEquiv.refl _,
    { q := q
      i := i
      q_hom := h1
      i_hom := h5
      q_flat := h2
      q_surjective := h3
      q_affine := h4
      isKernel := h6
      u := u
      coord := fun j V hV h => coord_of_hasWeight E.basis q i h2 h3 h4 h6 _ (u j) (hw j) V hV h
      trans := fun j j' k => unit_ext fun y hy => ?_
      act_le := fun j y hy => translate_mem q i h6 (fst _ _) (snd _ _) ((extBC f E).chart j) y hy
      equiv := fun j k => (hasWeight_iff i _ _ _ _ _).1 (hw j k)
      unit_norm := fun j k => unit_ext fun y hy => ?_ }, pullback.fst E.B.hom f,
    isGrpPullback_pullback E.B f, hq, fun χ => GtBaseChange.lbIso_refl (pull_isLB (E.O χ).isLB _),
    fun Z τ => ?_⟩
  · have hm : pullback.fst G.hom f y ∈ d.q.left ⁻¹ᵁ
        (E.chart (fun k => j k PUnit.unit) ⊓ E.chart (fun k => j' k PUnit.unit)) := ⟨le j hy.1, le j' hy.2⟩
    have e := congrArg (gm (pullback.fst G.hom f) y _)
      (d.trans (fun k => j k PUnit.unit) (fun k => j' k PUnit.unit) k)
    have e' := (gm_res _ y _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      ((gm_pull _ d.q.left y _ hm _).trans (gm_res (pullback.fst G.hom f ≫ d.q.left) y _ hm _))
      (gm_res _ y _ hm _))))
    refine ((gm_res (𝟙 _) y _ hy _).trans (gm_res_pullU' _ y (le j') hy.2 _)).trans (e'.trans (Eq.symm ?_))
    refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ?_
      ((gm_res (𝟙 _) y _ hy _).trans (gm_res_pullU' _ y (le j) hy.1 _)))
    refine ((gm_pull (𝟙 _) q.left y _ hy _).trans (gm_res (𝟙 _ ≫ q.left) y _ hy _)).trans ?_
    refine (gm_pull_g (E.O (E.basis k)).L (pullback.fst E.B.hom f) (𝟙 _ ≫ q.left) y (j k) (j' k)
      ((extBC f E).chart_le j k hy.1) ((extBC f E).chart_le j' k hy.2)).trans ?_
    rw [Category.id_comp, hq]
  · have hs := eSec_fst f G
    have h₁ : (eSec ((Over.pullback f).obj G) ≫ pullback.fst G.hom f) y ∈
        d.q.left ⁻¹ᵁ E.chart (fun k => j k PUnit.unit) := le j hy.1
    rw [hs] at h₁
    have h₂ := (rigChart f E.B (E.O (E.basis k)).L).le (fun _ => j k) hy.2
    let f' : (𝟙_ (Over S')).left ⟶ (𝟙_ (Over S)).left := f
    have hm : f' y ∈ eSec G ⁻¹ᵁ (d.q.left ⁻¹ᵁ E.chart (fun k => j k PUnit.unit)) ⊓
        ((E.O (E.basis k)).L.pull (eSec E.B)).U (fun _ => j k PUnit.unit) := ⟨h₁, h₂⟩
    have e := congrArg (gm f' y _) (d.unit_norm (fun k => j k PUnit.unit) k)
    have e' := ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      (gm_res_pullU f' _ y _ hm _) (gm_res f' y _ hm _))).symm.trans (e.trans (map_one _))
    refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ ?_)).trans (e'.trans (map_one _).symm)
    · refine (gm_res_pullU' _ y _ hy _).trans ((gm_res_pullU _ _ y (le j) hy.1 _).trans ?_)
      rw [hs]
    · exact (gm_res (𝟙 _) y _ hy _).trans
        (gm_res_pullU' f' y ((rigChart f E.B (E.O (E.basis k)).L).le (fun _ => j k)) hy.2 _)
  · have hτ : (eT.hom.left ≫ pullback.fst (splitTorus S E.X).hom f) ≫ (splitTorus S E.X).hom =
        (splitTorus S' E.X).hom ≫ f := by
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      exact congrArg (· ≫ f) (Over.w eT.hom)
    refine ⟨pushPt hτ τ, ?_, fun χ z => ?_⟩
    · change (τ.left ≫ eT.hom.left ≫ pullback.fst (splitTorus S E.X).hom f) ≫ d.i.left =
        (τ.left ≫ i.left) ≫ pullback.fst G.hom f
      exact (Category.assoc _ _ _).trans
        ((congrArg (τ.left ≫ ·) hi.symm).trans (Category.assoc _ _ _).symm)
    · have e₂ : charUnit S' E.X χ =
          pullU (eT.hom.left ≫ pullback.fst (splitTorus S E.X).hom f) ⊤ (charUnit S E.X χ) :=
        Units.ext (hT χ).symm
      refine Eq.trans ?_ (congrArg (gm τ.left z ⊤) e₂).symm
      exact (gm_pull τ.left _ z ⊤ trivial _).symm

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGtDatumBaseChangeMapsStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_gtDatum_baseChange_maps' : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (E : SplitExt S) (G : Over S) [GrpObj G] (d : E.GtDatum G), ∃ (E' : SplitExt S') (xe : E'.X ≃+ E.X) (d' : E'.GtDatum ((Over.pullback f).obj G)) (π : E'.B.left ⟶ E.B.left), IsGrpPullback E'.B E.B f π ∧ d'.q.left ≫ π = pullback.fst G.hom f ≫ d.q.left ∧ (∀ χ, LBIso (E'.O χ).L ((E.O (xe χ)).L.pull π)) ∧ ∀ (Z : Over S') (τ : Z ⟶ splitTorus S' E'.X), ∃ τ₀ : Over.mk (Z.hom ≫ f) ⟶ splitTorus S E.X, (τ₀ ≫ d.i).left = (τ ≫ d'.i).left ≫ pullback.fst G.hom f ∧ ∀ (χ : E'.X) (z : Z.left), gm (Y := Z.left) τ₀.left z ⊤ (charUnit S E.X (xe χ)) = gm τ.left z ⊤ (charUnit S' E'.X χ) := by
  first | exact @GlobalTheory.exists_gtDatum_baseChange_maps | exact GlobalTheory.exists_gtDatum_baseChange_maps | (intros; apply GlobalTheory.exists_gtDatum_baseChange_maps <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFactorClassicalPointOfLargeTest
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFactorClassicalPointOfLargeTest
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH
open GlobalTheory.Points

theorem exists_finset_closure_eq_top {o : Type} [CommRing o] [Algebra.FiniteType ℤ o] {X : Scheme.{0}}
    (s : X ⟶ Sp o) [LocallyOfFiniteType s] {W : X.Opens} (hW : IsAffineOpen W) :
    ∃ t : Finset Γ(X, W), Subring.closure (t : Set Γ(X, W)) = ⊤ := by
  have h1 : (s.appLE ⊤ W le_top).hom.FiniteType :=
    HasRingHomProperty.appLE (P := @LocallyOfFiniteType) s inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨W, hW⟩ le_top
  have h2 : ((Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom).FiniteType :=
    RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of o)).symm.commRingCatIsoToRingEquiv.surjective
  have h3 : (algebraMap ℤ o).FiniteType := RingHom.finiteType_algebraMap.2 inferInstance
  have h4 := (h1.comp h2).comp h3
  have h5 : (algebraMap ℤ Γ(X, W)).FiniteType := by
    convert h4 using 1
    exact RingHom.ext_int _ _
  obtain ⟨t, ht⟩ := (RingHom.finiteType_algebraMap.1 h5).out
  refine ⟨t, ?_⟩
  rw [Algebra.adjoin_int] at ht
  exact top_unique fun x _ => (show x ∈ subalgebraOfSubring (Subring.closure (t : Set Γ(X, W))) from
    ht ▸ Algebra.mem_top)

theorem exists_factor_of_closure {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (φ : A →+* C) (j : B →+* C)
    (hj : Function.Injective j) {t : Set A} (ht : Subring.closure t = ⊤) (h : ∀ a ∈ t, φ a ∈ j.range) :
    ∃ ψ : A →+* B, j.comp ψ = φ := by
  have h1 : ∀ a, φ a ∈ j.range := fun a =>
    (Subring.closure_le.2 (show t ⊆ (j.range.comap φ : Subring A) from h)) (ht ▸ Subring.mem_top a)
  let e : B ≃+* j.range := RingEquiv.ofBijective j.rangeRestrict
    ⟨fun _ _ hx => hj (congrArg Subtype.val hx), j.rangeRestrict_surjective⟩
  refine ⟨e.symm.toRingHom.comp (φ.codRestrict j.range h1), RingHom.ext fun a => ?_⟩
  exact congrArg Subtype.val (e.apply_symm_apply ⟨φ a, h1 a⟩)

theorem preimage_comp_eq_val {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (U₀ : M.Z.Opens)
    (hne : (U₀ : Set M.Z).Nonempty) (R : Subalgebra o Ω) (u₀ : U₀.toScheme ⟶ Sp R)
    (hu : ∀ eta : Sp Ω ⟶ U₀.toScheme, eta ≫ U₀.ι = M.pt → eta ≫ u₀ = spMap R.val.toRingHom)
    {K : Type} [Field K] (t : Sp K ⟶ U₀.toScheme) (a : R) :
    (Spec.preimage (t ≫ u₀)).hom a = M.val (t ≫ U₀.ι) a := by
  have hle : (⊤ : U₀.toScheme.Opens) ≤ U₀.ι ⁻¹ᵁ U₀ := fun x _ => x.2
  have hs : Function.Surjective (U₀.ι.appLE U₀ ⊤ hle).hom := by
    have : IsIso (U₀.ι.appLE U₀ ⊤ hle) := inferInstance
    exact (asIso (U₀.ι.appLE U₀ ⊤ hle)).commRingCatIsoToRingEquiv.surjective
  obtain ⟨f, hf⟩ := hs ((u₀.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
  have key : ∀ (L : Type) [Field L] (x : Sp L ⟶ U₀.toScheme),
      (Spec.preimage (x ≫ u₀)).hom a = valF (x ≫ U₀.ι) U₀ f := by
    intro L _ x
    rw [preimage_apply, ← valR_appLE x u₀ (U := ⊤) (V := ⊤) le_top (le_preimage_top _), ← hf,
      valR_appLE x U₀.ι hle (le_preimage_top _)]
    rfl
  have hr : Set.range M.pt ⊆ Set.range U₀.ι := by
    rw [Scheme.Opens.range_ι]
    exact (top_le_preimage_iff _ _).1 (M.top_le_preimage_pt hne)
  have h1 := key Ω (IsOpenImmersion.lift U₀.ι M.pt hr)
  rw [hu _ (IsOpenImmersion.lift_fac _ _ _), IsOpenImmersion.lift_fac, Spec.preimage_map] at h1
  rw [key K t]
  refine (RatModel.val_eq ?_ h1.symm).symm
  rintro _ ⟨w, rfl⟩
  exact (t w).2

theorem exists_fac_of_large_test : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), Set.range (gPt p ≫ y) ⊆ U₀ → ∃ (y₀ : S.R →+* PadicAlgCl p) (Fs : Finset (PadicAlgCl p)), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) ∧ ∀ u : ρ.UTest p y₀, (∀ x ∈ Fs, x ∈ Set.range (algebraMap (FractionRing u.V) (PadicAlgCl p))) → Nonempty (Q.Fac y u) := by
  intro o Ω _ _ _ hA S ρ M U₀ EE hB Q p _ y hy
  have hO := hB.ov
  let w : Sp (PadicAlgCl p) := IsLocalRing.closedPoint (PadicAlgCl p)
  have hw : (gPt p ≫ y) w ∈ (U₀ : Set M.Z) := hy ⟨w, rfl⟩
  have hle : S.R ≤ M.O ((gPt p ≫ y) w) := hO.le.trans (RatModel.ringOn_le_O hw)
  let y₀ : S.R →+* PadicAlgCl p :=
    (RatModel.valHom (gPt p ≫ y) _ (RatModel.range_eq_singleton _ w)).comp (Subalgebra.inclusion hle).toRingHom
  have hn : ∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1 := fun a =>
    RatModel.norm_val_le_one (y := y) rfl (x := algebraMap o Ω a) ((M.O _).algebraMap_mem a)
  have hat : S.At M y y₀ := fun _ => rfl
  obtain ⟨W, hW, hyW, -⟩ := exists_isAffineOpen_le y (le_preimage_top y)
  haveI := hA.ft
  haveI := M.lft
  obtain ⟨t, ht⟩ := exists_finset_closure_eq_top M.s hW
  refine ⟨y₀, t.image (fun f => (((valMap y W hyW).hom f : OO p) : PadicAlgCl p)), hn, fun u hu => ?_⟩
  have hj : Function.Injective u.j := fun a b h =>
    IsFractionRing.injective u.V (FractionRing u.V)
      ((algebraMap (FractionRing u.V) (PadicAlgCl p)).injective (congrArg Subtype.val h))
  obtain ⟨ψ, hψ⟩ := exists_factor_of_closure (valMap y W hyW).hom u.j hj ht (by
    intro a ha
    obtain ⟨x, hx⟩ := hu _ (Finset.mem_image_of_mem _ ha)
    obtain ⟨v, hv⟩ := (u.norm_le x).1 (by rw [hx]; exact (mem_OO_iff _).1 (Subtype.prop _))
    exact ⟨v, Subtype.ext (by rw [← hx, ← hv]; rfl)⟩)
  let yV : Sp u.V ⟶ M.Z := Spec.map (CommRingCat.ofHom ψ) ≫ hW.fromSpec
  have hfac : spMap u.j ≫ yV = y := by
    rw [← specMap_valMap_fromSpec hW y hyW, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ]
    rfl
  have hg : spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ≫ jK u.V ≫ yV = gPt p ≫ y := by
    have e : spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ≫ jK u.V = gPt p ≫ spMap u.j := by
      rw [← Spec.map_comp, ← Spec.map_comp]
      rfl
    rw [← hfac, ← Category.assoc, e, Category.assoc]
  have hr : Set.range (jK u.V ≫ yV) ⊆ Set.range U₀.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    rw [Subsingleton.elim x (spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) w)]
    rw [← hg] at hw
    exact hw
  refine ⟨⟨hat, yV, hfac, IsOpenImmersion.lift U₀.ι _ hr, IsOpenImmersion.lift_fac _ _ _, ?_⟩⟩
  rw [← Spec.map_preimage (IsOpenImmersion.lift U₀.ι _ hr ≫ Q.u₀)]
  congr 1
  ext a
  apply (algebraMap (FractionRing u.V) (PadicAlgCl p)).injective
  have h1 := preimage_comp_eq_val M U₀ hO.ne S.R Q.u₀ Q.u₀_pt
    (spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ≫ IsOpenImmersion.lift U₀.ι _ hr) a
  rw [Category.assoc, Category.assoc, IsOpenImmersion.lift_fac, hg, ← hat a, Spec.preimage_comp,
    Spec.preimage_map] at h1
  exact h1.trans (DFunLike.congr_fun u.fac a).symm

end GlobalTheory.ZH
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFactorClassicalPointOfLargeTestStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_factor_classicalPoint_of_large_test : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), Set.range (gPt p ≫ y) ⊆ U₀ → ∃ (y₀ : S.R →+* PadicAlgCl p) (Fs : Finset (PadicAlgCl p)), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) ∧ ∀ u : ρ.UTest p y₀, (∀ x ∈ Fs, x ∈ Set.range (algebraMap (FractionRing u.V) (PadicAlgCl p))) → Nonempty (Q.Fac y u) := by
  first | exact @GlobalTheory.ZH.exists_fac_of_large_test | exact GlobalTheory.ZH.exists_fac_of_large_test | (intros; apply GlobalTheory.ZH.exists_fac_of_large_test <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GtAddIotaSubExist
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH

theorem gt_add_iota_sub_exist : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀), (∀ g g' : GtPtF u.D.toPre (PadicAlgCl p), ∃ g'', GtPtF.IsAdd g g' g'') ∧ (∀ y, ∃ g : GtPtF u.D.toPre (PadicAlgCl p), GtPtF.IsIota y g) ∧ ∀ g h : GtPtF u.D.toPre (PadicAlgCl p), ∃ g', GtPtF.IsAdd g' h g := by
  intro _ o Ω _ _ _ _ S ρ p _ y₀ u
  letI := GlobalTheory.TorusExt.gtGroup u.D.toPre (PadicAlgCl p)
  exact ⟨fun g g' => ⟨g + g', (GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).2 rfl⟩,
    fun y => GlobalTheory.TorusExt.exists_iota u.D.tau_bimult y,
    fun g h => ⟨g - h, (GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).2 (sub_add_cancel g h).symm⟩⟩

end GlobalTheory.ZH
end
end
