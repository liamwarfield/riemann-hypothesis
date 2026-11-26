module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomFiniteFreeFinrankLeFourMulDim
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianPartConst
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumFinitePartMovesVacuumAsThetaModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTripleThetaKernelMinorsEqConstConjJet
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeUnobstructedSquareZeroAffine
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFirstDeRhamStructure
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorPeriodDefectIsCocycle

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqPowSmulOfPDivGroupTorsionTowerMap
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqPowSmulOfPDivGroupTorsionTowerMap
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.AV GlobalTheory.AV.AbVar
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

open ReciprocityTheory.ChartRestriction.G.Semi
open CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.AV.AbVar

theorem eq_zero_of_forall_pow_dvd {M : Type} [AddCommGroup M] [Module.Free ℤ M] {p : ℕ}
    (hp : 1 < p) (x : M) (h : ∀ n : ℕ, ∃ y : M, x = p ^ n • y) : x = 0 := by
  let b := Module.Free.chooseBasis ℤ M
  refine b.repr.injective (Finsupp.ext fun i => ?_)
  rw [map_zero, Finsupp.coe_zero, Pi.zero_apply]
  have e : ∀ (m : ℕ) (y : M), x = p ^ m • y → b.repr x i = (p : ℤ) ^ m * b.repr y i := by
    intro m y hy
    subst hy
    rw [map_nsmul, Finsupp.smul_apply, nsmul_eq_mul]
    push_cast
    rfl
  obtain ⟨y, hy⟩ := h (b.repr x i).natAbs
  have hd : ((p : ℤ) ^ (b.repr x i).natAbs) ∣ b.repr x i := ⟨b.repr y i, e _ y hy⟩
  refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd ?_
  rw [Int.natAbs_pow, Int.natAbs_natCast]
  exact Nat.lt_pow_self hp

theorem eq_pow_smul_of_torsionTower_map : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] (A B : AbVar k)
    (G H : PDivGroup p k) (t : G.TorsionTower A.X) (t' : H.TorsionTower B.X) (f : A ⟶ B),
    (∀ (n : ℕ) (g : G ⟶ H), t.map t' f.hom = (p : ℤ_[p]) ^ n • g → ∃ f' : A ⟶ B, f = p ^ n • f') ∧
    (t.map t' f.hom = 0 → f = 0) := by
  intro p _ k _ A B G H t t' f
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have key : ∀ (n : ℕ) (g : G ⟶ H), t.map t' f.hom = (p : ℤ_[p]) ^ n • g →
      ∃ f' : A ⟶ B, f = p ^ n • f' := by
    intro n g hg

    have happ : (t.map t' f.hom).app n = (0 : G ⟶ H).app n := by
      have h1 : Hom.conv (t.map t' f.hom) n = Hom.conv (0 : G ⟶ H) n := by
        rw [hg, pow_smul_conv, zero_conv]
      exact congrArg (fun c => c.ofConv) h1
    have hy : t.y n ≫ f.hom = 1 := by
      rw [← t.map_y t' f.hom n, happ]
      exact _root_.map_one (t'.pts n _)
    have hpn : ((p ^ n : ℕ) : ℤ) ≠ 0 := by
      exact_mod_cast (pow_pos (by omega : 0 < p) n).ne'
    have hiso : IsIsogeny ((p ^ n : ℕ) • 𝟙 A) := by
      have := (GlobalTheory.MulIsogeny.mul_isogeny k A ((p ^ n : ℕ) : ℤ) hpn).1
      rwa [natCast_zsmul] at this
    obtain ⟨f', hf'⟩ := exists_factor_of_isogeny k A A B ((p ^ n : ℕ) • 𝟙 A) f hiso
      (fun T x hx => by
        have hx' : x ≫ mulN A.X (p ^ n) = SemiCartesianMonoidalCategory.toUnit T ≫ MonObj.one := by
          rw [nsmul_hom, id_hom, MonObj.comp_pow, Category.comp_id] at hx
          rw [GrpTangent.comp_mulN, hx, CategoryTheory.Hom.one_def]
        have hP := TorsionTower.isPullback_y p k G A.X t n
        rw [← hP.lift_fst x (SemiCartesianMonoidalCategory.toUnit T) hx', Category.assoc, hy,
          MonObj.comp_one])
    exact ⟨f', by rw [← hf', Preadditive.nsmul_comp, Category.id_comp]⟩
  refine ⟨key, fun h0 => ?_⟩
  have hfree := (GlobalTheory.T.hom_finite_free_finrank_le_four_mul_dim k A B).2.1
  refine eq_zero_of_forall_pow_dvd hp f fun n => key n 0 ?_
  rw [h0, smul_zero]

end GlobalTheory.AV.AbVar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqPowSmulOfPDivGroupTorsionTowerMapStatement
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.AV GlobalTheory.AV.AbVar
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_pow_smul_of_pDivGroup_torsionTower_map : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] (A B : AbVar k) (G H : PDivGroup p k) (t : G.TorsionTower A.X) (t' : H.TorsionTower B.X) (f : A ⟶ B), (∀ (n : ℕ) (g : G ⟶ H), t.map t' f.hom = (p : ℤ_[p]) ^ n • g → ∃ f' : A ⟶ B, f = p ^ n • f') ∧ (t.map t' f.hom = 0 → f = 0) := by
  first | (exact @GlobalTheory.AV.AbVar.eq_pow_smul_of_torsionTower_map) | (exact GlobalTheory.AV.AbVar.eq_pow_smul_of_torsionTower_map) | (intros; apply GlobalTheory.AV.AbVar.eq_pow_smul_of_torsionTower_map  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocDerKDesc
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Heat.AbConst

open GlobalTheory.KS.GlueDer

section Ray

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
  {oa : Q.OAct O} (Y : Ray oa) {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R} (h : Heat Y.H Y.q.left Q.P.L dd D)

theorem desc_agree (hdd : ∀ a, IsField ⊤ (dd a)) {K : Type} [Field K] [CharZero K] (φ : R →+* K)
    (hΘ : ∀ a b, φ (h.Θ a b) = 0) {Z : Scheme.{0}} (p : Z ⟶ Sp K) (m : Z ⟶ Q.P.A.left)
    (hm : m ≫ Q.P.A.hom = p ≫ spMap φ) (V : h.J → Q.P.A.left.Opens) (hV : ∀ i, h.W i = Y.q.left ⁻¹ᵁ V i)
    (e : h.J → Fld Q.P.A.left)
    (hq : ∀ i V', V' ≤ V i → ∀ f, (Y.q.left.app V').hom (e i V' f) = h.d i _ ((Y.q.left.app V').hom f))
    (i i' : h.J) (W : Q.P.A.left.Opens) (hW : W ≤ V i ⊓ V i') (f : Γ(Q.P.A.left, W)) :
    (m.app W).hom (e i W f) = (m.app W).hom (e i' W f) := by
  have := Y.smooth_q
  have hs := (surjective_q Y).1
  let a := pullback.fst Y.q.left m
  let b := pullback.snd Y.q.left m
  have w : a ≫ Y.q.left = b ≫ m := pullback.condition
  have hle : b ⁻¹ᵁ (m ⁻¹ᵁ W) ≤ a ⁻¹ᵁ (Y.q.left ⁻¹ᵁ W) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, w]
  let π := (a.appLE _ _ hle).hom
  have key : ∀ x, (b.app _).hom ((m.app W).hom x) = π ((Y.q.left.app W).hom x) := fun x => by
    have k : ∀ (c : pullback Y.q.left m ⟶ Q.P.A.left) (_ : c = b ≫ m) (hc : b ⁻¹ᵁ (m ⁻¹ᵁ W) ≤ c ⁻¹ᵁ W),
        (b.app _).hom ((m.app W).hom x) = (c.appLE W _ hc).hom x := by
      rintro _ rfl hc
      rw [Scheme.Hom.comp_appLE, Scheme.Hom.app_eq_appLE b]
      rfl
    rw [k _ w hle]
    exact congrArg (fun ψ => ψ.hom x) (Scheme.Hom.comp_appLE a Y.q.left W _ hle)
  have hc : ∀ r, π (constFn Y.H.hom _ r) = constFn (b ≫ p) _ (φ r) := fun r => by
    rw [← res_const (b ≫ p) hle, ← app_const φ Y.H.hom (b ≫ p) a (by
      rw [← Over.w Y.q, reassoc_of% w, hm, Category.assoc])]
    rfl
  refine FunDescent.app_injective b _ ?_
  show (b.app _).hom ((m.app W).hom _) = (b.app _).hom ((m.app W).hom _)
  rw [key, key, hq i W (hW.trans inf_le_left), hq i' W (hW.trans inf_le_right)]
  refine lift_agree h hdd i i' _ (le_inf ((pre_mono _ (hW.trans inf_le_left)).trans (hV i).ge)
    ((pre_mono _ (hW.trans inf_le_right)).trans (hV i').ge)) π ?_ (fun a b => ?_) _
  · have := (two_ne_zero (α := K)).isUnit.map ((((b ≫ p).appLE ⊤ (b ⁻¹ᵁ (m ⁻¹ᵁ W)) (fun _ _ => trivial)).hom).comp
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom)
    rwa [map_ofNat] at this
  · rw [hc, hΘ, constFn, map_zero, map_zero]

end Ray

theorem exists_locDerK_desc : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R} (h : Heat Y.H Y.q.left Q.P.L dd D), (∀ a, IsField ⊤ (dd a)) → IsBasic Y h → ∀ {K : Type} [Field K] [CharZero K] (φ : R →+* K), (∀ a b, φ (h.Θ a b) = 0) → ∀ {Z : Scheme.{0}} (p : Z ⟶ Sp K) (m : Z ⟶ Q.P.A.left), m ≫ Q.P.A.hom = p ≫ spMap φ → ∃ dl : ∀ W : Q.P.A.left.Opens, Γ(Q.P.A.left, W) → Γ(Z, m ⁻¹ᵁ W), GlobalTheory.KS.LocDerK p Q.P.A.hom m (fun r => φ (D r)) ⊤ dl ∧ (∀ (Z' : Scheme.{0}) (a : Z' ⟶ Y.H.left) (b : Z' ⟶ Z), a ≫ Y.q.left = b ≫ m → ∀ (i : h.J) (W : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ W ≤ h.W i → ∀ f, pbT b (dl W f) (b ⁻¹ᵁ (m ⁻¹ᵁ W)) = pbT a (h.d i _ ((Y.q.left.app W).hom f)) (b ⁻¹ᵁ (m ⁻¹ᵁ W))) := by
  intro R _ _ Q O _ _ _ oa Y n dd D h hdd hB K _ _ φ hΘ Z p m hm
  have := Y.smooth_q
  have hs := (surjective_q Y).1
  choose V hV using fun i => (hB i).1
  choose e he hq using fun i => exists_desc Y (V i) (h.d i) D (hV i ▸ h.lift i)
    fun V' hV' => (hB i).2.2.2 0 V' ((pre_mono _ hV').trans (hV i).ge)
  have hc := fun i i' W hW f => desc_agree Y h hdd φ hΘ p m hm V hV e hq i i' W hW f
  have hcov : ∀ y, ∃ i, m y ∈ V i := fun y => by
    obtain ⟨x, hx⟩ := Y.q.left.surjective (m y)
    have hx' : x ∈ ⨆ i, h.W i := by rw [h.cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx'
    rw [hV] at hi
    exact ⟨i, hx ▸ hi⟩
  have hloc : ∀ i, KS.LocDerK p Q.P.A.hom m (fun r => φ (D r)) (V i) (fun W f => (m.app W).hom (e i W f)) := by
    intro i
    refine ⟨fun W hW f f' => ?_, fun W hW f f' => ?_, fun W W' h' hW f => ?_, fun W hW r => ?_⟩
    · rw [(he i).1.1 W hW, map_add (f := _)]
    · rw [(he i).1.2.1 W hW, map_add (f := _), map_mul, map_mul]
    · rw [(he i).1.2.2 W W' h' hW, rsT_eq (pre_mono m h'), res_app m h']
    · rw [(he i).2 W hW, app_const φ _ p m hm]
  obtain ⟨dl, hdl, hu⟩ := InteriorKS.glue_along p Q.P.A.hom m _ V hcov (fun i W f => (m.app W).hom (e i W f)) hloc hc
  refine ⟨dl, hdl, fun Z' a b w i W hWi f => ?_⟩
  have hWV : W ≤ V i := fun x hx => by
    obtain ⟨y, rfl⟩ := Y.q.left.surjective x
    exact (hWi.trans (hV i).le) hx
  have e1 : dl W f = (m.app W).hom (e i W f) := by
    refine hu W f _ fun j => ?_
    rw [res_app m inf_le_left, ← (he i).1.2.2 W (W ⊓ V j) inf_le_left hWV f]
    exact hc i j _ (le_inf (inf_le_left.trans hWV) inf_le_right) _
  have hle : b ⁻¹ᵁ (m ⁻¹ᵁ W) ≤ a ⁻¹ᵁ (Y.q.left ⁻¹ᵁ W) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, w]
  rw [e1, pbT, pbT, dite_eq_left (le_refl _), dite_eq_left hle, ← hq i W hWV]
  have k : ∀ (c : Z' ⟶ Q.P.A.left) (_ : c = b ≫ m) (hc : b ⁻¹ᵁ (m ⁻¹ᵁ W) ≤ c ⁻¹ᵁ W) x,
      (b.appLE (m ⁻¹ᵁ W) (b ⁻¹ᵁ (m ⁻¹ᵁ W)) (le_refl _)).hom ((m.app W).hom x) = (c.appLE W _ hc).hom x := by
    rintro _ rfl hc x
    rw [Scheme.Hom.comp_appLE]
    rfl
  rw [k (a ≫ Y.q.left) w (by rw [Scheme.Hom.comp_preimage]; exact hle)]
  exact congrArg (fun ψ => ψ.hom (e i W f)) (Scheme.Hom.comp_appLE a Y.q.left W _ hle)

end GlobalTheory.Heat.AbConst
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleConstantExists
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotIntertw

open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)

variable {D : D7}

theorem xiN_of_reads {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ) {S T : HSp D} {a d : ℕ}
    (hS : S.rank = a) (hT : T.rank = d) {δ : ℂ} (hs : δ ≠ 0) {G : VC D a d → ℂ} {f : WO S T → ℂ}
    (h : Reads ψ θ hS hT ⊤ δ 1 G f) :
    GlobalTheory.AdForm.xiN θ S T hS hT (-δ) (area (lamOf D ⊤ δ))⁻¹ f = G := by
  funext z
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have hsp : ∀ Z : D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ,
      (GlobalTheory.AdForm.realPt θ Z).map (finPart D) = 0 ∧ ∀ τ, compAt θ τ (GlobalTheory.AdForm.realPt θ Z) = Z τ := fun Z => by
    refine Classical.epsilon_spec (p := fun w : Mx D T.rank S.rank => w.map (finPart D) = 0 ∧ ∀ τ, compAt θ τ w = Z τ)
      ⟨Matrix.of fun i j => σ fun τ => Z τ i j, ?_, fun τ => ?_⟩
    · ext i j; exact hσ.fin _
    · ext i j; exact hσ.comp _ _
  unfold GlobalTheory.AdForm.xiN
  obtain ⟨h1, h2⟩ := hsp fun τ => Matrix.of fun i j => -((-δ)⁻¹ * z τ (Fin.cast hT i) (Fin.cast hS j))
  have hY : GlobalTheory.NormExact.coordY θ hS hT δ 1 (GlobalTheory.AdForm.realPt θ
      fun τ => Matrix.of fun i j => -((-δ)⁻¹ * z τ (Fin.cast hT i) (Fin.cast hS j))) = z := by
    funext τ i j
    unfold GlobalTheory.NormExact.coordY
    rw [h2, map_one, mul_one, Matrix.of_apply, inv_neg, neg_mul, neg_neg, ← mul_assoc, mul_inv_cancel₀ hs, one_mul]
    rfl
  rw [h.2 _ h1, hY, ← mul_assoc, ← Complex.exp_add]
  have hH : Formalism.L2.Ker.HV (area (lamOf D ⊤ δ))⁻¹ z z = Formalism.MainNotions.TaylorLogMetric.Hf D (tor0 D ⊤ δ) z z := by
    change (((area (lamOf D ⊤ δ))⁻¹ : ℝ) : ℂ) * _ = _ / ((area (lamOf D ⊤ δ) : ℝ) : ℂ)
    rw [div_eq_inv_mul, Complex.ofReal_inv]
  rw [hH, neg_mul, add_neg_cancel, Complex.exp_zero, one_mul]

theorem isFinPt_one (V : HSp D) {n : ℕ} (e : V.rank = n) :
    GlobalTheory.BotFormula.IsFinPt V 1 (1 : Formalism.MainNotions.StandardLatticesGL3.GA D n) := by
  subst e
  refine ⟨one_mem _, rfl, fun i j => ?_⟩
  rw [map_one]
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply, h]

theorem reads_of_fock {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {a d : ℕ}
    (hS : S.rank = a) (hT : T.rank = d) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {r : D.host.E} (hset : Setup ψ θ S T cc δ r)
    {χS χT : (Formalism.L2.Theta.AE D)ˣ →* Circle}
    {om : Formalism.L2.Theta.GA D S × Formalism.L2.Theta.GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : IsWeilDatumO ψ S T χS χT om)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hv : ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 1) f) :
    ∃ G ∈ TT D (tor0 D cc δ) a d, Reads ψ θ hS hT cc δ r G f := by
  obtain ⟨G, hG, hR⟩ := GlobalTheory.VacLine.exists_reads hS hT hset hf hv
  have hRt : ∀ z, Reads ψ θ hS hT cc δ r (Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) G)
      (wdPh D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) • heisO ψ S T (finPt hS hT r z) f) := fun z =>
    (GlobalTheory.NormExact.heisO_finPt_reads ψ θ S T hS hT cc δ r hset G f hR z).smul _
  obtain ⟨n, hn, hL⟩ := GlobalTheory.T.weilPair_moves_phasedHeisenbergTranslate ψ θ S T hS hT cc δ r hset χS χT om hom 1 1 1 1 (isFinPt_one S hS) (isFinPt_one T hT) f hf 0
  refine ⟨G, ⟨hG, n, hn, fun x hx => ?_⟩, hR⟩
  obtain ⟨z, rfl, hz⟩ := GlobalTheory.T.exists_rationalPoint_of_mem_movedThetaLattice D (GlobalTheory.InducedType.induced_type D).1 cc δ hset.crv.1.1 a d 1 1 _ _
    (GlobalTheory.NormSum.VacMove.moves_one D a) (GlobalTheory.NormSum.VacMove.moves_one D d) x hx
  simp only [OneMemClass.coe_one, inv_one, Units.val_one, Matrix.one_mul, Matrix.mul_one] at hz
  have hp : n • pt D (tor0 D cc δ) δ z = pt D (tor0 D cc δ) δ (n • z) := by
    funext τ i j
    simp [pt, embV, tor0]
    ring
  have h2 := hL (n • z) (fun i j => ⟨_, hz i j, by
    have h0 : (0 : Matrix (Fin d) (Fin a) D.host.E).map (inc D) = 0 := by ext; simp
    rw [h0, Matrix.mul_zero, Matrix.zero_mul, sub_zero]
    simp⟩)
  have e1 : om (1, 1) = 1 := map_one om
  rw [e1, Module.End.one_apply, Module.End.one_apply] at h2
  have h3 := hRt (n • z)
  have h4 := hRt 0
  rw [GlobalTheory.NormSum.VacMove.pt_zero, GlobalTheory.NormSum.wd_zero] at h4
  rw [GlobalTheory.NormSum.VacMove.pt_zero] at h2
  rw [← h2] at h3
  rw [hp]
  exact GlobalTheory.VacLine.reads_inj hset h3 h4

theorem conj_datum {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW} (hX : IsBottomTri W i j X) (s : T) :
    IsThetaFunO W.ψ A WW (fun w => starRingEnd ℂ (X.f s w)) ∧
      ∀ τ, IsFockVacAt (heisO W.ψ A WW) W.θ τ (cplxO 1 1) (fun w => starRingEnd ℂ (X.f s w)) := by
  have hI := hX.is
  have hψ := W.ψ_std
  have hθ := W.θ_is
  have hf : IsThetaFunO W.ψ (GlobalTheory.Grid.neg A) WW (X.f s) := (GlobalTheory.ConstRatio.theta_f hI s).1
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum (hI.idem s)
  have hv : ∀ τ, IsFockVacAt (heisO W.ψ (GlobalTheory.Grid.neg A) WW) W.θ τ (cplxO (-X.rA.s τ) (X.rW.s τ)) (X.f s) := fun τ =>
    GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hψ.1.1 hθ ho.infPart_eq ho.conj.infPart_eq (hI.fst s)
      hI.isVac.2.theta hf (hI.isVac.2.fock τ)
  refine ⟨GlobalTheory.CjNeg.theta_negS' hψ (show IsThetaFunO W.ψ (GlobalTheory.ChiGrid.negSp A) WW (X.f s) from hf), fun τ => ?_⟩
  have h := hv τ
  rw [(hX.std.2.2 τ).1, (hX.stdW.2.2 τ).1] at h
  exact GlobalTheory.BotFormula.ConjJet.isFockVacAt_conj hψ hθ A WW _ hf τ h

theorem bottom_finParts {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData L sc) {μ₀ : T} (hL : L.Is μ₀)
    {i j : Fin D.R.m} {s : T} {δ t0 : ℂ} {Q : ℕ} {P P' : Pair D ⊤ δ t0 Q} {𝔪 : Ideal (𝓞 D.host.E)}
    (hB : IsBottom G s i j 𝔪 P P') :
    HasFinPart (G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2))⁻¹ P.W.chV P.W.ep ∧
    HasFinPart ((G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2)) /
      (L.mu s (j + 1) * L.eta ^ (rankV D i j % 2)))⁻¹ P.W.chV' (-P.W.ep') := by
  refine ⟨fun x y hxy => ?_, fun x y hxy => ?_⟩
  · have h1 := GlobalTheory.T.heckeCharacter_finiteIdele_value_eq _ _ (G.ch.chi_eq (D.R.m - i) (by omega) (by omega)) x y hxy
    have h2 := GlobalTheory.T.heckeCharacter_finiteIdele_value_eq _ _ hL.eta x y hxy
    have e : (betaH G i j)⁻¹.1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D y) =
        ((G.ch.chiH (D.R.m - i)).1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D y) *
          L.C.eta.1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D y) ^ (rankV D i j % 2))⁻¹ := rfl
    rw [hB.chars.1 y, e, MonoidHom.inv_apply, Circle.coe_inv, MonoidHom.mul_apply, MonoidHom.pow_apply, Circle.coe_mul,
      Circle.coe_pow, h1, h2]
    simp
  · have eν : ((G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2)) /
        (L.mu s (j + 1) * L.eta ^ (rankV D i j % 2)))⁻¹ = G.nu s i (j + 1) := by
      rw [inv_div]; exact mul_div_mul_right_eq_div _ _ _
    have e : (nuH G s i j)⁻¹.1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D y) =
        ((nuH G s i j).1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D y))⁻¹ := rfl
    rw [eν, zpow_neg, hB.chars.2 y, e, inv_inv]
    exact GlobalTheory.T.heckeCharacter_finiteIdele_value_eq _ _ (chrEq_nu G s i j hL) x y hxy

end GlobalTheory.BotIntertw

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystalFiniteFreeReducesToDeRham
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystalFiniteFreeReducesToDeRham
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CrysFree

theorem isLocalRing_of_sq {Λ k : Type} [CommRing Λ] [Field k] (π : Λ →+* k) (hπ : Function.Surjective π)
    (hI : RingHom.ker π ^ 2 = 0) : IsLocalRing Λ := by
  have hmax : (RingHom.ker π).IsMaximal := RingHom.ker_isMaximal_of_surjective π hπ
  haveI := hmax.isPrime
  have hle : RingHom.ker π ≤ nilradical Λ := fun x hx ↦ ⟨2, by
    have : x * x ∈ RingHom.ker π ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul hx hx
    rw [hI] at this; simpa [pow_two] using this⟩
  have heq : nilradical Λ = RingHom.ker π := le_antisymm (nilradical_le_prime _) hle
  haveI : (nilradical Λ).IsMaximal := heq ▸ hmax
  exact IsLocalRing.of_isMaximal_nilradical Λ

theorem isDPMorphism_red {Λ k : Type} [CommRing Λ] [Field k] (π : Λ →+* k)
    (hI : RingHom.ker π ^ 2 = 0) : DividedPowers.IsDPMorphism (divided₂ hI) (dp0 k) π := by
  refine (DividedPowers.isDPMorphism_iff _ _ _).2 ⟨?_, fun n hn a ha ↦ ?_⟩
  · rw [Ideal.map_le_iff_le_comap]; intro x hx
    simpa using (RingHom.mem_ker.1 hx)
  · rw [RingHom.mem_ker.1 ha]
    rcases n with _ | _ | n
    · exact absurd rfl hn
    · rw [zero_add, (divided₂ hI).dpow_one ha, RingHom.mem_ker.1 ha, (dp0 k).dpow_one (Ideal.zero_mem _)]
    · rw [squareZeroDividedPowers_dpow hI (by omega), map_zero, DividedPowers.dpow_eval_zero _ hn]

theorem mem_smul_top_of_forall {Λ : Type} [CommRing Λ] {P : Type*} [AddCommGroup P] [Module Λ P]
    [Module.Finite Λ P] [Module.Free Λ P] (J : Ideal Λ) (h : Module.Dual Λ P) (hh : ∀ c, h c ∈ J) :
    h ∈ J • (⊤ : Submodule Λ (Module.Dual Λ P)) := by
  classical
  let b := Module.Free.chooseBasis Λ P
  rw [← b.sum_dual_apply_smul_coord h]
  exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem_smul (hh _) Submodule.mem_top

end GlobalTheory.CrysFree

namespace GlobalTheory.CrysFree

theorem crys_free_and_red : ∀ (F : Type) [Field F] [NumberField F] (Λ : Type) [CommRing Λ] (k : Type) [Field k] (π : Λ →+* k) (hπ : Function.Surjective π) (hI : RingHom.ker π ^ 2 = 0) (A₀ : Over (Sp k)) [GrpObj A₀] [IsCommMonObj A₀], IsAbelianScheme A₀ → ∀ a : OAct (𝓞 F) A₀, letI := tensorModule (divided₂ hI) (spMap π) a; letI := tensorModule (dp0 k) (𝟙 _) a; Module.Finite Λ (Crys (divided₂ hI) (spMap π) A₀) ∧ Module.Free Λ (Crys (divided₂ hI) (spMap π) A₀) ∧ ∃ f : Crys (divided₂ hI) (spMap π) A₀ →ₛₗ[(Algebra.TensorProduct.map π.toIntAlgHom (AlgHom.id ℤ (𝓞 F))).toRingHom] HdR A₀, Function.Surjective f ∧ ∀ m, f m = 0 → m ∈ (RingHom.ker π) • (⊤ : Submodule Λ (Crys (divided₂ hI) (spMap π) A₀)) := by
  intro F _ _ Λ _ k _ π hπ hI A₀ _ _ hA₀ a
  haveI := isLocalRing_of_sq π hπ hI
  letI : Algebra Λ k := π.toAlgebra
  obtain ⟨A, _, i, h, hA⟩ := GlobalTheory.T.abelianScheme_unobstructed_squareZero_affine Λ (RingHom.ker π) hI k π hπ rfl A₀ hA₀
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim Λ A hA
  obtain ⟨HFree, -, HBC, HRigid, -⟩ := GlobalTheory.T.abelianScheme_firstDeRham_structure
  have hrig := HRigid Λ A g hA hg (RingHom.ker π) (divided₂ hI) (isDPNilpotent_squareZero hI) k π hπ rfl A₀ i h
  let e : primDR A ≃ₗ[Λ] prim (divided₂ hI) (spMap π) A₀ :=
    LinearEquiv.ofBijective (liftMor (divided₂ hI) h).pull hrig
  obtain ⟨hfin, hproj, -⟩ := HFree.prim hA hg
  haveI : Module.Finite Λ (prim (divided₂ hI) (spMap π) A₀) := Module.Finite.equiv e
  haveI : Module.Projective Λ (prim (divided₂ hI) (spMap π) A₀) := Module.Projective.of_equiv e
  haveI := Module.finitePresentation_of_projective Λ (prim (divided₂ hI) (spMap π) A₀)
  haveI : Module.Free Λ (prim (divided₂ hI) (spMap π) A₀) := Module.free_of_flat_of_isLocalRing
  have m : GrpMor (divided₂ hI) (spMap π) A₀ (dp0 k) (𝟙 _) A₀ (algebraMap Λ k) (𝟙 _) (Over.Hom.left (𝟙 A₀)) :=
    ⟨isDPMorphism_red π hI, by simp, by simp, by
      intro T x y x₀ y₀ hx hy
      have ex : x₀.left = x.left := by simpa using hx
      have ey : y₀.left = y.left := by simpa using hy
      have eqx : x₀ = x := Over.OverMorphism.ext ex
      have eqy : y₀ = y := Over.OverMorphism.ext ey
      subst x₀
      subst y₀
      simp only [Over.id_left, Category.comp_id]
      rfl⟩
  have hm : m.IsBC := by
    have hb := (HBC Λ A g hA hg k A₀ i h).1
    let E := LinearEquiv.baseChange Λ k _ _ e
    have key : liftSemi m.pull ∘ₗ E.toLinearMap =
        liftSemi (GlobalTheory.Published.AbelianDeRham.bcMor (R' := k) h).pull := by
      refine LinearMap.ext fun z ↦ ?_
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul x c =>
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, E, LinearEquiv.baseChange_tmul,
          liftSemi_tmul]
        congr 1
        exact GrpMor.pull_pull (liftMor (divided₂ hI) h) m (GlobalTheory.Published.AbelianDeRham.bcMor (R' := k) h)
          (fun _ ↦ rfl) (by simp) c
      | add x y hx hy => rw [map_add (f := _), hx, hy, map_add (f := _)]
    have : liftSemi m.pull = liftSemi (GlobalTheory.Published.AbelianDeRham.bcMor (R' := k) h).pull ∘ₗ
        E.symm.toLinearMap := by
      rw [← key, LinearMap.comp_assoc, ← LinearEquiv.coe_trans, LinearEquiv.symm_trans_self]; rfl
    unfold GrpMor.IsBC
    rw [this]
    exact hb.comp E.symm.bijective
  refine ⟨inferInstance, inferInstance, ?_⟩
  have hact : ∀ (o : 𝓞 F) (x : Crys (divided₂ hI) (spMap π) A₀),
      hm.bcMap (act (divided₂ hI) (spMap π) a o x) = act (dp0 k) (𝟙 _) a o (hm.bcMap x) := by
    intro o x
    haveI := a.hom o
    rw [act_apply, act_apply]
    exact hm.corr_iff.1 (GrpMor.Corr.push (m := m) m (a.act o) (a.act o) (by simp) (hm.corr_iff.2 rfl))
  letI := tensorModule (divided₂ hI) (spMap π) a
  letI := tensorModule (dp0 k) (𝟙 _) a
  refine ⟨{ toFun := hm.bcMap, map_add' := hm.bcMap.map_add, map_smul' := ?_ }, ?_, ?_⟩
  · intro r x
    induction r using TensorProduct.induction_on with
    | zero => simp
    | tmul l o =>
      have e1 : (l ⊗ₜ[ℤ] o) • x = l • act (divided₂ hI) (spMap π) a o x := rfl
      have e2 : ∀ y : HdR A₀, ((Algebra.TensorProduct.map π.toIntAlgHom (AlgHom.id ℤ (𝓞 F))).toRingHom
          (l ⊗ₜ[ℤ] o)) • y = π l • act (dp0 k) (𝟙 _) a o y := fun y ↦ rfl
      rw [e1, e2, hm.bcMap.map_smulₛₗ, hact]
      rfl
    | add r s hr hs =>
      rw [add_smul, map_add (f := hm.bcMap), hr, hs, map_add (f := _), add_smul]
  · intro h'
    let l : prim (divided₂ hI) (spMap π) A₀ →ₗ[Λ] k :=
      { toFun c := h' (m.pull c)
        map_add' c d := by rw [map_add (f := _), map_add (f := _)]
        map_smul' r c := by
          rw [map_smulₛₗ, map_smul, smul_eq_mul, RingHom.id_apply, Algebra.smul_def] }
    obtain ⟨hh, hhl⟩ := Module.projective_lifting_property (Algebra.linearMap Λ k) l hπ
    exact ⟨hh, hm.corr_iff.1 fun c ↦ (LinearMap.congr_fun hhl c).symm⟩
  · intro x hx
    have hc : m.Corr x 0 := hm.corr_iff.2 hx
    exact mem_smul_top_of_forall _ x fun c ↦ RingHom.mem_ker.2 ((hc c).symm.trans (LinearMap.zero_apply _))

end GlobalTheory.CrysFree
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystalFiniteFreeReducesToDeRhamStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystal_finite_free_reduces_to_deRham : ∀ (F : Type) [Field F] [NumberField F] (Λ : Type) [CommRing Λ] (k : Type) [Field k] (π : Λ →+* k) (hπ : Function.Surjective π) (hI : RingHom.ker π ^ 2 = 0) (A₀ : Over (Sp k)) [GrpObj A₀] [IsCommMonObj A₀], IsAbelianScheme A₀ → ∀ a : OAct (𝓞 F) A₀, letI := tensorModule (divided₂ hI) (spMap π) a; letI := tensorModule (dp0 k) (𝟙 _) a; Module.Finite Λ (Crys (divided₂ hI) (spMap π) A₀) ∧ Module.Free Λ (Crys (divided₂ hI) (spMap π) A₀) ∧ ∃ f : Crys (divided₂ hI) (spMap π) A₀ →ₛₗ[(Algebra.TensorProduct.map π.toIntAlgHom (AlgHom.id ℤ (𝓞 F))).toRingHom] HdR A₀, Function.Surjective f ∧ ∀ m, f m = 0 → m ∈ (RingHom.ker π) • (⊤ : Submodule Λ (Crys (divided₂ hI) (spMap π) A₀)) := by
  first | exact @GlobalTheory.CrysFree.crys_free_and_red | exact GlobalTheory.CrysFree.crys_free_and_red | (intros; apply GlobalTheory.CrysFree.crys_free_and_red <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearUniformisationBaseChangeCompleteDvr
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PsiUnitOnOfNeUniv
noncomputable section

namespace GlobalTheory.DvrDataCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

section Ext

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

end Ext

section Move

variable {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

theorem psiUnitOn_of_ne_univ (D : DegPre R) (χ : D.X) {U : Set (Sp R)} (hU : U ≠ Set.univ) : PsiUnitOn D χ U := by
  intro j V _ hVU _ h
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have : IsLocalization.Away ϖ (FractionRing R) := by
    refine (isLocalization_iff _ _).2 ⟨?_, fun z => ?_, fun {x y} e => ⟨1, by rw [IsFractionRing.injective R _ e]⟩⟩
    · rintro ⟨_, n, rfl⟩
      exact IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective R _)).2 (pow_ne_zero n hϖ.ne_zero))
    · obtain ⟨⟨a, b⟩, e⟩ := IsLocalization.surj (nonZeroDivisors R) z
      obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (nonZeroDivisors.ne_zero b.2) hϖ
      refine ⟨⟨a * (u⁻¹ : Rˣ), ⟨ϖ ^ n, n, rfl⟩⟩, ?_⟩
      have e₁ : ϖ ^ n = (b : R) * (u⁻¹ : Rˣ) := by rw [hu, _root_.mul_right_comm, Units.mul_inv, _root_.one_mul]
      show z * algebraMap R _ (ϖ ^ n) = algebraMap R _ (a * (u⁻¹ : Rˣ))
      rw [e₁, map_mul, map_mul, ← _root_.mul_assoc]
      exact congrArg (· * _) e
  have : IsOpenImmersion (jK R) := IsOpenImmersion.of_isLocalization ϖ
  have hV : V ≤ (jK R).opensRange := by
    intro x hx
    have hx' : x ≠ closedPoint R := fun e => hU (Set.eq_univ_of_univ_subset (by
      have : V = ⊤ := (closedPoint_mem_iff V).1 (e ▸ hx)
      rw [this] at hVU
      exact hVU))
    have hb : x.asIdeal = ⊥ := by
      by_contra hb
      have := x.isPrime
      exact hx' (PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal (x.isPrime.isMaximal hb)))
    refine ⟨(⊥ : PrimeSpectrum (FractionRing R)), PrimeSpectrum.ext ?_⟩
    rw [hb]
    exact Ideal.comap_bot_of_injective (algebraMap R (FractionRing R)) (IsFractionRing.injective R _)
  have := (jK R).isIso_app V hV
  have hb := ConcreteCategory.bijective_of_isIso ((jK R).app V)
  obtain ⟨r, hr⟩ := hb.2 (((TK R).left.presheaf.map (homOfLE h).op).hom ((D.psi χ).s j).val)
  refine ⟨r, ?_, hr⟩
  have hu : IsUnit (((jK R).app V).hom r) := by
    have : ((jK R).app V).hom r = _ := hr
    rw [this]
    exact (Units.isUnit _).map _
  exact (MulEquiv.isUnit_map (RingEquiv.ofBijective ((jK R).app V).hom hb)).1 hu

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

end Move

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}

end GlobalTheory.DvrDataCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearUniformisationBaseChangeCompleteDvr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc Formalism.L2.Pj
open GlobalTheory
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UnifDvrBaseChange

theorem exists_pelUnif : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsLocalRing V], CDvr V → ∀ (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t) (W : Type) [CommRing W] [IsDomain W]
    [IsLocalRing W], GlobalTheory.Mum.Base W → IsDiscreteValuationRing W → ∀ f : V →+* W, Function.Injective f → IsLocalHom f →
    ∀ tW : SAB H (Sp W), Nonempty (SABMap tW t (spMap f)) →
      ∃ (PW : PELUnif (maximalIdeal W) tW) (e : PW.D.toPre.X ≃ₗ[𝓞 E] P.D.toPre.X),
        ∀ y r, PsiCoord P.D.toPre (e y) r → ∃ u : Wˣ, PsiCoord PW.D.toPre y (u * f r) := by
  intro E _ _ _ H V _ _ _ hV t P W _ _ _ hW hWd f hfi hfl tW ⟨m⟩
  obtain ⟨hVd, hVc, hV0⟩ := hV
  obtain ⟨⟨hWN, -, hWI, hWc⟩, hW0⟩ := hW
  obtain ⟨L₁, L₂, -⟩ := GlobalTheory.firstFiveLaws

  have j : Function.Injective ((algebraMap W (FractionRing W)).comp f) := (IsFractionRing.injective W _).comp hfi
  let g : FractionRing V →+* FractionRing W := IsFractionRing.lift j
  have eg : jK W ≫ spMap f = spMap g ≫ jK V :=
    (GlobalTheory.Ex.UnifModel.spMap_comp fun _ => rfl).trans
      (GlobalTheory.Ex.UnifModel.spMap_comp (IsFractionRing.lift_algebraMap j)).symm
  have hpW : GlobalTheory.LN.PolAt tW (jK W) := GlobalTheory.DatUniq.polAt_pull m (GlobalTheory.DatUniq.polAt_of_unif P) (jK W) (spMap g) eg.symm
  obtain ⟨B, -, gen, hg, hw, -⟩ := GlobalTheory.LN.exists_polAV_of_polAt L₁ L₂ E H W tW hpW

  have := t.semi.separated
  have := t.semi.smooth
  let p₀ : Sp (FractionRing V) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing V))
  have hgen : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum V) ∈ abLocus t.G := by
    rw [← GlobalTheory.TraitChartForm.jK_apply_eq_bot V p₀]
    exact (GlobalTheory.ZJ.AbelianLocus.mem_abLocus_iff t.G (IsPullback.of_hasPullback t.G.hom (jK V)) p₀).2
      (GlobalTheory.DatUniq.polAt_of_unif P).1

  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  let Wv : Set (Sp V) := abLocus t.G ∩ {p | ϖ ∉ p.asIdeal}
  have hWo : IsOpen Wv :=
    (GlobalTheory.AbLocusOpen.isOpen_abLocus_local t.G t.semi).inter (PrimeSpectrum.isOpen_basicOpen (a := ϖ))
  have hne : Wv ≠ Set.univ := fun h => by
    have : closedPoint V ∈ Wv := h ▸ Set.mem_univ _
    exact this.2 hϖ.not_isUnit
  have hψ : ∀ y, PsiUnitOn P.D.toPre y Wv := fun y => GlobalTheory.DvrDataCompare.psiUnitOn_of_ne_univ P.D.toPre y hne
  have hker : (⟨RingHom.ker f, RingHom.ker_isPrime f⟩ : PrimeSpectrum V) ∈ Wv := by
    have hk : (⟨RingHom.ker f, RingHom.ker_isPrime f⟩ : PrimeSpectrum V) = ⟨⊥, Ideal.isPrime_bot⟩ :=
      PrimeSpectrum.ext ((RingHom.injective_iff_ker_eq_bot f).1 hfi)
    rw [hk]
    exact ⟨hgen, fun h => hϖ.ne_zero ((Submodule.mem_bot V).1 h)⟩
  have hloc : ∀ a ∈ maximalIdeal V, f a ∈ maximalIdeal W := fun a ha =>
    (mem_maximalIdeal _).2 fun h => (mem_maximalIdeal _).1 ha (isUnit_of_map_unit f a h)
  obtain ⟨PW, e, he⟩ := GlobalTheory.PelCoordPull.exists_pelUnif_psiCoord E H V W f t tW m P Wv inferInstance inferInstance
    hVc hWN hWI hWc hloc hWo Set.inter_subset_left hψ hker ⟨B, gen, hg, hw⟩
  refine ⟨PW, e.symm, fun y r hr => ?_⟩
  obtain ⟨u, hu⟩ := he _ r hr
  exact ⟨u, by simpa using hu⟩

end GlobalTheory.UnifDvrBaseChange
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearUniformisationBaseChangeCompleteDvrStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc Formalism.L2.Pj
open GlobalTheory
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linear_uniformisation_base_change_complete_dvr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V]
    [IsLocalRing V], CDvr V → ∀ (t : SAB H (Sp V)) (P : PELUnif (maximalIdeal V) t) (W : Type) [CommRing W] [IsDomain W]
    [IsLocalRing W], GlobalTheory.Mum.Base W → IsDiscreteValuationRing W → ∀ f : V →+* W, Function.Injective f → IsLocalHom f →
    ∀ tW : SAB H (Sp W), Nonempty (SABMap tW t (spMap f)) →
      ∃ (PW : PELUnif (maximalIdeal W) tW) (e : PW.D.toPre.X ≃ₗ[𝓞 E] P.D.toPre.X),
        ∀ y r, PsiCoord P.D.toPre (e y) r → ∃ u : Wˣ, PsiCoord PW.D.toPre y (u * f r) := by
  first | exact @GlobalTheory.UnifDvrBaseChange.exists_pelUnif | exact GlobalTheory.UnifDvrBaseChange.exists_pelUnif | (intros; apply GlobalTheory.UnifDvrBaseChange.exists_pelUnif <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinBundleKernelSecondCoordEquations
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinBundleKernelSecondCoordEquations
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

namespace GlobalTheory.ZarhinKerB

open GlobalTheory.ZarhinFam

open GlobalTheory.CechPic GlobalTheory.AbDual

section RadialKernelIntegrals

variable {S : Scheme.{0}}

def precompHom {Y Y' G : Over S} [GrpObj G] (f : Y' ⟶ Y) : (Y ⟶ G) →* (Y' ⟶ G) :=
  MonoidHom.mk' (fun a => f ≫ a) (fun a b => MonObj.comp_mul f a b)

def postcompHom {Y G H : Over S} [GrpObj G] [GrpObj H] (g : G ⟶ H) [IsMonHom g] : (Y ⟶ G) →* (Y ⟶ H) :=
  MonoidHom.mk' (fun a => a ≫ g) (fun a b => MonObj.mul_comp a b g)

def evcHom {A T Y : Over S} [GrpObj A] {M : LB (A ⊗ T).left} (hM : M.IsLB) (h : IsAdditive M) (t : Y ⟶ T) :
    (Y ⟶ A) →* Multiplicative (Pic Y.left) :=
  MonoidHom.mk' (fun a => Multiplicative.ofAdd (evc hM a t)) (fun a b => by
    rw [(isAdditive_iff hM).1 h Y a b t]; rfl)

theorem evc_prod_zpow_left {A T Y : Over S} [GrpObj A] [IsCommMonObj A] {M : LB (A ⊗ T).left} (hM : M.IsLB)
    (h : IsAdditive M) {K : Type} [Fintype K] (a : K → (Y ⟶ A)) (n : K → ℤ) (t : Y ⟶ T) :
    evc hM (∏ k, a k ^ n k) t = ∑ k, n k • evc hM (a k) t := by
  have e := map_prod (evcHom hM h t) (fun k => a k ^ n k) Finset.univ
  simp only [map_zpow] at e
  exact congrArg Multiplicative.toAdd e

theorem evc_pow_left {A T Y : Over S} [GrpObj A] {M : LB (A ⊗ T).left} (hM : M.IsLB)
    (h : IsAdditive M) (a : Y ⟶ A) (n : ℕ) (t : Y ⟶ T) : evc hM (a ^ n) t = n • evc hM a t :=
  congrArg Multiplicative.toAdd (map_pow (evcHom hM h t) a n)

theorem evc_mul_right {A B Y : Over S} [GrpObj B] {M : LB (A ⊗ B).left} (hM : M.IsLB)
    (hs : IsAdditive (swap M)) (a : Y ⟶ A) (b b' : Y ⟶ B) : evc hM a (b * b') = evc hM a b + evc hM a b' := by
  have hs' : (swap M).IsLB := pull_isLB hM _
  rw [← evc_swap hM hs', ← evc_swap hM hs', ← evc_swap hM hs']
  exact (isAdditive_iff hs').1 hs Y b b' a

theorem evc_prod_zpow_right {A B Y : Over S} [GrpObj B] [IsCommMonObj B] {M : LB (A ⊗ B).left} (hM : M.IsLB)
    (hs : IsAdditive (swap M)) {K : Type} [Fintype K] (a : Y ⟶ A) (b : K → (Y ⟶ B)) (n : K → ℤ) :
    evc hM a (∏ k, b k ^ n k) = ∑ k, n k • evc hM a (b k) := by
  have hs' : (swap M).IsLB := pull_isLB hM _
  rw [← evc_swap hM hs', evc_prod_zpow_left hs' hs]
  exact Finset.sum_congr rfl fun k _ => by rw [evc_swap hM hs']

theorem evc_pow_right {A B Y : Over S} [GrpObj B] {M : LB (A ⊗ B).left} (hM : M.IsLB)
    (hs : IsAdditive (swap M)) (a : Y ⟶ A) (b : Y ⟶ B) (n : ℕ) : evc hM a (b ^ n) = n • evc hM a b := by
  have hs' : (swap M).IsLB := pull_isLB hM _
  rw [← evc_swap hM hs', evc_pow_left hs' hs, evc_swap hM hs']

theorem comp_prod_zpow'' {Y Y' G : Over S} [GrpObj G] [IsCommMonObj G] {K : Type} [Fintype K] (f : Y' ⟶ Y)
    (a : K → (Y ⟶ G)) (n : K → ℤ) : f ≫ ∏ k, a k ^ n k = ∏ k, (f ≫ a k) ^ n k := by
  have e := map_prod (precompHom f) (fun k => a k ^ n k) Finset.univ
  simp only [map_zpow] at e
  exact e

theorem prod_zpow_comp'' {Y G H : Over S} [GrpObj G] [GrpObj H] [IsCommMonObj G] [IsCommMonObj H] {K : Type}
    [Fintype K] (a : K → (Y ⟶ G)) (n : K → ℤ) (g : G ⟶ H) [IsMonHom g] :
    (∏ k, a k ^ n k) ≫ g = ∏ k, (a k ≫ g) ^ n k := by
  have e := map_prod (postcompHom (Y := Y) g) (fun k => a k ^ n k) Finset.univ
  simp only [map_zpow] at e
  exact e

end RadialKernelIntegrals

end GlobalTheory.ZarhinKerB

namespace GlobalTheory.ZarhinKerB

open GlobalTheory.ZarhinFam

open GlobalTheory.CechPic GlobalTheory.AbDual

section KerAux2

variable {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]

theorem mkZ_pa' {T : Over S} (u : Fin 4 → (T ⟶ A)) (v : Fin 4 → (T ⟶ B)) (i : Fin 4) :
    mkZ A B u v ≫ pa A B i = u i := by
  rw [pa, ← Category.assoc, mkZ, lift_fst]
  exact (Out.powIsLimit A 4).fac _ ⟨i⟩

theorem mkZ_pb' {T : Over S} (u : Fin 4 → (T ⟶ A)) (v : Fin 4 → (T ⟶ B)) (j : Fin 4) :
    mkZ A B u v ≫ pb A B j = v j := by
  rw [pb, ← Category.assoc, mkZ, lift_snd]
  exact (Out.powIsLimit B 4).fac _ ⟨j⟩

theorem pull_zCls {P : LB (A ⊗ A).left} (hP : P.IsLB) {Q : LB (A ⊗ B).left} (hQ : Q.IsLB) (d : ℕ) (mu : B ⟶ A)
    {Y : Over S} (p q : Y ⟶ Zob A B) :
    CechPic.pull (lift p q).left (zCls A B hP hQ d mu) =
      (∑ i, evc hP (p ≫ pa A B i) (q ≫ pa A B i)) +
      (∑ i, ∑ j, quat d j i • evc hQ (p ≫ pa A B i) (q ≫ pb A B j)) +
      (∑ i, ∑ j, quat d j i • evc hQ (q ≫ pa A B i) (p ≫ pb A B j)) +
      ∑ j, evc hQ (q ≫ pb A B j ≫ mu) (p ≫ pb A B j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [zCls, map_add (f := _), map_sum, map_zsmul, evc, ← pull_comp, ← Over.comp_left, comp_lift, lift_fst_assoc,
    lift_snd_assoc]

end KerAux2

end GlobalTheory.ZarhinKerB

namespace GlobalTheory.ZarhinKerB

open GlobalTheory.ZarhinFam

open GlobalTheory.CechPic GlobalTheory.AbDual

theorem zarhinBundle_kernel : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu) (T : Over S) (x : T ⟶ GlobalTheory.ZarhinFam.Zob c.A B), (∃ t : ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (snd (GlobalTheory.ZarhinFam.Zob c.A B) T ≫ x) (fst (GlobalTheory.ZarhinFam.Zob c.A B) T)).left).Gen, t.IsGen) → ∀ j, ((∏ i, (x ≫ GlobalTheory.ZarhinFam.pa c.A B i) ^ GlobalTheory.ZarhinFam.quat d j i) ≫ la) * (x ≫ GlobalTheory.ZarhinFam.pb c.A B j) ^ d = 1 := by
  intro h M d S t c B _ _ Q la mu hZ T x hx j
  have hQ : IsDual c.A B Q := hZ.2.1
  have hQ' : IsDual B c.A (swap Q) := hZ.2.2.1
  haveI hla : IsMonHom la := hZ.2.2.2.1
  haveI hmu : IsMonHom mu := hZ.2.2.2.2.1
  have hlm : la ≫ mu = 𝟙 c.A ^ d := hZ.2.2.2.2.2.1
  have hPQ := hZ.2.2.2.2.2.2.2
  have hzP := zarhinBundle_isLineBundle c.A B c.isLB hQ.isLB d mu
  have h0 : ∀ (Y : Over S) (s : Y ⟶ T) (z : Y ⟶ Zob c.A B),
      CechPic.pull (lift (s ≫ x) z).left (zCls c.A B c.isLB hQ.isLB d mu) = 0 := by
    intro Y s z
    have e := congrArg (CechPic.pull (lift z s).left) ((cls_eq_zero_iff (pull_isLB hzP _)).2 hx)
    rw [cls_pull hzP, cls_zP, map_zero, ← pull_comp, ← Over.comp_left, comp_lift, lift_snd_assoc, lift_fst] at e
    exact e

  have e := h0 (c.A ⊗ T) (snd c.A T)
    (mkZ c.A B (fun _ => 1) (fun j' => if j' = j then fst c.A T ≫ la else 1))
  rw [pull_zCls] at e
  simp only [mkZ_pa', mkZ_pb'] at e
  simp only [← Category.assoc, mkZ_pa', mkZ_pb'] at e
  have t2 : ∀ i, ∑ j', quat d j' i • evc hQ.isLB ((snd c.A T ≫ x) ≫ pa c.A B i)
      (if j' = j then fst c.A T ≫ la else 1) = quat d j i • evc hQ.isLB ((snd c.A T ≫ x) ≫ pa c.A B i) (fst c.A T ≫ la) :=
    fun i => by
      rw [Fintype.sum_eq_single j (fun j' hj' => by rw [if_neg hj', evc_one_right hQ.isLB hQ.zero, smul_zero]),
        if_pos rfl]
  have t4 : ∑ j', evc hQ.isLB ((if j' = j then fst c.A T ≫ la else 1) ≫ mu) ((snd c.A T ≫ x) ≫ pb c.A B j') =
      evc hQ.isLB ((fst c.A T ≫ la) ≫ mu) ((snd c.A T ≫ x) ≫ pb c.A B j) := by
    rw [Fintype.sum_eq_single j (fun j' hj' => by rw [if_neg hj', MonObj.one_comp, hQ.additive.evc_one hQ.isLB]),
      if_pos rfl]
  simp only [t2, t4, evc_one_right c.isLB c.rig₂, hQ.additive.evc_one hQ.isLB, smul_zero, Finset.sum_const_zero,
    zero_add, add_zero] at e
  have hPev : ∀ {Y : Over S} (p q : Y ⟶ c.A), evc c.isLB p q = evc hQ.isLB p (q ≫ la) := by
    intro Y p q
    have e1 : cls c.P c.isLB = evc hQ.isLB (fst c.A c.A) (snd c.A c.A ≫ la) :=
      (cls_eq_iff c.isLB (pull_isLB hQ.isLB _)).2 hPQ
    rw [evc, e1, pull_evc, lift_fst, lift_snd_assoc]
  have hPsymm : ∀ {Y : Over S} (p q : Y ⟶ c.A), evc c.isLB p q = evc c.isLB q p := by
    intro Y p q
    have e1 : cls c.P c.isLB = evc c.isLB (snd c.A c.A) (fst c.A c.A) :=
      (cls_eq_iff c.isLB (pull_isLB c.isLB _)).2 c.symm
    rw [evc, e1, pull_evc, lift_fst, lift_snd]
  have hQsw : ∀ {Y : Over S} (p q : Y ⟶ c.A), evc hQ.isLB p (q ≫ la) = evc hQ.isLB q (p ≫ la) := by
    intro Y p q
    rw [← hPev, ← hPev, hPsymm]
  refine (hQ.isPerfect hQ').ker_right T _ ((triv_ev_iff hQ.isLB _ _).2 ?_)
  rw [MonObj.comp_mul, ← Category.assoc, comp_prod_zpow'', prod_zpow_comp'', MonObj.comp_pow,
    evc_mul_right hQ.isLB hQ'.additive, evc_prod_zpow_right hQ.isLB hQ'.additive, evc_pow_right hQ.isLB hQ'.additive]
  rw [Category.assoc, hlm, MonObj.comp_pow, Category.comp_id, evc_pow_left hQ.isLB hQ.additive] at e
  rw [← e]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hQsw, Category.assoc]

end GlobalTheory.ZarhinKerB
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinBundleKernelSecondCoordEquationsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zarhinBundle_kernel_secondCoord_equations : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t) (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A) (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu) (T : Over S) (x : T ⟶ GlobalTheory.ZarhinFam.Zob c.A B), (∃ t : ((GlobalTheory.ZarhinFam.zP c.A B c.isLB hZ.2.1.isLB d mu).pull (lift (snd (GlobalTheory.ZarhinFam.Zob c.A B) T ≫ x) (fst (GlobalTheory.ZarhinFam.Zob c.A B) T)).left).Gen, t.IsGen) → ∀ j, ((∏ i, (x ≫ GlobalTheory.ZarhinFam.pa c.A B i) ^ GlobalTheory.ZarhinFam.quat d j i) ≫ la) * (x ≫ GlobalTheory.ZarhinFam.pb c.A B j) ^ d = 1 := by
  first | (exact @GlobalTheory.ZarhinKerB.zarhinBundle_kernel) | (exact GlobalTheory.ZarhinKerB.zarhinBundle_kernel) | (intros; apply GlobalTheory.ZarhinKerB.zarhinBundle_kernel <;> assumption)
end
end
