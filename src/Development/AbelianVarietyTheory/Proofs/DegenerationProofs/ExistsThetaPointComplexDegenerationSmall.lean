module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThEqClassicalThetaFunctionValues
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.TorusProjPeriodZeroEqReal
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HasSumLocallyUniformlyOnTerm
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FormalThetaSumShiftPeriodDiv
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AnalyticDictionaryIsPointPeriodOrigin
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAbelianFibreIsoOfMatchedTorsionTheta
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionLabelSystemsSeriesScalarIndependentOfLeve
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CmFieldHostElementAddConjEqOne
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLogFrame
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusExtensionPointsDivisible
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FamiliesValuesCorrespond
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionPairingValuesOfFamiliesValues

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FibLieOfLaws
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch

noncomputable section
namespace GlobalTheory.Ex.Arch

open GlobalTheory.PointUnif GlobalTheory.EigenSplit in
theorem fibLie_of_laws : Laws → FibLieSt := by
  intro _ R _ _ _ D J g Λ Hm χ ex fr hfib O _ act F hF τ n hn
  obtain ⟨-, P', φ, w, u, -, hφ, -, -, h1, h2, -, hex, -⟩ := hfib
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.LiePull.exists_pushEquiv hφ (𝟙_ _) (TF (R := R) ℂ).hom (Category.id_comp _).symm
  have he := isExp_push hφ u h1 h2 Φ hΦ
  have hx : ∀ z, Φ (u.ex z) = ex z := fun z => Over.OverMorphism.ext ((hΦ _).trans (hex z).symm)
  have hker : ∀ z, Φ (u.ex z) = 1 ↔ z ∈ u.Λ := fun z => (map_eq_one_iff Φ Φ.injective).trans (u.ker z)
  have hF' : ∀ a z, Φ (u.ex (F a z)) = Φ (u.ex z) ≫ act.act a := fun a z => by
    rw [hx, hx]; exact hF a z
  obtain ⟨ρ, hρ⟩ := he.exists_rep act u.Λ u.discrete hker fun a => ⟨F a, hF' a⟩
  have hρF : ∀ a, ρ a = F a := fun a => by
    refine sub_eq_zero.1 (linear_eq_zero_of_discrete u.Λ u.discrete _ fun z => (hker _).1 ?_)
    have := he.1 ((ρ a - F a) z) (F a z)
    simp only [LinearMap.sub_apply, sub_add_cancel] at this
    rw [hρ, ← hF'] at this
    exact mul_eq_right.1 this.symm
  have hy : (TF (R := R) ℂ).hom = spMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R _)) :=
    (Spec.map_comp _ _).symm
  rw [← hy] at hn
  have hE : (⨅ a, (F a).eigenspace (τ a) : Submodule ℂ (Fin g → ℂ)) = eigenSub ρ τ := by
    ext z
    simp only [mem_eigenSub, Submodule.mem_iInf, Module.End.mem_eigenspace_iff, hρF]
  rw [hE]
  exact he.finrank_eigenSub act ρ hρ hn

end GlobalTheory.Ex.Arch
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSumAppellHumbert
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)
noncomputable section
namespace GlobalTheory.Ex.Arch

theorem exists_symm_bilin_ext {L V : Type} [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L] [AddCommGroup V]
    [Module ℝ V] [Module ℂ V] [IsScalarTower ℝ ℂ V] (P : L →+ V) (hP : Submodule.span ℝ (Set.range P) = ⊤)
    (hr : Module.finrank ℤ L = Module.finrank ℝ V) (b : L →+ (V →ₗ[ℂ] ℂ)) (hb : ∀ a c, b a (P c) = b c (P a)) :
    ∃ Bs : V →ₗ[ℂ] V →ₗ[ℂ] ℂ, (∀ u v, Bs u v = Bs v u) ∧ ∀ a v, Bs (P a) v = b a v := by
  classical
  let e := Module.Free.chooseBasis ℤ L
  have htop : ⊤ ≤ Submodule.span ℝ (Set.range fun i => P (e i)) := by
    rw [← hP, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← e.sum_repr a, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_zsmul]
    exact zsmul_mem (Submodule.subset_span (Set.mem_range_self (f := fun i => P (e i)) i)) _
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ L) = Module.finrank ℝ V := by
    rw [← hr, Module.finrank_eq_card_chooseBasisIndex]
  let β := basisOfTopLeSpanOfCardEqFinrank _ htop hcard
  have hβ : ∀ i, β i = P (e i) := fun i => by simp [β]
  let f : V →ₗ[ℝ] (V →ₗ[ℂ] ℂ) := β.constr ℝ fun i => b (e i)
  have hf : ∀ a, f (P a) = b a := fun a => by
    rw [← e.sum_repr a]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_zsmul, ← hβ, f, Module.Basis.constr_basis]
  have hs : ∀ u v, f u v = f v u := by
    let F : V →ₗ[ℝ] V →ₗ[ℝ] ℂ := LinearMap.mk₂ ℝ (fun u v => f u v) (fun _ _ _ => by simp) (fun _ _ _ => by simp)
      (fun _ _ _ => by simp) (fun _ _ _ => by simp)
    have : F = F.flip := β.ext fun i => β.ext fun j => by
      change f (β i) (β j) = f (β j) (β i)
      rw [hβ, hβ, hf, hf, hb]
    exact fun u v => LinearMap.congr_fun₂ this u v
  refine ⟨LinearMap.mk₂ ℂ (fun u v => f u v) (fun _ _ _ => by simp) (fun c u v => ?_) (fun _ _ _ => by simp)
    (fun _ _ _ => by simp), hs, fun a v => ?_⟩
  · rw [hs, map_smul, hs]
  · exact congrArg (fun g => g v) (hf a)

theorem hermForm_sub_swap {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian) (z w : Fin g → ℂ) :
    hermForm Hm z w - hermForm Hm w z = 2 * Complex.I * (hermForm Hm z w).im := by
  have h : ∀ i k, starRingEnd ℂ (Hm i k) = Hm k i := fun i k => hH.apply k i
  have hc : starRingEnd ℂ (hermForm Hm z w) = hermForm Hm w z := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hermForm, dotProduct, Matrix.mulVec, map_sum, map_mul, Finset.mul_sum, h, Pi.star_apply,
      RCLike.star_def, Complex.conj_conj]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
  rw [← hc, Complex.sub_conj]
  push_cast; ring

variable {O : Type} [CommRing O] [StarRing O] (B : AnArc O)

theorem lin_period (w : ℂ) (a c : B.La) : lin B a (B.Pw w c) =
    -(2 * Real.pi * Complex.I) * (B.T c.y a.y + c.n a.y + w * B.be c.y a.y) +
      Real.pi * (B.H (B.ct a.y) c.l + B.H (B.ct c.y) a.l + B.H c.l a.l) := by
  have := Complex.I_ne_zero
  rw [lin, AnArc.Pw_fst_apply, AnArc.Pw_snd, AnArc.H_add_left]
  field_simp
  ring

theorem lin_period_sub (w : ℂ) (a c : B.La) :
    lin B a (B.Pw w c) - lin B c (B.Pw w a) = -(2 * Real.pi * Complex.I) * B.EF a c := by
  have h := hermForm_sub_swap B.Hm_herm a.l c.l
  rw [← B.Ef_eq, ← B.H_def, ← B.H_def] at h
  rw [lin_period, lin_period, B.T_symm c.y, B.be_symm c.y, AnArc.EF_apply]
  push_cast at h ⊢
  linear_combination (-Real.pi : ℂ) * h

theorem perFactor_of_isPrim {w₀ : O} (hp : IsPrim B w₀) (w : ℂ) (a : B.La) (v : B.V) :
    B.perFactor w a v = (-1) ^ B.EF a (w₀ • a) * Complex.exp (lin B a v + lin B a (B.Pw w a) / 2) := by
  obtain ⟨h1, h2, h3⟩ := hp
  have hy : w₀ • a.y + star w₀ • a.y = a.y := by rw [← add_smul, h1, one_smul]
  have hT : B.T a.y a.y = 2 * B.T a.y (w₀ • a.y) := by
    have := congrArg (B.T a.y) hy
    rw [map_add (f := _), ← B.T_adj, B.T_symm (w₀ • a.y)] at this
    rw [← this]; ring
  have hE : B.EF a (w₀ • a) = B.Ef a.l (B.FLam w₀ a.l) + (a.n a.y + 2 * (-a.n (w₀ • a.y))) := by
    have := congrArg a.n hy
    rw [map_add (f := _)] at this
    rw [AnArc.EF_apply, AnArc.La.smul_n_apply, AnArc.La.smul_y, AnArc.La.smul_l]
    omega
  have hq : (B.be a.y a.y : ℂ) = 2 * B.q a.y := by rw [← B.two_mul_q]; push_cast; ring
  have hs : ((-1 : ℂ)) ^ (a.n a.y + 2 * (-a.n (w₀ • a.y))) = Complex.exp (Real.pi * Complex.I * a.n a.y) := by
    rw [zpow_add₀ (by norm_num), zpow_mul, mul_comm _ (a.n a.y : ℂ), Complex.exp_int_mul, Complex.exp_pi_mul_I]
    norm_num
  rw [hE, zpow_add₀ (by norm_num), hs, AnArc.perFactor, AnArc.ah, h2, h3, lin_period, hT, hq, lin, AnArc.H_add_left,
    ← AnArc.e_add, ← AnArc.e_add, eTwoPi, ← Complex.exp_neg, mul_assoc (_ ^ _), mul_assoc (_ ^ _), ← Complex.exp_add,
    ← Complex.exp_add]
  congr 2
  ring

theorem theta_sum_appellHumbert : ThetaSt := by
  intro O _ _ B w₀ hp th hth w hS g h Hm hH hsp hE
  let b : B.La →+ (B.V →ₗ[ℂ] ℂ) := AddMonoidHom.mk' (fun a =>
    { toFun := fun v => lin B a v - Real.pi * hermForm Hm (h v) (h (B.Pw w a))
      map_add' := fun v v' => by
        simp only [lin, hermForm, map_add (f := _), add_dotProduct, Prod.fst_add, Prod.snd_add, AddMonoidHom.add_apply,
          AnArc.H_add_left]
        ring
      map_smul' := fun c v => by
        simp only [lin, hermForm, map_smul, smul_dotProduct, Prod.smul_fst, Prod.smul_snd, AddMonoidHom.smul_apply,
          AnArc.H_smul_left, smul_eq_mul, RingHom.id_apply]
        ring }) fun a a' => LinearMap.ext fun v => by
      simp only [lin, hermForm, map_add (f := _), star_add, Matrix.mulVec_add, dotProduct_add, AnArc.La.add_y, AnArc.La.add_l,
        Submodule.coe_add, AnArc.H_add_right, LinearMap.add_apply, LinearMap.coe_mk, AddHom.coe_mk]
      ring
  have hb : ∀ a v, b a v = lin B a v - Real.pi * hermForm Hm (h v) (h (B.Pw w a)) := fun _ _ => rfl
  obtain ⟨Bs, hs, hB⟩ := exists_symm_bilin_ext (B.Pw w) hsp B.finrank_La b fun a c => by
    have h1 := hermForm_sub_swap hH (h (B.Pw w a)) (h (B.Pw w c))
    rw [hE] at h1
    push_cast at h1
    rw [hb, hb]
    linear_combination lin_period_sub B w a c + (Real.pi : ℂ) * h1
  refine ⟨fun z => Complex.exp (-(Bs (h.symm z) (h.symm z) / 2)) * B.Sum 1 0 th w (h.symm z), ?_, fun v => ?_,
    fun a z => ?_, fun a m hm => ?_⟩
  · have hd : Differentiable ℂ fun z => h.symm z := h.symm.toContinuousLinearEquiv.differentiable
    let Bc : B.V →L[ℂ] B.V →L[ℂ] ℂ :=
      LinearMap.toContinuousLinearMap ((LinearMap.toContinuousLinearMap : (B.V →ₗ[ℂ] ℂ) ≃ₗ[ℂ] _).toLinearMap ∘ₗ Bs)
    have hq : Differentiable ℂ fun v : B.V => Bs v v := Bc.differentiable.clm_apply differentiable_id
    have hq' : Differentiable ℂ fun z => Bs (h.symm z) (h.symm z) := hq.comp hd
    have hq'' : Differentiable ℂ fun z => -(Bs (h.symm z) (h.symm z) / 2) := by
      simp only [div_eq_mul_inv]
      exact (hq'.mul_const _).neg
    exact hq''.cexp.mul (hS.comp hd)
  · simp only [h.symm_apply_apply, mul_eq_zero, Complex.exp_ne_zero, false_or]
  · obtain ⟨v, rfl⟩ := h.surjective z
    simp only [← map_add (f := _), h.symm_apply_apply]
    rw [B.Sum_add_period hth, pow_one, perFactor_of_isPrim B hp]
    simp only [map_add (f := _), LinearMap.add_apply, hs v (B.Pw w a), hB, hb]
    have e : ∀ s x y x' y' S : ℂ, x + y = x' + y' →
        Complex.exp x * (s * Complex.exp y * S) = s * Complex.exp x' * (Complex.exp y' * S) := fun s x y x' y' S e => by
      have := congrArg Complex.exp e
      rw [Complex.exp_add, Complex.exp_add] at this
      linear_combination s * S * this
    exact e _ _ _ _ _ _ (by ring)
  · have hm' : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hm
    simp only [← map_smul, h.symm_apply_apply]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hB, hb]
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    field_simp
    ring

end GlobalTheory.Ex.Arch
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TxStOfPtSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators
noncomputable section
namespace GlobalTheory.Ex.Arch
variable {O : Type} [CommRing O] [StarRing O] {N : NumD ℂ} {B : AnArc O}

namespace Dict
variable (d : Dict N B)

theorem tx_ex_zero : d.ex 0 = 1 := (d.ab.2.2.1 0).2 B.abelian₂.zero_mem

theorem tx_ex_smul (n : ℕ) (x : Fin B.gB → ℂ) : d.ex ((n : ℂ) • x) = d.ex x ^ n := by
  induction n with
  | zero => simp [d.tx_ex_zero]
  | succ n ih => rw [Nat.cast_succ, add_smul, one_smul, d.ab.1, ih, pow_succ]

theorem tx_ex_neg (x : Fin B.gB → ℂ) : d.ex (-x) = (d.ex x)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← d.ab.1, neg_add_cancel, d.tx_ex_zero])

theorem tx_dbl (x : Fin B.gB → ℂ) : dbl N.θ N.σ (d.ex x) * d.fr (x + x) = d.fr x ^ 4 := by
  have a := d.ab.2.2.2.2.2.1 x (-x) x
  have b := d.ab.2.2.2.2.2.2.1 x
  rw [add_neg_cancel, neg_add_cancel, zero_add, d.ab.2.2.2.1, d.tx_ex_neg] at a
  replace a := congrArg Additive.ofMul a
  replace b := congrArg Additive.ofMul b
  apply Additive.ofMul.injective
  simp only [dbl, ofMul_mul, ofMul_div, ofMul_pow, ofMul_one] at a b ⊢
  linear_combination (norm := abel) a - b

theorem tx_cubN (x : Fin B.gB → ℂ) (i : ℕ) :
    cubN N.θ i 1 (d.ex x) (d.ex x) * d.fr ((i : ℂ) • x) * d.fr x * d.fr (x + x) ^ i =
      d.fr ((i : ℂ) • x + x) * d.fr x ^ (2 * i) := by
  induction i with
  | zero => simp [cubN, d.ab.2.2.2.1]
  | succ i ih =>
    have a := d.ab.2.2.2.2.2.1 ((i : ℂ) • x) x x
    rw [d.tx_ex_smul] at a
    rw [cubN] at ih
    rw [cubN, Finset.prod_range_succ, Nat.cast_succ, add_smul, one_smul, one_mul, Nat.mul_succ, pow_add (d.fr x), pow_succ (d.fr (x + x))]
    replace a := congrArg Additive.ofMul a
    replace ih := congrArg Additive.ofMul ih
    apply Additive.ofMul.injective
    simp only [ofMul_mul, sq] at a ih ⊢
    linear_combination (norm := abel) a + ih

theorem tx_cubN_div (x : Fin B.gB → ℂ) (i : ℕ) :
    cubN N.θ i 1 (d.ex x) (d.ex x) / dbl N.θ N.σ (d.ex x) ^ i * d.fr ((i : ℂ) • x) * d.fr x * d.fr x ^ (2 * i) =
      d.fr ((i : ℂ) • x + x) := by
  have a := congrArg Additive.ofMul (d.tx_cubN x i)
  have b := congrArg (fun t => Additive.ofMul (t ^ i)) (d.tx_dbl x)
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_div, ofMul_pow] at a b ⊢
  linear_combination (norm := module) a - b

theorem tx_mulq (x : Fin B.gB → ℂ) (n : ℕ) :
    mulq N.θ N.σ n (d.ex x) * d.fr x ^ (n ^ 2) = d.fr ((n : ℂ) • x) := by
  induction n with
  | zero => simp [mulq, d.ab.2.2.2.1]
  | succ n ih =>
    rw [mulq] at ih
    rw [mulq, Finset.prod_range_succ, Nat.cast_succ, add_smul, one_smul, ← d.tx_cubN_div, ← ih,
      show (n + 1) ^ 2 = n ^ 2 + 1 + 2 * n by ring, pow_add, pow_succ]
    simp only [mul_assoc, mul_left_comm]

theorem tx_isPt_pow (h : PtSt) {v : B.V} {g : N.Gt} (hg : d.IsPt v g) (n : ℕ) : d.IsPt ((n : ℂ) • v) (g ^ n) := by
  obtain ⟨-, -, h3, h4, -⟩ := h O N B d
  induction n with
  | zero =>
    rw [pow_zero, h4]
    exact ⟨0, rfl, by simp⟩
  | succ n ih =>
    rw [Nat.cast_succ, add_smul, one_smul, pow_succ]
    exact h3 _ _ _ _ ih hg

theorem tx_vt {v : B.V} {g : N.Gt} (hg : d.IsPt v g) (x : B.X) :
    N.vt g (d.eX x) = B.term 1 0 d.th x v * d.fr v.2 := by
  have a := hg.2 x
  have b := congrArg Units.val (d.ψ_eq x)
  rw [NumD.vt, hg.1, d.c_eq, ← d.ab.1, d.ab.2.2.2.2.2.2.2.2, AnArc.term, add_comm v.2, ← b]
  simp only [Units.val_mul, pow_one, map_zero, AnArc.e_zero, zero_add, one_smul]
  linear_combination (N.ψ (d.eX x) : ℂ) * d.th (B.ct x + v.2) * a
end Dict

theorem Dict.tx_wQ (d : Dict N B) {k t : ℕ} (hk : k = 2 * t + 1) {la : B.La} {p : N.QT k} (hp : d.Rep k la p) :
    (N.wQ p : ℂ) * d.fr ((k : ℂ)⁻¹ • B.P0 la).2 ^ k * B.ah la.l (B.ct la.y) =
      B.psi la.y * Complex.exp (lin B la (B.P0 la) / k) ^ t := by
  obtain ⟨hy, hb, hs⟩ := hp
  have k0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  replace hs := hs la.y
  have hx : (k : ℂ) • ((k : ℂ)⁻¹ • B.P0 la).2 = B.ct la.y + la.l := by
    rw [Prod.smul_snd, smul_inv_smul₀ k0, AnArc.degeneratingTori_basePeriodMap_snd]
  have hE : Complex.exp (lin B la (B.P0 la) / k) * eTwoPi (((k : ℂ)⁻¹ • B.P0 la).1 la.y) =
      Complex.exp (Real.pi * B.H ((k : ℂ)⁻¹ • B.P0 la).2 la.l) := by
    rw [eTwoPi, ← Complex.exp_add, lin, Prod.smul_snd, B.H_smul_left, Prod.smul_fst, AddMonoidHom.smul_apply,
      smul_eq_mul]
    congr 1
    ring
  generalize ((k : ℂ)⁻¹ • B.P0 la).2 = x at *
  generalize Complex.exp (lin B la (B.P0 la) / k) = E at *
  generalize eTwoPi (((k : ℂ)⁻¹ • B.P0 la).1 la.y) = e at *
  have f1 := d.ab.2.2.2.2.1 la.l (B.ct la.y)
  have f2 := d.ab.2.2.2.2.1 la.l (B.ct la.y + x)
  rw [B.ah_add, ← hE, add_right_comm] at f2
  have a := congrArg Units.val (d.tx_mulq x k)
  have b := congrArg Units.val (d.tx_cubN_div x k)
  have c := congrArg Units.val (d.ψ_eq la.y)
  rw [hx] at a b
  have ht : (k - 1) / 2 = t := by omega
  rw [NumD.wQ, NumB.wS, hy, hb, ht, mul_div_assoc (p.1.2.s _)]
  generalize cubN N.θ k 1 (d.ex x) (d.ex x) / dbl N.θ N.σ (d.ex x) ^ k = D at *
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_div_eq_div_val] at a b c ⊢
  have hD : (p.1.2.s (d.eX la.y) : ℂ) * D * (d.fr x ^ (2 * k) * E) = 1 := by
    refine mul_right_cancel₀ (b := (d.fr (B.ct la.y) : ℂ) * d.fr x * e) ?_ ?_
    · refine mul_ne_zero (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _)) ?_
      rintro rfl
      exact Complex.exp_ne_zero _ (hE.symm.trans (mul_zero _))
    · linear_combination hs - (p.1.2.s (d.eX la.y) : ℂ) * f2 +
        (p.1.2.s (d.eX la.y) : ℂ) * B.ah la.l (B.ct la.y) * E * e * b +
        (p.1.2.s (d.eX la.y) : ℂ) * D * (d.fr x ^ (2 * k) * E) * d.fr x * e * f1
  have hD' := (mul_eq_one_iff_inv_eq₀ (mul_ne_zero (Units.ne_zero _) (Units.ne_zero _))).1 hD
  rw [div_eq_mul_inv, ← inv_pow, hD', mul_pow, ← pow_mul, ← c, f1, ← a,
    show k ^ 2 = 2 * k * t + k by rw [sq]; nth_rw 2 [hk]; ring, pow_add]
  ring

theorem IsPrim.tx_sign {w₀ : O} (h : IsPrim B w₀) (la : B.La) :
    (B.psi la.y : ℂ) =
      (-1) ^ B.EF la (w₀ • la) * Complex.exp (-(lin B la (B.P0 la) / 2)) * B.ah la.l (B.ct la.y) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hy : la.y = w₀ • la.y + star w₀ • la.y := by rw [← add_smul, h1, one_smul]
  have hT : B.T la.y la.y = 2 * B.T la.y (w₀ • la.y) := by
    have : B.T la.y la.y = B.T la.y (w₀ • la.y + star w₀ • la.y) := by rw [← hy]
    rw [this, map_add (f := _), ← B.T_adj, B.T_symm (w₀ • la.y), two_mul]
  have hn : la.n la.y = la.n (w₀ • la.y) + la.n (star w₀ • la.y) := by rw [← map_add (f := _), ← hy]
  have hm : ∀ z : ℤ, (-1 : ℂ) ^ z = Complex.exp (z * (Real.pi * Complex.I)) := fun z => by
    rw [Complex.exp_int_mul, Complex.exp_pi_mul_I]
  rw [h3, AnArc.ah, h2, hm, hm, eTwoPi, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add,
    Complex.exp_eq_exp_iff_exists_int]
  refine ⟨-(la.n (star w₀ • la.y) + B.Ef la.l (B.FLam w₀ la.l)), ?_⟩
  simp only [lin, AnArc.EF_apply, AnArc.La.smul_y, AnArc.La.smul_n_apply, AnArc.La.smul_l, AnArc.degeneratingTori_basePeriodMap_fst_apply,
    AnArc.degeneratingTori_basePeriodMap_snd, AnArc.H_add_left, hT, hn]
  have := Complex.I_ne_zero
  push_cast
  field_simp
  ring

theorem txSt_of_ptSt (h : PtSt) : TxSt := by
  intro O _ _ N B d w₀ hw k β hβ m hm ho w u hu la p hp x
  obtain ⟨t, ht⟩ := ho.pow (n := 2)
  have m0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 ho.pos.ne'
  have hQ := d.tx_wQ ht hp
  have hv := d.tx_vt (d.tx_isPt_pow h hp.2 m) x
  have hq := congrArg Units.val (d.tx_mulq (((m ^ 2 : ℕ) : ℂ)⁻¹ • B.P0 la).2 m)
  have hmm : (m : ℂ) • ((m ^ 2 : ℕ) : ℂ)⁻¹ • B.P0 la = (m : ℂ)⁻¹ • B.P0 la := by
    rw [smul_smul]
    congr 1
    push_cast
    field_simp
  rw [← Prod.smul_snd (m : ℂ), hmm] at hq
  rw [hmm] at hv
  rw [hw.tx_sign, mul_right_comm _ (B.ah _ _), mul_left_inj' (B.ah_ne_zero _ _), mul_assoc, ← Complex.exp_nat_mul,
    ← Complex.exp_add] at hQ
  have hterm : B.term 1 0 d.th x ((m : ℂ)⁻¹ • B.Pw w la) =
      B.term 1 0 d.th x ((m : ℂ)⁻¹ • B.P0 la) * eTwoPi ((m : ℂ)⁻¹ * (w * B.be la.y x)) := by
    have e1 : ((m : ℂ)⁻¹ • B.Pw w la).1 (0 + 1 • x) =
        ((m : ℂ)⁻¹ • B.P0 la).1 (0 + 1 • x) + (m : ℂ)⁻¹ * (w * B.be la.y x) := by
      simp only [zero_add, one_smul, Prod.smul_fst, AddMonoidHom.smul_apply, smul_eq_mul, AnArc.Pw_fst_apply,
        AnArc.degeneratingTori_basePeriodMap_fst_apply]
      ring
    have e2 : ((m : ℂ)⁻¹ • B.Pw w la).2 = ((m : ℂ)⁻¹ • B.P0 la).2 := by
      rw [Prod.smul_snd, Prod.smul_snd, AnArc.Pw_snd, AnArc.degeneratingTori_basePeriodMap_snd]
    rw [AnArc.term, AnArc.term, e1, e2, AnArc.e_add]
    ring
  have hlin : lin B la (B.Pw w la) = lin B la (B.P0 la) - 2 * Real.pi * Complex.I * (w * B.be la.y la.y) := by
    simp only [lin, AnArc.Pw_fst_apply, AnArc.degeneratingTori_basePeriodMap_fst_apply, AnArc.Pw_snd, AnArc.degeneratingTori_basePeriodMap_snd]
    ring
  obtain ⟨c, hc⟩ : (2 * (m : ℤ) ^ 2) ∣ β.be (d.eX la.y + m • d.eX x) (d.eX la.y + m • d.eX x) :=
    (mul_dvd_mul_left 2 (by exact_mod_cast hm)).trans (β.dvd _ _)
  have hc' : 2 * (m : ℤ) ^ 2 * c = B.be la.y la.y + 2 * m * B.be la.y x + m ^ 2 * (2 * B.q x) := by
    rw [← hc, ← map_nsmul, ← map_add (f := _), ← hβ, B.two_mul_q]
    simp only [map_add (f := _), map_nsmul, LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul, B.be_symm x la.y]
    ring
  replace hc' : (c : ℂ) = (B.be la.y la.y + 2 * m * B.be la.y x + m ^ 2 * (2 * B.q x)) / (2 * m ^ 2) := by
    rw [eq_div_iff (mul_ne_zero two_ne_zero (pow_ne_zero _ m0)), mul_comm]
    exact_mod_cast hc'
  have ht' : (t : ℂ) = (m ^ 2 - 1) / 2 := by
    have : (m : ℂ) ^ 2 = 2 * t + 1 := by exact_mod_cast ht
    rw [this]; ring
  have key : eTwoPi (w * c) * Complex.exp (-(lin B la (B.P0 la) / 2) + t * (lin B la (B.P0 la) / (m ^ 2 : ℕ))) =
      Complex.exp (-(lin B la (B.Pw w la) / (2 * (m : ℂ) ^ 2))) * eTwoPi ((m : ℂ)⁻¹ * (w * B.be la.y x)) *
        eTwoPi (w * B.exponent 1 0 x) := by
    simp only [eTwoPi, ← Complex.exp_add, hlin, hc', ht', AnArc.exponent, map_zero]
    congr 1
    push_cast
    field_simp
    ring
  have m0' : (2 * (m : ℤ) ^ 2) ≠ 0 := mul_ne_zero two_ne_zero (pow_ne_zero _ (Int.natCast_ne_zero.2 ho.pos.ne'))
  rw [N.twist_txT β u m hm ho, hp.1, hc, Int.mul_ediv_cancel_left _ m0', Units.val_zpow_eq_zpow_val, hu,
    ← AnArc.e_mul_intCast, NumD.txT, hv, hterm, hp.2.1, ← hq, Units.val_div_eq_div_val, Units.val_mul,
    Units.val_pow_eq_pow_val]
  have hmq := (mulq N.θ N.σ m (d.ex (((m ^ 2 : ℕ) : ℂ)⁻¹ • B.P0 la).2)).ne_zero
  linear_combination (eTwoPi (w * c) * B.term 1 0 d.th x ((m : ℂ)⁻¹ • B.P0 la)) * hQ +
    (-1) ^ B.EF la (w₀ • la) * B.term 1 0 d.th x ((m : ℂ)⁻¹ • B.P0 la) * key +
    eTwoPi (w * c) * B.term 1 0 d.th x ((m : ℂ)⁻¹ • B.P0 la) * N.wQ p *
      (d.fr (((m ^ 2 : ℕ) : ℂ)⁻¹ • B.P0 la).2 : ℂ) ^ m ^ 2 * inv_mul_cancel₀ hmq

end GlobalTheory.Ex.Arch
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PeriodConstantPartEqZeroInjective
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch

namespace GlobalTheory.Ex.Arch

theorem period_constantPart_eq_zero_injective {O : Type} [CommRing O] [StarRing O] (B : AnArc O) (la : B.La) (hy : la.y = 0)
    (h : B.P0 la = 0) : la = 0 := by
  have hl : la.l = 0 := by
    have := congrArg Prod.snd h
    rw [AnArc.degeneratingTori_basePeriodMap_snd, hy, map_zero, zero_add] at this
    exact Subtype.ext this
  refine AnArc.La.ext hy (AddMonoidHom.ext fun x => ?_) hl
  have : (B.P0 la).1 x = 0 := by rw [h]; rfl
  rw [AnArc.degeneratingTori_basePeriodMap_fst_apply, hy, hl] at this
  simpa using this

theorem qkSt_of_ptSt : PtSt → QkSt := by
  intro hP O _ _ N B d k hk
  obtain ⟨h1, h2, h3, h4, h5⟩ := hP O N B d
  choose E hE hU using h1
  have hiff : ∀ v g, d.IsPt v g ↔ g = E v := fun v g => ⟨hU v g, fun h => h ▸ hE v⟩
  have hadd : ∀ v v', E (v + v') = E v * E v' := fun v v' => (hU _ _ (h3 _ _ _ _ (hE v) (hE v'))).symm
  have hzero : E 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have hpow : ∀ (n : ℕ) v, E (n • v) = E v ^ n := fun n v => by
    induction n with
    | zero => rw [zero_nsmul, pow_zero, hzero]
    | succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]
  have hper : ∀ la : B.La, E (B.P0 la) = N.io (d.eX la.y) := fun la => (hU _ _ (h5 la)).symm
  have hker : ∀ v v', E v = E v' → ∃ la : B.La, la.y = 0 ∧ v = v' + B.P0 la := fun v v' h => by
    have e : E (v - v') * E v' = E v' := by rw [← hadd, sub_add_cancel, h]
    obtain ⟨la, hy, hl⟩ := (h4 (v - v')).1 ((hiff _ _).2 (mul_eq_right.1 e).symm)
    exact ⟨la, hy, by rw [← hl, add_sub_cancel]⟩
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have hc1 : ∀ v : B.V, (k : ℂ)⁻¹ • (k • v) = v := fun v => by
    rw [← Nat.cast_smul_eq_nsmul ℂ, inv_smul_smul₀ hk0]
  have hc2 : ∀ v : B.V, k • ((k : ℂ)⁻¹ • v) = v := fun v => by
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_inv_smul₀ hk0]
  have hrep : ∀ (la : B.La) (p : N.QT k), d.Rep k la p ↔
      p.1.1.toAdd = d.eX la.y ∧ p.1.2 = E ((k : ℂ)⁻¹ • B.P0 la) := fun la p => and_congr Iff.rfl (hiff _ _)
  refine ⟨fun p => ?_, fun la => ?_, fun la la' p p' h h' => ?_, fun la la' p p' h h' => ?_⟩
  · obtain ⟨v, hv⟩ := h2 p.1.2
    have hv' := (hiff _ _).1 hv
    have e : E (k • v) = E (B.P0 (AnArc.La.mk (d.eX.symm p.1.1.toAdd) 0 0)) := by
      rw [hpow, hper, ← hv', AnArc.La.mk_y, AddEquiv.apply_symm_apply]
      exact N.mem_QT.1 p.2
    obtain ⟨la, hy, hl⟩ := hker _ _ e
    refine ⟨AnArc.La.mk (d.eX.symm p.1.1.toAdd) 0 0 + la, (hrep _ _).2 ⟨?_, ?_⟩⟩
    · rw [AnArc.La.add_y, hy, add_zero, AnArc.La.mk_y, AddEquiv.apply_symm_apply]
    · rw [map_add (f := _), ← hl, hc1, hv']
  · refine ⟨⟨(Multiplicative.ofAdd (d.eX la.y), E ((k : ℂ)⁻¹ • B.P0 la)), ?_⟩, (hrep _ _).2 ⟨rfl, rfl⟩, fun p hp => ?_⟩
    · rw [NumD.mem_QT, ← hpow, hc2, hper]
      rfl
    · obtain ⟨a, b⟩ := (hrep _ _).1 hp
      exact Subtype.ext (Prod.ext a b)
  · obtain ⟨a, b⟩ := (hrep _ _).1 h
    obtain ⟨a', b'⟩ := (hrep _ _).1 h'
    refine (hrep _ _).2 ⟨?_, ?_⟩
    · rw [AnArc.La.add_y, map_add (f := _), ← a, ← a']
      rfl
    · rw [map_add (f := _), smul_add, hadd, ← b, ← b']
      rfl
  · obtain ⟨a, b⟩ := (hrep _ _).1 h
    obtain ⟨a', b'⟩ := (hrep _ _).1 h'
    constructor
    · rintro ⟨z, c, c'⟩
      set z₀ : B.La := AnArc.La.mk (d.eX.symm z) 0 0 with hz₀
      have hz : d.eX z₀.y = z := by rw [hz₀, AnArc.La.mk_y, AddEquiv.apply_symm_apply]
      have e : E ((k : ℂ)⁻¹ • B.P0 la') = E ((k : ℂ)⁻¹ • B.P0 la + B.P0 z₀) := by
        rw [hadd, hper, hz, ← b, ← b', c']
      obtain ⟨e₀, hy, hl⟩ := hker _ _ e
      refine ⟨z₀ + e₀, sub_eq_zero.1 (period_constantPart_eq_zero_injective B _ ?_ ?_)⟩
      · apply d.eX.injective
        rw [AnArc.La.sub_y, AnArc.La.add_y, AnArc.La.nsmul_y, AnArc.La.add_y, hy, add_zero, map_sub, map_add (f := _),
          map_nsmul, hz, ← a, ← a', c, sub_self, map_zero]
      · rw [map_sub, map_add (f := _), map_nsmul, map_add (f := _), ← hc2 (B.P0 la'), hl, add_assoc, smul_add, hc2, sub_self]
    · rintro ⟨e, rfl⟩
      refine ⟨d.eX e.y, ?_, ?_⟩
      · rw [a, a', AnArc.La.add_y, AnArc.La.nsmul_y, map_add (f := _), map_nsmul]
      · rw [b, b', map_add (f := _), map_nsmul, smul_add, hc1, hadd, hper]

end GlobalTheory.Ex.Arch
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSymPmaps
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch

noncomputable section
namespace GlobalTheory.Ex.Arch.FibSym
open GlobalTheory.FrameValue GlobalTheory.TorusExt GlobalTheory.DegPull

theorem vF_down {A : Over (Sp ℂ)} [GrpObj A] {L' : LB A.left} {g : ℕ} {u : HolUnif A L' g} (hL' : L'.IsLB)
    {X Y Y' : Scheme.{0}} {L : LB X} {Φ : A.left ⟶ X} {K : Type} [Fintype K] {w : LB.Iso L' (L.pull Φ)}
    {φ' : K → (Y' ⟶ A.left)} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {h : Y' ⟶ Y} (hψ : ∀ k, φ' k ≫ Φ = h ≫ φ k)
    {a : LB.Gen (LB.LinComb L' φ' ε)} {t : LB.Gen (LB.LinComb L φ ε)} (ha : a.IsGen) (H : PMaps w φ' φ ε a t h)
    {J : (Sp ℂ ⟶ X) → L.ι} (hJ : ∀ ψ : Sp ℂ ⟶ X, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ)) {fr : (Fin g → ℂ) → ℂˣ}
    (hfr : ∀ z i, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L'.U i →
      (fr z : ℂ) = valAt' (u.ex z).left _ (w.s (fun _ => J ((u.ex z).left ≫ Φ), i)).val * u.fr i z)
    {y : Sp ℂ ⟶ Y'} {z : K → Fin g → ℂ} (hz : IsLift u φ' y z) :
    vF t (y ≫ h) J = genVal u hL' a y z * ∏ k, (fr (z k) : ℂ) ^ ε k := by
  let p : Sp ℂ := IsLocalRing.closedPoint ℂ
  have gJ : ∀ q : Sp ℂ, Good L q J := fun q ψ => hJ ψ trivial
  have gJ' : ∀ q : Sp ℂ, Good L' q (chartAt hL') := fun q ψ => le_chartAt hL' ψ trivial
  have key : ∀ {Z : Scheme.{0}} (x : Sp ℂ ⟶ Z) (U : Z.Opens) (f : Γ(Z, U)ˣ), ⊤ ≤ x ⁻¹ᵁ U →
      (gm x p U f).val = stalkConst p (valAt' x U f.val) := fun x U f hU =>
    (gs_unit x p U (hU trivial) f).symm.trans (gs_eq_stalkConst x p hU _)
  have e := congrArg Units.val (pmaps_val hψ H y p (gJ p) (gJ' p))
  have e₁ : (val t (y ≫ h) p J).val = stalkConst p (vF t (y ≫ h) J) :=
    key _ _ _ (fun q _ => (gJ q).mem φ (y ≫ h))
  have e₂ : (val a y p (chartAt hL')).val = stalkConst p (genVal u hL' a y z *
      frameProd u ε z fun k => chartAt hL' (y ≫ φ' k)) :=
    (key _ _ _ (le_wchart_chartAt hL' φ' y)).trans (congrArg _ (valAt'_gen hL' ha hz (le_wchart_chartAt hL' φ' y)))
  have hm : ∀ x : Sp ℂ ⟶ A.left, ⊤ ≤ x ⁻¹ᵁ ((L.pull Φ).U (fun _ => J (x ≫ Φ)) ⊓ L'.U (chartAt hL' x)) :=
    fun x q _ => ⟨mem_pull.2 (gJ q (x ≫ Φ)), gJ' q x⟩
  have e₃ : ∀ x : Sp ℂ ⟶ A.left, Geo.Tor.gw w x p (J (x ≫ Φ)) (chartAt hL' x) = stalkUnits p
      (Units.mk0 (valAt' x _ (w.s (fun _ => J (x ≫ Φ), chartAt hL' x)).val)
        (CubeValues.val_unit_ne_zero x SymmetricSemicharacter.valueRules (hm x) _)) := fun x =>
    Units.ext (key x _ _ (hm x))
  rw [Units.val_mul, e₁, e₂] at e
  simp only [e₃, ← map_zpow, ← map_prod] at e
  rw [stalkUnits_val, ← map_mul] at e
  rw [(stalkConst p).injective e, mul_left_comm, frameProd, Units.coe_prod, ← Finset.prod_mul_distrib]
  refine congrArg _ (Finset.prod_congr rfl fun k _ => ?_)
  rw [Units.val_zpow_eq_zpow_val, ← mul_zpow, hz k, hfr (z k) _ (le_chartAt hL' _)]
  rfl

theorem exists_sym_pmaps {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] [IsCommMonObj G]
    [IsCommMonObj G'] {f : S' ⟶ S} {F : G'.left ⟶ G.left} (gp : IsGrpPullback G' G f F) {L : LB G.left}
    {L' : LB G'.left} (hL : L.IsLB) (hL' : L'.IsLB) {w : LB.Iso L' (L.pull F)} (hw : PGen w)
    (s : LB.Gen (LB.LinComb L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])) (hs : s.IsGen)
    (hr : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ s (eSec G)) (LB.oneGen L)) :
    ∃ s' : LB.Gen (LB.LinComb L' (K := Fin 2) ![(ι[G']).left, 𝟙 G'.left] ![1, -1]), s'.IsGen ∧
      LB.Gen.Corr L' _ _ _ _ (LB.pullGen L' _ _ s' (eSec G')) (LB.oneGen L') ∧
      (∀ k : Fin 2, ![(ι[G']).left, 𝟙 G'.left] k ≫ F = F ≫ ![(ι[G]).left, 𝟙 G.left] k) ∧ PMaps w _ _ _ s' s F := by
  have hι : (ι[G']).left ≫ F = F ≫ (ι[G]).left := by
    have e := congrArg (fun q => q.left) (map_inv (pushHom gp G') (𝟙 G'))
    simp only [Hom.inv_def, Category.id_comp] at e
    refine Eq.trans e ?_
    show (𝟙 _ ≫ F) ≫ _ = _
    rw [Category.id_comp]
  have hψ : ∀ k : Fin 2, ![(ι[G']).left, 𝟙 G'.left] k ≫ F = F ≫ ![(ι[G]).left, 𝟙 G.left] k := fun k => by
    fin_cases k
    · exact hι
    · exact (Category.id_comp _).trans (Category.comp_id _).symm
  obtain ⟨s', hs', H⟩ := exists_pmaps hw hL hL' F hψ s hs
  refine ⟨s', hs', corr_of_val hL' fun y J' hJ' => ?_, hψ, H⟩
  obtain ⟨J, hJ⟩ := exists_good' hL y
  have e := pmaps_val hψ H (eSec G') y hJ hJ'
  have e₀ : eSec G' ≫ (ι[G']).left = eSec G' := by
    rw [eSec, ← Over.comp_left]; simp
  have he : eSec G' ≫ F = f ≫ eSec G := (cubeMapOf gp).e_comm
  rw [Fin.prod_univ_two] at e
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, e₀, Category.comp_id, zpow_one, zpow_neg,
    mul_inv_cancel, _root_.one_mul] at e
  refine (val_pull hJ' _ _ _).trans (Eq.trans ?_ (val_one _).symm)
  rw [Category.id_comp, ← e, he]
  exact (val_pull hJ s (eSec G) f).symm.trans ((val_corr hJ hr f).trans (val_one _))

theorem fibSymSt : Laws → FibSymSt := by
  intro _ R _ _ _ D J g Λ Hm χ ex fr hF
  obtain ⟨hJ, P', φ, w, u, rfl, gp, hw, hAH, -, -, -, hex, hfr⟩ := hF
  obtain ⟨s, hs, hr, hψ, H⟩ := exists_sym_pmaps gp D.P.isLB P'.isLB ((isGen_iff w).1 hw) D.sym D.sym_gen D.sym_rig
  obtain ⟨h₁, h₂⟩ := genVal_sym P'.isLB hAH s hs hr
  refine ⟨fun x => ?_, h₂⟩
  have e := vF_down P'.isLB hψ hs H hJ (fr := fr) (fun z i hi => hex z ▸ hfr z i hi) (isLift_sym u x)
  rw [h₁, Fin.prod_univ_two] at e
  rw [hex x]
  refine (congrArg (· * (fr x : ℂ)) e).trans ?_
  simp

end GlobalTheory.Ex.Arch.FibSym
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsPtNsmul
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.Arch

namespace GlobalTheory.Ex.Arch

attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.Ex.Arch.towerSt_of : _root_.GlobalTheory.Ex.BrGtSt → _root_.GlobalTheory.Ex.BrWpSt → _root_.GlobalTheory.Ex.Arch.PtSt → _root_.GlobalTheory.Ex.Arch.QkSt → _root_.GlobalTheory.Ex.Arch.WpSt → _root_.GlobalTheory.Ex.Arch.TowerSt := by
  intro hGt hWp hPt hQk hWA
  unfold _root_.GlobalTheory.Ex.BrGtSt _root_.GlobalTheory.Ex.AllN at hGt
  unfold _root_.GlobalTheory.Ex.BrWpSt _root_.GlobalTheory.Ex.AllN at hWp
  unfold _root_.GlobalTheory.Ex.Arch.PtSt _root_.GlobalTheory.Ex.Arch.AllDict at hPt
  unfold _root_.GlobalTheory.Ex.Arch.QkSt _root_.GlobalTheory.Ex.Arch.AllDict at hQk
  unfold _root_.GlobalTheory.Ex.Arch.WpSt _root_.GlobalTheory.Ex.Arch.AllDict at hWA
  beta_reduce at hGt hWp hPt hQk hWA
  unfold _root_.GlobalTheory.Ex.Arch.TowerSt _root_.GlobalTheory.Ex.AllD
  intro E _ _ _ H D R _ _ _ A B dd hl
  letI := H.starRing
  have hG := hGt R A.D₀ A.even A.bimult ℂ A.N A.ν
  have hW := hWp R A.D₀ A.even A.bimult ℂ A.N A.ν
  have hV := hPt (𝓞 E) A.N _ dd
  have hL := hQk (𝓞 E) A.N _ dd
  have hE := hWA (𝓞 E) A.N _ dd
  have hq := A.hq
  have hT := _root_.GlobalTheory.NestQVal.qval_add_tower E H D R A.D₀ A.oa A.even A.bimult ℂ A.I A.N A.ν A.q
    hG.1 hG.2.2.1 (fun k => ⟨(hG.2.2.2.2 k).1, (hG.2.2.2.2 k).2.2⟩) hq
  choose! f hf using fun n (hn : 0 < n) (a : D.La) => (hL n hn).1 (A.q n a)
  have hpow : ∀ (m : ℕ) v g, dd.IsPt v g → dd.IsPt (m • v) (g ^ m) := by
    obtain ⟨g₀, hg₀, hu⟩ := hV.1 0
    have h00 := hV.2.2.1 0 0 g₀ g₀ hg₀ hg₀
    rw [add_zero] at h00
    have hg₁ : g₀ = 1 := mul_eq_left.1 (hu _ h00)
    intro m v g hg
    induction m with
    | zero => simpa [hg₁] using hg₀
    | succ k ih => simpa [succ_nsmul, pow_succ] using hV.2.2.1 _ _ _ _ ih hg
  refine ⟨f, ?_, hf⟩
  unfold _root_.GlobalTheory.Ex.Arch.IsTower
  intro n hn
  obtain ⟨-, hRep, hmul, hmod⟩ := hL n hn
  have hQn := (hG.2.2.2.2 n).2.2
  have hadd : ∀ a b, ∃ e, f n (a + b) = f n a + f n b + n • e := fun a b =>
    (hmod _ _ _ _ (hmul _ _ _ _ (hf n hn a) (hf n hn b)) (hf n hn (a + b))).1 (hT.1 n hn a b)
  refine ⟨hadd, ?_, ?_, ?_, ?_, ?_⟩
  · intro c a
    obtain ⟨Q, hQy, hQg, hQe⟩ := A.I.lin n hn c a
    obtain ⟨p', hp', -⟩ := hRep (c • f n a)
    obtain ⟨hya, hga⟩ := hq n a
    obtain ⟨c'', hc'', -⟩ := hG.1 Q.g
    have hRa := hf n hn a
    have hv := hl.2 c _ _ _ _ _ hga hc'' hQg hRa.2
    rw [map_smul, ← _root_.GlobalTheory.AnArc.degeneratingTori_basePeriodMap_smul] at hv
    have hc : c'' = (p' : Multiplicative A.N.X × A.N.Gt).2 := (hV.1 _).unique hv hp'.2
    have hQp : A.ν.QPt Q p' := by
      refine ⟨?_, hc ▸ hc''⟩
      rw [hp'.1, _root_.GlobalTheory.AnArc.La.smul_y, hl.1, hQy, ← hya, hRa.1]
      unfold _root_.GlobalTheory.Ex.ArcF.act
      simp
    exact (hmod _ _ _ _ hp' (hf n hn (c • a))).1 ((hQn _ _ _ _ hQp (hq n (c • a))).1 hQe)
  · intro a
    obtain ⟨e₀, he₀⟩ : ∃ e, f n 0 = n • e := by
      obtain ⟨e, he⟩ := hadd 0 0
      rw [add_zero] at he
      refine ⟨-e, ?_⟩
      rw [smul_neg, eq_neg_iff_add_eq_zero]
      calc f n 0 + n • e = (f n 0 + f n 0 + n • e) - f n 0 := by abel
        _ = 0 := by rw [← he, sub_self]
    have key : (∃ e, f n 0 = f n a + n • e) ↔ ∃ b, a = n • b := by
      rw [← hmod _ _ _ _ (hf n hn a) (hf n hn 0), ← hQn _ _ _ _ (hq n a) (hq n 0), A.I.ker n hn a 0]
      simp
    rw [← key]
    constructor
    · rintro ⟨e, he⟩
      exact ⟨e₀ - e, by rw [he₀, he, smul_sub]; abel⟩
    · rintro ⟨e, he⟩
      exact ⟨e₀ - e, by rw [smul_sub, ← he₀, he]; abel⟩
  · intro x
    obtain ⟨p, hp, -⟩ := hRep x
    obtain ⟨P, hP⟩ := (hG.2.2.2.2 n).2.1 p
    obtain ⟨a, ha⟩ := A.I.onto n hn P
    obtain ⟨e, he⟩ := (hmod _ _ _ _ (hf n hn a) hp).1 ((hQn _ _ _ _ (hq n a) hP).1 ha)
    exact ⟨a, e, he⟩
  · intro m hm a
    have hnm : 0 < n * m := Nat.mul_pos hn hm
    obtain ⟨p, hp, -⟩ := hRep (f (n * m) a)
    have hR := hf (n * m) hnm a
    have h1 : (p : Multiplicative A.N.X × A.N.Gt).1 = (A.q (n * m) a : Multiplicative A.N.X × A.N.Gt).1 := by
      apply Multiplicative.toAdd.injective
      rw [hp.1, hR.1]
    have h2 : (p : Multiplicative A.N.X × A.N.Gt).2 = (A.q (n * m) a : Multiplicative A.N.X × A.N.Gt).2 ^ m := by
      apply (hV.1 _).unique hp.2
      convert hpow m _ _ hR.2 using 1
      rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
      congr 1
      have : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
      have : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
      push_cast
      field_simp
    obtain ⟨e, he⟩ := (hmod _ _ _ _ hp (hf n hn a)).1 (hT.2 n m hn hm a p h1 h2)
    exact ⟨-e, by rw [he, smul_neg]; abel⟩
  · intro a b
    rw [(hW n hn _ _ _ _ _ (hq n a) (hq n b)).1 (A.I.isom n hn a b)]
    exact hE n hn _ _ _ _ (hf n hn a) (hf n hn b)

end GlobalTheory.Ex.Arch
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsThetaPointComplexDegenerationSmall
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
noncomputable section
namespace GlobalTheory.Ex.Arch

theorem isThetaPt_classical (hL : Laws) (hL2 : Laws2) (hT : ThetaUnifAV) (P : PolAV (Sp ℂ))
    (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (θ : (Fin P.g → ℂ) → ℂ) (N : ℕ)
    {I : Type} (x : I → (baseOver (Sp ℂ) ⟶ P.A)) (l : I → u.Λ) (hN : Odd N) (hAH : u.IsAH Hm χ)
    (hθ : u.IsThetaFn Hm χ 1 θ) (h0 : θ ≠ 0) (hx : ∀ i, x i = u.ex (((N : ℂ) ^ 2)⁻¹ • (l i : Fin P.g → ℂ))) :
    IsThetaPt P N x fun i => fnOf (χ (l i) * Complex.exp (-(Real.pi / 2 / (N : ℂ) ^ 2) * hermForm Hm (l i) (l i)) *
      θ ((N : ℂ)⁻¹ • (l i : Fin P.g → ℂ))) := by
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN.pos.ne'
  refine ⟨hN, isUnit_natCast_sp hN0, fun q => ⟨⊤, trivial, ?_⟩⟩
  let T : Over (Sp ℂ) := overRes (T := baseOver (Sp ℂ)) ⊤
  haveI : IsIso T.hom := by
    show IsIso ((⊤ : (Sp ℂ).Opens).ι ≫ 𝟙 _)
    rw [Category.comp_id]
    exact inferInstanceAs (IsIso (Sp ℂ).topIso.hom)
  let p : 𝟙_ (Over (Sp ℂ)) ⟶ T := Over.homMk (inv T.hom) (by simp)
  have hp : p ≫ overResι (T := baseOver (Sp ℂ)) ⊤ = 𝟙 _ := by
    ext1
    show inv T.hom ≫ (⊤ : (Sp ℂ).Opens).ι = 𝟙 _
    rw [IsIso.inv_comp_eq]
    rfl
  have htor : ∀ i, x i ^ (N ^ 2) = 1 := fun i => by
    rw [hx]
    refine (ThetaClassical.ex_nsmul u _ _).symm.trans ((u.ker _).2 ?_)
    rw [← Nat.cast_smul_eq_nsmul ℂ, Nat.cast_pow, smul_inv_smul₀ (pow_ne_zero _ hN0)]
    exact (l i).2
  have key := ThetaClassical.isThetaPtOver hL hL2 hT P u Hm χ θ N T p (fun i => overResι ⊤ ≫ x i) l
    hN hAH hθ h0 (fun i => (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ x i) hp).trans
      ((Category.id_comp _).trans (hx i))))
    (fun i => ThetaClassical.exists_symLift hL P (N ^ 2) _ (by push_cast; rfl) hN.pow (x i) (htor i))
  convert key using 2 with i
  exact ThetaClassical.constFn_top _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_tateIso (D : Datum H) {La : Type} [AddCommGroup La] [Module (𝓞 E) La] (EF : LinearMap.BilinForm ℤ La)
    (Q : PolAV (Sp ℂ)) (act : 𝓞 E → (Q.A ⟶ Q.A)) (hact : ∀ c, IsMonHom (act c)) {g : ℕ} (u : HolUnif Q.A Q.L g)
    (P : La →+ (Fin g → ℂ)) (hinj : Function.Injective P) (hker : ∀ z, z ∈ u.Λ ↔ ∃ a, z = P a)
    (hlin : ∀ (c : 𝓞 E) (s : ℂ) a, u.ex (s • P (c • a)) = u.ex (s • P a) ≫ act c)
    (hW : ∀ (k : ℕ) a b (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (EF a b : ℂ) / k) →
      WeilIs Q.A Q.L k (u.ex ((k : ℂ)⁻¹ • P a)) (u.ex ((k : ℂ)⁻¹ • P b)) (unitOn c))
    (ζ : ℕ → ℂˣ) (hp : ∀ n, 0 < n → IsPrimitiveRoot (ζ n) n) (hc : ∀ n m, 0 < n → 0 < m → ζ (n * m) ^ m = ζ n)
    (f : ℕ → D.La → La) (hf : IsTower D EF ζ f) :
    ∃ I : TateIso D ℂ (baseOver (Sp ℂ) ⟶ Q.A) (fun a x => x ≫ act a) (fun n x x' c => WeilIs Q.A Q.L n x x' (unitOn c)),
      I.ζ = ζ ∧ ∀ (n : ℕ) a, I.ev n a = u.ex ((n : ℂ)⁻¹ • P (f n a)) := by
  let e : (Fin g → ℂ) → (baseOver (Sp ℂ) ⟶ Q.A) := u.ex
  have eadd : ∀ z w, e (z + w) = e z * e w := u.ex_add
  have eker : ∀ z, e z = 1 ↔ ∃ a, z = P a := fun z => (u.ker z).trans (hker z)
  have epow : ∀ z (n : ℕ), e z ^ n = e (n • z) := fun z n => (ThetaClassical.ex_nsmul u z n).symm
  have e0 : e 0 = 1 := (eker 0).2 ⟨0, (map_zero P).symm⟩
  have hn : ∀ n : ℕ, 0 < n → (n : ℂ) ≠ 0 := fun n h => Nat.cast_ne_zero.2 h.ne'
  have sm : ∀ n : ℕ, 0 < n → ∀ a, (n : ℂ)⁻¹ • P (n • a) = P a := fun n h a => by
    rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, inv_smul_smul₀ (hn n h)]
  have sm' : ∀ n : ℕ, 0 < n → ∀ z : Fin g → ℂ, n • (n : ℂ)⁻¹ • z = z := fun n h z => by
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_inv_smul₀ (hn n h)]
  have md : ∀ n : ℕ, 0 < n → ∀ a b, e ((n : ℂ)⁻¹ • P (a + n • b)) = e ((n : ℂ)⁻¹ • P a) := fun n h a b => by
    rw [map_add (f := _), smul_add, eadd, sm n h, (eker _).2 ⟨b, rfl⟩, _root_.mul_one]
  refine ⟨{ ζ := ζ, ζ_prim := hp, ζ_pow := hc, ev := fun n a => e ((n : ℂ)⁻¹ • P (f n a)), add := fun n a b => ?_,
            lin := fun n c a => ?_, ker := fun n h a => ?_, onto := fun n h x => ⟨fun hx => ?_, ?_⟩,
            tower := fun n m h h' a => ?_, isom := fun n h a b => ?_ }, rfl, fun _ _ => rfl⟩
  · rcases n.eq_zero_or_pos with rfl | h
    · simp only [Nat.cast_zero, inv_zero, zero_smul, e0, _root_.mul_one]
    · obtain ⟨c, hc⟩ := (hf n h).1 a b
      rw [hc, md n h, map_add (f := _), smul_add, eadd]
  · rcases n.eq_zero_or_pos with rfl | h
    · haveI := hact c
      simp only [Nat.cast_zero, inv_zero, zero_smul, e0, MonObj.one_comp]
    · obtain ⟨b, hb⟩ := (hf n h).2.1 c a
      rw [hb, md n h]
      exact hlin c _ _
  · rw [← (hf n h).2.2.1 a, eker]
    refine exists_congr fun b => ⟨fun hb => hinj ?_, fun hb => by rw [hb, sm n h]⟩
    rw [map_nsmul, ← hb, sm' n h]
  · obtain ⟨z, rfl⟩ : ∃ z, e z = x := u.ex_onto x
    rw [epow, eker] at hx
    obtain ⟨b, hb⟩ := hx
    obtain ⟨a, c, rfl⟩ := (hf n h).2.2.2.1 b
    refine ⟨a, ?_⟩
    rw [← md n h _ c, ← hb, ← Nat.cast_smul_eq_nsmul ℂ, inv_smul_smul₀ (hn n h)]
  · rintro ⟨a, rfl⟩
    rw [epow, sm' n h]
    exact (eker _).2 ⟨_, rfl⟩
  · obtain ⟨b, hb⟩ := (hf n h).2.2.2.2.1 m h' a
    rw [epow, hb, Nat.cast_mul, mul_inv, mul_comm, mul_smul, sm' m h', md n h]
  · exact hW n _ _ _ h ((hf n h).2.2.2.2.2 a b)

theorem exists_log (T : ℝ) (u : ℂˣ) (hu : ‖(u : ℂ)‖ < Real.exp (-(2 * Real.pi * T))) :
    ∃ w : ℂ, T < w.im ∧ (u : ℂ) = eTwoPi w := by
  have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have e : (u : ℂ) = eTwoPi (Complex.log u / (2 * Real.pi * Complex.I)) := by
    rw [eTwoPi, mul_div_cancel₀ _ h2, Complex.exp_log u.ne_zero]
  refine ⟨_, ?_, e⟩
  generalize Complex.log u / (2 * Real.pi * Complex.I) = w at e
  rw [e, eTwoPi, Complex.norm_exp, Real.exp_lt_exp] at hu
  simp at hu
  have := Real.pi_pos
  nlinarith

theorem of_steps (hL : Laws) (hL2 : Laws2) (hT : ThetaUnifAV) (hdict : DictSt) (htow : TowerSt) (hty : TypeSt)
    (hobj : ObjSt) (hth : ThetaSt) (htx : TxSt) : AllD fun {_} _ _ _ {H} D => ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ] (A : ArcF D R ℂ), A.ρ = H.rt0 → ∀ (k : ℕ) (β : A.N.Form k), A.Bal β → ∀ (m : ℕ) (hm : m ^ 2 ∣ k), Odd m → ∃ ε : ℝ, 0 < ε ∧ ∀ u : ℂˣ, ‖(u : ℂ)‖ < ε → (∀ x, Summable fun χ => ‖(A.N.twist β u).txT m (A.N.twQ β u hm (A.q _ x)) χ‖) ∧ ∃ o : Full D ℂ, o.ρ = H.rt0 ∧ o.I.ζ (m ^ 2) = A.I.ζ (m ^ 2) ∧ o.Theta m fun x => (A.N.twist β u).tx m (A.N.twQ β u hm (A.q _ x)) := by
  intro E _ _ _ H D R _ _ _ A hρ k β hβ m hm hodd
  letI := H.starRing
  obtain ⟨B, d, hact, hbe, hprim, hth0, hsig⟩ := hdict E H D R A k β hβ
  obtain ⟨f, hf, hrep⟩ := htow E H D R A B d hact
  obtain ⟨g, ty, h, htyp, hh⟩ := hty E H D B (hρ ▸ hsig)
  obtain ⟨-, hbij, hadj, T₁, hT₁⟩ := B.periods_polarised
  obtain ⟨T₂, hT₂⟩ := B.exists_convergence
  have hmem : d.th ∈ B.Theta 1 0 := d.ab.2.2.2.2.2.2.2.1
  obtain ⟨-, hsum, -, hdiff, -⟩ := hT₂ 1 0 d.th hmem
  refine ⟨Real.exp (-(2 * Real.pi * max T₁ T₂)), Real.exp_pos _, fun u hu => ?_⟩
  obtain ⟨w, hw, huw⟩ := exists_log _ u hu
  have hw₁ : T₁ < w.im := (le_max_left _ _).trans_lt hw
  have hw₂ : T₂ < w.im := (le_max_right _ _).trans_lt hw
  have hm2 : 0 < m ^ 2 := pow_pos hodd.pos 2
  have hterm := fun x => htx (𝓞 E) A.N B d H.w0 hprim k β hbe m hm hodd w u huw _ _ (hrep _ hm2 x)
  refine ⟨fun x => ?_, ?_⟩
  · refine (d.eX.toEquiv.summable_iff (f := fun χ : A.N.X => ‖(A.N.twist β u).txT m (A.N.twQ β u hm (A.q _ x)) χ‖)).1 ?_
    exact ((hsum w hw₂ ((m : ℂ)⁻¹ • B.Pw w (f (m ^ 2) x))).mul_left _).congr fun y =>
      (norm_mul _ _).symm.trans (congrArg norm (hterm x y).symm)
  obtain ⟨-, -, hlin, -, hspan, -, -, -, hper⟩ := hT₁ w hw₁
  let P : B.La →+ (Fin g → ℂ) := h.toLinearMap.toAddMonoidHom.comp (B.Pw w)
  obtain ⟨hinj, hdisc, hsp, Hm, hherm, hpos, him⟩ := hper g h P fun _ => rfl
  have hPlin : ∀ (a : 𝓞 E) x i, P (a • x) i = ty i (a : E) * P x i := fun a x i =>
    (congrArg (fun v => h v i) (hlin a x)).trans (hh a _ i)
  obtain ⟨Q, oa, U, Hm', χ, F, hΛ, hpr, hdet, hAH, hΛ', him', hχ, hex, hW⟩ :=
    hobj E H D B.La B.EF g ty P Hm htyp hbij hadj hPlin hinj hdisc hsp hherm hpos him
  let P' : B.La →+ (Fin Q.g → ℂ) := F.toLinearMap.toAddMonoidHom.comp P
  obtain ⟨I, hI, hev⟩ := exists_tateIso D B.EF Q oa.act oa.hom U P' (F.injective.comp hinj)
    (fun z => ⟨hΛ' z, fun ⟨a, ha⟩ => ha ▸ hΛ a⟩) (fun c s a => by
      have := hex c (s • P a)
      rw [map_smul] at this
      refine Eq.trans (congrArg U.ex ?_) this
      refine (map_smul F s _).symm.trans (congrArg F (funext fun i => ?_))
      simp only [Pi.smul_apply, hPlin, smul_eq_mul]
      ring) hW A.I.ζ A.I.ζ_prim A.I.ζ_pow f hf
  have hS : Differentiable ℂ (B.Sum 1 0 d.th w) := fun v =>
    ((hdiff.differentiableAt ((isOpen_lt continuous_const (Complex.continuous_im.comp continuous_fst)).mem_nhds
      (show T₂ < ((w, v) : ℂ × B.V).1.im from hw₂))).comp v
      ((differentiableAt_const w).prodMk differentiableAt_id) :)
  obtain ⟨Θ, hΘ, hΘ0, hΘp, hΘv⟩ := hth (𝓞 E) B H.w0 hprim d.th hmem w hS Q.g (h.trans F) Hm' hAH.1 hspan him'
  have hne : Θ ≠ 0 := by
    obtain ⟨v, hv⟩ := B.exists_Sum_ne_zero one_ne_zero 0 hth0 (w := w) fun z => (hsum w hw₂ _).of_norm
    exact fun e => hv ((hΘ0 v).1 (congrFun e _))
  have hfn : U.IsThetaFn Hm' χ 1 Θ := ⟨hΘ, fun l z => by
    obtain ⟨l, hl⟩ := l
    obtain ⟨a, rfl⟩ := hΛ' l hl
    rw [pow_one, hχ]
    exact hΘp a z⟩
  refine ⟨⟨Q, oa, hpr, H.rt0, H.sqrt_neg_disc_sq, hdet, I, inferInstance⟩, rfl, congrFun hI _, ?_⟩
  have key := isThetaPt_classical hL hL2 hT Q U Hm' χ Θ m (I.ev (m ^ 2)) (fun x => ⟨F (P (f _ x)), hΛ _⟩) hodd hAH hfn hne
    fun x => by rw [hev, Nat.cast_pow]; rfl
  refine Eq.mp (congrArg (IsThetaPt Q m (I.ev (m ^ 2))) (funext fun x => congrArg fnOf ?_)) key
  rw [hχ, _root_.mul_assoc]
  refine (congrArg (_ * ·) (hΘv _ m hodd.pos.ne')).trans ?_
  rw [← _root_.mul_assoc, AnArc.Sum, ← tsum_mul_left]
  exact (tsum_congr fun y => (hterm x y).symm).trans
    (d.eX.toEquiv.tsum_eq fun χ : A.N.X => (A.N.twist β u).txT m (A.N.twQ β u hm (A.q _ x)) χ)

theorem exists_full_of_small : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllD fun {_} _ _ _ {H} D => ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ] (A : ArcF D R ℂ), A.ρ = H.rt0 → ∀ (k : ℕ) (β : A.N.Form k), A.Bal β → ∀ (m : ℕ) (hm : m ^ 2 ∣ k), Odd m → ∃ ε : ℝ, 0 < ε ∧ ∀ u : ℂˣ, ‖(u : ℂ)‖ < ε → (∀ x, Summable fun χ => ‖(A.N.twist β u).txT m (A.N.twQ β u hm (A.q _ x)) χ‖) ∧ ∃ o : Full D ℂ, o.ρ = H.rt0 ∧ o.I.ζ (m ^ 2) = A.I.ζ (m ^ 2) ∧ o.Theta m fun x => (A.N.twist β u).tx m (A.N.twQ β u hm (A.q _ x)) := fun hV _ _ _ _ _ hT =>
  have hL : Laws := hV.1.1
  have hL2 : Laws2 := hV.1.2.1
  have hF : BrFamSt := _root_.GlobalTheory.Ex.brFam hL hL2
  of_steps hL hL2 hT
    (_root_.GlobalTheory.Ex.Arch.dict_of_val (_root_.GlobalTheory.ActValues.brAct hL) (_root_.GlobalTheory.Ex.Arch.AbVal.valSt hL hF (_root_.GlobalTheory.Ex.Arch.FibEx.fibEx hL hT) _root_.GlobalTheory.Ex.Arch.fibGrp (_root_.GlobalTheory.Ex.Arch.fibCubeSt hL) (_root_.GlobalTheory.Ex.Arch.FibSym.fibSymSt hL)
      (_root_.GlobalTheory.Ex.Arch.FibRos.fibRosSt hL) (_root_.GlobalTheory.Ex.Arch.FibPrim.fibPrim_of_laws hL) _root_.GlobalTheory.Ex.Arch.fibSec (_root_.GlobalTheory.Ex.Arch.fibLie_of_laws hL)))
    (_root_.GlobalTheory.Ex.Arch.towerSt_of _root_.GlobalTheory.Ex.GtValues.points_correspond (_root_.GlobalTheory.WeilValues.weil_eq_values _root_.GlobalTheory.Ex.GtValues.points_correspond hF) _root_.GlobalTheory.Ex.Arch.ptSt (_root_.GlobalTheory.Ex.Arch.qkSt_of_ptSt _root_.GlobalTheory.Ex.Arch.ptSt) _root_.GlobalTheory.Ex.Arch.Wp.wp_eq)
    _root_.GlobalTheory.Ex.Arch.typeSt (_root_.GlobalTheory.Ex.Arch.objSt_of_triple_reframe hL (_root_.GlobalTheory.Ex.Arch.tripleSt_of_laws hL hT) (_root_.GlobalTheory.Ex.Arch.reframe hT)) _root_.GlobalTheory.Ex.Arch.theta_sum_appellHumbert (_root_.GlobalTheory.Ex.Arch.txSt_of_ptSt _root_.GlobalTheory.Ex.Arch.ptSt)

end GlobalTheory.Ex.Arch
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsThetaPointComplexDegenerationSmallStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaPoint_complexDegeneration_small : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → AllD fun {_} _ _ _ {H} D => ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra (FractionRing R) ℂ] (A : ArcF D R ℂ), A.ρ = H.rt0 → ∀ (k : ℕ) (β : A.N.Form k), A.Bal β → ∀ (m : ℕ) (hm : m ^ 2 ∣ k), Odd m → ∃ ε : ℝ, 0 < ε ∧ ∀ u : ℂˣ, ‖(u : ℂ)‖ < ε → (∀ x, Summable fun χ => ‖(A.N.twist β u).txT m (A.N.twQ β u hm (A.q _ x)) χ‖) ∧ ∃ o : Full D ℂ, o.ρ = H.rt0 ∧ o.I.ζ (m ^ 2) = A.I.ζ (m ^ 2) ∧ o.Theta m fun x => (A.N.twist β u).tx m (A.N.twQ β u hm (A.q _ x)) := by
  first | exact @GlobalTheory.Ex.Arch.exists_full_of_small | exact GlobalTheory.Ex.Arch.exists_full_of_small | (intros; apply GlobalTheory.Ex.Arch.exists_full_of_small <;> assumption)
end
