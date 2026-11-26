module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LinearModelSplitPlaceCharacterEquivariance
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousPhiPrV

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeterssonStepZeroScalarFormsEqPosMulInner
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitOfUnitary
noncomputable section

open Formalism.BasicNotions Formalism.L2.Forms Matrix MeasureTheory MvPolynomial
open Formalism.REAL (fockF)
open scoped ComplexOrder

namespace GlobalTheory.ValSchur

theorem fockF_swap {σ : Type} (f g : MvPolynomial σ ℂ) : fockF f g = star (fockF g f) := by
  classical
  rw [Formalism.L2.Col.fockF_eq_sum f g (f.support ∪ g.support) Finset.subset_union_left,
    Formalism.L2.Col.fockF_eq_sum g f (f.support ∪ g.support) Finset.subset_union_right, star_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [star_mul', star_star, star_natCast]
  ring

theorem fockF_pos {σ : Type} {f : MvPolynomial σ ℂ} (hf : f ≠ 0) : ∃ r : ℝ, 0 < r ∧ fockF f f = (r : ℂ) := by
  refine ⟨∑ m ∈ f.support, Complex.normSq (f.coeff m) * ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℝ), ?_, ?_⟩
  · refine Finset.sum_pos (fun m hm => mul_pos (Complex.normSq_pos.2 (mem_support_iff.1 hm)) ?_) (support_nonempty.2 hf)
    exact_mod_cast Finset.prod_pos fun k _ => Nat.factorial_pos _
  · unfold fockF
    rw [Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_mul, Complex.ofReal_natCast]

variable {ι : Type} [Fintype ι] {n : ℕ}

theorem nfAll_swap (lam : ι → DomWeight n) (p q : MvPolynomial (ι × Fin n × Fin n) ℂ) :
    nfAll lam p q = star (nfAll lam q p) := by
  unfold nfAll
  rw [star_div₀, star_prod, ← fockF_swap]
  congr 1
  exact Finset.prod_congr rfl fun τ _ => fockF_swap _ _

theorem nfAll_pos (lam : ι → DomWeight n) {p : MvPolynomial (ι × Fin n × Fin n) ℂ} (hp : p ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ nfAll lam p p = (r : ℂ) := by
  obtain ⟨r, hr, e⟩ := fockF_pos hp
  choose s hs es using fun τ => fockF_pos (f := extremal ℂ n (lam τ)) (Formalism.GradedWeylDivisibility.hwNe ℂ n n le_rfl (lam τ).natW)
  refine ⟨r / ∏ τ, s τ, div_pos hr (Finset.prod_pos fun τ _ => hs τ), ?_⟩
  unfold nfAll
  rw [e, Complex.ofReal_div, Complex.ofReal_prod]
  simp only [es]

variable {G : ι → Matrix (Fin n) (Fin n) ℂ}

theorem tr_mem (lam : ι → DomWeight n) (g : ι → Matrix (Fin n) (Fin n) ℂ) (hg : ∀ τ, IsUnit (g τ).det)
    {v : Frames G → ℂ} (hv : v ∈ ValC G lam) : (fun z => v (Frames.tr g hg z)) ∈ ValC G lam :=
  Formalism.MainNotions.Ext.Lw.valC_tr G lam g hg hv

theorem isUnit_inv {g : ι → Matrix (Fin n) (Fin n) ℂ} (hg : ∀ τ, IsUnit (g τ).det) (τ : ι) : IsUnit ((g τ)⁻¹).det := by
  rw [det_nonsing_inv]; exact (hg τ).ringInverse

omit [Fintype ι] in
theorem tr_tr_inv {g : ι → Matrix (Fin n) (Fin n) ℂ} (hg : ∀ τ, IsUnit (g τ).det) (hg' : ∀ τ, IsUnit ((g τ)⁻¹).det)
    (z : Frames G) : Frames.tr g hg (Frames.tr (fun τ => (g τ)⁻¹) hg' z) = z :=
  Subtype.ext (funext fun τ => by
    show g τ * ((g τ)⁻¹ * z.1 τ) = z.1 τ
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hg τ), Matrix.one_mul])

omit [Fintype ι] in
theorem tr_inv_tr {g : ι → Matrix (Fin n) (Fin n) ℂ} (hg : ∀ τ, IsUnit (g τ).det) (hg' : ∀ τ, IsUnit ((g τ)⁻¹).det)
    (z : Frames G) : Frames.tr (fun τ => (g τ)⁻¹) hg' (Frames.tr g hg z) = z :=
  Subtype.ext (funext fun τ => by
    show (g τ)⁻¹ * (g τ * z.1 τ) = z.1 τ
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hg τ), Matrix.one_mul])

theorem fnOf_tr (s : ι → ℤ) (M g : ι → Matrix (Fin n) (Fin n) ℂ) (hg : ∀ τ, IsUnit (g τ).det)
    (P : MvPolynomial (ι × Fin n × Fin n) ℂ) (z : Frames G) :
    fnOf G s M P (Frames.tr g hg z) = fnOf G s (fun τ => M τ * g τ) P z := by
  simp only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, Frames.tr, Matrix.mul_assoc]

theorem exists_coord (lam : ι → DomWeight n) (o : Frames G) {v : Frames G → ℂ} (hv : v ∈ ValC G lam) :
    ∃ P ∈ CSpan lam, v = fnOf G (shiftOf lam) (fun τ => (o.1 τ)⁻¹) P := by
  obtain ⟨P, hP, e⟩ := Submodule.mem_map.1 (tr_mem lam o.1 o.2 hv)
  refine ⟨P, hP, funext fun z => ?_⟩
  have h := congrFun e (Frames.tr (fun τ => (o.1 τ)⁻¹) (isUnit_inv o.2) z)
  simp only [tr_tr_inv, fnOf_tr, Pi.one_apply, Matrix.one_mul] at h
  exact h.symm

omit [Fintype ι] in
theorem unit_of_unitary (hG : ∀ τ, (G τ).PosDef) {g : ι → Matrix (Fin n) (Fin n) ℂ} (hu : ∀ τ, (g τ)ᴴ * G τ * g τ = G τ) (τ : ι) :
    IsUnit (g τ).det := by
  have h := congrArg Matrix.det (hu τ)
  rw [det_mul] at h
  have h2 : IsUnit (G τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (hG τ).isUnit
  rw [← h] at h2
  exact isUnit_of_mul_isUnit_right h2

omit [Fintype ι] in
theorem inv_unitary {g : ι → Matrix (Fin n) (Fin n) ℂ} (hg : ∀ τ, IsUnit (g τ).det) (hu : ∀ τ, (g τ)ᴴ * G τ * g τ = G τ) (τ : ι) :
    ((g τ)⁻¹)ᴴ * G τ * (g τ)⁻¹ = G τ := by
  conv_lhs => rw [← hu τ]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← conjTranspose_mul, Matrix.mul_nonsing_inv _ (hg τ), conjTranspose_one,
    Matrix.one_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hg τ), Matrix.mul_one]

omit [Fintype ι] in
theorem exists_isON (hG : ∀ τ, (G τ).PosDef) : ∃ o : Frames G, o.IsON := by
  have h : ∀ τ, ∃ B : Matrix (Fin n) (Fin n) ℂ, IsUnit B.det ∧ G τ = Bᴴ * B := fun τ => by
    open scoped MatrixOrder in
    obtain ⟨B, hB, e⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.1 (hG τ).isStrictlyPositive
    exact ⟨B, (Matrix.isUnit_iff_isUnit_det _).1 hB, e⟩
  choose B hu hJ using h
  refine ⟨⟨fun τ => (B τ)⁻¹, fun τ => ?_⟩, fun τ => Or.inl ?_⟩
  · rw [det_nonsing_inv]; exact (hu τ).ringInverse
  · show ((B τ)⁻¹)ᴴ * G τ * (B τ)⁻¹ = 1
    rw [hJ τ, conjTranspose_nonsing_inv, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ (by rw [det_conjTranspose]; exact (hu τ).star), Matrix.one_mul, Matrix.mul_nonsing_inv _ (hu τ)]

def IsFock (G : ι → Matrix (Fin n) (Fin n) ℂ) (lam : ι → DomWeight n) (ip : (Frames G → ℂ) → (Frames G → ℂ) → ℂ) : Prop :=
  ∀ o : Frames G, o.IsON → ∀ P ∈ CSpan lam, ∀ Q ∈ CSpan lam,
    ip (fnOf G (shiftOf lam) (fun τ => (o.1 τ)⁻¹) P) (fnOf G (shiftOf lam) (fun τ => (o.1 τ)⁻¹) Q) = nfAll lam Q P

variable {lam : ι → DomWeight n} {ip ip' : (Frames G → ℂ) → (Frames G → ℂ) → ℂ}

theorem IsFock.eq (hG : ∀ τ, (G τ).PosDef) (h : IsFock G lam ip) (h' : IsFock G lam ip') {f g : Frames G → ℂ}
    (hf : f ∈ ValC G lam) (hg : g ∈ ValC G lam) : ip f g = ip' f g := by
  obtain ⟨o, ho⟩ := exists_isON hG
  obtain ⟨P, hP, rfl⟩ := exists_coord lam o hf
  obtain ⟨Q, hQ, rfl⟩ := exists_coord lam o hg
  rw [h o ho P hP Q hQ, h' o ho P hP Q hQ]

theorem IsFock.swap (hG : ∀ τ, (G τ).PosDef) (h : IsFock G lam ip) {f g : Frames G → ℂ}
    (hf : f ∈ ValC G lam) (hg : g ∈ ValC G lam) : ip g f = star (ip f g) := by
  obtain ⟨o, ho⟩ := exists_isON hG
  obtain ⟨P, hP, rfl⟩ := exists_coord lam o hf
  obtain ⟨Q, hQ, rfl⟩ := exists_coord lam o hg
  rw [h o ho P hP Q hQ, h o ho Q hQ P hP, nfAll_swap]

theorem IsFock.pos (hG : ∀ τ, (G τ).PosDef) (h : IsFock G lam ip) {f : Frames G → ℂ}
    (hf : f ∈ ValC G lam) (h0 : f ≠ 0) : ∃ r : ℝ, 0 < r ∧ ip f f = (r : ℂ) := by
  obtain ⟨o, ho⟩ := exists_isON hG
  obtain ⟨P, hP, rfl⟩ := exists_coord lam o hf
  rw [h o ho P hP P hP]
  exact nfAll_pos lam fun e => h0 (by rw [e, map_zero])

theorem IsFock.tr (hG : ∀ τ, (G τ).PosDef) (h : IsFock G lam ip) {k : ι → Matrix (Fin n) (Fin n) ℂ} (hk : ∀ τ, IsUnit (k τ).det)
    (hu : ∀ τ, (k τ)ᴴ * G τ * k τ = G τ) {f g : Frames G → ℂ} (hf : f ∈ ValC G lam) (hg : g ∈ ValC G lam) :
    ip (fun z => f (Frames.tr k hk z)) (fun z => g (Frames.tr k hk z)) = ip f g := by
  obtain ⟨o, ho⟩ := exists_isON hG
  obtain ⟨P, hP, rfl⟩ := exists_coord lam o hf
  obtain ⟨Q, hQ, rfl⟩ := exists_coord lam o hg
  have ho' := ho.tr (fun τ => (k τ)⁻¹) (isUnit_inv hk) (inv_unitary hk hu)
  have e : (fun τ => ((Frames.tr (fun τ => (k τ)⁻¹) (isUnit_inv hk) o).1 τ)⁻¹) = fun τ => (o.1 τ)⁻¹ * k τ := funext fun τ => by
    show ((k τ)⁻¹ * o.1 τ)⁻¹ = _
    rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (hk τ)]
  have h2 := h _ ho' P hP Q hQ
  rw [e] at h2
  rw [h o ho P hP Q hQ, ← h2]
  simp only [fnOf_tr]

theorem continuous_val {X : Type} [TopologicalSpace X] {m : X → ι → Matrix (Fin n) (Fin n) ℂ} (hm : ∀ x τ, IsUnit (m x τ).det)
    (hc : ∀ τ, Continuous fun x => m x τ) (y : Frames G) {f : Frames G → ℂ} (hf : f ∈ ValC G lam) :
    Continuous fun x => f (Frames.tr (m x) (hm x) y) := by
  obtain ⟨P, -, rfl⟩ := hf
  simp only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, Pi.one_apply, Matrix.one_mul]
  refine (continuous_finsetProd _ fun τ _ => ?_).mul ((MvPolynomial.continuous_eval P).comp (continuous_pi fun v => ?_))
  · exact (((hc τ).matrix_mul continuous_const).matrix_det).zpow₀ _ fun x => Or.inl ((Frames.tr (m x) (hm x) y).2 τ).ne_zero
  · exact ((hc v.1).matrix_mul continuous_const).matrix_elem _ _

theorem exists_val_ne (lam : ι → DomWeight n) (y : Frames G) : ∃ f ∈ ValC G lam, f y ≠ 0 := by
  obtain ⟨f, hf, h0⟩ := (Submodule.ne_bot_iff _).1 (GlobalTheory.Core.Rk.Top.Model.valC_ne_bot G lam)
  obtain ⟨z, hz⟩ := Function.ne_iff.1 h0
  have hu : ∀ τ, IsUnit (z.1 τ * (y.1 τ)⁻¹).det := fun τ => by
    rw [det_mul]; exact (z.2 τ).mul (isUnit_inv y.2 τ)
  refine ⟨_, tr_mem lam _ hu hf, ?_⟩
  have e : Frames.tr _ hu y = z := Subtype.ext (funext fun τ => by
    show z.1 τ * (y.1 τ)⁻¹ * y.1 τ = z.1 τ
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (y.2 τ), Matrix.mul_one])
  simp only [e]
  exact hz

def IsSesq (ip : (Frames G → ℂ) → (Frames G → ℂ) → ℂ) : Prop :=
  (∀ (a : ℂ) (f f' g : Frames G → ℂ), ip (a • f + f') g = star a * ip f g + ip f' g) ∧
    ∀ (a : ℂ) (f g g' : Frames G → ℂ), ip f (a • g + g') = a * ip f g + ip f g'

theorem avg_eq (hG : ∀ τ, (G τ).PosDef) (lam : ι → DomWeight n) {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    [CompactSpace K] [T2Space K] [MeasurableSpace K] [BorelSpace K] (ν : Measure K) [ν.IsHaarMeasure]
    (m : K → ι → Matrix (Fin n) (Fin n) ℂ) (hm : ∀ k τ, IsUnit (m k τ).det) (hc : ∀ τ, Continuous fun k => m k τ)
    (hmul : ∀ a b τ, m (a * b) τ = m a τ * m b τ)
    (hs : ∀ g : ι → Matrix (Fin n) (Fin n) ℂ, (∀ τ, (g τ)ᴴ * G τ * g τ = G τ) → ∃ k, ∀ τ, m k τ = g τ) (y : Frames G) :
    ∃ c : ℝ, 0 < c ∧ ∀ ip, IsFock G lam ip → IsSesq ip → ∀ f ∈ ValC G lam, ∀ g ∈ ValC G lam,
      ∫ k, g (Frames.tr (m k) (hm k) y) * star (f (Frames.tr (m k) (hm k) y)) ∂ν = (c : ℂ) * ip f g := by
  by_cases hex : ∃ ip, IsFock G lam ip ∧ IsSesq ip
  swap
  · exact ⟨1, one_pos, fun ip h1 h2 => absurd ⟨ip, h1, h2⟩ hex⟩
  obtain ⟨ip, hF, hS⟩ := hex
  set Φ : (Frames G → ℂ) → (Frames G → ℂ) → ℂ := fun f g =>
    ∫ k, g (Frames.tr (m k) (hm k) y) * star (f (Frames.tr (m k) (hm k) y)) ∂ν with hΦ
  have hcont : ∀ f ∈ ValC G lam, ∀ g ∈ ValC G lam,
      Continuous fun k => g (Frames.tr (m k) (hm k) y) * star (f (Frames.tr (m k) (hm k) y)) := fun f hf g hg =>
    (continuous_val hm hc y hg).mul (continuous_val hm hc y hf).star
  have hint : ∀ f ∈ ValC G lam, ∀ g ∈ ValC G lam,
      Integrable (fun k => g (Frames.tr (m k) (hm k) y) * star (f (Frames.tr (m k) (hm k) y))) ν := fun f hf g hg =>
    integrableOn_univ.1 ((hcont f hf g hg).continuousOn.integrableOn_compact isCompact_univ)
  have Φl : ∀ (a : ℂ) (f f' g : Frames G → ℂ), f ∈ ValC G lam → f' ∈ ValC G lam → g ∈ ValC G lam →
      Φ (a • f + f') g = star a * Φ f g + Φ f' g := fun a f f' g hf hf' hg => by
    simp only [hΦ]
    rw [← integral_const_mul, ← integral_add ((hint f hf g hg).const_mul _) (hint f' hf' g hg)]
    congr 1; funext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, star_add, star_mul']
    ring
  have Φr : ∀ (a : ℂ) (f g g' : Frames G → ℂ), f ∈ ValC G lam → g ∈ ValC G lam → g' ∈ ValC G lam →
      Φ f (a • g + g') = a * Φ f g + Φ f g' := fun a f g g' hf hg hg' => by
    simp only [hΦ]
    rw [← integral_const_mul, ← integral_add ((hint f hf g hg).const_mul _) (hint f hf g' hg')]
    congr 1; funext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have Φtr : ∀ (g : ι → Matrix (Fin n) (Fin n) ℂ) (hg : ∀ τ, IsUnit (g τ).det), (∀ τ, (g τ)ᴴ * G τ * g τ = G τ) →
      ∀ f f', Φ (fun z => f (Frames.tr g hg z)) (fun z => f' (Frames.tr g hg z)) = Φ f f' := fun g hg hu f f' => by
    obtain ⟨k0, hk0⟩ := hs g hu
    have e : ∀ k, Frames.tr g hg (Frames.tr (m k) (hm k) y) = Frames.tr (m (k0 * k)) (hm _) y := fun k =>
      Subtype.ext (funext fun τ => by
        show g τ * (m k τ * y.1 τ) = m (k0 * k) τ * y.1 τ
        rw [hmul, hk0, Matrix.mul_assoc])
    simp only [hΦ, e]
    exact integral_mul_left_eq_self (fun k => f' (Frames.tr (m k) (hm k) y) * star (f (Frames.tr (m k) (hm k) y))) k0
  obtain ⟨c, e, he, he0, hce⟩ := (GlobalTheory.riesz_and_eigenvector_of_sesq_on_fun_space (Frames G) (ValC G lam) inferInstance ip Φ
    (fun a f f' g _ _ _ => hS.1 a f f' g) (fun a f g g' _ _ _ => hS.2 a f g g') (fun f g hf hg => hF.swap hG hf hg)
    (fun f hf h0 => by obtain ⟨r, hr, er⟩ := hF.pos hG hf h0; rw [er]; exact hr) Φl Φr).2
    (GlobalTheory.Core.Rk.Top.Model.valC_ne_bot G lam)
  obtain ⟨-, -, ia, is⟩ := GlobalTheory.sesq_rules_of_combination (ValC G lam) ip (fun a f f' g _ _ _ => hS.1 a f f' g)
    (fun a f g g' _ _ _ => hS.2 a f g g')
  obtain ⟨-, -, pa, ps⟩ := GlobalTheory.sesq_rules_of_combination (ValC G lam) Φ Φl Φr
  let W : Submodule ℂ (Frames G → ℂ) :=
    { carrier := {g | g ∈ ValC G lam ∧ ∀ f ∈ ValC G lam, Φ f g = c * ip f g}
      add_mem' := fun {a b} ha hb => ⟨add_mem ha.1 hb.1, fun f hf => by
        rw [pa f a b hf ha.1 hb.1, ia f a b hf ha.1 hb.1, ha.2 f hf, hb.2 f hf, mul_add]⟩
      zero_mem' := ⟨zero_mem _, fun f hf => by
        have h1 := ps 0 f 0 hf (zero_mem _)
        have h2 := is 0 f 0 hf (zero_mem _)
        rw [zero_smul, zero_mul] at h1 h2
        rw [h1, h2, mul_zero]⟩
      smul_mem' := fun a b hb => ⟨Submodule.smul_mem _ _ hb.1, fun f hf => by
        rw [ps a f b hf hb.1, is a f b hf hb.1, hb.2 f hf]; ring⟩ }
  have hW : W = ValC G lam := by
    refine Formalism.L2.SG.Pf.valuation_character_irreducible ι n G (fun τ => Or.inl (hG τ)) lam W (fun g hg => hg.1) ?_ ?_
    · exact (Submodule.ne_bot_iff _).2 ⟨e, ⟨he, hce⟩, he0⟩
    · intro g hu F hFW
      have hg := unit_of_unitary hG hu
      refine ⟨fun z => F (Frames.tr g hg z), ⟨tr_mem lam g hg hFW.1, fun f hf => ?_⟩, fun z z' hz => ?_⟩
      · have hf' := tr_mem lam _ (isUnit_inv hg) hf
        have ef : f = fun z => (fun z => f (Frames.tr (fun τ => (g τ)⁻¹) (isUnit_inv hg) z)) (Frames.tr g hg z) :=
          funext fun z => by simp only [tr_inv_tr]
        have a1 := Φtr g hg hu (fun z => f (Frames.tr (fun τ => (g τ)⁻¹) (isUnit_inv hg) z)) F
        have a2 := hF.tr hG hg hu hf' hFW.1
        rw [← ef] at a1 a2
        exact a1.trans ((hFW.2 _ hf').trans (congrArg (c * ·) a2.symm))
      · exact congrArg F (Subtype.ext (funext fun τ => (hz τ).symm))
  have hall : ∀ f ∈ ValC G lam, ∀ g ∈ ValC G lam, Φ f g = c * ip f g := fun f hf g hg =>
    (show g ∈ W from hW ▸ hg).2 f hf
  obtain ⟨f0, hf0, hy⟩ := exists_val_ne lam y
  obtain ⟨r, hr, er⟩ := hF.pos hG hf0 (fun h => hy (by rw [h]; rfl))
  have h1 : ∀ τ, m 1 τ = 1 := fun τ => by
    have := hmul 1 1 τ
    rw [mul_one] at this
    calc m 1 τ = (m 1 τ)⁻¹ * (m 1 τ * m 1 τ) := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hm 1 τ), Matrix.one_mul]
      _ = 1 := by rw [← this, Matrix.nonsing_inv_mul _ (hm 1 τ)]
  have hcn : Continuous fun k => Complex.normSq (f0 (Frames.tr (m k) (hm k) y)) :=
    Complex.continuous_normSq.comp (continuous_val hm hc y hf0)
  have hpos : 0 < ∫ k, Complex.normSq (f0 (Frames.tr (m k) (hm k) y)) ∂ν := by
    refine hcn.integral_pos_of_hasCompactSupport_nonneg_nonzero (HasCompactSupport.of_compactSpace _)
      (fun k => Complex.normSq_nonneg _) (x := 1) ?_
    have e1 : Frames.tr (m 1) (hm 1) y = y := Subtype.ext (funext fun τ => by
      show m 1 τ * y.1 τ = y.1 τ
      rw [h1, Matrix.one_mul])
    rw [e1]
    exact (Complex.normSq_pos.2 hy).ne'
  have hΦ0 : Φ f0 f0 = ((∫ k, Complex.normSq (f0 (Frames.tr (m k) (hm k) y)) ∂ν : ℝ) : ℂ) := by
    simp only [hΦ, Complex.star_def, Complex.mul_conj]
    exact integral_ofReal
  have hc0 := hall f0 hf0 f0 hf0
  rw [hΦ0, er] at hc0
  refine ⟨(∫ k, Complex.normSq (f0 (Frames.tr (m k) (hm k) y)) ∂ν) / r, div_pos hpos hr, fun ip' hF' _ f hf g hg => ?_⟩
  have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  rw [Complex.ofReal_div, hc0, mul_div_cancel_right₀ _ hr', hF'.eq hG hF hf hg]
  exact hall f hf g hg

end GlobalTheory.ValSchur
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeterssonStepZeroScalarFormsEqPosMulInner
noncomputable section

namespace GlobalTheory.StepZeroNorm

section Chi

open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {gp : Fin 2 → ℕ}

theorem eventually_chi {S : StepLevel F E σ J T f bad} {G : GLoc F E σ gp} {a t nb skip fc : ℕ} {zl : Bool}
    (L : GLev S G a t nb skip fc zl) (hgp : ∀ a, gp a ≠ 0) :
    letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
    ∀ᶠ x : UPts σ J (FiniteAdeleRing (𝓞 F) F) in nhds 1, ∃ hx : x.1 ∈ S.U, S.chi ⟨x.1, hx⟩ = 1 := by
  letI := tensTopL (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
  haveI := Formalism.L2.Col.rlt_topRing (F := F) (E := E)
  have hfin : ∀ a, {v : HeightOneSpectrum (𝓞 F) | (gp a : 𝓞 F) ∈ v.asIdeal}.Finite := fun a => by
    have h0 : Ideal.span {(gp a : 𝓞 F)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact Nat.cast_ne_zero.2 (hgp a)
    refine (Ideal.finite_factors h0).subset fun v hv => ?_
    exact Ideal.dvd_span_singleton.2 hv
  have h1 : ∀ᶠ x : UPts σ J (FiniteAdeleRing (𝓞 F) F) in nhds 1, x.1 ∈ S.U := S.U_open.mem_nhds S.U.one_mem
  have hone : ∀ a v h, G.mat a v h (L.fr a v h) (bc (prV (E := E) v) (1 : UPts σ J (FiniteAdeleRing (𝓞 F) F)).1) = 1 := by
    intro a v h
    simp [GLoc.mat]
  have h2 : ∀ᶠ x : UPts σ J (FiniteAdeleRing (𝓞 F) F) in nhds 1, ∀ a : Fin 2, ∀ v ∈ {v : HeightOneSpectrum (𝓞 F) | (gp a : 𝓞 F) ∈ v.asIdeal},
      ∀ h : (gp a : 𝓞 F) ∈ v.asIdeal, redM F v (G.mat a v h (L.fr a v h) (bc (prV (E := E) v) x.1)) = 1 := by
    refine Filter.eventually_all.2 fun a => (Filter.eventually_all_finite (hfin a)).2 fun v h => ?_
    have hc : Continuous fun x : UPts σ J (FiniteAdeleRing (𝓞 F) F) => G.mat a v h (L.fr a v h) (bc (prV (E := E) v) x.1) := by
      have c0 : Continuous fun x : UPts σ J (FiniteAdeleRing (𝓞 F) F) => (x.1.val).map ((G.phi a v h).comp (prV (E := E) v)) :=
        (Units.continuous_val.comp continuous_subtype_val).matrix_map (GlobalTheory.LevelCharOpen.continuous_phi_prV G a v h)
      exact ((continuous_const (y := ((L.fr a v h)⁻¹).val)).matrix_mul c0).matrix_mul (continuous_const (y := (L.fr a v h).val))
    have h3 : ∀ᶠ x : UPts σ J (FiniteAdeleRing (𝓞 F) F) in nhds 1, ∀ i j,
        Valued.v (G.mat a v h (L.fr a v h) (bc (prV (E := E) v) x.1) i j - (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j) < 1 := by
      refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_
      have c1 : Continuous fun x : UPts σ J (FiniteAdeleRing (𝓞 F) F) =>
          G.mat a v h (L.fr a v h) (bc (prV (E := E) v) x.1) i j - (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j :=
        (hc.matrix_elem i j).sub continuous_const
      have ho : IsOpen {y : v.adicCompletion F | Valued.v y < 1} := by
        simpa using Valued.isOpen_ball (v.adicCompletion F) 1
      refine (ho.preimage c1).mem_nhds ?_
      rw [Set.mem_preimage, Set.mem_setOf_eq, hone, sub_self, map_zero]
      exact zero_lt_one
    exact h3.mono fun x hx _ => GlobalTheory.LevelCharOpen.redM_eq_one v _ hx
  filter_upwards [h1, h2] with x hx hr
  refine ⟨hx, Units.ext ?_⟩
  have hr1 : ∀ a v h, redM F v (G.mat a v h (L.fr a v h) (bc (prV (E := E) v) (1 : S.U).1)) = 1 := fun a v h =>
    GlobalTheory.LevelCharOpen.redM_eq_one v _ fun i j => by
      have := hone a v h
      simp only [OneMemClass.coe_one] at this ⊢
      rw [this, sub_self, map_zero]
      exact zero_lt_one
  rw [← map_one S.chi, L.chi_eq, L.chi_eq]
  refine Finset.prod_congr rfl fun a _ => finprod_congr fun v => finprod_congr fun h => ?_
  rw [hr a v h h, hr1]

end Chi

section Gen

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_open {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) {J : Matrix (Fin n) (Fin n) D.host.E}
    (hJ : J = V.gram.reindex (finCongr hn) (finCongr hn)) {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
    {S : StepLevel D.host.F D.host.E (sigD D) J T f bad} {G : GLoc D.host.F D.host.E (sigD D) D.host.g} {a t nb skip fc : ℕ} {zl : Bool}
    (L : GLev S G a t nb skip fc zl) :
    ∃ W : Subgroup (GA D V), IsOpen (W : Set (GA D V)) ∧ ∀ k ∈ W, k ∈ GfC V → ∀ κ : S.U, κ.1.1 = finM V hn k → S.chi κ = 1 := by
  subst hn
  subst hJ
  letI := tensTopL (F := D.host.F) (E := D.host.E) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have hev := eventually_chi L fun a => (D.host.g_prime a).ne_zero
  let φ : GA D V →* GL (Fin V.rank) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
    (bc (toEAf D)).comp (matHom V)
  have hφ : ∀ g, (φ g).1 = finM V rfl g := fun g => RdLaw.finGL_val V g
  have hmem : ∀ g, φ g ∈ UPts (sigD D) (V.gram.reindex (finCongr rfl) (finCongr rfl)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) := fun g => by
    obtain ⟨x, hx⟩ := RdVal.finM_mem V rfl _ rfl g
    have e : φ g = x.1 := Units.ext (by rw [hφ, hx])
    rw [e]; exact x.2
  have hc : Continuous fun g => (⟨φ g, hmem g⟩ : UPts (sigD D) (V.gram.reindex (finCongr rfl) (finCongr rfl)) _) :=
    (RdLaw.continuous_finGL V).subtype_mk _
  refine ⟨(S.chi.ker.map S.U.subtype).comap φ, Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_, ?_⟩
  · have e1 : (⟨φ 1, hmem 1⟩ : UPts (sigD D) (V.gram.reindex (finCongr rfl) (finCongr rfl)) _) = 1 := Subtype.ext (map_one φ)
    have ht := hc.tendsto' 1 1 e1
    refine (ht.eventually hev).mono ?_
    rintro g ⟨hx, h1⟩
    exact ⟨⟨φ g, hx⟩, h1, rfl⟩
  · rintro k ⟨κ', h1, e⟩ - κ hκ
    have : κ = κ' := Subtype.ext (Units.ext (by rw [hκ, ← hφ, ← e]; rfl))
    rw [this]
    exact h1


set_option maxHeartbeats 2000000 in
theorem card_stab {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) {J : Matrix (Fin n) (Fin n) D.host.E}
    (hJ : J = V.gram.reindex (finCongr hn) (finCongr hn)) {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
    (S : StepLevel D.host.F D.host.E (sigD D) J T f bad) (y : UPts (sigD D) J (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    {Γ : Type} [Group Γ] (i : Γ →* UJ (sigD D : D.host.E →+* D.host.E) J) (hi : Function.Injective i)
    (hr : ∀ γ : UJ (sigD D : D.host.E →+* D.host.E) J, γ ∈ i.range ↔
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 ∈ S.U.map (MulAut.conj y.1).toMonoidHom) :
    Nat.card {γ : GQ V // ∃ κ : S.U, finM V hn γ.1 * y.1.1 = y.1.1 * κ.1.1} = Nat.card Γ := by
  subst hn
  subst hJ
  have hinj : Function.Injective (incA D) :=
    Algebra.TensorProduct.includeRight_injective (NumberField.AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F)
  have hm : ∀ δ : UJ (sigD D : D.host.E →+* D.host.E) (V.gram.reindex (finCongr rfl) (finCongr rfl)),
      bc (incA D) δ.1 ∈ HR (AF D.host.F) D.sp.cm.sig V.gram := fun δ => by
    have hδ' : cT (sigD D : D.host.E →+* D.host.E) δ.1.1 * V.gram * δ.1.1 = V.gram := δ.2
    have h2 := congrArg (fun M => M.map (incA D)) hδ'
    simp only [Matrix.map_mul] at h2
    exact h2
  let e : UJ (sigD D : D.host.E →+* D.host.E) (V.gram.reindex (finCongr rfl) (finCongr rfl)) → GQ V := fun δ =>
    ⟨⟨bc (incA D) δ.1, hm δ⟩, Subgroup.mem_subgroupOf.2 ⟨δ.1, δ.2, rfl⟩⟩
  have he : ∀ δ, finM V rfl (e δ).1 = (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) δ.1).1 := fun δ =>
    RdLaw.rat_finM V δ.1 _ rfl
  have key : ∀ δ, (∃ κ : S.U, finM V rfl (e δ).1 * y.1.1 = y.1.1 * κ.1.1) ↔ δ ∈ i.range := fun δ => by
    rw [hr, he]
    generalize bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) δ.1 = x
    constructor
    · rintro ⟨κ, hκ⟩
      have h1 : x * y.1 = y.1 * κ.1 := Units.ext hκ
      exact ⟨κ.1, κ.2, (mul_inv_eq_of_eq_mul h1.symm)⟩
    · rintro ⟨κ, hκ, h1⟩
      have h2 : y.1 * κ * y.1⁻¹ = x := h1
      exact ⟨⟨κ, hκ⟩, congrArg Units.val (eq_mul_of_mul_inv_eq h2).symm⟩
  refine (Nat.card_eq_of_bijective (fun s : Γ => (⟨e (i s), (key _).2 ⟨s, rfl⟩⟩ :
    {γ : GQ V // ∃ κ : S.U, finM V rfl γ.1 * y.1.1 = y.1.1 * κ.1.1})) ⟨fun s s' h => hi ?_, ?_⟩).symm
  · have h1 : (i s).1.1.map (incA D) = (i s').1.1.map (incA D) := congrArg (fun z => z.1.1.1.1) h
    exact Subtype.ext (Units.ext (Matrix.map_injective hinj h1))
  · rintro ⟨γ, hγ⟩
    obtain ⟨δ, hδ, e'⟩ := Subgroup.mem_subgroupOf.1 γ.2
    have h1 : e ⟨δ, hδ⟩ = γ := Subtype.ext (Subtype.ext e')
    obtain ⟨s, hs⟩ := (key ⟨δ, hδ⟩).1 (h1 ▸ hγ)
    exact ⟨s, Subtype.ext (by simp only [hs, h1])⟩


set_option maxHeartbeats 2000000 in
theorem integral_rdS {D : D7} (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) {n : ℕ} (hn : V.rank = n) {J : Matrix (Fin n) (Fin n) D.host.E}
    (hJ : J = V.gram.reindex (finCongr hn) (finCongr hn)) {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
    (S : StepLevel D.host.F D.host.E (sigD D) J T f bad) {cl : Type} [Fintype cl]
    (yc : cl → UPts (sigD D) J (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hb : Function.Bijective (fun c => (Quotient.mk'' (yc c) : Cls S))) (hS : V.SigOK) (hP : V.IsPosDef)
    (hχ : ∀ κ : S.U, ‖(S.chi κ : ℂ)‖ = 1)
    (hW : ∃ W : Subgroup (GA D V), IsOpen (W : Set (GA D V)) ∧ ∀ k ∈ W, k ∈ GfC V → ∀ κ : S.U, κ.1.1 = finM V hn k → S.chi κ = 1)
    (lam : D.what₂.Tau → DomWeight n) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (hμ : μ.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) (y : Frames (gramC J (embT D))) :
    ∃ c : ℝ, 0 < c ∧ ∀ ip : cl → (Frames (gramC J (embT D)) → ℂ) → (Frames (gramC J (embT D)) → ℂ) → ℂ,
      (∀ a, GlobalTheory.ValSchur.IsFock _ lam (ip a) ∧ GlobalTheory.ValSchur.IsSesq (ip a)) →
      ∀ φ ∈ FiC S (embT D) lam yc, ∀ ψ ∈ FiC S (embT D) lam yc,
        ∫ g in 𝓕, rdS θ V hn S yc φ y g * star (rdS θ V hn S yc ψ y g) ∂μ =
          (c : ℂ) * ∑ a, ((Nat.card {γ : GQ V // ∃ κ : S.U, finM V hn γ.1 * (yc a).1.1 = (yc a).1.1 * κ.1.1} : ℕ) : ℂ)⁻¹ *
            ip a (ψ a) (φ a) := by
  subst hn
  subst hJ
  have hPD : ∀ τ, (gramAt D V τ).PosDef := fun τ => by
    have := hS (tauE D τ)
    rw [hP] at this
    exact GlobalTheory.DefiniteQuotient.posDef_of_signature this
  choose h hh1 hh2 using fun a => GlobalTheory.Core.Mi.PinModel.exists_finM V rfl (yc a)
  obtain ⟨vol, ν, hvol, hν, -, hsum⟩ := GlobalTheory.T.integral_definiteQuotient_eq_classSum D θ hθ V _ rfl _ rfl T f bad S cl yc hb hS hPD μ 𝓕 hμ h𝓕 h
    fun a => ⟨hh1 a, hh2 a⟩
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  haveI : T2Space (GA D V) := by
    have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
    first | exact hT.1 | exact hT.2.1 | exact hT.2.2.1 | exact hT.2.2.2.1 | exact hT.2.2.2.2.1 | exact hT.2.2.2.2.2.1 | exact hT.2.2.2.2.2.2
  haveI : CompactSpace (GinfC V) := isCompact_iff_compactSpace.1 (Formalism.IndefR.Eqv.isCompact_GinfC hS fun τ => Or.inl (hP τ))
  haveI : BorelSpace (GinfC V) := Subtype.borelSpace _
  have hone : ∀ τ, infM θ V rfl 1 τ = 1 := RdLaw.infM_fin θ V 1 (one_mem _)
  have hu : ∀ (k : GinfC V) τ, IsUnit (infM θ V rfl k.1 τ).det := fun k τ =>
    Matrix.isUnit_det_of_right_inverse (B := infM θ V rfl k.1⁻¹ τ) (by rw [← RdLaw.infM_mul, mul_inv_cancel, hone])
  obtain ⟨c, hc, havg⟩ := GlobalTheory.ValSchur.avg_eq (G := gramC (V.gram.reindex (finCongr rfl) (finCongr rfl)) (embT D)) hPD lam ν
    (fun k : GinfC V => infM θ V rfl k.1) hu (fun τ => (RdLaw.continuous_infM θ hθ V τ).comp continuous_subtype_val)
    (fun a b τ => RdLaw.infM_mul θ V a.1 b.1 τ) (fun g hg => by
      obtain ⟨k, hk, e⟩ := (GlobalTheory.SmoothForms.RealPts.glue θ hθ V).2 g hg
      exact ⟨⟨k, hk⟩, fun τ => (RdLaw.infM_rfl θ V k τ).trans (e τ)⟩) y
  refine ⟨vol * c, mul_pos hvol hc, fun ip hip φ hφ ψ hψ => ?_⟩
  have L1 := RdLaw.rdS_laws D θ hθ V _ rfl _ rfl T f bad S cl yc hb lam φ hφ y
  have L2 := RdLaw.rdS_laws D θ hθ V _ rfl _ rfl T f bad S cl yc hb lam ψ hψ y
  have hval : ∀ φ ∈ FiC S (embT D) lam yc, ∀ a, φ a ∈ ValC _ lam ∧ ∀ k : GinfC V,
      rdS θ V rfl S yc φ y (h a * k.1) = φ a (Frames.tr (infM θ V rfl k.1) (hu k) y) := by
    rintro _ ⟨Φ, hΦ, rfl⟩ a
    refine ⟨(Submodule.mem_inf.1 hΦ).2 (yc a) (Set.mem_univ _), fun k => ?_⟩
    refine (GlobalTheory.AdForm.rdS_val D θ hθ V _ rfl _ rfl T f bad S cl yc hb Φ (Submodule.mem_inf.1 hΦ).1 y (h a * k.1)).2.2
      (yc a) _ ?_ fun τ => ?_
    · rw [RdLaw.finM_mul, RdLaw.finM_inf V k.1 k.2, Matrix.mul_one, hh2]
    · rw [RdLaw.infM_mul, RdLaw.infM_fin θ V _ (hh1 a), Matrix.one_mul]
      rfl
  refine (hsum (fun g => rdS θ V rfl S yc φ y g * star (rdS θ V rfl S yc ψ y g)) ((L1.2.2.2 hW).mul (L2.2.2.2 hW).star)
    (fun γ hγ x => by simp only [L1.1 γ hγ, L2.1 γ hγ]) ?_).trans ?_
  swap
  · rw [Complex.ofReal_mul, mul_assoc, Finset.mul_sum (a := (c : ℂ))]
    refine congrArg _ (Finset.sum_congr rfl fun a _ => ?_)
    simp only [(hval φ hφ a).2, (hval ψ hψ a).2]
    rw [havg _ (hip a).1 (hip a).2 _ (hval ψ hψ a).1 _ (hval φ hφ a).1]
    ring
  · rintro k hk ⟨κ, hκ⟩ x
    have h1 : (S.chi κ : ℂ) * star (S.chi κ : ℂ) = 1 := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hχ]; simp
    simp only [L1.2.1 k hk κ hκ, L2.2.1 k hk κ hκ, star_mul']
    linear_combination (rdS θ V rfl S yc φ y x * star (rdS θ V rfl S yc ψ y x)) * h1

end Gen

end GlobalTheory.StepZeroNorm

end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl GlobalTheory.SeeSaw ValuativeRel IsLocalRing
attribute [local instance] Formalism.BasicNotions.Host.cmStar


set_option maxHeartbeats 2000000 in
theorem GlobalTheory.StepZeroNorm.integral_rd_eq_inner : ∀ (D : D7) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (θ : InfFam D), IsInfFam θ → CoCpt (D.sp.X 0) → ∀ (vS : Vol (D.sp.X 0)) (y : (D.mem u).C.Y 0), ∃ c : ℝ, 0 < c ∧ ∀ φ ψ : D.what₂.Mu u, ∫ g in vS.𝓕, (GlobalTheory.Core.Mi.chart0 F).rd θ (D.eMu u φ).1 y g * star ((GlobalTheory.Core.Mi.chart0 F).rd θ (D.eMu u ψ).1 y g) ∂vS.μ = (c : ℂ) * inner ℂ ψ φ := by
  intro D u F θ hθ _ vS y
  obtain ⟨c, hc, H⟩ := GlobalTheory.StepZeroNorm.integral_rdS θ hθ (D.sp.X 0) (Formalism.L2.Forms.rankN D 0 (Nat.zero_le _)) rfl F.cls0.lev
    F.cls0.y F.cls0.y_bij (D.sp.X_sig 0) (D7.X_posDef D 0 (Nat.zero_le _)) F.glev0.chi_unit
    (GlobalTheory.StepZeroNorm.exists_open _ _ rfl F.glev0) (Formalism.L2.Forms.lamT u 0) vS.μ vS.𝓕 vS.haar vS.fund (F.val0.eY y)
  refine ⟨c, hc, fun φ ψ => ?_⟩
  have hm : ∀ φ : D.what₂.Mu u, (fun a z => (D.eMu u φ).1 a (F.val0.eY.symm z)) ∈
      Formalism.L2.Forms.FiC F.cls0.lev (Formalism.L2.Forms.embT D) (Formalism.L2.Forms.lamT u 0) F.cls0.y := fun φ =>
    (F.val0.Fi _).1 (by rw [(D.fm u).Fi_zero]; exact (D.eMu u φ).2.1)
  have h1 := H (fun a f g => (D.fm u).ipV 0 a (fun z => f (F.val0.eY z)) (fun z => g (F.val0.eY z))) (fun a => ⟨?_, ?_, ?_⟩)
    _ (hm φ) _ (hm ψ)
  · refine h1.trans (congrArg _ ?_)
    rw [D.eMu_isom, MemberForms.ipC]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [GlobalTheory.StepZeroNorm.card_stab _ _ rfl F.cls0.lev (F.cls0.y a) (F.cls0.stabI a) (F.cls0.stabI_inj a) (F.cls0.stabI_range a)]
    simp only [Equiv.symm_apply_apply]
    rfl
  · intro o ho P hP Q hQ
    have h2 := F.val0.ipV a o ho P (Formalism.L2.Forms.lamT_zero u ▸ hP) Q (Formalism.L2.Forms.lamT_zero u ▸ hQ)
    rw [← Formalism.L2.Forms.lamT_zero u] at h2
    exact h2
  · intro z f f' g
    have e : (fun x => (z • f + f') (F.val0.eY x)) = z • (fun x => f (F.val0.eY x)) + fun x => f' (F.val0.eY x) := rfl
    simp only [e, map_add (f := _), LinearMap.map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply]
  · intro z f g g'
    have e : (fun x => (z • g + g') (F.val0.eY x)) = z • (fun x => g (F.val0.eY x)) + fun x => g' (F.val0.eY x) := rfl
    simp only [e, map_add (f := _), map_smul, smul_eq_mul]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeterssonStepZeroScalarFormsEqPosMulInnerStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl GlobalTheory.SeeSaw ValuativeRel IsLocalRing
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.petersson_stepZeroScalarForms_eq_pos_mul_inner : ∀ (D : D7) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (θ : InfFam D), IsInfFam θ → CoCpt (D.sp.X 0) → ∀ (vS : Vol (D.sp.X 0)) (y : (D.mem u).C.Y 0), ∃ c : ℝ, 0 < c ∧ ∀ φ ψ : D.what₂.Mu u, ∫ g in vS.𝓕, (GlobalTheory.Core.Mi.chart0 F).rd θ (D.eMu u φ).1 y g * star ((GlobalTheory.Core.Mi.chart0 F).rd θ (D.eMu u ψ).1 y g) ∂vS.μ = (c : ℂ) * inner ℂ ψ φ := by
  first | exact @GlobalTheory.StepZeroNorm.integral_rd_eq_inner | exact GlobalTheory.StepZeroNorm.integral_rd_eq_inner | (intros; apply GlobalTheory.StepZeroNorm.integral_rd_eq_inner <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPrimeOperatorsStepZeroScaleNorms
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl GlobalTheory.SeeSaw ValuativeRel IsLocalRing
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RamStepZero

theorem isLinearMap_of_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (f : E → E) (Q : ℝ)
    (h : ∀ x y, inner ℂ (f x) (f y) = (Q : ℂ) * inner ℂ x y) : IsLinearMap ℂ f := by
  constructor
  · intro x y
    have key : inner ℂ (f (x + y) - (f x + f y)) (f (x + y) - (f x + f y)) = 0 := by
      simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right, h]
      ring
    exact (sub_eq_zero.mp (inner_self_eq_zero.mp key))
  · intro a x
    have key : inner ℂ (f (a • x) - a • f x) (f (a • x) - a • f x) = 0 := by
      simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, h]
      ring
    exact (sub_eq_zero.mp (inner_self_eq_zero.mp key))

theorem norm_of_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (f : E → E) (Q : ℝ) (hQ : 0 ≤ Q)
    (h : ∀ x y, inner ℂ (f x) (f y) = (Q : ℂ) * inner ℂ x y) (x : E) : ‖f x‖ = Real.sqrt Q * ‖x‖ := by
  have h1 := h x x
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h1
  have h2 : ‖f x‖ ^ 2 = Q * ‖x‖ ^ 2 := by
    apply Complex.ofReal_injective
    push_cast
    exact h1
  rw [← Real.sqrt_sq (norm_nonneg (f x)), h2, Real.sqrt_mul hQ, Real.sqrt_sq (norm_nonneg x)]

end GlobalTheory.RamStepZero

namespace GlobalTheory.RamStepZero

theorem comm_of_sub_one_mul {R : Type*} [Ring R] (M N : R) (h1 : (M - 1) * (N - 1) = 0) (h2 : (N - 1) * (M - 1) = 0) :
    M * N = N * M := by
  have e1 : (M - 1) * (N - 1) = M * N - M - N + 1 := by noncomm_ring
  have e2 : (N - 1) * (M - 1) = N * M - N - M + 1 := by noncomm_ring
  have key : M * N - M - N + 1 = N * M - N - M + 1 := by rw [← e1, ← e2, h1, h2]
  calc M * N = (M * N - M - N + 1) + (M + N - 1) := by abel
    _ = (N * M - N - M + 1) + (M + N - 1) := by rw [key]
    _ = N * M := by abel

theorem placeIdem_mul {D : D7} {v v' : HeightOneSpectrum (𝓞 D.host.F)} {ε ε' : AF D.host.F}
    (h : IsPlaceIdem D v ε) (h' : IsPlaceIdem D v' ε') (hv : v ≠ v') : ε * ε' = 0 := by
  obtain ⟨α, rfl, h1, h0⟩ := h
  obtain ⟨α', rfl, h1', h0'⟩ := h'
  have hα : α * α' = 0 := by
    apply RestrictedProduct.ext
    intro w
    have e : evalV D.host.F w (α * α') = 0 := by
      rw [map_mul]
      by_cases hw : w = v
      · subst hw
        rw [h0' w hv, mul_zero]
      · rw [h0 w hw, zero_mul]
    exact e
  show ((0 : Ainf D.host.F), α) * ((0 : Ainf D.host.F), α') = 0
  rw [Prod.mk_mul_mk, mul_zero, hα]
  rfl

theorem gl_comm_other : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p p' : SplitPt D k) (S : HSp D) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (β : Frame p S n) (β' : Frame p' S n') (g : GL n k) (h : GL n' k), p.v ≠ p'.v → β.gl g * β'.gl h = β'.gl h * β.gl g := by
  intro D k _ _ _ _ p p' S n n' _ _ _ _ β β' g h hv
  obtain ⟨ε, hε, he⟩ := p.above
  obtain ⟨ε', hε', he'⟩ := p'.above
  have hεε : algebraMap (AF D.host.F) (AE D) ε * algebraMap (AF D.host.F) (AE D) ε' = 0 := by
    rw [← map_mul, placeIdem_mul hε hε' hv, map_zero]
  have hM := β.gl_supp g
  have hN := β'.gl_supp h
  unfold SuppAt at hM hN
  rw [he] at hM
  rw [he'] at hN
  set M := mt S (β.gl g)
  set N := mt S (β'.gl h)
  have h1 : (M - 1) * (N - 1) = 0 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [← hM i l, ← hN l j]
    calc _ = (algebraMap (AF D.host.F) (AE D) ε * algebraMap (AF D.host.F) (AE D) ε') * ((M - 1) i l * (N - 1) l j) := by ring
      _ = 0 := by rw [hεε, zero_mul]
  have h2 : (N - 1) * (M - 1) = 0 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [← hM l j, ← hN i l]
    calc _ = (algebraMap (AF D.host.F) (AE D) ε * algebraMap (AF D.host.F) (AE D) ε') * ((N - 1) i l * (M - 1) l j) := by ring
      _ = 0 := by rw [hεε, zero_mul]
  have hMN : M * N = N * M := comm_of_sub_one_mul M N h1 h2
  have hinj : Function.Injective (matHom S) := Subtype.val_injective
  apply hinj
  rw [map_mul, map_mul]
  exact Units.ext hMN

end GlobalTheory.RamStepZero

namespace GlobalTheory.RamStepZero

section
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {p p' : SplitPt D k} {S : HSp D} {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

theorem rep_comm (β : Frame p S n) (β' : Frame p' S n') (hv : p.v ≠ p'.v) (g : GL n k) (h : GL n' k) (f : GA D S → ℂ) :
    β.rep g (β'.rep h f) = β'.rep h (β.rep g f) := by
  funext x
  simp only [Frame.rep, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.funLeft_apply]
  rw [mul_assoc, gl_comm_other D k p p' S n n' β β' g h hv, ← mul_assoc]

theorem sOp_ramAt_other' (β : Frame p S n) (β' : Frame p' S n') (P : Pair k n) (P' : Pair k n') (q : Unif k)
    (χ : AddChar 𝓀[k] ℂ) (ε : 𝓀[k]ˣ) (φ₀ : GA D S → ℂ) (hv : p.v ≠ p'.v) (h : RamAt β' P' φ₀) :
    RamAt β' P' (sOp β P q χ ε φ₀) := by
  classical
  obtain ⟨φ, ⟨hEq, hM, hC⟩, rfl⟩ := h
  let T : (GA D S → ℂ) →ₗ[ℂ] (GA D S → ℂ) := ∑ P₁ ∈ withKer (ε • P).lat,
    χ (-cross q P₁ (ε • P)) • β.rep (Classical.epsilon fun g : GL n k => g • P = P₁)
  have hT : ∀ f, T f = ∑ P₁ ∈ withKer (ε • P).lat,
      χ (-cross q P₁ (ε • P)) • β.rep (Classical.epsilon fun g : GL n k => g • P = P₁) f := by
    intro f
    simp [T, LinearMap.sum_apply]
  have hTc : ∀ h' : GL n' k, ∀ f, T (β'.rep h' f) = β'.rep h' (T f) := by
    intro h' f
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hT, hT, map_sum]
    refine Finset.sum_congr rfl fun P₁ _ => ?_
    rw [map_smul, rep_comm β β' hv]
  refine ⟨fun P₂ => T (φ P₂), ⟨?_, ?_, ?_⟩, ?_⟩
  · intro g P₂
    show T (φ (g • P₂)) = β'.rep g (T (φ P₂))
    rw [hEq g P₂, hTc]
  · let _ := Fintype.ofFinite 𝓀[k]ˣ
    rw [mem_Mram] at hM ⊢
    intro P₂
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, hM P₂, map_zero]
  · intro P₂
    show IsContAut S (T (φ P₂))
    rw [hT]
    refine ⟨?_, ?_⟩
    · intro γ hγ x
      simp only [Finset.sum_apply, Pi.smul_apply]
      refine Finset.sum_congr rfl fun P₁ _ => ?_
      simp only [Frame.rep, MonoidHom.coe_mk, OneHom.coe_mk, LinearMap.funLeft_apply]
      rw [mul_assoc, (hC P₂).1 γ hγ]
    · rw [Finset.sum_fn]
      refine continuous_finsetSum _ fun P₁ _ => ?_
      simp only [Frame.rep, MonoidHom.coe_mk, OneHom.coe_mk]
      exact continuous_const.mul ((hC P₂).2.comp (continuous_mul_const _))
  · show T (φ P') = _
    rw [hT]
    rfl

end
end GlobalTheory.RamStepZero

namespace GlobalTheory.RamStepZero

theorem normStepZero : ∀ (D : D7) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (θ : InfFam D), IsInfFam θ → CoCpt (D.sp.X 0) → ∀ (vS : Vol (D.sp.X 0)) (y : (D.mem u).C.Y 0), ∃ c : ℝ, 0 < c ∧ ∀ φ ψ : D.what₂.Mu u, ∫ g in vS.𝓕, (GlobalTheory.Core.Mi.chart0 F).rd θ (D.eMu u φ).1 y g * star ((GlobalTheory.Core.Mi.chart0 F).rd θ (D.eMu u ψ).1 y g) ∂vS.μ = (c : ℂ) * inner ℂ ψ φ := GlobalTheory.T.petersson_stepZeroScalarForms_eq_pos_mul_inner

theorem sOp_ramAt_other : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p p' : SplitPt D k) (S : HSp D) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (β : Frame p S n) (β' : Frame p' S n') (P : Pair k n) (P' : Pair k n') (q : Unif k) (χ : AddChar 𝓀[k] ℂ) (ε : 𝓀[k]ˣ) (φ₀ : GA D S → ℂ), p.v ≠ p'.v → RamAt β' P' φ₀ → RamAt β' P' (sOp β P q χ ε φ₀) :=
  by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ β β' P P' q χ ε φ₀ hv h
  exact sOp_ramAt_other' β β' P P' q χ ε φ₀ hv h

section Fold

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}
  (p : ι → SplitPt D k) {S : HSp D} {n : Type} [Fintype n] [DecidableEq n] (β : ∀ i, Frame (p i) S n) (Q : ι → Pair k n)
  (q : Unif k) (χ' : ι → AddChar 𝓀[k] ℂ) (η : ι → 𝓀[k]ˣ)

theorem ramAt_foldr (i : ι) (f : GA D S → ℂ) : ∀ I : List ι, (∀ j ∈ I, (p j).v ≠ (p i).v) → RamAt (β i) (Q i) f →
    RamAt (β i) (Q i) (I.foldr (fun j g => sOp (β j) (Q j) q (χ' j) (η j) g) f)
  | [], _, h => h
  | j :: I, hI, h => by
    simp only [List.foldr_cons]
    exact sOp_ramAt_other D k (p j) (p i) S n n (β j) (β i) (Q j) (Q i) q (χ' j) (η j) _ (hI j (by simp))
      (ramAt_foldr i f I (fun j' hj' => hI j' (by simp [hj'])) h)

theorem inner_foldr (hRU : RamUnitary D) (hS : CoCpt S) (vS : Vol S) (χ : ι → AddChar k Circle)
    (hχ : ∀ i, HasConductor (χ i) 1) (hinj : Function.Injective fun i => (p i).v) :
    ∀ I : List ι, I.Nodup → ∀ f f' : GA D S → ℂ, (∀ i ∈ I, RamAt (β i) (Q i) f) → (∀ i ∈ I, RamAt (β i) (Q i) f') →
      ∫ g in vS.𝓕, I.foldr (fun j h => sOp (β j) (Q j) q (resChar (χ j) (hχ j) q) (η j) h) f g *
          star (I.foldr (fun j h => sOp (β j) (Q j) q (resChar (χ j) (hχ j) q) (η j) h) f' g) ∂vS.μ =
        (resCard k : ℂ) ^ (Fintype.card n * I.length) * ∫ g in vS.𝓕, f g * star (f' g) ∂vS.μ
  | [], _, f, f', _, _ => by simp
  | i :: I, hnd, f, f', hf, hf' => by
    have hnd' := List.nodup_cons.mp hnd
    have hne : ∀ j ∈ I, (p j).v ≠ (p i).v := fun j hj h => hnd'.1 (hinj h ▸ hj)
    simp only [List.foldr_cons]
    rw [hRU k (p i) n q (χ i) (hχ i) (η i) S hS vS (β i) (Q i) _ _
        (ramAt_foldr p β Q q (fun j => resChar (χ j) (hχ j) q) η i f I hne (hf i (by simp)))
        (ramAt_foldr p β Q q (fun j => resChar (χ j) (hχ j) q) η i f' I hne (hf' i (by simp))),
      inner_foldr hRU hS vS χ hχ hinj I hnd'.2 f f' (fun j hj => hf j (by simp [hj])) (fun j hj => hf' j (by simp [hj]))]
    rw [List.length_cons, Nat.mul_succ, pow_add]
    ring

end Fold

end GlobalTheory.RamStepZero

namespace GlobalTheory.RamStepZero

theorem opsStepZero_norm : ∀ (D : D7) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (θ : InfFam D), IsInfFam θ → RamUnitary D → CoCpt (D.sp.X 0) → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (q : Unif k) (χ : ι → AddChar k Circle) (hχ : ∀ i, HasConductor (χ i) 1) (β : ∀ i, Frame (p i) (D.sp.X 0) (Fin (D.sp.X 0).rank)) (Q : ι → Pair k (Fin (D.sp.X 0).rank)), I.Nodup → (Function.Injective fun i => (p i).v) → (∀ (φ : D.what₂.Mu u) y i, RamAt (β i) (Q i) ((GlobalTheory.Core.Mi.chart0 F).rd θ (D.eMu u φ).1 y)) → ∀ η : ι → 𝓀[k]ˣ, (∀ φ : D.what₂.Mu u, ∃ φ' : D.what₂.Mu u, ∀ y, (GlobalTheory.Core.Mi.chart0 F).rd θ (D.eMu u φ').1 y = I.foldr (fun i f => sOp (β i) (Q i) q (resChar (χ i) (hχ i) q) (η i) f) ((GlobalTheory.Core.Mi.chart0 F).rd θ (D.eMu u φ).1 y)) → ∃ (S : D.what₂.Mu u ≃ₗ[ℂ] D.what₂.Mu u) (r : ℝ), 0 < r ∧ (∀ φ, ‖S φ‖ = r * ‖φ‖) ∧ ∀ φ y, (GlobalTheory.Core.Mi.chart0 F).rd θ (D.eMu u (S φ)).1 y = I.foldr (fun i f => sOp (β i) (Q i) q (resChar (χ i) (hχ i) q) (η i) f) ((GlobalTheory.Core.Mi.chart0 F).rd θ (D.eMu u φ).1 y) := by
  intro D u F θ hθ hRU hcpt k _ _ _ _ ι p I q χ hχ β Q hnd hinj hram η hS
  classical
  obtain ⟨vS⟩ := GlobalTheory.Unf.Inhab.nonempty_vol (D.sp.X 0)
  by_cases hY : Nonempty ((D.mem u).C.Y 0)
  swap
  · exact ⟨LinearEquiv.refl ℂ _, 1, one_pos, fun φ => by simp, fun φ y => (hY ⟨y⟩).elim⟩
  obtain ⟨y₀⟩ := hY
  obtain ⟨c, hc, hN⟩ := normStepZero D u F θ hθ hcpt vS y₀
  choose Sf hSf using hS
  have hk : (0 : ℝ) < resCard k := by
    unfold resCard
    exact_mod_cast Nat.card_pos
  set Q0 : ℝ := (resCard k : ℝ) ^ (Fintype.card (Fin (D.sp.X 0).rank) * I.length) with hQ0def
  have hQ0 : 0 < Q0 := pow_pos hk _
  have hinner : ∀ φ ψ, inner ℂ (Sf φ) (Sf ψ) = (Q0 : ℂ) * inner ℂ φ ψ := by
    intro φ ψ
    have h1 := hN (Sf ψ) (Sf φ)
    rw [hSf ψ y₀, hSf φ y₀,
      inner_foldr p β Q q η hRU hcpt vS χ hχ hinj I hnd _ _ (fun i _ => hram ψ y₀ i) (fun i _ => hram φ y₀ i),
      hN ψ φ] at h1
    have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    rw [hQ0def]
    push_cast
    apply mul_left_cancel₀ hc'
    rw [← h1]
    ring
  have hlin := isLinearMap_of_inner Sf Q0 hinner
  let L : D.what₂.Mu u →ₗ[ℂ] D.what₂.Mu u := hlin.mk' Sf
  have hL : ∀ φ, L φ = Sf φ := fun φ => rfl
  have hnorm : ∀ φ, ‖Sf φ‖ = Real.sqrt Q0 * ‖φ‖ := norm_of_inner Sf Q0 hQ0.le hinner
  have hinjL : Function.Injective L := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    have h := hnorm a
    rw [← hL, ha, norm_zero] at h
    have hs : 0 < Real.sqrt Q0 := Real.sqrt_pos.mpr hQ0
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg a])
  refine ⟨LinearEquiv.ofInjectiveEndo L hinjL, Real.sqrt Q0, Real.sqrt_pos.mpr hQ0, fun φ => ?_, fun φ y => ?_⟩
  · rw [LinearEquiv.coe_ofInjectiveEndo, hL]
    exact hnorm φ
  · rw [LinearEquiv.coe_ofInjectiveEndo, hL]
    exact hSf φ y

end GlobalTheory.RamStepZero
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPrimeOperatorsStepZeroScaleNormsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl GlobalTheory.SeeSaw ValuativeRel IsLocalRing
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelPrime_operators_stepZero_scale_norms : ∀ (D : D7) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (θ : InfFam D), IsInfFam θ → RamUnitary D → CoCpt (D.sp.X 0) → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (p : ι → SplitPt D k) (I : List ι) (q : Unif k) (χ : ι → AddChar k Circle) (hχ : ∀ i, HasConductor (χ i) 1) (β : ∀ i, Frame (p i) (D.sp.X 0) (Fin (D.sp.X 0).rank)) (Q : ι → Pair k (Fin (D.sp.X 0).rank)), I.Nodup → (Function.Injective fun i => (p i).v) → (∀ (φ : D.what₂.Mu u) y i, RamAt (β i) (Q i) ((GlobalTheory.Core.Mi.chart0 F).rd θ (D.eMu u φ).1 y)) → ∀ η : ι → 𝓀[k]ˣ, (∀ φ : D.what₂.Mu u, ∃ φ' : D.what₂.Mu u, ∀ y, (GlobalTheory.Core.Mi.chart0 F).rd θ (D.eMu u φ').1 y = I.foldr (fun i f => sOp (β i) (Q i) q (resChar (χ i) (hχ i) q) (η i) f) ((GlobalTheory.Core.Mi.chart0 F).rd θ (D.eMu u φ).1 y)) → ∃ (S : D.what₂.Mu u ≃ₗ[ℂ] D.what₂.Mu u) (r : ℝ), 0 < r ∧ (∀ φ, ‖S φ‖ = r * ‖φ‖) ∧ ∀ φ y, (GlobalTheory.Core.Mi.chart0 F).rd θ (D.eMu u (S φ)).1 y = I.foldr (fun i f => sOp (β i) (Q i) q (resChar (χ i) (hχ i) q) (η i) f) ((GlobalTheory.Core.Mi.chart0 F).rd θ (D.eMu u φ).1 y) := by
  first | exact @GlobalTheory.RamStepZero.opsStepZero_norm | exact GlobalTheory.RamStepZero.opsStepZero_norm | (intros; apply GlobalTheory.RamStepZero.opsStepZero_norm <;> assumption)
end
