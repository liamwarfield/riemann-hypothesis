module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
public import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVSubRight
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmFiniteAdeleIntegralSeparatedComplete

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.EvenTheta

def IsLat (Λ : AddSubgroup ℂ) : Prop :=
  ∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧ Λ = AddSubgroup.closure {w₁, w₂}

def sqTh (Λ : AddSubgroup ℂ) (v z : ℂ) : ℂ := sgStar Λ (v + z) * sgStar Λ (v - z) / sgStar Λ v ^ 2

def AlgEnt (F : ℂ → ℂ) : Prop := Differentiable ℂ F ∧ ∀ n, coef1 F n ∈ Qbar

def IntSer {K : Type*} [NormedField K] (f : PowerSeries K) : Prop := ∀ n, ‖PowerSeries.coeff n f‖ ≤ 1

def BddSer {K : Type*} [NormedField K] (f : PowerSeries K) : Prop :=
  ∃ B : ℝ, ∀ n, ‖PowerSeries.coeff n f‖ ≤ B

def lineSer {K : Type*} [CommRing K] (e : PowerSeries K) (x : K) : PowerSeries K :=
  e - PowerSeries.C x * PowerSeries.X ^ 2

def IsWpSer {K : Type*} [CommRing K] (a b : K) (P : PowerSeries K) : Prop :=
  PowerSeries.constantCoeff P = 1 ∧
    (PowerSeries.X * PowerSeries.derivativeFun P - 2 * P) ^ 2 =
      4 * P ^ 3 - PowerSeries.C a * PowerSeries.X ^ 4 * P - PowerSeries.C b * PowerSeries.X ^ 6

def xAt {p : ℕ} [Fact p.Prime] (g : GL3Theta.G1 p) (v : ℂ) : ℂ_[p] :=
  ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ^ 2 * (lamC g.lam (wpF g.abelian₂ v) - g.C.r)

variable {Λ : AddSubgroup ℂ}

theorem IsLat.differentiable (h : IsLat Λ) : Differentiable ℂ (sgStar Λ) :=
  (GlobalTheory.OddTheta.sgStar_laws Λ h).1.1

theorem IsLat.sg_neg (h : IsLat Λ) (z : ℂ) : sgStar Λ (-z) = -sgStar Λ z :=
  (GlobalTheory.OddTheta.sgStar_laws Λ h).1.2.2.1 z

theorem IsLat.sg_eq_zero (h : IsLat Λ) (z : ℂ) : sgStar Λ z = 0 ↔ z ∈ Λ :=
  (GlobalTheory.OddTheta.sgStar_laws Λ h).2.1 z

theorem IsLat.sg_law (h : IsLat Λ) {ω : ℂ} (hω : ω ∈ Λ) (z : ℂ) :
    U1 Λ ω (sgStar Λ) z = (if ω / 2 ∈ Λ then 1 else -1) * sgStar Λ z :=
  (GlobalTheory.OddTheta.sgStar_laws Λ h).1.2.2.2 ω hω z

theorem IsLat.dense_compl (h : IsLat Λ) : Dense (Λ : Set ℂ)ᶜ := by
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair Λ h
  have : (Λ : Set ℂ) = (L.lattice : Set ℂ) := Set.ext fun z => hL z
  rw [this]
  exact GlobalTheory.dense_compl_lattice L

theorem IsLat.differentiable_sqTh (h : IsLat Λ) (v : ℂ) : Differentiable ℂ (sqTh Λ v) := by
  have := h.differentiable
  unfold sqTh
  fun_prop

theorem sqTh_neg (v z : ℂ) : sqTh Λ v (-z) = sqTh Λ v z := by
  simp only [sqTh, sub_neg_eq_add, ← sub_eq_add_neg, mul_comm]

theorem IsLat.sqTh_zero (h : IsLat Λ) {v : ℂ} (hv : v ∉ Λ) : sqTh Λ v 0 = 1 := by
  have := (h.sg_eq_zero v).not.2 hv
  simp only [sqTh, add_zero, sub_zero]
  field_simp

theorem IsLat.sqTh_eq_zero (h : IsLat Λ) {v : ℂ} (hv : v ∉ Λ) (z : ℂ) :
    sqTh Λ v z = 0 ↔ v + z ∈ Λ ∨ v - z ∈ Λ := by
  have := (h.sg_eq_zero v).not.2 hv
  simp [sqTh, this, h.sg_eq_zero]

theorem IsLat.sqTh_eq (h : IsLat Λ) {v z : ℂ} (hv : v ∉ Λ) (hz : z ∉ Λ) :
    sqTh Λ v z = sgStar Λ z ^ 2 * (wpF Λ z - wpF Λ v) := by
  have h0 := (h.sg_eq_zero v).not.2 hv
  have h1 := (GlobalTheory.OddTheta.sgStar_laws Λ h).2.2.2.1 v z hv hz
  rw [sqTh, div_eq_iff (pow_ne_zero 2 h0)]
  linear_combination h1

theorem IsLat.sqTh_sub (h : IsLat Λ) {v w : ℂ} (hv : v ∉ Λ) (hw : w ∉ Λ) (z : ℂ) :
    sqTh Λ v z = sqTh Λ w z + (wpF Λ w - wpF Λ v) * sgStar Λ z ^ 2 := by
  have h1 := (h.differentiable_sqTh v).continuous
  have h2 := (h.differentiable_sqTh w).continuous
  have h3 := h.differentiable.continuous
  refine congrFun (Continuous.ext_on h.dense_compl h1
    (g := fun z => sqTh Λ w z + (wpF Λ w - wpF Λ v) * sgStar Λ z ^ 2) (by fun_prop) fun z hz => ?_) z
  beta_reduce
  rw [h.sqTh_eq hv hz, h.sqTh_eq hw hz]
  ring

theorem IsLat.wp_eq_iff (h : IsLat Λ) {v w : ℂ} (hv : v ∉ Λ) (hw : w ∉ Λ) :
    wpF Λ w = wpF Λ v ↔ v + w ∈ Λ ∨ v - w ∈ Λ := by
  rw [← h.sqTh_eq_zero hv, h.sqTh_eq hv hw]
  simp [(h.sg_eq_zero w).not.2 hw, sub_eq_zero]

theorem IsLat.sqTh_mul (h : IsLat Λ) {v : ℂ} (hv : v ∉ Λ) (z : ℂ) :
    (U1 Λ v (sgStar Λ) 0 * U1 Λ (-v) (sgStar Λ) 0) * sqTh Λ v z =
      U1 Λ v (sgStar Λ) z * U1 Λ (-v) (sgStar Λ) z := by
  have h0 := (h.sg_eq_zero v).not.2 hv
  have e : ∀ z : ℂ, U1 Λ v (sgStar Λ) z * U1 Λ (-v) (sgStar Λ) z =
      -(sgStar Λ (v + z) * sgStar Λ (v - z)) *
        Complex.exp (-((Real.pi : ℂ) * v * (starRingEnd ℂ) v / (area Λ : ℂ))) := by
    intro z
    simp only [U1]
    rw [show z + -v = -(v - z) by ring, h.sg_neg, add_comm z v, mul_mul_mul_comm, ← Complex.exp_add]
    congr 1
    · ring
    · congr 1
      simp only [map_neg]
      ring
  rw [e, e, sqTh]
  simp only [add_zero, sub_zero]
  field_simp

end GlobalTheory.EvenTheta
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ActAApply
noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.FinWeil

def sgO (D : D7) : 𝓞 D.host.E →+* 𝓞 D.host.E := MulSemiringAction.toRingHom _ (𝓞 D.host.E) D.host.conj

theorem coe_sgO (D : D7) (r : 𝓞 D.host.E) : ((sgO D r : 𝓞 D.host.E) : D.host.E) = D.host.conj (r : D.host.E) := rfl

abbrev XA (D : D7) (N N' : ℕ) : Type := Matrix (Fin N') (Fin N) (AE D)

theorem smul_AE (D : D7) (r : 𝓞 D.host.E) (y : AE D) : r • y = inc D (r : D.host.E) * y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [TensorProduct.smul_tmul']
    simp [inc, Formalism.UG.inclE, Algebra.smul_def]
  | add x y hx hy => rw [smul_add, mul_add, hx, hy]

theorem ihE_mul (D : D7) (cc : Ideal (𝓞 D.host.K)) {s t : AE D} (hs : s ∈ OhE D) (ht : t ∈ IhE D cc) : s * t ∈ IhE D cc := by
  induction ht using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨c, hc, a, ha, s', hs', rfl⟩ := hy
    exact AddSubgroup.subset_closure ⟨c, hc, a, ha, s * s', mul_mem hs hs', by ring⟩
  | zero => simpa using zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [mul_neg]; exact neg_mem hx

def latA (D : D7) (cc : Ideal (𝓞 D.host.K)) (N N' : ℕ) : Submodule (𝓞 D.host.E) (XA D N N') where
  carrier := {ζ | ∀ i j, ζ i j ∈ IhE D cc}
  add_mem' := fun ha hb i j => add_mem (ha i j) (hb i j)
  zero_mem' := fun _ _ => zero_mem _
  smul_mem' := fun r ζ h i j => by
    rw [Matrix.smul_apply, smul_AE]
    exact ihE_mul D cc ((AdLattice.incl_mem_iff (F := ℚ) _).2 ⟨r, rfl⟩) (h i j)

theorem mem_latA {D : D7} {cc : Ideal (𝓞 D.host.K)} {N N' : ℕ} {ζ : XA D N N'} :
    ζ ∈ latA D cc N N' ↔ ∀ i j, ζ i j ∈ IhE D cc := Iff.rfl

def actA (D : D7) (N N' : ℕ) : GA D N × GA D N' →* Module.End (𝓞 D.host.E) (XA D N N') where
  toFun u :=
    { toFun := fun ζ => ((u.2 : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) * ζ *
        (((u.1 : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))
      map_add' := fun x y => by rw [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun r x => by
        have h : ∀ {a b : ℕ} (y : Matrix (Fin a) (Fin b) (AE D)), r • y = inc D (r : D.host.E) • y := fun y => by
          ext i j
          rw [Matrix.smul_apply, Matrix.smul_apply, smul_AE, smul_eq_mul]
        rw [RingHom.id_apply, h, h, Matrix.mul_smul, Matrix.smul_mul] }
  map_one' := by
    ext1 ζ
    simp
  map_mul' u v := by
    ext1 ζ
    simp [Matrix.mul_assoc]

theorem actA_apply {D : D7} {N N' : ℕ} (g : GA D N) (g' : GA D N') (ζ : XA D N N') :
    actA D N N' (g, g') ζ = ((g' : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) * ζ *
      (((g : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) := rfl

theorem wd_add {D : D7} {T : Tor D} {N N' : ℕ} (x : VC D N N') (F G : VC D N N' → ℂ) :
    Wd D T x (F + G) = Wd D T x F + Wd D T x G := by
  funext z
  simp only [Wd, U, Pi.add_apply]
  ring

theorem wd_smul {D : D7} {T : Tor D} {N N' : ℕ} (x : VC D N N') (c : ℂ) (F : VC D N N' → ℂ) :
    Wd D T x (c • F) = c • Wd D T x F := by
  funext z
  simp only [Wd, U, Pi.smul_apply, smul_eq_mul]
  ring

def TTs (D : D7) (T : Tor D) (N N' : ℕ) : Submodule ℂ (VC D N N' → ℂ) where
  carrier := TT D T N N'
  add_mem' := by
    rintro F G ⟨hF, m, hm, h⟩ ⟨hG, n, hn, h'⟩
    refine ⟨hF.add hG, m * n, Nat.mul_pos hm hn, fun x hx => ?_⟩
    rw [wd_add]
    congr 1
    · rw [mul_smul]; exact h _ (AddSubgroup.nsmul_mem _ hx n)
    · rw [mul_comm, mul_smul]; exact h' _ (AddSubgroup.nsmul_mem _ hx m)
  zero_mem' := ⟨differentiable_const _, 1, one_pos, fun x _ => by funext z; simp [Wd, U]⟩
  smul_mem' := by
    rintro c F ⟨hF, m, hm, h⟩
    exact ⟨hF.const_smul c, m, hm, fun x hx => by rw [wd_smul, h x hx]⟩

def psi0 (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (a : D.host.E) : ℂ :=
  ee (-(‖δ‖ ^ 2 / area (lamOf D cc δ) * (∑ τ, embT D τ a).im))

def IsPsi (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (ψ : AE D → ℂ) : Prop :=
  (∀ x y, ψ (x + y) = ψ x * ψ y) ∧ ψ 0 = 1 ∧ (∀ a, ψ (inc D a) = psi0 D cc δ a) ∧ (∀ y, ψ (y + sgA D y) = 1) ∧
    ∃ m : ℕ, 0 < m ∧ ∀ s ∈ OhE D, ψ ((m : AE D) * s) = 1

def gamA {D : D7} (ψ : AE D → ℂ) {N N' : ℕ} (ζ η : XA D N N') : ℂ := ψ (∑ i, ∑ j, ζ i j * sgA D (η i j))

def IsModel (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N N' : ℕ) (w : 𝓞 D.host.E) (γ : XA D N N' → XA D N N' → ℂ)
    (WA : XA D N N' → TTs D (tor0 D cc δ) N N' →ₗ[ℂ] TTs D (tor0 D cc δ) N N') : Prop :=
  IsHeis (sgO D) w γ WA ∧ SelfDual γ (latA D cc N N') ∧
  (∀ u ζ η, γ (actA D N N' u ζ) (actA D N N' u η) = γ ζ η) ∧
  (∀ (z : Matrix (Fin N') (Fin N) D.host.E) (F : TTs D (tor0 D cc δ) N N'),
    (WA (z.map (inc D)) F : VC D N N' → ℂ) = Wd D (tor0 D cc δ) (pt D (tor0 D cc δ) δ z) F) ∧
  ∀ ζ F, ∃ m : ℕ, 0 < m ∧ ∀ a ∈ latA D cc N N', WA (ζ + m • a) F = WA ζ F

end GlobalTheory.FinWeil
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HESmulRight
noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.InertSign

abbrev Lat (D : D7) (n : ℕ) : Type := Submodule (𝓞 D.host.E) (Fin n → D.host.E)

def hE (D : D7) {n : ℕ} (x y : Fin n → D.host.E) : D.host.E := ∑ i, x i * D.host.conj (y i)

def IntE (D : D7) (e : D.host.E) : Prop := e ∈ (algebraMap (𝓞 D.host.E) D.host.E).range

def sgO (D : D7) : 𝓞 D.host.E →+* 𝓞 D.host.E :=
  MulSemiringAction.toRingHom (D.host.E ≃ₐ[ℚ] D.host.E) (𝓞 D.host.E) D.host.conj

theorem sgO_coe (D : D7) (a : 𝓞 D.host.E) : ((sgO D a : 𝓞 D.host.E) : D.host.E) = D.host.conj a := rfl

theorem conj_conj (D : D7) (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  letI := D.host.cmStar
  rw [← AdLattice.star_eq_conj, ← AdLattice.star_eq_conj]
  exact star_star x

theorem sgO_sgO (D : D7) (a : 𝓞 D.host.E) : sgO D (sgO D a) = a :=
  Subtype.ext (conj_conj D a)

theorem embT_conj (D : D7) (τ : D.what₂.Tau) (x : D.host.E) :
    embT D τ (D.host.conj x) = (starRingEnd ℂ) (embT D τ x) := by
  letI := D.host.isCMField_hostE
  rw [← AdLattice.star_eq_conj]
  exact NumberField.IsCMField.complexEmbedding_complexConj D.host.E (embT D τ) x

theorem conj_hE (D : D7) {n : ℕ} (x y : Fin n → D.host.E) : D.host.conj (hE D x y) = hE D y x := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hE, map_sum, map_mul, conj_conj, mul_comm]

theorem hE_add_left (D : D7) {n : ℕ} (x x' y : Fin n → D.host.E) : hE D (x + x') y = hE D x y + hE D x' y := by
  simp only [hE, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem hE_add_right (D : D7) {n : ℕ} (x y y' : Fin n → D.host.E) : hE D x (y + y') = hE D x y + hE D x y' := by
  simp only [hE, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]

theorem hE_smul_left (D : D7) {n : ℕ} (a : D.host.E) (x y : Fin n → D.host.E) : hE D (a • x) y = a * hE D x y := by
  simp only [hE, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem hE_smul_right (D : D7) {n : ℕ} (a : D.host.E) (x y : Fin n → D.host.E) :
    hE D x (a • y) = D.host.conj a * hE D x y := by
  simp only [hE, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, map_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem IntE.conj {D : D7} {e : D.host.E} (h : IntE D e) : IntE D (D.host.conj e) := by
  obtain ⟨a, rfl⟩ := h
  exact ⟨sgO D a, rfl⟩

theorem sd_iff (D : D7) {n : ℕ} (L : Lat D n) : SD D L ↔
    L.FG ∧ Submodule.span D.host.E (L : Set (Fin n → D.host.E)) = ⊤ ∧ ∀ y, y ∈ L ↔ ∀ x ∈ L, IntE D (hE D y x) := by
  unfold SD IsSDLat
  simp only [stdH, AdLattice.star_eq_conj, IntE, hE, mul_comm]

def nbM (D : D7) {n : ℕ} (B : Lat D n) (x : Fin n → D.host.E) : Lat D n where
  carrier := {y | y ∈ B ∧ IntE D (hE D y x)}
  add_mem' := fun {a b} ha hb => ⟨B.add_mem ha.1 hb.1, by rw [hE_add_left]; exact add_mem ha.2 hb.2⟩
  zero_mem' := ⟨B.zero_mem, by simp only [hE, Pi.zero_apply, zero_mul, Finset.sum_const_zero]; exact zero_mem _⟩
  smul_mem' := fun c a ha => ⟨B.smul_mem c ha.1, by
    rw [← algebraMap_smul D.host.E c a, hE_smul_left]; exact mul_mem ⟨c, rfl⟩ ha.2⟩

theorem mem_nbM {D : D7} {n : ℕ} {B : Lat D n} {x y : Fin n → D.host.E} :
    y ∈ nbM D B x ↔ y ∈ B ∧ IntE D (hE D y x) := Iff.rfl

def nbr (D : D7) {n : ℕ} (B : Lat D n) (x : Fin n → D.host.E) : Lat D n :=
  nbM D B x ⊔ Submodule.span (𝓞 D.host.E) {x}

def NbD (D : D7) {n : ℕ} (P : Ideal (𝓞 D.host.E)) (B : Lat D n) (x : Fin n → D.host.E) : Prop :=
  x ∉ B ∧ (∀ p ∈ P, p • x ∈ B) ∧ IntE D (hE D x x)

def Tri (D : D7) {n : ℕ} (P : Ideal (𝓞 D.host.E)) (A B C : Lat D n) : Prop :=
  SD D A ∧ SD D B ∧ SD D C ∧ ∃ (M : Lat D n) (b x : Fin n → D.host.E),
    A = M ⊔ Submodule.span (𝓞 D.host.E) {b + x} ∧ B = M ⊔ Submodule.span (𝓞 D.host.E) {b} ∧
    C = M ⊔ Submodule.span (𝓞 D.host.E) {x} ∧ (∀ p ∈ P, p • b ∈ M ∧ p • x ∈ M) ∧ ¬ IntE D (hE D b x)

def Bet (D : D7) {n : ℕ} (L₁ L₂ L₃ : Lat D n) : Prop := L₂ ≤ (L₁ ⊓ L₂) ⊔ (L₂ ⊓ L₃) ∧ L₁ ⊓ L₃ ≤ L₂

def cT (D : D7) {m n : ℕ} (s : Matrix (Fin m) (Fin n) D.host.E) : Matrix (Fin n) (Fin m) D.host.E :=
  (s.map D.host.conj).transpose

def SAt (D : D7) {n : ℕ} (q : ℕ) (s : Matrix (Fin n) (Fin n) D.host.E) (L L₁ : Lat D n) : Prop :=
  ∃ m : ℕ, Nat.Coprime m q ∧ (∀ v ∈ L, (m : D.host.E) • s.mulVec v ∈ L₁) ∧
    ∀ v ∈ L₁, (m : D.host.E) • (cT D s).mulVec v ∈ L

def Iid (D : D7) (cc : Ideal (𝓞 D.host.K)) : Submodule (𝓞 D.host.E) D.host.E :=
  Submodule.span (𝓞 D.host.E) {t | ∃ c ∈ cc, ∃ a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E),
    t = ((c : D.host.K) : D.host.E) * a}

def RL (D : D7) (cc : Ideal (𝓞 D.host.K)) {N N' : ℕ} (L : Lat D N) (L' : Lat D N') :
    Submodule (𝓞 D.host.E) (Matrix (Fin N') (Fin N) D.host.E) :=
  Submodule.span (𝓞 D.host.E) {z | ∃ t ∈ Iid D cc, ∃ A ∈ homL D L L', z = t • A}

def bc (D : D7) (T : Tor D) {N N' : ℕ} (x y : VC D N N') : ℂ :=
  Complex.exp (-(Real.pi : ℂ) * Complex.I *
    ((Real.sqrt D.host.d * (Hf D T x y).re + (Hf D T x y).im : ℝ) : ℂ))

theorem Hf_add_left (D : D7) (T : Tor D) {N N' : ℕ} (x x' y : VC D N N') :
    Hf D T (x + x') y = Hf D T x y + Hf D T x' y := by
  simp only [Hf, Pi.add_apply, add_mul, Finset.sum_add_distrib, add_div]

theorem Hf_add_right (D : D7) (T : Tor D) {N N' : ℕ} (x y y' : VC D N N') :
    Hf D T x (y + y') = Hf D T x y + Hf D T x y' := by
  simp only [Hf, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib, add_div]

theorem Hf_conj (D : D7) (T : Tor D) {N N' : ℕ} (x y : VC D N N') :
    (starRingEnd ℂ) (Hf D T x y) = Hf D T y x := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Hf, map_div₀, map_sum, map_mul, Complex.conj_conj, Complex.conj_ofReal, mul_comm]

theorem bc_ne_zero (D : D7) (T : Tor D) {N N' : ℕ} (x y : VC D N N') : bc D T x y ≠ 0 := Complex.exp_ne_zero _

theorem bc_add_left (D : D7) (T : Tor D) {N N' : ℕ} (x x' y : VC D N N') :
    bc D T (x + x') y = bc D T x y * bc D T x' y := by
  rw [bc, bc, bc, ← Complex.exp_add, Hf_add_left, Complex.add_re, Complex.add_im]
  congr 1; push_cast; ring

theorem bc_add_right (D : D7) (T : Tor D) {N N' : ℕ} (x y y' : VC D N N') :
    bc D T x (y + y') = bc D T x y * bc D T x y' := by
  rw [bc, bc, bc, ← Complex.exp_add, Hf_add_right, Complex.add_re, Complex.add_im]
  congr 1; push_cast; ring

theorem bc_zero_left (D : D7) (T : Tor D) {N N' : ℕ} (y : VC D N N') : bc D T 0 y = 1 := by
  have h := bc_add_left D T 0 0 y
  rw [add_zero] at h
  exact (mul_eq_left₀ (bc_ne_zero D T 0 y)).1 h.symm

theorem bc_zero_right (D : D7) (T : Tor D) {N N' : ℕ} (x : VC D N N') : bc D T x 0 = 1 := by
  have h := bc_add_right D T x 0 0
  rw [add_zero] at h
  exact (mul_eq_left₀ (bc_ne_zero D T x 0)).1 h.symm

theorem bc_comm (D : D7) (T : Tor D) {N N' : ℕ} (x y : VC D N N') :
    bc D T x y = Complex.exp (-(2 * Real.pi * Complex.I) * ((Hf D T x y).im : ℂ)) * bc D T y x := by
  rw [bc, bc, ← Complex.exp_add, ← Hf_conj D T x y, Complex.conj_re, Complex.conj_im]
  congr 1; push_cast; ring

theorem Wd_Wd (D : D7) (T : Tor D) {N N' : ℕ} (x y : VC D N N') (F : VC D N N' → ℂ) :
    Wd D T x (Wd D T y F) = bc D T x y • Wd D T (x + y) F := by
  funext z
  have hc := Hf_conj D T x y
  have hre : (Hf D T y x).re = (Hf D T x y).re := by rw [← hc, Complex.conj_re]
  have h2 : Hf D T y x = Hf D T x y - 2 * Complex.I * ((Hf D T x y).im : ℂ) := by
    rw [← hc]; apply Complex.ext <;> simp <;> ring
  simp only [Wd, U, wdPh, ee, bc, qH, Pi.smul_apply, smul_eq_mul, Hf_add_left, Hf_add_right, Complex.add_re, hre,
    add_assoc]
  rw [h2]
  have key : ∀ a b c d' e f g' : ℂ, ∀ v : ℂ, a + b + c + d' = e + f + g' →
      Complex.exp a * (Complex.exp b * (v * Complex.exp c) * Complex.exp d') =
        Complex.exp e * (Complex.exp f * (v * Complex.exp g')) := by
    intro a b c d' e f g' v h
    have := congrArg Complex.exp h
    simp only [Complex.exp_add] at this
    linear_combination v * this
  apply key
  push_cast; ring

theorem Wd_add (D : D7) (T : Tor D) {N N' : ℕ} (x : VC D N N') (F G : VC D N N' → ℂ) :
    Wd D T x (F + G) = Wd D T x F + Wd D T x G := by
  funext z; simp only [Wd, U, Pi.add_apply]; ring

theorem Wd_smul (D : D7) (T : Tor D) {N N' : ℕ} (x : VC D N N') (a : ℂ) (F : VC D N N' → ℂ) :
    Wd D T x (a • F) = a • Wd D T x F := by
  funext z; simp only [Wd, U, Pi.smul_apply, smul_eq_mul]; ring

def Nice (D : D7) (T : Tor D) {N N' : ℕ} (A : AddSubgroup (VC D N N')) : Prop :=
  (∀ x ∈ A, ∀ F, Wd D T x F = fun z => al D T x * U D T x F z) ∧ (∀ x ∈ A, ∀ y ∈ A, bc D T x y = 1) ∧
    ∀ x, (∀ y ∈ A, bc D T x y = bc D T y x) → x ∈ A

theorem Nice.mem_ThSp {D : D7} {T : Tor D} {N N' : ℕ} {A : AddSubgroup (VC D N N')} (h : Nice D T A)
    (F : VC D N N' → ℂ) : F ∈ ThSp D T A ↔ Differentiable ℂ F ∧ ∀ x ∈ A, Wd D T x F = F := by
  refine and_congr_right fun _ => forall₂_congr fun x hx => ?_
  rw [h.1 x hx, funext_iff]

theorem Nice.Iop_eq {D : D7} {T : Tor D} {N N' : ℕ} (A : AddSubgroup (VC D N N')) {B : AddSubgroup (VC D N N')}
    (h : Nice D T B) (F : VC D N N' → ℂ) :
    Iop D T A B F = fun z => ((Real.sqrt ((A.addSubgroupOf B).index : ℝ))⁻¹ : ℂ) *
      ∑ᶠ q : B ⧸ A.addSubgroupOf B, Wd D T ((Quotient.out q : B) : VC D N N') F z := by
  funext z
  simp only [Iop]
  congr 1
  exact finsum_congr fun q => by rw [h.1 _ (Quotient.out q : B).2]

def Trip (D : D7) (T : Tor D) {N N' : ℕ} (A₁ A₂ A₃ : AddSubgroup (VC D N N')) (e : VC D N N' → ℂ) (μ : ℂ) : Prop :=
  Nice D T A₁ ∧ Nice D T A₂ ∧ Nice D T A₃ ∧ (A₁.addSubgroupOf A₂).index ≠ 0 ∧ (A₂.addSubgroupOf A₃).index ≠ 0 ∧
    (A₁.addSubgroupOf A₃).index ≠ 0 ∧ e ∈ ThSp D T A₁ ∧ e ≠ 0 ∧ μ ^ 8 = 1 ∧
    Iop D T A₂ A₃ (Iop D T A₁ A₂ e) = fun z => μ * Iop D T A₁ A₃ e z

def Dist {V : Type} [AddCommGroup V] (A₁ A₂ A₃ : AddSubgroup V) : Prop :=
  ∀ x ∈ A₂, ∀ y ∈ A₃, x + y ∈ A₁ → x ∈ (A₁ ⊓ A₂) ⊔ (A₂ ⊓ A₃)

def TriDat (D : D7) (T : Tor D) {N N' : ℕ} (A₁ A₂ A₃ : AddSubgroup (VC D N N')) (P : Ideal (𝓞 D.host.E)) (r : ℕ) : Prop :=
  ∃ (X Y : Fin r → 𝓞 D.host.E →+ VC D N N') (φ : Fin r → 𝓞 D.host.E →+ ℂ),
    (∀ i j a a', Hf D T (Y i a') (X j a) = if i = j then φ i (a' * sgO D a) else 0) ∧
    (∀ i a, X i a ∈ A₂ ∧ Y i a ∈ A₃ ∧ X i a + Y i a ∈ A₁) ∧
    (∀ i, ∀ p ∈ P, X i p ∈ A₁ ⊓ A₃ ∧ Y i p ∈ A₁ ⊓ A₂) ∧
    (∀ z ∈ A₂, ∃ a : Fin r → 𝓞 D.host.E, z - ∑ i, X i (a i) ∈ A₁ ⊓ A₃) ∧
    (∀ z ∈ A₃, ∃ a : Fin r → 𝓞 D.host.E, z - ∑ i, Y i (a i) ∈ A₁ ⊓ A₂) ∧
    (∀ a : Fin r → 𝓞 D.host.E, ∑ i, X i (a i) ∈ A₁ → ∀ i, a i ∈ P) ∧
    (∀ a : Fin r → 𝓞 D.host.E, ∑ i, Y i (a i) ∈ A₂ → ∀ i, a i ∈ P)

end GlobalTheory.InertSign
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CdScaleIsTrueScale
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory NumberField GlobalTheory.Mem.Vol Matrix Topology

namespace GlobalTheory.Mem.Vol.Scale

variable {n P Q : ℕ} {ε : Fin n → Bool}

def Sorts (ε : Fin n → Bool) (e : Fin P ⊕ Fin Q ≃ Fin n) : Prop :=
  (∀ i, ε (e (Sum.inl i)) = true) ∧ ∀ j, ε (e (Sum.inr j)) = false

theorem Sorts.reindex_Jpq {e : Fin P ⊕ Fin Q ≃ Fin n} (h : Sorts ε e) :
    Matrix.reindex e e (Formalism.UG.Jpq P Q) = Formalism.REAL.Jm ε := by
  ext i j
  obtain ⟨a, rfl⟩ := e.surjective i
  obtain ⟨b, rfl⟩ := e.surjective j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Formalism.REAL.Jm,
    Matrix.diagonal_apply, EmbeddingLike.apply_eq_iff_eq, Formalism.UG.Jpq]
  rcases a with a | a <;> rcases b with b | b <;> simp [Matrix.one_apply, h.1, h.2]
  split_ifs <;> simp

theorem Sorts.card_true {e : Fin P ⊕ Fin Q ≃ Fin n} (h : Sorts ε e) : Nat.card {a // ε a = true} = P := by
  have : Function.Bijective fun i : Fin P => (⟨e (Sum.inl i), h.1 i⟩ : {a // ε a = true}) := by
    refine ⟨fun i j hij => Sum.inl_injective (e.injective (congrArg Subtype.val hij)), ?_⟩
    rintro ⟨a, ha⟩
    obtain ⟨b | b, rfl⟩ := e.surjective a
    · exact ⟨b, rfl⟩
    · rw [h.2] at ha; cases ha
  rw [← Nat.card_eq_of_bijective _ this]; simp

theorem Sorts.add_eq (e : Fin P ⊕ Fin Q ≃ Fin n) : P + Q = n := by
  simpa using Fintype.card_congr e

theorem exists_sorts (ε : Fin n → Bool) : ∃ (P Q : ℕ) (e : Fin P ⊕ Fin Q ≃ Fin n), Sorts ε e := by
  refine ⟨_, _, (Equiv.sumCongr (Fintype.equivFin {a // ε a = true}).symm
    (Fintype.equivFin {a // ¬ ε a = true}).symm).trans (Equiv.sumCompl fun a => ε a = true), fun i => ?_, fun j => ?_⟩
  · exact ((Fintype.equivFin {a // ε a = true}).symm i).2
  · exact Bool.eq_false_iff.2 ((Fintype.equivFin {a // ¬ ε a = true}).symm j).2

def reindexUnits (e : Fin P ⊕ Fin Q ≃ Fin n) :
    GL (Fin P ⊕ Fin Q) ℂ ≃ₜ* (Matrix (Fin n) (Fin n) ℂ)ˣ where
  toMulEquiv := Units.mapEquiv (Matrix.reindexAlgEquiv ℂ ℂ e).toMulEquiv
  continuous_toFun := Units.continuous_map
    (f := ((Matrix.reindexAlgEquiv ℂ ℂ e).toMulEquiv.toMonoidHom))
    (continuous_id.matrix_reindex _ _)
  continuous_invFun := Units.continuous_map
    (f := ((Matrix.reindexAlgEquiv ℂ ℂ e).toMulEquiv.symm.toMonoidHom))
    ((continuous_id.matrix_reindex e.symm e.symm).congr fun _ => rfl)

theorem reindexUnits_val (e : Fin P ⊕ Fin Q ≃ Fin n) (g : GL (Fin P ⊕ Fin Q) ℂ) :
    (reindexUnits e g : Matrix (Fin n) (Fin n) ℂ) =
      Matrix.reindex e e (g : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) := rfl

theorem Sorts.mem_iff {e : Fin P ⊕ Fin Q ≃ Fin n} (h : Sorts ε e) (g : GL (Fin P ⊕ Fin Q) ℂ) :
    reindexUnits e g ∈ Formalism.REAL.UJ ε ↔ g ∈ Formalism.UG.Upq P Q := by
  change Formalism.REAL.inUJ ε (reindexUnits e g : Matrix (Fin n) (Fin n) ℂ) ↔
    (g : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ).conjTranspose * Formalism.UG.Jpq P Q *
      (g : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) = Formalism.UG.Jpq P Q
  rw [Formalism.REAL.inUJ, reindexUnits_val, ← h.reindex_Jpq, Matrix.conjTranspose_reindex]
  rw [← (Matrix.reindex (α := ℂ) e e).injective.eq_iff]
  simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]

def Sorts.equiv {e : Fin P ⊕ Fin Q ≃ Fin n} (h : Sorts ε e) : UpqT P Q ≃ₜ* Formalism.REAL.UJ ε where
  toFun g := ⟨reindexUnits e (g : Formalism.UG.Upq P Q).1, (h.mem_iff _).2 (g : Formalism.UG.Upq P Q).2⟩
  invFun k := (⟨(reindexUnits e).symm k.1, (h.mem_iff _).1 (by simpa using k.2)⟩ : Formalism.UG.Upq P Q)
  left_inv g := Subtype.ext ((reindexUnits e).symm_apply_apply _)
  right_inv k := Subtype.ext ((reindexUnits e).apply_symm_apply _)
  map_mul' g k := Subtype.ext (map_mul (reindexUnits e) _ _)
  continuous_toFun := ((reindexUnits e).continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((reindexUnits e).symm.continuous.comp continuous_subtype_val).subtype_mk _

theorem Sorts.umat_equiv {e : Fin P ⊕ Fin Q ≃ Fin n} (h : Sorts ε e) (g : UpqT P Q) :
    umat (h.equiv g) = Matrix.reindex e e (UpqT.mat g) := rfl

theorem umat_injective : Function.Injective (umat : Formalism.REAL.UJ ε → _) :=
  fun _ _ h => Subtype.ext (Units.ext h)

theorem Sorts.set_eq {e : Fin P ⊕ Fin Q ≃ Fin n} (h : Sorts ε e) (A : Set (Formalism.REAL.UJ ε)) :
    {g | ∃ a ∈ A, umat a = Matrix.reindex e e (UpqT.mat g)} = h.equiv ⁻¹' A := by
  ext g
  constructor
  · rintro ⟨a, ha, hg⟩
    rw [← h.umat_equiv] at hg
    rw [Set.mem_preimage, ← umat_injective hg]
    exact ha
  · intro hg
    exact ⟨_, hg, rfl⟩

theorem Sorts.exists_conj {e e' : Fin P ⊕ Fin Q ≃ Fin n} (h : Sorts ε e) (h' : Sorts ε e') :
    ∃ u : UpqT P Q, ∀ g, h'.equiv g = h.equiv (u * g * u⁻¹) := by
  set σ : Fin P ⊕ Fin Q ≃ Fin P ⊕ Fin Q := e.trans e'.symm with hσ
  have hJ : (Formalism.UG.Jpq P Q).submatrix σ σ = Formalism.UG.Jpq P Q := by
    apply (Matrix.reindex (α := ℂ) e e).injective
    rw [h.reindex_Jpq, ← h'.reindex_Jpq]
    ext i j
    simp [hσ]
  have hmem : (1 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ).submatrix σ id ∈
      Set.range (UpqT.mat (P := P) (Q := Q)) := by
    rw [GlobalTheory.UpqTopology.range_mat]
    change _ = _
    rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_one]
    conv_lhs => rw [← hJ]
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
    simp
  obtain ⟨u, hu⟩ := hmem
  refine ⟨u, fun g => ?_⟩
  rw [← h.equiv.symm_apply_eq, eq_mul_inv_iff_mul_eq]
  apply GlobalTheory.UpqTopology.isClosedEmbedding_mat.injective
  have h1 : UpqT.mat (h.equiv.symm (h'.equiv g)) = (UpqT.mat g).submatrix σ σ := by
    apply (Matrix.reindex (α := ℂ) e e).injective
    rw [← h.umat_equiv, h.equiv.apply_symm_apply, h'.umat_equiv]
    ext i j
    simp [hσ]
  change UpqT.mat (h.equiv.symm (h'.equiv g)) * UpqT.mat u = UpqT.mat u * UpqT.mat g
  rw [h1, hu, Matrix.submatrix_mul_equiv, Matrix.mul_one]
  have := Matrix.submatrix_mul_equiv (1 : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) (UpqT.mat g) σ
    (Equiv.refl _) id
  simpa using this.symm

theorem Sorts.measurable_equiv {e : Fin P ⊕ Fin Q ≃ Fin n} (h : Sorts ε e) : Measurable h.equiv := by
  haveI : BorelSpace (UpqT P Q) := ⟨rfl⟩
  exact h.equiv.continuous.measurable

theorem Sorts.map_eq (cd : CDHaar) {P' Q' : ℕ} {e : Fin P ⊕ Fin Q ≃ Fin n} {e' : Fin P' ⊕ Fin Q' ≃ Fin n}
    (h : Sorts ε e) (h' : Sorts ε e') : (cd.cd P' Q').map h'.equiv = (cd.cd P Q).map h.equiv := by
  obtain rfl : P = P' := h.card_true.symm.trans h'.card_true
  obtain rfl : Q = Q' := by
    have h1 := Sorts.add_eq e
    have h2 := Sorts.add_eq e'
    omega
  haveI : IsTopologicalGroup (UpqT P Q) := inferInstanceAs (IsTopologicalGroup (Formalism.UG.Upq P Q))
  haveI : BorelSpace (UpqT P Q) := ⟨rfl⟩
  haveI := cd.haar P Q
  haveI := GlobalTheory.UpqHaarRight.isMulRightInvariant P Q _ (cd.haar P Q)
  obtain ⟨u, hu⟩ := h.exists_conj h'
  have : (h'.equiv : UpqT P Q → Formalism.REAL.UJ ε) = h.equiv ∘ (fun g => g * u⁻¹) ∘ fun g => u * g := funext hu
  rw [this, ← Measure.map_map h.measurable_equiv ((measurable_mul_const _).comp (measurable_const_mul _)),
    ← Measure.map_map (measurable_mul_const _) (measurable_const_mul _), map_mul_left_eq_self,
    map_mul_right_eq_self]

theorem Sorts.exists_scale (cd : CDHaar) {e : Fin P ⊕ Fin Q ≃ Fin n} (h : Sorts ε e) :
    ∃ c : NNReal, 0 < c ∧ (cd.cd P Q).map h.equiv = (c : ENNReal) • Formalism.REAL.muG ε := by
  haveI : IsTopologicalGroup (UpqT P Q) := inferInstanceAs (IsTopologicalGroup (Formalism.UG.Upq P Q))
  haveI : BorelSpace (UpqT P Q) := ⟨rfl⟩
  haveI := cd.haar P Q
  haveI : ((cd.cd P Q).map h.equiv).IsHaarMeasure := h.equiv.isHaarMeasure_map _
  exact ⟨_, Measure.haarScalarFactor_pos_of_isHaarMeasure _ _,
    Measure.isMulLeftInvariant_eq_smul ((cd.cd P Q).map h.equiv) (Formalism.REAL.muG ε)⟩

theorem exists_cdScaleIs (cd : CDHaar) :
    ∃ sc : ∀ n : ℕ, (Fin n → Bool) → NNReal, (∀ n ε, 0 < sc n ε) ∧ CdScaleIs cd sc := by
  choose P Q e he using fun (n : ℕ) (ε : Fin n → Bool) => exists_sorts ε
  choose sc hpos hsc using fun (n : ℕ) (ε : Fin n → Bool) => (he n ε).exists_scale cd
  refine ⟨sc, hpos, fun n ε P' Q' e' h1 h2 A hA => ?_⟩
  have h' : Sorts ε e' := ⟨h1, h2⟩
  rw [h'.set_eq, ← Measure.map_apply h'.measurable_equiv hA, (he n ε).map_eq cd h', hsc]

theorem cdScaleIs_trueScale : ∀ cd : CDHaar, CdScaleIs cd (trueScale cd) := by
  intro cd
  unfold trueScale
  rw [dite_eq_left (exists_cdScaleIs cd)]
  exact (Classical.choose_spec (exists_cdScaleIs cd)).2

theorem cdScaleIs_unique (cd : CDHaar) {sc sc' : ∀ n : ℕ, (Fin n → Bool) → NNReal}
    (h : CdScaleIs cd sc) (h' : CdScaleIs cd sc') : sc = sc' := by
  funext n ε
  obtain ⟨P, Q, e, he⟩ := exists_sorts ε
  obtain ⟨K⟩ : Nonempty (TopologicalSpace.PositiveCompacts (Formalism.REAL.UJ ε)) := inferInstance
  have hm : MeasurableSet (K : Set (Formalism.REAL.UJ ε)) := K.isCompact.measurableSet
  have h0 : Formalism.REAL.muG ε K ≠ 0 := (Measure.measure_pos_of_nonempty_interior _ K.interior_nonempty).ne'
  have ht : Formalism.REAL.muG ε K ≠ ⊤ := K.isCompact.measure_lt_top.ne
  have := (h n ε P Q e he.1 he.2 K hm).trans (h' n ε P Q e he.1 he.2 K hm).symm
  rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul] at this
  exact ENNReal.coe_injective ((ENNReal.mul_left_inj h0 ht).1 this)

end GlobalTheory.Mem.Vol.Scale
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaLatticePointMemThetaLatticeOfAdelic
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaLatticePointMemThetaLatticeOfAdelic
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Pointwise

noncomputable section

namespace GlobalTheory.NormSum.MovedLattice

theorem halfDifferent_ne_bot (D : D7) : D.host.𝔟 ≠ ⊥ := by
  intro h
  have h2 := D.host.𝔟_spec.2
  rw [h] at h2
  simp at h2

theorem inverseHalfDifferent_ne_zero (D : D7) : D.host.AA0 ≠ 0 := by
  unfold Host.AA0
  exact inv_ne_zero (FractionalIdeal.coeIdeal_ne_zero.2 (halfDifferent_ne_bot D))

def ext (D : D7) (cc : Ideal (𝓞 D.host.K)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E :=
  ((Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc : Ideal (𝓞 D.host.E)) :
    FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)

theorem ext_ne_zero (D : D7) {cc : Ideal (𝓞 D.host.K)} (h : cc ≠ ⊥) : ext D cc ≠ 0 := by
  unfold ext
  rw [FractionalIdeal.coeIdeal_ne_zero, Ne, Ideal.map_eq_bot_iff_of_injective]
  · exact h
  · exact FaithfulSMul.algebraMap_injective _ _

theorem coe_alg (D : D7) (c : 𝓞 D.host.K) :
    algebraMap (𝓞 D.host.E) D.host.E (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c) =
      ((c : D.host.K) : D.host.E) := rfl

theorem mem_ext (D : D7) {cc : Ideal (𝓞 D.host.K)} {c : 𝓞 D.host.K} (h : c ∈ cc) :
    ((c : D.host.K) : D.host.E) ∈ ext D cc := by
  rw [← coe_alg]
  exact FractionalIdeal.mem_coeIdeal_of_mem _ (Ideal.mem_map_of_mem _ h)

theorem inc_mul_mem (D : D7) {cc : Ideal (𝓞 D.host.K)} (h : cc ≠ ⊥) {j : D.host.E}
    (hj : j ∈ (ext D cc * D.host.AA0)⁻¹) {y : AE D} (hy : y ∈ IhE D cc) : inc D j * y ∈ OhE D := by
  have hJ : ext D cc * D.host.AA0 ≠ 0 := mul_ne_zero (ext_ne_zero D h) (inverseHalfDifferent_ne_zero D)
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨c, hc, a, ha, s, hs, rfl⟩ := hy
    rw [← mul_assoc, ← map_mul]
    refine mul_mem ?_ hs
    have h1 := FractionalIdeal.mul_mem_mul hj (FractionalIdeal.mul_mem_mul (mem_ext D hc) ha)
    rw [inv_mul_cancel₀ hJ, FractionalIdeal.mem_one_iff] at h1
    exact (AdLattice.incl_mem_iff (F := ℚ) _).2 h1
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [mul_neg]; exact neg_mem hx

theorem smul_mem_homL (D : D7) {N N' : ℕ} (g : GL (Fin N) (AE D)) (g' : GL (Fin N') (AE D))
    {L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (h : Moves D g L₁) (h' : Moves D g' L₁') (z : Matrix (Fin N') (Fin N) D.host.E) (j : D.host.E)
    (hz : ∀ a b, inc D j * (((g'⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) * z.map (inc D) *
      (g : Matrix (Fin N) (Fin N) (AE D))) a b ∈ OhE D) : j • z ∈ homL D L₁ L₁' := by
  refine Submodule.subset_span fun x hx => ?_
  rw [h] at hx
  rw [h']
  intro i
  have key : ((g'⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)).mulVec
      (fun k => inc D ((j • z).mulVec x k)) =
      (inc D j • (((g'⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) * z.map (inc D) *
      (g : Matrix (Fin N) (Fin N) (AE D)))).mulVec
        (((g⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)).mulVec (fun k => inc D (x k))) := by
    rw [Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, Units.mul_inv,
      Matrix.mul_one, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_smul _ (inc D j)]
    congr 1
    funext k
    rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul,
      RingHom.map_mulVec]
    rfl
  rw [key]
  simp only [Matrix.mulVec, dotProduct] at hx ⊢
  exact sum_mem fun k _ => mul_mem (hz i k) (hx k)

theorem pt_add (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ}
    (y y' : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ (y + y') = pt D (tor0 D cc δ) δ y + pt D (tor0 D cc δ) δ y' := by
  funext τ a b
  simp [pt, embV, tor0, mul_add]

theorem pt_smul_mem (D : D7) (hD : GL3Theta.InducedCMType D) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ}
    (L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    {m : D.host.E} (hm : m ∈ ext D cc) {y : Matrix (Fin N') (Fin N) D.host.E} (hy : y ∈ YYl D L₁ L₁') :
    pt D (tor0 D cc δ) δ (m • y) ∈ La D (tor0 D cc δ) L₁ L₁' := by
  obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hm
  clear hm
  induction hb using Submodule.span_induction generalizing y with
  | mem b hb =>
    obtain ⟨c, hc, rfl⟩ := hb
    refine AddSubgroup.subset_closure ⟨δ * D.host.φ₀ ((c : D.host.K) : D.host.E),
      AddSubgroup.subset_closure ⟨c, hc, rfl⟩, y, hy, ?_⟩
    funext τ a b
    rw [coe_alg]
    simp only [pt, embV, tor0, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, map_mul, hD τ, mul_assoc]
  | zero =>
    have : pt D (tor0 D cc δ) δ (algebraMap (𝓞 D.host.E) D.host.E 0 • y) = 0 := by
      funext τ a b
      simp [pt, embV, tor0]
    rw [this]; exact zero_mem _
  | add b b' _ _ hb hb' =>
    rw [map_add (f := _), add_smul, pt_add]
    exact add_mem (hb hy) (hb' hy)
  | smul r b _ hb =>
    have := hb ((YYl D L₁ L₁').smul_mem r hy)
    rwa [← algebraMap_smul D.host.E r y, smul_smul, ← map_mul, mul_comm] at this

end GlobalTheory.NormSum.MovedLattice


open GlobalTheory.NormSum.MovedLattice in
theorem GlobalTheory.NormSum.pt_mem_La_of_adelic : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), cc ≠ ⊥ → ∀ (N N' : ℕ) (g : GA D N) (g' : GA D N') (L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), Moves D (g : GL (Fin N) (AE D)) L₁ → Moves D (g' : GL (Fin N') (AE D)) L₁' → ∀ z : Matrix (Fin N') (Fin N) D.host.E, (∀ i j, ((((g' : GL (Fin N') (AE D))⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) * z.map (inc D) * ((g : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))) i j ∈ IhE D cc) → pt D (tor0 D cc δ) δ z ∈ La D (tor0 D cc δ) L₁ L₁' := by
  intro D hD cc δ hcc N N' g g' L₁ L₁' h h' z hz
  have hJ : ext D cc * D.host.AA0 ≠ 0 := mul_ne_zero (ext_ne_zero D hcc) (inverseHalfDifferent_ne_zero D)
  have hY : ∀ n ∈ D.host.AA0 * (ext D cc * D.host.AA0)⁻¹, n • z ∈ YYl D L₁ L₁' := by
    intro n hn
    refine FractionalIdeal.mul_induction_on hn (fun a ha j hj => ?_) (fun x y hx hy => ?_)
    · refine Submodule.subset_span ⟨a, ha, j • z, ?_, mul_smul _ _ _⟩
      exact smul_mem_homL D _ _ h h' z j fun a b => inc_mul_mem D hcc hj (hz a b)
    · rw [add_smul]; exact add_mem hx hy
  have h1 : (1 : D.host.E) ∈ ext D cc * (D.host.AA0 * (ext D cc * D.host.AA0)⁻¹) := by
    rw [← mul_assoc, mul_inv_cancel₀ hJ]
    exact FractionalIdeal.one_mem_one _
  have h2 : ∀ e ∈ ext D cc * (D.host.AA0 * (ext D cc * D.host.AA0)⁻¹),
      pt D (tor0 D cc δ) δ (e • z) ∈ La D (tor0 D cc δ) L₁ L₁' := by
    intro e he
    refine FractionalIdeal.mul_induction_on he (fun m hm n hn => ?_) (fun x y hx hy => ?_)
    · rw [mul_smul]
      exact pt_smul_mem D hD.1 cc δ L₁ L₁' hm (hY n hn)
    · rw [add_smul, pt_add]; exact add_mem hx hy
  simpa using h2 1 h1
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaLatticePointMemThetaLatticeOfAdelicStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmThetaLatticePoint_mem_thetaLattice_of_adelic : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), cc ≠ ⊥ → ∀ (N N' : ℕ) (g : GA D N) (g' : GA D N') (L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), Moves D (g : GL (Fin N) (AE D)) L₁ → Moves D (g' : GL (Fin N') (AE D)) L₁' → ∀ z : Matrix (Fin N') (Fin N) D.host.E, (∀ i j, ((((g' : GL (Fin N') (AE D))⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) * z.map (inc D) * ((g : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))) i j ∈ IhE D cc) → pt D (tor0 D cc δ) δ z ∈ La D (tor0 D cc δ) L₁ L₁' := by
  first | exact @GlobalTheory.NormSum.pt_mem_La_of_adelic | exact GlobalTheory.NormSum.pt_mem_La_of_adelic | (intros; apply GlobalTheory.NormSum.pt_mem_La_of_adelic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPointStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.Lt_eq_iff_inv_mul_mem_intG_and_transport : ∀ (D : D7) (N : ℕ), ∃ Lt : GA D N → Submodule (𝓞 D.host.E) (Fin N → D.host.E), (∀ g : GA D N, Moves D (g : GL (Fin N) (AE D)) (Lt g) ∧ SD D (Lt g)) ∧ Lt 1 = stdL D N ∧ (∀ g g' : GA D N, Lt g = Lt g' ↔ g⁻¹ * g' ∈ intG D N) ∧ (∀ (γA g : GA D N) γ, IsRat D (γA : GL (Fin N) (AE D)) γ → ∀ x, x ∈ Lt g ↔ γ.mulVec x ∈ Lt (γA * g)) ∧ (∀ (p : ℕ) (g : GA D N), p.Prime → TrivAt D p (g : GL (Fin N) (AE D)) → EqAt D p (stdL D N) (Lt g)) := by
  first | exact @GlobalTheory.NormSum.exists_lattice_of_adelic_point | exact GlobalTheory.NormSum.exists_lattice_of_adelic_point | (intros; apply GlobalTheory.NormSum.exists_lattice_of_adelic_point <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DetRationalMatrixTwoSidedMulEqProdEmbeddings
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DetRationalMatrixTwoSidedMulEqProdEmbeddings
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.RatEqui
open scoped BigOperators

noncomputable section

namespace GlobalTheory.TwoSidedDet

def sandwich {m n : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ) :
    (Fin m → Fin n → ℂ) →ₗ[ℂ] (Fin m → Fin n → ℂ) where
  toFun z := (A * Matrix.of z * B : Matrix _ _ ℂ)
  map_add' z w := by
    change A * (Matrix.of z + Matrix.of w) * B = _
    rw [Matrix.mul_add, Matrix.add_mul]; rfl
  map_smul' c z := by
    change A * (c • Matrix.of z) * B = _
    rw [Matrix.mul_smul, Matrix.smul_mul]; rfl

theorem det_sandwich {m n : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) (B : Matrix (Fin n) (Fin n) ℂ) :
    LinearMap.det (sandwich A B) = A.det ^ n * B.det ^ m := by
  let e : (Fin m × Fin n → ℂ) ≃ₗ[ℂ] (Fin m → Fin n → ℂ) := LinearEquiv.curry ℂ ℂ (Fin m) (Fin n)
  have h : sandwich A B = (e : _ →ₗ[ℂ] _) ∘ₗ (Matrix.toLin' (Matrix.kroneckerMap (· * ·) A B.transpose)) ∘ₗ (e.symm : _ →ₗ[ℂ] _) := by
    refine LinearMap.ext fun z => ?_
    funext i j
    change (A * Matrix.of z * B) i j = (Matrix.kroneckerMap (· * ·) A B.transpose).mulVec (Function.uncurry z) (i, j)
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
      Matrix.transpose_apply, Matrix.of_apply, Function.uncurry_apply_pair, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [h, LinearMap.det_conj, LinearMap.det_toLin', Matrix.det_kronecker, Matrix.det_transpose]
  simp

theorem det_mulV (D : D7) (N N' : ℕ) (M' : Matrix (Fin N') (Fin N') D.host.E)
    (M : Matrix (Fin N) (Fin N) D.host.E) :
    LinearMap.det (mulV D M' M) = ∏ τ, embT D τ M'.det ^ N * embT D τ M.det ^ N' := by
  have h : mulV D M' M = LinearMap.pi (fun τ : D.what₂.Tau =>
      (sandwich (M'.map (embT D τ)) (M.map (embT D τ))) ∘ₗ LinearMap.proj τ) := by
    refine LinearMap.ext fun z => ?_
    rfl
  rw [h, LinearMap.det_pi]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [det_sandwich, RingHom.map_det, RingHom.map_det]
  rfl

end GlobalTheory.TwoSidedDet
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DetRationalMatrixTwoSidedMulEqProdEmbeddingsStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.RatEqui
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_rationalMatrixTwoSidedMul_eq_prod_embeddings : ∀ (D : D7) (N N' : ℕ) (M' : Matrix (Fin N') (Fin N') D.host.E) (M : Matrix (Fin N) (Fin N) D.host.E), LinearMap.det (mulV D M' M) = ∏ τ, embT D τ M'.det ^ N * embT D τ M.det ^ N' := by
  first | exact @GlobalTheory.TwoSidedDet.det_mulV | exact GlobalTheory.TwoSidedDet.det_mulV | (intros; apply GlobalTheory.TwoSidedDet.det_mulV <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmFiniteAdeleIntegralSeparatedCompleteStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmFiniteAdele_integral_separated_complete : ∀ (D : D7), (∀ y : AE D, (∀ N : ℕ, 0 < N → ∃ w ∈ OhE D, y = (N : AE D) * w) → y = 0) ∧ ∀ x : ℕ → AE D, (∀ N, x N ∈ OhE D) → (∀ N m : ℕ, 0 < N → 0 < m → ∃ w ∈ OhE D, x (N * m) = x N + (N : AE D) * w) → ∃ y ∈ OhE D, ∀ N : ℕ, 0 < N → ∃ w ∈ OhE D, y = x N + (N : AE D) * w := by
  first | exact @GlobalTheory.IntAdeleComplete.integral_separated_complete | exact GlobalTheory.IntAdeleComplete.integral_separated_complete | (intros; apply GlobalTheory.IntAdeleComplete.integral_separated_complete <;> assumption)
end
