module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadNatZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemCompletedLatticeConjugateHalfIffDual

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeHalfRepresentativesModReductions
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeHalfRepresentativesModReductions
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
namespace GlobalTheory.ZRepBlock

theorem zrep_block : ∀ (D : D7) (S T : HSp D) {m k : ℕ} (Λ Λ' : AddSubgroup (WO S T)) (e : AE D) (Q : Finset (Pl D.host.E)) (fm : WO S T → Matrix (Fin m) (Fin k) (EAf D)), (∀ w w', fm (w - w') = fm w - fm w') → (∀ w, IsHalf e w → (w ∈ Λ ↔ IsIntM (fm w))) → (∀ w ∈ Λ, ∀ w' ∈ Λ, IsHalf e w → IsHalf e w' → (w - w' ∈ Λ' ↔ ∀ PP ∈ Q, redM PP (fm w) = redM PP (fm w'))) → (∀ Y : ∀ PP : Pl D.host.E, Matrix (Fin m) (Fin k) (kP PP), ∃ w, IsHalf e w ∧ IsIntM (fm w) ∧ ∀ PP ∈ Q, redM PP (fm w) = Y PP) → ∃ X : Finset (WO S T), (∀ x ∈ X, x ∈ Λ ∧ IsHalf e x) ∧ (∀ w ∈ Λ, IsHalf e w → ∃! x, x ∈ X ∧ w - x ∈ Λ') ∧ X.card = (∏ PP ∈ Q, Nat.card (kP PP)) ^ (m * k) ∧ (∀ Y : ∀ PP : Pl D.host.E, Matrix (Fin m) (Fin k) (kP PP), ∃! x, x ∈ X ∧ ∀ PP ∈ Q, redM PP (fm x) = Y PP) := by
  intro D S T m k Λ Λ' e Q fm _hsub H1 H2 H3
  classical

  let Ix := ∀ PP : Q, Matrix (Fin m) (Fin k) (kP (PP : Pl D.host.E))
  haveI : ∀ PP : Pl D.host.E, Fintype (kP PP) := fun PP => Fintype.ofFinite _
  let ext : Ix → ∀ PP : Pl D.host.E, Matrix (Fin m) (Fin k) (kP PP) :=
    fun Y PP => if h : PP ∈ Q then Y ⟨PP, h⟩ else 0
  choose w hwh hwi hwr using H3
  let g : Ix → WO S T := fun Y => w (ext Y)
  have hgr : ∀ Y : Ix, ∀ PP (h : PP ∈ Q), redM PP (fm (g Y)) = Y ⟨PP, h⟩ := by
    intro Y PP h
    have := hwr (ext Y) PP h
    simpa [g, ext, h] using this
  have hginj : Function.Injective g := by
    intro Y Y' hYY
    funext PP
    rw [← hgr Y PP.1 PP.2, ← hgr Y' PP.1 PP.2, hYY]
  have hgΛ : ∀ Y, g Y ∈ Λ ∧ IsHalf e (g Y) :=
    fun Y => ⟨(H1 _ (hwh _)).2 (hwi _), hwh _⟩
  refine ⟨Finset.univ.image g, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨Y, -, rfl⟩ := Finset.mem_image.1 hx
    exact hgΛ Y
  · intro v hv hvh
    let Y : Ix := fun PP => redM (PP : Pl D.host.E) (fm v)
    refine ⟨g Y, ⟨Finset.mem_image.2 ⟨Y, Finset.mem_univ _, rfl⟩, ?_⟩, ?_⟩
    · refine (H2 v hv (g Y) (hgΛ Y).1 hvh (hgΛ Y).2).2 ?_
      intro PP h
      rw [hgr Y PP h]
    · rintro x ⟨hx, hvx⟩
      obtain ⟨Y', -, rfl⟩ := Finset.mem_image.1 hx
      congr 1
      funext PP
      have h1 := (H2 v hv (g Y') (hgΛ Y').1 hvh (hgΛ Y').2).1 hvx PP.1 PP.2
      rw [hgr Y' PP.1 PP.2] at h1
      exact h1.symm
  · rw [Finset.card_image_of_injective _ hginj, Finset.card_univ, Fintype.card_pi]
    calc ∏ i : Q, Fintype.card (Fin m → Fin k → kP (i : Pl D.host.E))
        = ∏ i : Q, Nat.card (kP (i : Pl D.host.E)) ^ (m * k) := by
          refine Finset.prod_congr rfl (fun i _ => ?_)
          simp only [Fintype.card_fun, Fintype.card_fin, Nat.card_eq_fintype_card]
          ring
      _ = (∏ PP ∈ Q, Nat.card (kP PP)) ^ (m * k) := by
          rw [Finset.prod_pow, Finset.prod_coe_sort Q (fun PP => Nat.card (kP PP))]
  · intro Y
    let Y' : Ix := fun PP => Y PP
    refine ⟨g Y', ⟨Finset.mem_image.2 ⟨Y', Finset.mem_univ _, rfl⟩, fun PP h => hgr Y' PP h⟩, ?_⟩
    rintro x ⟨hx, hxr⟩
    obtain ⟨Y'', -, rfl⟩ := Finset.mem_image.1 hx
    congr 1
    funext PP
    rw [← hgr Y'' PP.1 PP.2, hxr PP.1 PP.2]

end GlobalTheory.ZRepBlock
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeHalfRepresentativesModReductionsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_half_representatives_mod_reductions : ∀ (D : D7) (S T : HSp D) {m k : ℕ} (Λ Λ' : AddSubgroup (WO S T)) (e : AE D) (Q : Finset (Pl D.host.E)) (fm : WO S T → Matrix (Fin m) (Fin k) (EAf D)), (∀ w w', fm (w - w') = fm w - fm w') → (∀ w, IsHalf e w → (w ∈ Λ ↔ IsIntM (fm w))) → (∀ w ∈ Λ, ∀ w' ∈ Λ, IsHalf e w → IsHalf e w' → (w - w' ∈ Λ' ↔ ∀ PP ∈ Q, redM PP (fm w) = redM PP (fm w'))) → (∀ Y : ∀ PP : Pl D.host.E, Matrix (Fin m) (Fin k) (kP PP), ∃ w, IsHalf e w ∧ IsIntM (fm w) ∧ ∀ PP ∈ Q, redM PP (fm w) = Y PP) → ∃ X : Finset (WO S T), (∀ x ∈ X, x ∈ Λ ∧ IsHalf e x) ∧ (∀ w ∈ Λ, IsHalf e w → ∃! x, x ∈ X ∧ w - x ∈ Λ') ∧ X.card = (∏ PP ∈ Q, Nat.card (kP PP)) ^ (m * k) ∧ (∀ Y : ∀ PP : Pl D.host.E, Matrix (Fin m) (Fin k) (kP PP), ∃! x, x ∈ X ∧ ∀ PP ∈ Q, redM PP (fm x) = Y PP) := by
  first | exact @GlobalTheory.ZRepBlock.zrep_block | exact GlobalTheory.ZRepBlock.zrep_block | (intros; apply GlobalTheory.ZRepBlock.zrep_block <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralScalarInverseUniformisersIdempotentSum
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralScalarInverseUniformisersIdempotentSum
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CentralScalar

section Alg

variable {R ι : Type} [CommRing R] {s : Finset ι} {p q : ι → R}

def comp (s : Finset ι) (p q u v : ι → R) : R := 1 + ∑ i ∈ s, (p i * (u i - 1) + q i * (v i - 1))

theorem comp_swap (u v : ι → R) : comp s p q u v = comp s q p v u := by
  unfold comp
  congr 1
  exact Finset.sum_congr rfl fun i _ => add_comm _ _

theorem left_mul_comp (h1 : ∀ i ∈ s, p i * p i = p i) (h2 : ∀ i ∈ s, ∀ j ∈ s, j ≠ i → p i * p j = 0)
    (h3 : ∀ i ∈ s, ∀ j ∈ s, p i * q j = 0) (u v : ι → R) {i : ι} (hi : i ∈ s) :
    p i * comp s p q u v = p i * u i := by
  unfold comp
  rw [mul_add, Finset.mul_sum, Finset.sum_eq_single_of_mem i hi]
  · rw [mul_add, ← mul_assoc, ← mul_assoc, h1 i hi, h3 i hi i hi]; ring
  · intro j hj hji
    rw [mul_add, ← mul_assoc, ← mul_assoc, h2 i hi j hj hji, h3 i hi j hj]; ring

theorem comp_mul (hp : ∀ u v : ι → R, ∀ i ∈ s, p i * comp s p q u v = p i * u i)
    (hq : ∀ u v : ι → R, ∀ i ∈ s, q i * comp s p q u v = q i * v i) (u v u' v' : ι → R) :
    comp s p q u v * comp s p q u' v' = comp s p q (fun i => u i * u' i) (fun i => v i * v' i) := by
  have h : comp s p q u v * comp s p q u' v' =
      comp s p q u' v' + ∑ i ∈ s, (p i * u' i * (u i - 1) + q i * v' i * (v i - 1)) := by
    conv_lhs => rw [comp]
    rw [add_mul, one_mul, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [← hp u' v' i hi, ← hq u' v' i hi]; ring
  rw [h]
  unfold comp
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

theorem comp_eq_one {u v : ι → R} (hu : ∀ i ∈ s, u i = 1) (hv : ∀ i ∈ s, v i = 1) : comp s p q u v = 1 := by
  unfold comp
  rw [Finset.sum_eq_zero, add_zero]
  intro i hi
  rw [hu i hi, hv i hi]; ring

theorem mul_pow_of_mul_eq {e a w : R} (h : e * a = e * w) (n : ℕ) : e * a ^ n = e * w ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, ← mul_assoc, ih, mul_right_comm, h, pow_succ]; ring

theorem map_comp (c : R →+* R) (hc : ∀ x, c (c x) = x) (u v : ι → R) :
    c (comp s p (fun i => c (p i)) u v) = comp s p (fun i => c (p i)) (fun i => c (v i)) (fun i => c (u i)) := by
  unfold comp
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_add (f := _), map_one, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [map_add (f := _), map_mul, map_sub, map_one, hc]
  ring

end Alg

variable {D : D7}

theorem cA_incA (x : D.host.E) : cA D (incA D x) = incA D (star x) := rfl

theorem mt_inj (V : HSp D) {a b : GA D V} (h : Formalism.L2.Theta.mt V a = Formalism.L2.Theta.mt V b) : a = b :=
  Subtype.ext (Units.ext h)

theorem exists_scalar (V : HSp D) (a : AE D) (ha : cA D a * a = 1) :
    ∃ z : GA D V, Formalism.L2.Theta.mt V z = Matrix.diagonal fun _ => a := by
  have h1 : (Matrix.diagonal fun _ : Fin V.rank => a) * (Matrix.diagonal fun _ => cA D a) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, mul_comm, ha, Matrix.diagonal_one]
  have h2 : (Matrix.diagonal fun _ : Fin V.rank => cA D a) * (Matrix.diagonal fun _ => a) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ha, Matrix.diagonal_one]
  refine ⟨⟨⟨_, _, h1, h2⟩, ?_⟩, rfl⟩
  change Formalism.UG.cT (cA D) (Matrix.diagonal fun _ => a) * _ * (Matrix.diagonal fun _ => a) = _
  have h3 : Formalism.UG.cT (cA D) (Matrix.diagonal fun _ : Fin V.rank => a) = Matrix.diagonal fun _ => cA D a := by
    ext i j
    by_cases h : i = j
    · subst h; simp [Formalism.UG.cT]
    · simp [Formalism.UG.cT, Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]
  rw [h3]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, mul_right_comm, ha, one_mul]

theorem scalar_central (V : HSp D) {a : AE D} {z : GA D V} (hz : Formalism.L2.Theta.mt V z = Matrix.diagonal fun _ => a) :
    z ∈ Subgroup.center (GA D V) := by
  rw [Subgroup.mem_center_iff]
  intro g
  apply mt_inj V
  change Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V z = Formalism.L2.Theta.mt V z * Formalism.L2.Theta.mt V g
  rw [hz]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, mul_comm]

theorem scalar_fin (V : HSp D) {a : AE D} (ha : infPart D a = 1) {z : GA D V}
    (hz : Formalism.L2.Theta.mt V z = Matrix.diagonal fun _ => a) : z ∈ GfC V := by
  refine MonoidHom.mem_ker.2 (Units.ext ?_)
  change (Formalism.L2.Theta.mt V z).map (infPart D) = 1
  rw [hz, Matrix.diagonal_map (map_zero _)]
  simp only [ha, Matrix.diagonal_one]

theorem scalar_inv (V : HSp D) {a : AE D} (ha : cA D a * a = 1) {z : GA D V}
    (hz : Formalism.L2.Theta.mt V z = Matrix.diagonal fun _ => a) :
    Formalism.L2.Theta.mt V z⁻¹ = Matrix.diagonal fun _ => cA D a := by
  have h1 : (Matrix.diagonal fun _ : Fin V.rank => a) * (Matrix.diagonal fun _ => cA D a) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, mul_comm, ha, Matrix.diagonal_one]
  have h := Formalism.IndefR.Fin.LevelGroupLemmas.Lat.mt_inv_mul V z
  rw [← Matrix.mul_one (Formalism.L2.Theta.mt V z⁻¹), ← h1, ← Matrix.mul_assoc, ← hz, h, Matrix.one_mul]

theorem scalar_supp (V : HSp D) {e a : AE D} (ha : (e + cA D e) * (a - 1) = a - 1) {z : GA D V}
    (hz : Formalism.L2.Theta.mt V z = Matrix.diagonal fun _ => a) : SuppAt e V z := by
  intro i j
  rw [hz]
  by_cases h : i = j
  · subst h
    simpa only [Matrix.sub_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq] using ha
  · rw [Matrix.sub_apply, Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h, sub_zero, mul_zero]

theorem centralScalar : ∀ (D : D7) (V : HSp D) (Q : Finset (Pl D.host.E)) (es : Pl D.host.E → AE D) (ϖ : Pl D.host.E → 𝓞 D.host.E), (∀ PP ∈ Q, Formalism.L2.NTheta.IsIdemAt (es PP) PP) → (∑ PP ∈ Q, es PP) * cA D (∑ PP ∈ Q, es PP) = 0 → (∀ PP ∈ Q, ϖ PP ≠ 0) → (∃ z : GA D V, mt V z = Matrix.diagonal fun _ => (1 + ∑ PP ∈ Q, (es PP * (incA D ((ϖ PP : D.host.E)⁻¹) - 1) + cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) - 1)))) ∧ ∀ z : GA D V, mt V z = Matrix.diagonal (fun _ => (1 + ∑ PP ∈ Q, (es PP * (incA D ((ϖ PP : D.host.E)⁻¹) - 1) + cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) - 1)))) → z ∈ Subgroup.center (GA D V) ∧ z ∈ GfC V ∧ SuppAt (∑ PP ∈ Q, es PP) V z ∧ (∃ x : (AE D)ˣ, IsDetAt (cA D (∑ PP ∈ Q, es PP)) V z x ∧ (x : AE D) = 1 + ∑ PP ∈ Q, cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) ^ V.rank - 1)) ∧ mt V z⁻¹ = Matrix.diagonal (fun _ => cA D (1 + ∑ PP ∈ Q, (es PP * (incA D ((ϖ PP : D.host.E)⁻¹) - 1) + cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) - 1)))) ∧ (1 + ∑ PP ∈ Q, (es PP * (incA D ((ϖ PP : D.host.E)⁻¹) - 1) + cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) - 1))) * (∑ PP ∈ Q, es PP) = ∑ PP ∈ Q, es PP * incA D ((ϖ PP : D.host.E)⁻¹) ∧ cA D (1 + ∑ PP ∈ Q, (es PP * (incA D ((ϖ PP : D.host.E)⁻¹) - 1) + cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) - 1))) * (∑ PP ∈ Q, es PP) = ∑ PP ∈ Q, es PP * incA D (ϖ PP : D.host.E) ∧ (1 + ∑ PP ∈ Q, (es PP * (incA D ((ϖ PP : D.host.E)⁻¹) - 1) + cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) - 1))) * cA D (∑ PP ∈ Q, es PP) = cA D (∑ PP ∈ Q, es PP * incA D (ϖ PP : D.host.E)) ∧ cA D (1 + ∑ PP ∈ Q, (es PP * (incA D ((ϖ PP : D.host.E)⁻¹) - 1) + cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) - 1))) * cA D (∑ PP ∈ Q, es PP) = cA D (∑ PP ∈ Q, es PP * incA D ((ϖ PP : D.host.E)⁻¹)) := by
  intro D V Q es ϖ hes hc hϖ
  have h1 : ∀ i ∈ Q, es i * es i = es i := fun i hi => (hes i hi).1.1
  have hx := GlobalTheory.PlaceDatum.cross_eq_zero (R := AE D) GlobalTheory.PlaceDatum.isUnit_natCast (cA D) es Q h1 hc
  have h2 : ∀ i ∈ Q, ∀ j ∈ Q, j ≠ i → es i * es j = 0 := fun i hi j hj h =>
    GlobalTheory.PlaceDatum.idemAt_mul (hes i hi) (hes j hj) (hx i hi j hj) (hx j hj i hi) h
  have hp : ∀ u v : Pl D.host.E → AE D, ∀ i ∈ Q,
      es i * comp Q es (fun i => cA D (es i)) u v = es i * u i := fun u v i hi => left_mul_comp h1 h2 hx u v hi
  have hq : ∀ u v : Pl D.host.E → AE D, ∀ i ∈ Q,
      cA D (es i) * comp Q es (fun i => cA D (es i)) u v = cA D (es i) * v i := fun u v i hi => by
    rw [comp_swap]
    refine left_mul_comp (p := fun i => cA D (es i)) (fun i hi => ?_) (fun i hi j hj h => ?_) (fun i hi j hj => ?_) v u hi
    · rw [← map_mul, h1 i hi]
    · rw [← map_mul, h2 i hi j hj h, map_zero]
    · rw [mul_comm]; exact hx j hj i hi
  have hne : ∀ i ∈ Q, (ϖ i : D.host.E) ≠ 0 := fun i hi h => hϖ i hi (RingOfIntegers.coe_eq_zero_iff.1 h)
  set a : AE D := 1 + ∑ PP ∈ Q, (es PP * (incA D ((ϖ PP : D.host.E)⁻¹) - 1) +
    cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) - 1)) with ha
  have ha' : a = comp Q es (fun i => cA D (es i)) (fun PP => incA D ((ϖ PP : D.host.E)⁻¹))
    (fun PP => incA D (star (ϖ PP : D.host.E))) := rfl
  have hca : cA D a = comp Q es (fun i => cA D (es i)) (fun PP => incA D (ϖ PP : D.host.E))
      (fun PP => incA D (star (ϖ PP : D.host.E)⁻¹)) := by
    rw [ha', map_comp (cA D) GlobalTheory.DualPairCheck.cA_cA]
    simp only [cA_incA, star_star]
  have hn : cA D a * a = 1 := by
    rw [hca, ha', comp_mul hp hq]
    refine comp_eq_one (fun i hi => ?_) (fun i hi => ?_)
    · rw [← map_mul, mul_inv_cancel₀ (hne i hi), map_one]
    · rw [← map_mul, ← star_mul, mul_inv_cancel₀ (hne i hi), star_one, map_one]
  refine ⟨exists_scalar V a hn, fun z hz => ⟨scalar_central V hz, scalar_fin V ?_ hz, scalar_supp V ?_ hz, ?_,
    scalar_inv V hn hz, ?_, ?_, ?_, ?_⟩⟩
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [ha, map_add (f := _), map_one, map_sum, Finset.sum_eq_zero, add_zero]
    intro i hi
    have h0 := Formalism.IndefR.Fin.LevelGroupLemmas.Lat.infPart_of_splitIdem (hes i hi).1
    rw [map_add (f := _), map_mul, map_mul, h0, GlobalTheory.PlaceVec.infPart_cA h0, zero_mul, zero_mul, add_zero]
  · have : a - 1 = ∑ PP ∈ Q, (es PP * (incA D ((ϖ PP : D.host.E)⁻¹) - 1) +
      cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) - 1)) := by rw [ha, add_sub_cancel_left]
    conv_rhs => rw [this]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, ← Finset.sum_add_distrib, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [add_mul, mul_sub, mul_sub, ha', hp _ _ i hi, hq _ _ i hi]
    ring
  · have hu : comp Q es (fun i => cA D (es i)) (fun _ => 1) (fun PP => incA D (star (ϖ PP : D.host.E)) ^ V.rank) *
        comp Q es (fun i => cA D (es i)) (fun _ => 1) (fun PP => incA D (star (ϖ PP : D.host.E)⁻¹) ^ V.rank) = 1 := by
      rw [comp_mul hp hq]
      refine comp_eq_one (fun i _ => one_mul _) (fun i hi => ?_)
      rw [← mul_pow, ← map_mul, ← star_mul, inv_mul_cancel₀ (hne i hi), star_one, map_one, one_pow]
    have hv : comp Q es (fun i => cA D (es i)) (fun _ => 1) (fun PP => incA D (star (ϖ PP : D.host.E)) ^ V.rank) =
        1 + ∑ PP ∈ Q, cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) ^ V.rank - 1) := by
      simp only [comp, sub_self, mul_zero, zero_add]
    refine ⟨Units.mkOfMulEqOne _ _ hu, ?_, hv⟩
    change comp Q es (fun i => cA D (es i)) (fun _ => 1) (fun PP => incA D (star (ϖ PP : D.host.E)) ^ V.rank) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hv, hz, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin, map_sum, Finset.sum_mul]
    have : ∀ i ∈ Q, cA D (es i) * a ^ V.rank = cA D (es i) * incA D (star (ϖ i : D.host.E)) ^ V.rank :=
      fun i hi => mul_pow_of_mul_eq (hq _ _ i hi) _
    rw [Finset.sum_congr rfl this]
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
    ring
  · rw [mul_comm, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i hi => hp _ _ i hi
  · rw [mul_comm, Finset.sum_mul, hca]
    exact Finset.sum_congr rfl fun i hi => hp _ _ i hi
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [mul_comm, map_sum, map_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i hi => by rw [map_mul, cA_incA]; exact hq _ _ i hi
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [mul_comm, map_sum, map_sum, Finset.sum_mul, hca]
    exact Finset.sum_congr rfl fun i hi => by rw [map_mul, cA_incA]; exact hq _ _ i hi

end GlobalTheory.CentralScalar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralScalarInverseUniformisersIdempotentSumStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centralScalar_inverse_uniformisers_idempotent_sum : ∀ (D : D7) (V : HSp D) (Q : Finset (Pl D.host.E)) (es : Pl D.host.E → AE D) (ϖ : Pl D.host.E → 𝓞 D.host.E), (∀ PP ∈ Q, Formalism.L2.NTheta.IsIdemAt (es PP) PP) → (∑ PP ∈ Q, es PP) * cA D (∑ PP ∈ Q, es PP) = 0 → (∀ PP ∈ Q, ϖ PP ≠ 0) → (∃ z : GA D V, mt V z = Matrix.diagonal fun _ => (1 + ∑ PP ∈ Q, (es PP * (incA D ((ϖ PP : D.host.E)⁻¹) - 1) + cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) - 1)))) ∧ ∀ z : GA D V, mt V z = Matrix.diagonal (fun _ => (1 + ∑ PP ∈ Q, (es PP * (incA D ((ϖ PP : D.host.E)⁻¹) - 1) + cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) - 1)))) → z ∈ Subgroup.center (GA D V) ∧ z ∈ GfC V ∧ SuppAt (∑ PP ∈ Q, es PP) V z ∧ (∃ x : (AE D)ˣ, IsDetAt (cA D (∑ PP ∈ Q, es PP)) V z x ∧ (x : AE D) = 1 + ∑ PP ∈ Q, cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) ^ V.rank - 1)) ∧ mt V z⁻¹ = Matrix.diagonal (fun _ => cA D (1 + ∑ PP ∈ Q, (es PP * (incA D ((ϖ PP : D.host.E)⁻¹) - 1) + cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) - 1)))) ∧ (1 + ∑ PP ∈ Q, (es PP * (incA D ((ϖ PP : D.host.E)⁻¹) - 1) + cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) - 1))) * (∑ PP ∈ Q, es PP) = ∑ PP ∈ Q, es PP * incA D ((ϖ PP : D.host.E)⁻¹) ∧ cA D (1 + ∑ PP ∈ Q, (es PP * (incA D ((ϖ PP : D.host.E)⁻¹) - 1) + cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) - 1))) * (∑ PP ∈ Q, es PP) = ∑ PP ∈ Q, es PP * incA D (ϖ PP : D.host.E) ∧ (1 + ∑ PP ∈ Q, (es PP * (incA D ((ϖ PP : D.host.E)⁻¹) - 1) + cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) - 1))) * cA D (∑ PP ∈ Q, es PP) = cA D (∑ PP ∈ Q, es PP * incA D (ϖ PP : D.host.E)) ∧ cA D (1 + ∑ PP ∈ Q, (es PP * (incA D ((ϖ PP : D.host.E)⁻¹) - 1) + cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) - 1))) * cA D (∑ PP ∈ Q, es PP) = cA D (∑ PP ∈ Q, es PP * incA D ((ϖ PP : D.host.E)⁻¹)) := by
  first | exact @GlobalTheory.CentralScalar.centralScalar | exact GlobalTheory.CentralScalar.centralScalar | (intros; apply GlobalTheory.CentralScalar.centralScalar <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniformiserFamilyHostFieldIntegers
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniformiserFamilyHostFieldIntegers
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory

theorem exists_uniformiser_family_host :
    ∀ (D : D7), ∃ ϖ : Pl D.host.E → 𝓞 D.host.E, ∀ PP : Pl D.host.E, ϖ PP ∈ PP.asIdeal ∧ ϖ PP ∉ PP.asIdeal ^ 2 := by
  intro D
  have h : ∀ PP : Pl D.host.E, ∃ x : 𝓞 D.host.E, x ∈ PP.asIdeal ∧ x ∉ PP.asIdeal ^ 2 := by
    intro PP
    have hlt : PP.asIdeal ^ 2 < PP.asIdeal :=
      Ideal.pow_lt_self _ PP.ne_bot PP.isPrime.ne_top 2 le_rfl
    obtain ⟨x, hx1, hx2⟩ := SetLike.exists_of_lt hlt
    exact ⟨x, hx1, hx2⟩
  choose f hf using h
  exact ⟨f, hf⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniformiserFamilyHostFieldIntegersStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformiser_family_hostField_integers : ∀ (D : D7), ∃ ϖ : Pl D.host.E → 𝓞 D.host.E, ∀ PP : Pl D.host.E, ϖ PP ∈ PP.asIdeal ∧ ϖ PP ∉ PP.asIdeal ^ 2 := by
  first | exact @GlobalTheory.exists_uniformiser_family_host | exact GlobalTheory.exists_uniformiser_family_host | (intros; apply GlobalTheory.exists_uniformiser_family_host <;> assumption)
end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section

namespace GlobalTheory.ZRep

open Formalism.IndefR.Fin.LevelGroupLemmas.Lat (mt_one isHalf_actO redM_of_int)

variable {D : D7}

theorem actO_one_eq {S T : HSp D} (g : GA D S) (s : AE D) (hg : mt S g⁻¹ = Matrix.diagonal (fun _ => s)) (w : WO S T) :
    actO S T g 1 w = s • w := by
  unfold actO
  rw [hg, mt_one, Matrix.one_mul]
  ext i j
  simp [Matrix.mul_diagonal, Matrix.smul_apply, mul_comm]

theorem smul_half {m n : ℕ} {e : AE D} (s : AE D) {w : Mx D m n} (hw : IsHalf e w) : s • w = (s * e) • w := by
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul, mul_assoc, hw i j]

theorem isHalf_smul {m n : ℕ} {e : AE D} (s : AE D) {w : Mx D m n} (hw : IsHalf e w) : IsHalf e (s • w) := by
  intro i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [mul_left_comm, hw i j]

theorem isHalf_sub {m n : ℕ} {e : AE D} {w w' : Mx D m n} (hw : IsHalf e w) (hw' : IsHalf e w') : IsHalf e (w - w') := by
  intro i j
  simp only [Matrix.sub_apply, mul_sub, hw i j, hw' i j]

theorem redM_sub (PP : Pl D.host.E) {b a : ℕ} {N M : Matrix (Fin b) (Fin a) (EAf D)} (hN : IsIntM N) (hM : IsIntM M) :
    redM PP (N - M) = redM PP N - redM PP M := by
  ext i j
  have hNM : IsIntM (N - M) := fun i j => sub_mem (hN i j) (hM i j)
  rw [Matrix.sub_apply, redM_of_int PP hNM, redM_of_int PP hN, redM_of_int PP hM, ← map_sub]
  rfl

theorem isIntM_smul {b a : ℕ} {c : EAf D} (hc : c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) {N : Matrix (Fin b) (Fin a) (EAf D)}
    (hN : IsIntM N) : IsIntM (c • N) := fun i j => by
  rw [Matrix.smul_apply, smul_eq_mul]; exact mul_mem hc (hN i j)

theorem frMapO_sub {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (w w' : WO S T) :
    frMapO S T βS βT (w - w') = frMapO S T βS βT w - frMapO S T βS βT w' := by
  rw [sub_eq_add_neg, Formalism.IndefR.Fin.LevelGroupLemmas.Lat.frMapO_add, Formalism.IndefR.Fin.LevelGroupLemmas.Lat.frMapO_neg, ← sub_eq_add_neg]

theorem frMapAdj_sub {S T : HSp D} (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (w w' : WO S T) :
    frMapAdj S T βS βT (w - w') = frMapAdj S T βS βT w - frMapAdj S T βS βT w' := by
  rw [sub_eq_add_neg, Formalism.IndefR.Fin.LevelGroupLemmas.Lat.frMapAdj_add, Formalism.IndefR.Fin.LevelGroupLemmas.Lat.frMapAdj_neg, ← sub_eq_add_neg]

theorem isIntM_smul_iff (Q : Finset (Pl D.host.E)) (es : Pl D.host.E → AE D) (ϖ : Pl D.host.E → 𝓞 D.host.E)
    (hes : ∀ PP ∈ Q, Formalism.L2.NTheta.IsIdemAt (es PP) PP) (hc : (∑ PP ∈ Q, es PP) * cA D (∑ PP ∈ Q, es PP) = 0)
    (hϖ : ∀ PP ∈ Q, ϖ PP ∈ PP.asIdeal ∧ ϖ PP ∉ PP.asIdeal ^ 2) {b a : ℕ} (N : Matrix (Fin b) (Fin a) (EAf D))
    (hN : IsIntM N) (he : toEAf D (∑ PP ∈ Q, es PP) • N = N) :
    IsIntM (toEAf D (∑ PP ∈ Q, es PP * incA D ((ϖ PP : D.host.E)⁻¹)) • N) ↔ ∀ PP ∈ Q, redM PP N = 0 := by
  have key : ∀ i j, (toEAf D (∑ PP ∈ Q, es PP * incA D ((ϖ PP : D.host.E)⁻¹)) * N i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔
      ∀ PP ∈ Q, resS D.host.F PP ⟨N i j, hN i j⟩ = 0) := fun i j =>
    GlobalTheory.T.idempotentSum_integral_div_uniformisers_iff_reduction_zero D Q es ϖ hes hc hϖ (N i j) (hN i j) (by
      have := congrFun (congrFun he i) j
      rwa [Matrix.smul_apply, smul_eq_mul] at this)
  constructor
  · intro h PP hPP
    ext i j
    rw [redM_of_int PP hN, Matrix.zero_apply]
    exact (key i j).1 (by simpa [Matrix.smul_apply] using h i j) PP hPP
  · intro h i j
    rw [Matrix.smul_apply, smul_eq_mul]
    refine (key i j).2 fun PP hPP => ?_
    have := congrFun (congrFun (h PP hPP) i) j
    rwa [redM_of_int PP hN] at this

end GlobalTheory.ZRep


open GlobalTheory.ZRep in
theorem GlobalTheory.ZRep.central_reps : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0
    : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra
    Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i
    : Fin D.R.m) (t : T0), (∃ eQ : AE D, IsIdemSum eQ (R.Q
    t)) ∧ (∃ ϖ : Pl D.host.E → 𝓞 D.host.E, ∀ PP : Pl D.host.E, ϖ PP ∈ PP.asIdeal ∧ ϖ PP ∉ PP.asIdeal ^ 2) ∧ ∀ (eQ
    : AE D) (es : Pl D.host.E → AE D) (ϖ : Pl D.host.E → 𝓞 D.host.E), IsIdemSum eQ (R.Q
    t) → (∀ PP ∈ R.Q t, Formalism.L2.NTheta.IsIdemAt (es
    PP) PP) → (∀ PP ∈ R.Q t, ϖ PP ∈ PP.asIdeal ∧ ϖ PP ∉ PP.asIdeal ^ 2) → eQ = ∑ PP ∈ R.Q t, es PP → (∃ z : GA D (Vc
    D i), mt (Vc D i) z = Matrix.diagonal fun _ => (1 + ∑ PP ∈ R.Q t, (es PP * (incA D ((ϖ PP
    : D.host.E)⁻¹) - 1) + cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) - 1)))) ∧ ∀ z : GA D (Vc D
    i), (mt (Vc D i) z = Matrix.diagonal fun _ => (1 + ∑ PP ∈ R.Q t, (es PP * (incA D ((ϖ PP
    : D.host.E)⁻¹) - 1) + cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) -
    1)))) → ∀ Λ : AddSubgroup (WO (Vc D i) (Wc D i)), Λ = latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW
    i) (fun _ => True) → (IsCentAt i (R.Q t) z ∧ SuppAt eQ (Vc D i) z ∧ (∃ x : (AE D)ˣ, IsDetAt (cA
    D eQ) (Vc D i) z x ∧ (x : AE D) = 1 + ∑ PP ∈ R.Q t, cA D (es PP) * (incA D (star (ϖ PP
    : D.host.E)) ^ (Vc D i).rank - 1)) ∧ (∀ w : WO (Vc D i) (Wc D i), IsHalf eQ w → actO (Vc D
    i) (Wc D i) z 1 w = (∑ PP ∈ R.Q t, es PP * incA D (ϖ PP : D.host.E)) • w ∧ actO (Vc D i) (Wc D
    i) z⁻¹ 1 w = (∑ PP ∈ R.Q t, es PP * incA D ((ϖ PP : D.host.E)⁻¹)) • w) ∧ (∀ w : WO (Vc D i) (Wc
    D i), IsHalf (cA D eQ) w → actO (Vc D i) (Wc D i) z 1 w = cA D (∑ PP ∈ R.Q t, es PP * incA D ((ϖ
    PP : D.host.E)⁻¹)) • w ∧ actO (Vc D i) (Wc D i) z⁻¹ 1 w = cA D (∑ PP ∈ R.Q t, es PP * incA D (ϖ
    PP : D.host.E)) • w)) ∧ ∃ (Λe Λc : AddSubgroup (WO (Vc D i) (Wc D i))) (Xe Xc Re Rc : Finset (WO
    (Vc D i) (Wc D i))), Rc = Xc.image (actO (Vc D i) (Wc D i) z 1) ∧ Re = Xe.image (actO (Vc D i)
    (Wc D i) z⁻¹ 1) ∧ ((∀ w, w ∈ Λe ↔ IsHalf eQ w ∧ actO (Vc D i) (Wc D i) z⁻¹ 1 w ∈ Λ) ∧
    (∀ u ∈ Λ, u.map (fun y => eQ * y) ∈ Λ) ∧ Λe ≤ Λ ∧ (∀ w ∈ Λ, IsHalf eQ w → actO (Vc D i) (Wc D
    i) z 1 w ∈ Λ) ∧ (∀ u, IsHalf (cA D eQ) u → (u ∈ Λ ↔ ∀ l ∈ Λ, IsHalf eQ l → R.ψ (symplO (Vc D i)
    (Wc D i) l u) = 1)) ∧ (∀ u, IsHalf (cA D eQ) u → ((∀ l ∈ Λe, IsHalf eQ l → R.ψ (symplO (Vc D i)
    (Wc D i) l u) = 1) ↔ actO (Vc D i) (Wc D i) z⁻¹ 1 u ∈ Λ)) ∧
    (∀ d ∈ Λ, IsHalf eQ d → d ∉ Λe → ∃ u, IsHalf (cA D eQ) u ∧ (∀ l ∈ Λe, IsHalf eQ l → R.ψ (symplO
    (Vc D i) (Wc D i) l u) = 1) ∧ R.ψ (symplO (Vc D i) (Wc D i) d u) ≠ 1) ∧
    (∀ x ∈ Xe, x ∈ Λ ∧ IsHalf eQ x) ∧ (∀ w ∈ Λ, IsHalf eQ w → ∃! x, x ∈ Xe ∧ w - x ∈ Λe) ∧
    (∀ u ∈ Rc, IsHalf (cA D eQ) u ∧ ∀ l ∈ Λe, IsHalf eQ l → R.ψ (symplO (Vc D i) (Wc D i) l u) = 1)
    ∧ (∀ u, IsHalf (cA D eQ) u → (∀ l ∈ Λe, IsHalf eQ l → R.ψ (symplO (Vc D i) (Wc D i) l
    u) = 1) → ∃! v, v ∈ Rc ∧ u - v ∈ Λ) ∧ (∀ u ∈ Rc, actO (Vc D i) (Wc D i) z⁻¹ 1 u ∈ Λ ∧ IsHalf (cA
    D eQ) u) ∧ (∀ w, actO (Vc D i) (Wc D i) z⁻¹ 1 w ∈ Λ → IsHalf (cA D
    eQ) w → ∃! v, v ∈ Rc ∧ w - v ∈ Λ) ∧ Xe.card = (∏ PP ∈ R.Q t, Nat.card (kP PP)) ^ ((Vc D i).rank
    * (Wc D i).rank) ∧ Rc.card = (∏ PP ∈ R.Q t, Nat.card (kP PP)) ^ ((Vc D i).rank * (Wc D i).rank)
    ∧ (∀ w, IsHalf eQ w → (w ∈ Λ ↔ IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) w))) ∧
    (∀ w ∈ Λ, ∀ w' ∈ Λ, IsHalf eQ w → IsHalf eQ w' → (w - w' ∈ Λe ↔ ∀ PP ∈ R.Q t, redM PP (frMapO
    (Vc D i) (Wc D i) (R.βV i) (R.βW i) w) = redM PP (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i)
    w'))) ∧ (∀ Y : ∀ PP : Pl D.host.E, Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) (kP
    PP), ∃! x, x ∈ Xe ∧ ∀ PP ∈ R.Q t, redM PP (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i)
    x) = Y PP)) ∧ ((∀ w, w ∈ Λc ↔ IsHalf (cA D eQ) w ∧ actO (Vc D i) (Wc D i) z 1 w ∈ Λ) ∧
    (∀ u ∈ Λ, u.map (fun y => (cA D eQ) * y) ∈ Λ) ∧ Λc ≤ Λ ∧ (∀ w ∈ Λ, IsHalf (cA D eQ) w → actO (Vc
    D i) (Wc D i) z⁻¹ 1 w ∈ Λ) ∧ (∀ u, IsHalf (cA D (cA D eQ)) u → (u ∈ Λ ↔ ∀ l ∈ Λ, IsHalf (cA D
    eQ) l → R.ψ (symplO (Vc D i) (Wc D i) l u) = 1)) ∧ (∀ u, IsHalf (cA D (cA D
    eQ)) u → ((∀ l ∈ Λc, IsHalf (cA D eQ) l → R.ψ (symplO (Vc D i) (Wc D i) l u) = 1) ↔ actO (Vc D
    i) (Wc D i) z 1 u ∈ Λ)) ∧ (∀ d ∈ Λ, IsHalf (cA D eQ) d → d ∉ Λc → ∃ u, IsHalf (cA D (cA D
    eQ)) u ∧ (∀ l ∈ Λc, IsHalf (cA D eQ) l → R.ψ (symplO (Vc D i) (Wc D i) l u) = 1) ∧ R.ψ (symplO
    (Vc D i) (Wc D i) d u) ≠ 1) ∧ (∀ x ∈ Xc, x ∈ Λ ∧ IsHalf (cA D eQ) x) ∧ (∀ w ∈ Λ, IsHalf (cA D
    eQ) w → ∃! x, x ∈ Xc ∧ w - x ∈ Λc) ∧ (∀ u ∈ Re, IsHalf (cA D (cA D eQ)) u ∧ ∀ l ∈ Λc, IsHalf (cA
    D eQ) l → R.ψ (symplO (Vc D i) (Wc D i) l u) = 1) ∧ (∀ u, IsHalf (cA D (cA D
    eQ)) u → (∀ l ∈ Λc, IsHalf (cA D eQ) l → R.ψ (symplO (Vc D i) (Wc D i) l
    u) = 1) → ∃! v, v ∈ Re ∧ u - v ∈ Λ) ∧ (∀ u ∈ Re, actO (Vc D i) (Wc D i) z 1 u ∈ Λ ∧ IsHalf (cA D
    (cA D eQ)) u) ∧ (∀ w, actO (Vc D i) (Wc D i) z 1 w ∈ Λ → IsHalf (cA D (cA D
    eQ)) w → ∃! v, v ∈ Re ∧ w - v ∈ Λ) ∧ Xc.card = (∏ PP ∈ R.Q t, Nat.card (kP PP)) ^ ((Vc D i).rank
    * (Wc D i).rank) ∧ Re.card = (∏ PP ∈ R.Q t, Nat.card (kP PP)) ^ ((Vc D i).rank * (Wc D i).rank)
    ∧ (∀ w, IsHalf (cA D eQ) w → (w ∈ Λ ↔ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) w)))
    ∧ (∀ w ∈ Λ, ∀ w' ∈ Λ, IsHalf (cA D eQ) w → IsHalf (cA D eQ) w' → (w - w' ∈ Λc ↔
    ∀ PP ∈ R.Q t, redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) w) = redM PP (frMapAdj (Vc D
    i) (Wc D i) (R.βV i) (R.βW i) w'))) ∧ (∀ Y : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin
    (Wc D i).rank) (kP PP), ∃! x, x ∈ Xc ∧ ∀ PP ∈ R.Q t, redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV
    i) (R.βW i) x) = Y PP)) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hR hQ i t
  obtain ⟨hvac, -, -, -⟩ := hR.thP.vP i t
  have hψ : IsStdChar D R.ψ (-1) := hvac.1
  obtain ⟨cV, hcV⟩ := hR.lev.βV i
  obtain ⟨cW, hcW⟩ := hR.lev.βW i
  have fV : Formalism.L2.DIV.IsFrame (R.βV i) (R.ΛV i) := hcV.1
  have fW : Formalism.L2.DIV.IsFrame (R.βW i) (R.ΛW i) := hcW.1
  have sV : IsSelfDualC (Vc D i) (R.ΛV i) :=
    GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hR.lev.βV i))
  have sW : IsSelfDualC (Wc D i) (R.ΛW i) :=
    GlobalTheory.AdTh.RecPair.selfDual_of_coe (GlobalTheory.AdTh.RecPair.coe_eq_of_frame (hR.lev.βW i))
  have hP := hQ.2 t
  refine ⟨?_, GlobalTheory.T.exists_uniformiser_family_hostField_integers D, ?_⟩
  · obtain ⟨f, eg, eQ, fg, -, hq, -⟩ := (GlobalTheory.FlatVecExist.flatVec_existsUnique D G Pl0 T0 A Ks R F hR hQ i t).1
    exact ⟨eQ, hq⟩
  intro eQ es ϖ hq hes hϖ heQ
  subst heQ
  have hc : (∑ PP ∈ R.Q t, es PP) * cA D (∑ PP ∈ R.Q t, es PP) = 0 := hq.2
  have hϖ0 : ∀ PP ∈ R.Q t, ϖ PP ≠ 0 := fun PP hPP h0 => (hϖ PP hPP).2 (by rw [h0]; exact zero_mem _)
  obtain ⟨hex, hZ⟩ := GlobalTheory.T.centralScalar_inverse_uniformisers_idempotent_sum D (Vc D i) (R.Q t) es ϖ hes hc hϖ0
  refine ⟨hex, fun z hz Λ hΛ => ?_⟩
  obtain ⟨hcen, hGf, hsupp, hdet, hinv, ha1, ha2, ha3, ha4⟩ := hZ z hz

  have act1 : ∀ w : WO (Vc D i) (Wc D i), actO (Vc D i) (Wc D i) z 1 w = cA D (1 + ∑ PP ∈ R.Q t, (es PP * (incA D ((ϖ PP : D.host.E)⁻¹) - 1) + cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) - 1))) • w := fun w => actO_one_eq z _ hinv w
  have act2 : ∀ w : WO (Vc D i) (Wc D i), actO (Vc D i) (Wc D i) z⁻¹ 1 w = (1 + ∑ PP ∈ R.Q t, (es PP * (incA D ((ϖ PP : D.host.E)⁻¹) - 1) + cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) - 1))) • w := fun w =>
    actO_one_eq z⁻¹ _ (by rw [inv_inv]; exact hz) w
  have zz : ∀ w : WO (Vc D i) (Wc D i), actO (Vc D i) (Wc D i) z 1 (actO (Vc D i) (Wc D i) z⁻¹ 1 w) = w := fun w => by
    rw [Formalism.IndefR.Fin.LevelGroupLemmas.Lat.actO_actO, mul_inv_cancel, mul_one, Formalism.IndefR.Fin.LevelGroupLemmas.Lat.actO_one]
  have z'z : ∀ w : WO (Vc D i) (Wc D i), actO (Vc D i) (Wc D i) z⁻¹ 1 (actO (Vc D i) (Wc D i) z 1 w) = w := fun w => by
    rw [Formalism.IndefR.Fin.LevelGroupLemmas.Lat.actO_actO, inv_mul_cancel, mul_one, Formalism.IndefR.Fin.LevelGroupLemmas.Lat.actO_one]
  have actsub : ∀ (g : GA D (Vc D i)) (x y : WO (Vc D i) (Wc D i)), actO (Vc D i) (Wc D i) g 1 (x - y) =
      actO (Vc D i) (Wc D i) g 1 x - actO (Vc D i) (Wc D i) g 1 y := fun g x y => by
    unfold actO; rw [Matrix.mul_sub, Matrix.sub_mul]
  set e := ∑ PP ∈ R.Q t, es PP with he
  set π := ∑ PP ∈ R.Q t, es PP * incA D (ϖ PP : D.host.E) with hπ
  set π' := ∑ PP ∈ R.Q t, es PP * incA D ((ϖ PP : D.host.E)⁻¹) with hπ'
  have part1 : IsCentAt i (R.Q t) z ∧ SuppAt e (Vc D i) z ∧ (∃ x : (AE D)ˣ, IsDetAt (cA D e) (Vc D i) z x ∧ (x : AE D) = 1 + ∑ PP ∈ R.Q t, cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) ^ (Vc D i).rank - 1)) ∧ (∀ w : WO (Vc D i) (Wc D i), IsHalf e w → actO (Vc D i) (Wc D i) z 1 w = π • w ∧ actO (Vc D i) (Wc D i) z⁻¹ 1 w = π' • w) ∧ (∀ w : WO (Vc D i) (Wc D i), IsHalf (cA D e) w → actO (Vc D i) (Wc D i) z 1 w = cA D π' • w ∧ actO (Vc D i) (Wc D i) z⁻¹ 1 w = cA D π • w) := by
    refine ⟨⟨hcen, hGf, e, hq, hsupp⟩, hsupp, hdet, fun w hw => ⟨?_, ?_⟩, fun w hw => ⟨?_, ?_⟩⟩
    · rw [act1, smul_half _ hw, ha2]
    · rw [act2, smul_half _ hw, ha1]
    · rw [act1, smul_half _ hw, ha4]
    · rw [act2, smul_half _ hw, ha3]
  refine ⟨part1, ?_⟩
  have he_idem : e * e = e := GlobalTheory.PlaceDatum.idemSum_mul_self hq
  have heInt : finPart D e ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, he_idem])
  have heInf : infPart D e = 0 := Formalism.IndefR.Fin.LevelGroupLemmas.Lat.infPart_of_idemSum hq
  have hceInt : finPart D (cA D e) ∈ intAE D := by
    rw [Formalism.IndefR.Fin.LevelGroupLemmas.Lat.finPart_cA]; exact Formalism.IndefR.Fin.LevelGroupLemmas.Lat.cA_mem_intAE heInt
  have hceInf : infPart D (cA D e) = 0 := Formalism.IndefR.Fin.LevelGroupLemmas.Lat.infPart_cA_idemSum hq
  have hce_idem : cA D e * cA D e = cA D e := by rw [← map_mul, he_idem]
  have hcc : cA D e * cA D (cA D e) = 0 := by rw [cA_cA, mul_comm, hc]
  have hπi : toEAf D π ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hπ, map_sum]
    exact sum_mem fun PP hPP => by
      rw [map_mul]
      exact mul_mem (GlobalTheory.IdemRes.resS_idem_eq_one D _ PP (hes PP hPP)).1 (GlobalTheory.IdemIntegral.eToEAf_int D (ϖ PP))
  subst hΛ
  set Λ := latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) (fun _ => True) with hΛ
  have H1e : ∀ w : WO (Vc D i) (Wc D i), IsHalf e w → (w ∈ Λ ↔ IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) w)) :=
    GlobalTheory.T.mem_completedLattice_half_iff_frameMatrix_integral D _ _ _ _ _ _ sV sW fV fW (R.Q t) e hq hP
  have H1c : ∀ w : WO (Vc D i) (Wc D i), IsHalf (cA D e) w → (w ∈ Λ ↔ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) w)) :=
    fun w hw => ⟨fun h => GlobalTheory.HalfAdjInt.frMapAdj_int_of_half D _ _ _ _ _ _ sV sW fV fW _ e hq hP w h hw,
      fun h => GlobalTheory.HalfAdjLattice.mem_latO_of_adj_int D _ _ _ _ _ _ sV sW fV fW _ e hq hP w hw h⟩
  have smulΛe : ∀ c : AE D, toEAf D c ∈ Formalism.L2.Herm.intAf D.host.F D.host.E → ∀ w ∈ Λ, IsHalf e w → c • w ∈ Λ :=
    fun c hci w hw hh => (H1e _ (isHalf_smul c hh)).2 (by
      rw [GlobalTheory.RedHalfDrop.frMapO_smul_eq]; exact isIntM_smul hci ((H1e w hh).1 hw))
  have smulΛc : ∀ c : AE D, toEAf D (cA D c) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E → ∀ w ∈ Λ, IsHalf (cA D e) w → c • w ∈ Λ :=
    fun c hci w hw hh => (H1c _ (isHalf_smul c hh)).2 (by
      rw [GlobalTheory.RedHalfDrop.frMapAdj_smul_eq]; exact isIntM_smul hci ((H1c w hh).1 hw))
  have hπci : toEAf D (cA D (cA D π)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by rw [cA_cA]; exact hπi
  have Dc := GlobalTheory.T.mem_completedLattice_conjugateHalf_iff_dual D R.ψ _ _ _ _ hψ sV sW e he_idem hc heInf heInt
  have De := GlobalTheory.T.mem_completedLattice_conjugateHalf_iff_dual D R.ψ _ _ _ _ hψ sV sW (cA D e) hce_idem hcc hceInf hceInt

  let Λe : AddSubgroup (WO (Vc D i) (Wc D i)) :=
    { carrier := {w | IsHalf e w ∧ actO (Vc D i) (Wc D i) z⁻¹ 1 w ∈ Λ}
      add_mem' := fun {x y} hx hy => ⟨Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_add hx.1 hy.1, by
        rw [act2, smul_add, ← act2, ← act2]; exact add_mem hx.2 hy.2⟩
      zero_mem' := ⟨Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_zero e, by rw [act2, smul_zero]; exact zero_mem _⟩
      neg_mem' := fun {x} hx => ⟨by
        have := isHalf_smul (-1 : AE D) hx.1; rwa [neg_one_smul] at this, by
        rw [act2, smul_neg, ← act2]; exact neg_mem hx.2⟩ }
  let Λc : AddSubgroup (WO (Vc D i) (Wc D i)) :=
    { carrier := {w | IsHalf (cA D e) w ∧ actO (Vc D i) (Wc D i) z 1 w ∈ Λ}
      add_mem' := fun {x y} hx hy => ⟨Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_add hx.1 hy.1, by
        rw [act1, smul_add, ← act1, ← act1]; exact add_mem hx.2 hy.2⟩
      zero_mem' := ⟨Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_zero _, by rw [act1, smul_zero]; exact zero_mem _⟩
      neg_mem' := fun {x} hx => ⟨by
        have := isHalf_smul (-1 : AE D) hx.1; rwa [neg_one_smul] at this, by
        rw [act1, smul_neg, ← act1]; exact neg_mem hx.2⟩ }
  have memΛe : ∀ w, w ∈ Λe ↔ IsHalf e w ∧ actO (Vc D i) (Wc D i) z⁻¹ 1 w ∈ Λ := fun w => Iff.rfl
  have memΛc : ∀ w, w ∈ Λc ↔ IsHalf (cA D e) w ∧ actO (Vc D i) (Wc D i) z 1 w ∈ Λ := fun w => Iff.rfl
  have H2e : ∀ w ∈ Λ, ∀ w' ∈ Λ, IsHalf e w → IsHalf e w' → (w - w' ∈ Λe ↔ ∀ PP ∈ R.Q t,
      redM PP (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) w) = redM PP (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) w')) := by
    intro w hw w' hw' hh hh'
    have hd := isHalf_sub hh hh'
    have hi := (H1e w hh).1 hw
    have hi' := (H1e w' hh').1 hw'
    have hN : IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (w - w')) := (H1e _ hd).1 (sub_mem hw hw')
    have heN : toEAf D e • frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (w - w') = frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (w - w') := by
      rw [← GlobalTheory.RedHalfDrop.frMapO_smul_eq]; congr 1; ext a b; exact hd a b
    rw [memΛe, act2, smul_half _ hd, ha1, H1e _ (isHalf_smul _ hd), GlobalTheory.RedHalfDrop.frMapO_smul_eq,
      isIntM_smul_iff (R.Q t) es ϖ hes hc hϖ _ hN heN]
    constructor
    · rintro ⟨-, h⟩ PP hPP
      have := h PP hPP
      rw [frMapO_sub, redM_sub PP hi hi'] at this
      exact sub_eq_zero.1 this
    · intro h
      refine ⟨hd, fun PP hPP => ?_⟩
      rw [frMapO_sub, redM_sub PP hi hi', h PP hPP, sub_self]
  have H2c : ∀ w ∈ Λ, ∀ w' ∈ Λ, IsHalf (cA D e) w → IsHalf (cA D e) w' → (w - w' ∈ Λc ↔ ∀ PP ∈ R.Q t,
      redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) w) = redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) w')) := by
    intro w hw w' hw' hh hh'
    have hd := isHalf_sub hh hh'
    have hi := (H1c w hh).1 hw
    have hi' := (H1c w' hh').1 hw'
    have hN : IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) (w - w')) := (H1c _ hd).1 (sub_mem hw hw')
    have heN : toEAf D e • frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) (w - w') = frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) (w - w') := by
      have := GlobalTheory.RedHalfDrop.frMapAdj_smul_eq (R.βV i) (R.βW i) (cA D e) (w - w')
      rw [cA_cA] at this
      rw [← this]; congr 1; ext a b; exact hd a b
    rw [memΛc, act1, smul_half _ hd, ha4, H1c _ (isHalf_smul _ hd), GlobalTheory.RedHalfDrop.frMapAdj_smul_eq, cA_cA,
      isIntM_smul_iff (R.Q t) es ϖ hes hc hϖ _ hN heN]
    constructor
    · rintro ⟨-, h⟩ PP hPP
      have := h PP hPP
      rw [frMapAdj_sub, redM_sub PP hi hi'] at this
      exact sub_eq_zero.1 this
    · intro h
      refine ⟨hd, fun PP hPP => ?_⟩
      rw [frMapAdj_sub, redM_sub PP hi hi', h PP hPP, sub_self]
  have H3e : ∀ Y : ∀ PP : Pl D.host.E, Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) (kP PP), ∃ w, IsHalf e w ∧
      IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) w) ∧ ∀ PP ∈ R.Q t, redM PP (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) w) = Y PP := by
    intro Y
    choose N hN heN hNY using fun (ij : Fin (Wc D i).rank × Fin (Vc D i).rank) =>
      GlobalTheory.T.exists_integral_lift_residues_idempotentSum D (R.Q t) es hes hc (fun PP => Y PP ij.1 ij.2)
    obtain ⟨y, hyh, -, hyz⟩ := GlobalTheory.HalfDuality.exists_half_frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) e he_idem
      (fun a b => N (a, b)) (fun a b => heN (a, b))
    have hI : IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) y) := by rw [hyz]; exact fun a b => hN (a, b)
    refine ⟨y, hyh, hI, fun PP hPP => ?_⟩
    ext a b
    rw [Formalism.IndefR.Fin.LevelGroupLemmas.Lat.redM_of_int PP hI]
    have := hNY (a, b) PP hPP
    convert this using 2
    exact Subtype.ext (congrFun (congrFun hyz a) b)
  have WeightCompositions : ∀ Y : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP), ∃ w, IsHalf (cA D e) w ∧
      IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) w) ∧ ∀ PP ∈ R.Q t, redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) w) = Y PP := by
    intro Y
    choose N hN heN hNY using fun (ij : Fin (Vc D i).rank × Fin (Wc D i).rank) =>
      GlobalTheory.T.exists_integral_lift_residues_idempotentSum D (R.Q t) es hes hc (fun PP => Y PP ij.1 ij.2)
    obtain ⟨y, hyh, -, hyz⟩ := GlobalTheory.T.exists_conjugateHalf_prescribed_adjoint_frameMatrix D (Vc D i) (Wc D i) (R.βV i) (R.βW i) e he_idem
      (fun a b => N (a, b)) (fun a b => heN (a, b))
    have hI : IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) y) := by rw [hyz]; exact fun a b => hN (a, b)
    refine ⟨y, hyh, hI, fun PP hPP => ?_⟩
    ext a b
    rw [Formalism.IndefR.Fin.LevelGroupLemmas.Lat.redM_of_int PP hI]
    have := hNY (a, b) PP hPP
    convert this using 2
    exact Subtype.ext (congrFun (congrFun hyz a) b)
  obtain ⟨Xe, hXe1, hXe2, hXecard, hXeY⟩ := GlobalTheory.T.lattice_half_representatives_mod_reductions D (Vc D i) (Wc D i) Λ Λe e (R.Q t)
    (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i)) (frMapO_sub _ _) H1e H2e H3e
  obtain ⟨Xc, hXc1, hXc2, hXccard, hXcY⟩ := GlobalTheory.T.lattice_half_representatives_mod_reductions D (Vc D i) (Wc D i) Λ Λc (cA D e) (R.Q t)
    (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i)) (frMapAdj_sub _ _) H1c H2c WeightCompositions

  have cl6e : ∀ u, IsHalf (cA D e) u → ((∀ l ∈ Λe, IsHalf e l → R.ψ (symplO (Vc D i) (Wc D i) l u) = 1) ↔
      actO (Vc D i) (Wc D i) z⁻¹ 1 u ∈ Λ) := by
    intro u hu
    constructor
    · intro h
      refine (Dc _ (Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ _ _ hu)).2 fun l hl hlh => ?_
      have := h (actO (Vc D i) (Wc D i) z 1 l) ⟨Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ _ _ hlh, by rw [z'z]; exact hl⟩
        (Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ _ _ hlh)
      rw [← GlobalTheory.SplitHecke.symplO_actO _ _ z 1, zz]; exact this
    · intro h l hl hlh
      have := (Dc _ (Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ _ _ hu)).1 h (actO (Vc D i) (Wc D i) z⁻¹ 1 l) hl.2
        (Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ _ _ hlh)
      rwa [GlobalTheory.SplitHecke.symplO_actO] at this
  have cl6c : ∀ u, IsHalf (cA D (cA D e)) u → ((∀ l ∈ Λc, IsHalf (cA D e) l → R.ψ (symplO (Vc D i) (Wc D i) l u) = 1) ↔
      actO (Vc D i) (Wc D i) z 1 u ∈ Λ) := by
    intro u hu
    constructor
    · intro h
      refine (De _ (Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ _ _ hu)).2 fun l hl hlh => ?_
      have := h (actO (Vc D i) (Wc D i) z⁻¹ 1 l) ⟨Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ _ _ hlh, by rw [zz]; exact hl⟩
        (Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ _ _ hlh)
      rw [← GlobalTheory.SplitHecke.symplO_actO _ _ z⁻¹ 1, z'z]; exact this
    · intro h l hl hlh
      have := (De _ (Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ _ _ hu)).1 h (actO (Vc D i) (Wc D i) z 1 l) hl.2
        (Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ _ _ hlh)
      rwa [GlobalTheory.SplitHecke.symplO_actO] at this
  have cl13e : ∀ w, actO (Vc D i) (Wc D i) z⁻¹ 1 w ∈ Λ → IsHalf (cA D e) w →
      ∃! v, v ∈ Xc.image (actO (Vc D i) (Wc D i) z 1) ∧ w - v ∈ Λ := by
    intro w hw hwh
    obtain ⟨x, ⟨hxX, hxd⟩, hxu⟩ := hXc2 _ hw (Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ _ _ hwh)
    refine ⟨actO (Vc D i) (Wc D i) z 1 x, ⟨Finset.mem_image_of_mem _ hxX, by
      have := hxd.2; rwa [actsub, zz] at this⟩, ?_⟩
    rintro v ⟨hv, hvw⟩
    obtain ⟨x', hx', rfl⟩ := Finset.mem_image.1 hv
    rw [hxu x' ⟨hx', isHalf_sub (Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ _ _ hwh) (hXc1 x' hx').2, by
      rw [actsub, zz]; exact hvw⟩]
  have cl13c : ∀ w, actO (Vc D i) (Wc D i) z 1 w ∈ Λ → IsHalf (cA D (cA D e)) w →
      ∃! v, v ∈ Xe.image (actO (Vc D i) (Wc D i) z⁻¹ 1) ∧ w - v ∈ Λ := by
    intro w hw hwh
    rw [cA_cA] at hwh
    obtain ⟨x, ⟨hxX, hxd⟩, hxu⟩ := hXe2 _ hw (Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ _ _ hwh)
    refine ⟨actO (Vc D i) (Wc D i) z⁻¹ 1 x, ⟨Finset.mem_image_of_mem _ hxX, by
      have := hxd.2; rwa [actsub, z'z] at this⟩, ?_⟩
    rintro v ⟨hv, hvw⟩
    obtain ⟨x', hx', rfl⟩ := Finset.mem_image.1 hv
    rw [hxu x' ⟨hx', isHalf_sub (Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ _ _ hwh) (hXe1 x' hx').2, by
      rw [actsub, z'z]; exact hvw⟩]
  have injz : Function.Injective (actO (Vc D i) (Wc D i) z 1) := fun x y h => by rw [← z'z x, h, z'z]
  have injz' : Function.Injective (actO (Vc D i) (Wc D i) z⁻¹ 1) := fun x y h => by rw [← zz x, h, zz]
  refine ⟨Λe, Λc, Xe, Xc, Xe.image (actO (Vc D i) (Wc D i) z⁻¹ 1), Xc.image (actO (Vc D i) (Wc D i) z 1), rfl, rfl, ?_, ?_⟩
  · refine ⟨memΛe, fun u hu => ?_, fun w hw => ?_, fun w hw hh => ?_, Dc, cl6e, fun d hd hdh hdn => ?_, hXe1, hXe2,
      fun u hu => ?_, fun u hu h => cl13e u ((cl6e u hu).1 h) hu, fun u hu => ?_, cl13e, by rw [hXecard, mul_comm],
      by rw [Finset.card_image_of_injective _ injz, hXccard], H1e, H2e, hXeY⟩
    · have e1 : u.map (fun y => e * y) = e • u := by ext a b; simp [Matrix.smul_apply]
      rw [e1]; exact Formalism.IndefR.Fin.LevelGroupLemmas.Lat.smul_mem_latAll heInt hu
    · obtain ⟨hh, hm⟩ := hw
      have hh' := Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ z⁻¹ 1 hh
      rw [← zz w, (part1.2.2.2.1 _ hh').1]
      exact smulΛe π hπi _ hm hh'
    · rw [(part1.2.2.2.1 _ hh).1]; exact smulΛe π hπi w hw hh
    · have hv : actO (Vc D i) (Wc D i) z⁻¹ 1 d ∉ Λ := fun h => hdn ⟨hdh, h⟩
      have hvh : IsHalf (cA D (cA D e)) (actO (Vc D i) (Wc D i) z⁻¹ 1 d) := by
        rw [cA_cA]; exact Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ _ _ hdh
      obtain ⟨l, hl, hlh, hne⟩ : ∃ l ∈ Λ, IsHalf (cA D e) l ∧
          R.ψ (symplO (Vc D i) (Wc D i) l (actO (Vc D i) (Wc D i) z⁻¹ 1 d)) ≠ 1 := by
        by_contra hcon
        push Not at hcon
        exact hv ((De _ hvh).2 hcon)
      refine ⟨actO (Vc D i) (Wc D i) z 1 l, Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ _ _ hlh,
        (cl6e _ (Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ _ _ hlh)).2 (by rw [z'z]; exact hl), ?_⟩
      rw [← GlobalTheory.SplitHecke.symplO_actO _ _ z⁻¹ 1, z'z, GlobalTheory.OrientedHeis.symplO_skew, AddChar.map_neg_eq_inv]
      exact fun h => hne (inv_eq_one.1 h)
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hu
      exact ⟨Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ _ _ (hXc1 x hx).2,
        (cl6e _ (Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ _ _ (hXc1 x hx).2)).2 (by rw [z'z]; exact (hXc1 x hx).1)⟩
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hu
      exact ⟨by rw [z'z]; exact (hXc1 x hx).1, Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ _ _ (hXc1 x hx).2⟩
  · refine ⟨memΛc, fun u hu => ?_, fun w hw => ?_, fun w hw hh => ?_, De, cl6c, fun d hd hdh hdn => ?_, hXc1, hXc2,
      fun u hu => ?_, fun u hu h => cl13c u ((cl6c u hu).1 h) hu, fun u hu => ?_, cl13c, hXccard,
      by rw [Finset.card_image_of_injective _ injz', hXecard, mul_comm], H1c, H2c, hXcY⟩
    · have e1 : u.map (fun y => cA D e * y) = cA D e • u := by ext a b; simp [Matrix.smul_apply]
      rw [e1]; exact Formalism.IndefR.Fin.LevelGroupLemmas.Lat.smul_mem_latAll hceInt hu
    · obtain ⟨hh, hm⟩ := hw
      have hh' := Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ z 1 hh
      rw [← z'z w, (part1.2.2.2.2 _ hh').2]
      exact smulΛc (cA D π) hπci _ hm hh'
    · rw [(part1.2.2.2.2 _ hh).2]; exact smulΛc (cA D π) hπci w hw hh
    · have hv : actO (Vc D i) (Wc D i) z 1 d ∉ Λ := fun h => hdn ⟨hdh, h⟩
      have hvh : IsHalf (cA D e) (actO (Vc D i) (Wc D i) z 1 d) := Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ _ _ hdh
      obtain ⟨l, hl, hlh, hne⟩ : ∃ l ∈ Λ, IsHalf e l ∧
          R.ψ (symplO (Vc D i) (Wc D i) l (actO (Vc D i) (Wc D i) z 1 d)) ≠ 1 := by
        by_contra hcon
        push Not at hcon
        exact hv ((Dc _ hvh).2 hcon)
      have hlh' : IsHalf (cA D (cA D e)) (actO (Vc D i) (Wc D i) z⁻¹ 1 l) := by
        rw [cA_cA]; exact Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ _ _ hlh
      refine ⟨actO (Vc D i) (Wc D i) z⁻¹ 1 l, hlh', (cl6c _ hlh').2 (by rw [zz]; exact hl), ?_⟩
      rw [← GlobalTheory.SplitHecke.symplO_actO _ _ z 1, zz, GlobalTheory.OrientedHeis.symplO_skew, AddChar.map_neg_eq_inv]
      exact fun h => hne (inv_eq_one.1 h)
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hu
      have hxh : IsHalf (cA D (cA D e)) (actO (Vc D i) (Wc D i) z⁻¹ 1 x) := by
        rw [cA_cA]; exact Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ _ _ (hXe1 x hx).2
      exact ⟨hxh, (cl6c _ hxh).2 (by rw [zz]; exact (hXe1 x hx).1)⟩
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hu
      exact ⟨by rw [zz]; exact (hXe1 x hx).1, by rw [cA_cA]; exact Formalism.IndefR.Fin.LevelGroupLemmas.Lat.isHalf_actO _ _ _ (hXe1 x hx).2⟩
