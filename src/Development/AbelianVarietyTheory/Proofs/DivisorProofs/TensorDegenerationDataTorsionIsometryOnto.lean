module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareZeroLiftSystemFiltrationInfEqAndFull
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartValueIsIntegralOfIntegralAtPoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorQuotientTorsionOrderActionMatrix

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingTensorTorsionEqProdComponents
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorsionPairingEqProdFactorPairings
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorsionPairingEqProdFactorPairings
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

namespace GlobalTheory.Mum.TensTor.PairVal

theorem cubN_succ {A U : Type} [CommGroup A] [CommGroup U] (θ : A → A → A → U) (k : ℕ) (m x : A) :
    cubN θ (k + 1) 1 m x = cubN θ k 1 m x * θ (m ^ k) m x := by
  simp [cubN, Finset.prod_range_succ]

theorem comp_one {B C : Type} [CommGroup B] [CommGroup C] {r : ℕ} {φ : B → Fin r → C}
    (h : ∀ x y j, φ (x * y) j = φ x j * φ y j) (j : Fin r) : φ 1 j = 1 := by
  have := h 1 1 j
  rw [_root_.one_mul] at this
  exact mul_eq_left.1 this.symm

theorem comp_pow {B C : Type} [CommGroup B] [CommGroup C] {r : ℕ} {φ : B → Fin r → C}
    (h : ∀ x y j, φ (x * y) j = φ x j * φ y j) (x : B) (m : ℕ) (j : Fin r) : φ (x ^ m) j = φ x j ^ m := by
  induction m with
  | zero => simp [comp_one h]
  | succ m ih => rw [pow_succ, h, ih, pow_succ]

variable {F : Type} [Field F] {N N' : NumD F} {r : ℕ}

theorem cube_prod (W : Matrix (Fin r) (Fin r) ℤ) (φ : N'.A → Fin r → N.A) (U : N'.A → Fˣ)
    (hφ : ∀ x y j, φ (x * y) j = φ x j * φ y j)
    (hc : ∀ x y u, N'.θ x y u * U (x * y * u) * U x * U y * U u =
      (∏ i, ∏ j, (N.θ (φ x i * φ x j) (φ y i * φ y j) (φ u i * φ u j) /
        (N.θ (φ x i) (φ y i) (φ u i) * N.θ (φ x j) (φ y j) (φ u j))) ^ W i j) *
      U (x * y) * U (x * u) * U (y * u) * U 1) (k : ℕ) (b a : N'.A) :
    cubN N'.θ k 1 b a * U (b ^ k * a) * U 1 * (U b * U a) ^ k =
      (∏ i, ∏ j, (cubN N.θ k 1 (φ b i * φ b j) (φ a i * φ a j) /
        (cubN N.θ k 1 (φ b i) (φ a i) * cubN N.θ k 1 (φ b j) (φ a j))) ^ W i j) *
      U (b ^ k) * U a * (U (b * a) * U 1) ^ k := by
  induction k with
  | zero => simp [cubN, mul_comm]
  | succ k ih =>
    have h := hc (b ^ k) b a
    simp only [comp_pow hφ, ← mul_pow] at h
    have split : ∀ P p Q q R s : Fˣ, P * p / (Q * q * (R * s)) = P / (Q * R) * (p / (q * s)) := by
      intro P p Q q R s
      rw [_root_.mul_mul_mul_comm, div_mul_div_comm]
    simp only [cubN_succ, split, mul_zpow, Finset.prod_mul_distrib, pow_succ]
    apply Additive.ofMul.injective
    have ih' := congrArg Additive.ofMul ih
    have h' := congrArg Additive.ofMul h
    simp only [ofMul_mul, ofMul_pow] at ih' h' ⊢
    linear_combination (norm := abel) ih' + h'

theorem torusExtensionPair_correction_eq_value_quotient (N : NumD F) (g g' : N.Gt) (z z' : N.X) (C C₁ C₂ : Fˣ) :
    g'.s z * g.s z' / (N.θ (N.c z') g'.b (N.c z) * N.θ (N.c z') g'.b g.b * N.θ (N.c z) g.b (N.c z' * g'.b)) *
      (C / (C₁ * C₂)) = (g * g').s (z + z') * C / (g.s z * C₁ * (g'.s z' * C₂)) := by
  rw [NumD.Gt.mul_s, N.c_add]
  have m1 := g.mult z z'
  have m2 := g'.mult z z'
  have co := N.cub.coc (N.c z) (N.c z') g'.b g.b
  rw [N.cub.s12 (N.c z * N.c z') g'.b g.b] at co
  rw [N.cub.s12 (N.c z') g'.b (N.c z), N.cub.s01 (N.c z') (N.c z), N.cub.s12 (N.c z) g.b]
  apply Additive.ofMul.injective
  replace m1 := congrArg Additive.ofMul m1
  replace m2 := congrArg Additive.ofMul m2
  replace co := congrArg Additive.ofMul co
  simp only [ofMul_mul, ofMul_div] at m1 m2 co ⊢
  linear_combination (norm := abel) -m1 - m2 + co

end GlobalTheory.Mum.TensTor.PairVal

namespace GlobalTheory.Mum.TensTor.PairVal

variable {F : Type} [Field F] {N N' : NumD F} {r : ℕ}

theorem tk_tens (W : Matrix (Fin r) (Fin r) ℤ) (φ : N'.A → Fin r → N.A) (e : N'.X → Fin r → N.X) (wv : N'.A → F)
    (hT : TensFacts W φ e wv) (U : N'.A → Fˣ) (hU : ∀ x, wv x = (U x : F)) {k : ℕ} (q' p' : N'.QT k)
    (qs ps : Fin r → N.QT k) (hq : QRelV W φ e wv q' qs) (hp : QRelV W φ e wv p' ps) :
    N'.tk q' p' * (U p'.1.2.b * U q'.1.2.b) ^ k =
      (∏ i, ∏ j, (N.tk (qs i * qs j) (ps i * ps j) / (N.tk (qs i) (ps i) * N.tk (qs j) (ps j))) ^ W i j) *
      (U (p'.1.2.b * q'.1.2.b) * U 1) ^ k := by
  obtain ⟨hφ, -, -, -, -, -, hcube, -⟩ := hT
  have hcU : ∀ x y u, N'.θ x y u * U (x * y * u) * U x * U y * U u =
      (∏ i, ∏ j, (N.θ (φ x i * φ x j) (φ y i * φ y j) (φ u i * φ u j) /
        (N.θ (φ x i) (φ y i) (φ u i) * N.θ (φ x j) (φ y j) (φ u j))) ^ W i j) *
      U (x * y) * U (x * u) * U (y * u) * U 1 := by
    intro x y u
    apply Units.ext
    simp only [Units.val_mul, ← hU]
    exact hcube x y u
  have hA := cube_prod W φ U hφ hcU k p'.1.2.b q'.1.2.b
  simp only [hp.2.1, hq.2.1] at hA
  have hG := hq.2.2 p'.1.1.toAdd
  simp only [hU, ← Units.val_mul] at hG
  replace hG := Units.ext hG
  simp only [hp.1, hq.2.1, ← N'.QT_pow_b p'] at hG
  have hX : ∀ i j, N.tk (qs i * qs j) (ps i * ps j) / (N.tk (qs i) (ps i) * N.tk (qs j) (ps j)) =
      (qs j).1.2.s (ps i).1.1.toAdd * (qs i).1.2.s (ps j).1.1.toAdd /
        (N.θ (N.c (ps j).1.1.toAdd) (qs j).1.2.b (N.c (ps i).1.1.toAdd) *
          N.θ (N.c (ps j).1.1.toAdd) (qs j).1.2.b (qs i).1.2.b *
          N.θ (N.c (ps i).1.1.toAdd) (qs i).1.2.b (N.c (ps j).1.1.toAdd * (qs j).1.2.b)) *
      (cubN N.θ k 1 ((ps i).1.2.b * (ps j).1.2.b) ((qs i).1.2.b * (qs j).1.2.b) /
        (cubN N.θ k 1 (ps i).1.2.b (qs i).1.2.b * cubN N.θ k 1 (ps j).1.2.b (qs j).1.2.b)) :=
    fun i j => (torusExtensionPair_correction_eq_value_quotient N (qs i).1.2 (qs j).1.2 (ps i).1.1.toAdd (ps j).1.1.toAdd _ _ _).symm
  simp only [hX, mul_zpow, Finset.prod_mul_distrib]
  rw [NumD.tk]
  apply Additive.ofMul.injective
  have hA' := congrArg Additive.ofMul hA
  have hG' := congrArg Additive.ofMul hG
  simp only [ofMul_mul, ofMul_pow] at hA' hG' ⊢
  linear_combination (norm := abel) hA' + hG'

theorem wp_eq_prod : ∀ (F : Type) [Field F] (N N' : NumD F) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (φ : N'.A → Fin r → N.A) (e : N'.X → Fin r → N.X) (wv : N'.A → F), TensFacts W φ e wv → ∀ (k : ℕ), 1 ≤ k → ∀ (q' p' : N'.QT k) (qs ps : Fin r → N.QT k), QRelV W φ e wv q' qs → QRelV W φ e wv p' ps → N'.wp q' p' = ∏ i, ∏ j, N.wp (qs i) (ps j) ^ (W + W.transpose) i j := by
  intro F _ N N' r W φ e wv hT k _ q' p' qs ps hq hp
  let U : N'.A → Fˣ := fun x => Units.mk0 (wv x) (hT.2.2.2.2.2.1 x)
  have hU : ∀ x, wv x = (U x : F) := fun x => rfl
  have h1 := tk_tens W φ e wv hT U hU q' p' qs ps hq hp
  have h2 := tk_tens W φ e wv hT U hU p' q' ps qs hp hq
  rw [mul_comm q'.1.2.b p'.1.2.b] at h2
  have hper : ∀ i j, N.wp (qs i) (ps j) * N.wp (qs j) (ps i) =
      N.tk (qs i * qs j) (ps i * ps j) / (N.tk (qs i) (ps i) * N.tk (qs j) (ps j)) /
        (N.tk (ps i * ps j) (qs i * qs j) / (N.tk (ps i) (qs i) * N.tk (ps j) (qs j))) := by
    intro i j
    have e1 := WpPairing.wp_mul_left N (qs i) (qs j) (ps i * ps j)
    have e2 := WpPairing.wp_mul_right N (qs i) (ps i) (ps j)
    have e3 := WpPairing.wp_mul_right N (qs j) (ps i) (ps j)
    simp only [NumD.wp] at e1 e2 e3 ⊢
    apply Additive.ofMul.injective
    replace e1 := congrArg Additive.ofMul e1
    replace e2 := congrArg Additive.ofMul e2
    replace e3 := congrArg Additive.ofMul e3
    simp only [ofMul_mul, ofMul_div] at e1 e2 e3 ⊢
    linear_combination (norm := abel) -e1 - e2 - e3
  have hR : ∏ i, ∏ j, N.wp (qs i) (ps j) ^ (W + W.transpose) i j =
      ∏ i, ∏ j, (N.wp (qs i) (ps j) * N.wp (qs j) (ps i)) ^ W i j := by
    simp only [Matrix.add_apply, Matrix.transpose_apply, zpow_add, Finset.prod_mul_distrib, mul_zpow]
    congr 1
    rw [Finset.prod_comm]
  have hD : ∀ f g : Fin r → Fin r → Fˣ, ∏ i, ∏ j, (f i j / g i j) ^ W i j =
      (∏ i, ∏ j, f i j ^ W i j) / ∏ i, ∏ j, g i j ^ W i j := by
    intro f g
    simp only [div_zpow, Finset.prod_div_distrib]
  rw [hR]
  simp only [hper]
  rw [hD]
  rw [NumD.wp]
  apply Additive.ofMul.injective
  have h1' := congrArg Additive.ofMul h1
  have h2' := congrArg Additive.ofMul h2
  simp only [ofMul_mul, ofMul_pow, ofMul_div] at h1' h2' ⊢
  linear_combination (norm := abel) h1' - h2'

end GlobalTheory.Mum.TensTor.PairVal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorsionPairingEqProdFactorPairingsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorTorsionPairing_eq_prod_factor_pairings : ∀ (F : Type) [Field F] (N N' : NumD F) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (φ : N'.A → Fin r → N.A) (e : N'.X → Fin r → N.X) (wv : N'.A → F), TensFacts W φ e wv → ∀ (k : ℕ), 1 ≤ k → ∀ (q' p' : N'.QT k) (qs ps : Fin r → N.QT k), QRelV W φ e wv q' qs → QRelV W φ e wv p' ps → N'.wp q' p' = ∏ i, ∏ j, N.wp (qs i) (ps j) ^ (W + W.transpose) i j := by
  first | exact @GlobalTheory.Mum.TensTor.PairVal.wp_eq_prod | exact GlobalTheory.Mum.TensTor.PairVal.wp_eq_prod | (intros; apply GlobalTheory.Mum.TensTor.PairVal.wp_eq_prod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingTensorTorsionEqProdComponents
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

namespace GlobalTheory.Mum.TensTor

theorem weilQk_tens : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N') (k : ℕ), 0 < k → ∀ (p' q' : QkPt D'.toPre F k) (ps qs : Fin r → QkPt D.toPre F k), PtRel T ν ν' p' ps → PtRel T ν ν' q' qs → ∀ z : Fin r → Fin r → Fˣ, (∀ i j, WeilQkIs D.toPre F k (ps i) (qs j) (z i j : F)) → WeilQkIs D'.toPre F k p' q' ((∏ i, ∏ j, z i j ^ (W + W.transpose) i j : Fˣ) : F) := by
  intro R _ _ _ _ D D' r W T F _ _ _ N N' ν ν' k hk p' q' ps qs hp hq z hz
  have gt : BrGtSt := GlobalTheory.Ex.GtValues.points_correspond
  have wp : BrWpSt := GlobalTheory.WeilValues.weil_eq_values gt (GlobalTheory.Ex.brFam GlobalTheory.allSixLaws.1 GlobalTheory.allSixLaws.2.1)
  have hk1 : 1 ≤ k := hk
  have hW := wp R D.toPre D.psi_even D.tau_bimult F N ν k hk1
  have hW' := wp R D'.toPre D'.psi_even D'.tau_bimult F N' ν' k hk1
  have hF := GlobalTheory.T.tensorData_values_facts R ‹_› D D' W T F N N' ν ν'
  obtain ⟨a', as, ha', has, hra⟩ := hp
  obtain ⟨b', bs, hb', hbs, hrb⟩ := hq
  have hv := GlobalTheory.T.tensorTorsionPairing_eq_prod_factor_pairings F N N' W (cmp T ν ν') (chi T ν ν') (wv T ν ν') hF k hk1 a' b' as bs hra hrb
  refine (hW' p' q' a' b' _ ha' hb').2 ?_
  rw [hv]
  have hz' : ∀ i j, z i j = N.wp (as i) (bs j) := fun i j =>
    Units.ext ((hW (ps i) (qs j) (as i) (bs j) _ (has i) (hbs j)).1 (hz i j))
  simp only [hz']

end GlobalTheory.Mum.TensTor
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingTensorTorsionEqProdComponentsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_pairing_tensor_torsion_eq_prod_components : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N') (k : ℕ), 0 < k → ∀ (p' q' : QkPt D'.toPre F k) (ps qs : Fin r → QkPt D.toPre F k), PtRel T ν ν' p' ps → PtRel T ν ν' q' qs → ∀ z : Fin r → Fin r → Fˣ, (∀ i j, WeilQkIs D.toPre F k (ps i) (qs j) (z i j : F)) → WeilQkIs D'.toPre F k p' q' ((∏ i, ∏ j, z i j ^ (W + W.transpose) i j : Fˣ) : F) := by
  first | exact @GlobalTheory.Mum.TensTor.weilQk_tens | exact GlobalTheory.Mum.TensTor.weilQk_tens | (intros; apply GlobalTheory.Mum.TensTor.weilQk_tens <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComponentTupleTensorTorsionUnimodular
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusComponentsOfUnimodularTensor
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGtOver
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

namespace GlobalTheory.Mum.TensTor.Vonto

theorem sum_sym_inv {G : Type} [AddCommGroup G] {r : ℕ} (W C : Matrix (Fin r) (Fin r) ℤ)
    (h : (W + W.transpose) * C = 1) (a : Fin r → Fin r → G) :
    ∑ i, ∑ j, W i j • ((∑ k, C j k • a i k) + ∑ k, C i k • a j k) = ∑ i, a i i := by
  have e3 : ∀ i k, ∑ j, (W i j + W j i) * C j k = if i = k then 1 else 0 := fun i k => by
    have := congrFun (congrFun h i) k
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    simpa using this
  have e1 : ∀ i, ∑ j, W i j • ((∑ k, C j k • a i k) + ∑ k, C i k • a j k) =
      ∑ j, W i j • ∑ k, C j k • a i k + ∑ j, W i j • ∑ k, C i k • a j k := fun i => by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun j _ => smul_add _ _ _
  rw [Finset.sum_congr rfl fun i _ => e1 i, Finset.sum_add_distrib]
  rw [show (∑ i, ∑ j, W i j • ∑ k, C i k • a j k) = ∑ i, ∑ j, W j i • ∑ k, C j k • a i k from Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  simp_rw [← add_smul, Finset.smul_sum, ← mul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, e3, ite_smul, one_smul, zero_smul]
  simp

end GlobalTheory.Mum.TensTor.Vonto

namespace GlobalTheory.Mum.TensTor.Vonto

section Split

variable {X U : Type} [AddCommGroup X] [CommGroup U]

@[ext] structure ExtPt (f : X → X → U) where

  a : X

  u : U

instance (f : X → X → U) : Add (ExtPt f) := ⟨fun p q => ⟨p.a + q.a, p.u * q.u / f p.a q.a⟩⟩

instance (f : X → X → U) : Zero (ExtPt f) := ⟨⟨0, 1⟩⟩

instance (f : X → X → U) : Neg (ExtPt f) := ⟨fun p => ⟨-p.a, f p.a (-p.a) / p.u⟩⟩

def extGroup (f : X → X → U) (f0 : ∀ a, f 0 a = 1) (fs : ∀ a b, f a b = f b a)
    (fc : ∀ a b c, f (a + b) c * f a b = f a (b + c) * f b c) : AddCommGroup (ExtPt f) where
  add_assoc p q w := by
    refine ExtPt.ext (add_assoc p.a q.a w.a) ?_
    change p.u * q.u / f p.a q.a * w.u / f (p.a + q.a) w.a = p.u * (q.u * w.u / f q.a w.a) / f p.a (q.a + w.a)
    have h := congrArg Additive.ofMul (fc p.a q.a w.a)
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div] at h ⊢
    linear_combination (norm := abel) -h
  zero_add p := by
    refine ExtPt.ext (zero_add p.a) ?_
    change 1 * p.u / f 0 p.a = p.u
    rw [f0, _root_.one_mul, div_one]
  add_zero p := by
    refine ExtPt.ext (add_zero p.a) ?_
    change p.u * 1 / f p.a 0 = p.u
    rw [fs, f0, _root_.mul_one, div_one]
  neg_add_cancel p := by
    refine ExtPt.ext (neg_add_cancel p.a) ?_
    change f p.a (-p.a) / p.u * p.u / f (-p.a) p.a = 1
    rw [fs (-p.a), div_mul_cancel, div_self']
  add_comm p q := by
    refine ExtPt.ext (add_comm p.a q.a) ?_
    change p.u * q.u / f p.a q.a = q.u * p.u / f q.a p.a
    rw [mul_comm p.u, fs]
  nsmul := nsmulRec
  zsmul := zsmulRec

theorem exists_split [Module.Free ℤ X] (f : X → X → U) (f0 : ∀ a, f 0 a = 1) (fs : ∀ a b, f a b = f b a)
    (fc : ∀ a b c, f (a + b) c * f a b = f a (b + c) * f b c) :
    ∃ s : X → U, ∀ a b, s (a + b) * f a b = s a * s b := by
  letI := extGroup f f0 fs fc
  let bX := Module.Free.chooseBasis ℤ X
  let h : X →ₗ[ℤ] ExtPt f := bX.constr ℤ fun i => ⟨bX i, 1⟩
  let p : ExtPt f →ₗ[ℤ] X := AddMonoidHom.toIntLinearMap ⟨⟨ExtPt.a, rfl⟩, fun _ _ => rfl⟩
  have hp : p ∘ₗ h = LinearMap.id := bX.ext fun i => by
    change (h (bX i)).a = bX i
    simp only [h, bX.constr_basis]
  have ha : ∀ x, (h x).a = x := fun x => LinearMap.congr_fun hp x
  refine ⟨fun x => (h x).u, fun a b => ?_⟩
  have e : (h (a + b)).u = (h a).u * (h b).u / f (h a).a (h b).a := congrArg ExtPt.u (map_add h a b)
  show (h (a + b)).u * f a b = (h a).u * (h b).u
  rw [e, ha, ha, div_mul_cancel]

end Split

theorem exists_gt_over {F : Type} [Field F] (N : NumD F) (b : N.A) : ∃ g : N.Gt, g.b = b := by
  obtain ⟨s, hs⟩ := exists_split (fun χ χ' => N.θ (N.c χ) (N.c χ') b)
    (fun a => by rw [N.c_zero, N.cub.face]) (fun a a' => N.cub.s01 _ _ _)
    (fun a a' a'' => by simp only [N.c_add]; exact N.cub.coc _ _ _ _)
  exact ⟨⟨b, s, hs⟩, rfl⟩

end GlobalTheory.Mum.TensTor.Vonto

namespace GlobalTheory.Mum.TensTor.Vonto

variable {F : Type} [Field F] {N N' : NumD F} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
  {φ : N'.A → Fin r → N.A} {e : N'.X → Fin r → N.X} {wv : N'.A → F}

theorem tor_rel (hT : TensFacts W φ e wv) (hdet : IsUnit (W + W.transpose).det) (t' : Multiplicative N'.X →* Fˣ) :
    ∃ ts : Fin r → (Multiplicative N.X →* Fˣ), GtRelV W φ e wv (N'.tor t') fun j => N.tor (ts j) := by
  obtain ⟨hφm, -, hem, heb, -, -, -, -⟩ := hT
  have hBC : (W + W.transpose) * (W + W.transpose)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  let E : N'.X ≃+ (Fin r → N.X) := AddEquiv.ofBijective (AddMonoidHom.mk' e fun a b => funext (hem a b)) heb
  let sH : Fin r → Multiplicative N.X →* Fˣ := fun k =>
    t'.comp (AddMonoidHom.toMultiplicative ((E.symm : (Fin r → N.X) →+ N'.X).comp (AddMonoidHom.single (fun _ : Fin r => N.X) k)))
  let C : Fin r → Fin r → ℤ := ((W + W.transpose)⁻¹ : Matrix (Fin r) (Fin r) ℤ)
  let M : Fin r → Fin r → ℤ := W
  refine ⟨fun j => ∏ k, sH k ^ C j k, fun j => ?_, fun χ' => ?_⟩
  · have h1 := hφm 1 1 j
    rw [_root_.mul_one] at h1
    exact mul_eq_left.1 h1.symm
  · have hχ : χ' = ∑ i, E.symm (Pi.single i (e χ' i)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_sum, Finset.univ_sum_single]; exact (E.symm_apply_apply χ').symm
    have ht : t' (Multiplicative.ofAdd χ') = ∏ i, sH i (Multiplicative.ofAdd (e χ' i)) := by
      conv_lhs => rw [hχ]
      rw [ofAdd_sum, map_prod]
      rfl
    simp only [NumD.torus_generator_apply, NumD.tor_b, N.cub.face₂, N.cub.face₃, _root_.mul_one, div_one]
    congr 2
    congr 1
    rw [ht]
    change (∏ i, sH i (Multiplicative.ofAdd (e χ' i))) =
      ∏ i, ∏ j, ((∏ k, sH k ^ C j k) (Multiplicative.ofAdd (e χ' i)) *
        (∏ k, sH k ^ C i k) (Multiplicative.ofAdd (e χ' j))) ^ M i j
    have hp (f : Fin r → (Multiplicative N.X →* Fˣ)) (x : Multiplicative N.X) :
        (∏ k, f k) x = ∏ k, f k x := by
      exact map_prod (MonoidHom.eval x) _ _
    simp only [hp, MonoidHom.zpow_apply]
    apply Additive.ofMul.injective
    simp only [ofMul_prod, ofMul_zpow, ofMul_mul]
    exact (sum_sym_inv W C hBC fun i k => Additive.ofMul (sH k (Multiplicative.ofAdd (e χ' i)))).symm

end GlobalTheory.Mum.TensTor.Vonto

namespace GlobalTheory.Mum.TensTor.Vonto

variable {F : Type} [Field F] {N N' : NumD F} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
  {φ : N'.A → Fin r → N.A} {e : N'.X → Fin r → N.X} {wv : N'.A → F}

theorem of_exist_mul (hT : TensFacts W φ e wv) (hdet : IsUnit (W + W.transpose).det)
    (hex : ∀ vs : Fin r → N.Gt, ∃ v' : N'.Gt, GtRelV W φ e wv v' vs)
    (hmul : ∀ (v' u' : N'.Gt) (vs us : Fin r → N.Gt), GtRelV W φ e wv v' vs → GtRelV W φ e wv u' us →
      GtRelV W φ e wv (v' * u') (vs * us))
    (v' : N'.Gt) : ∃ vs : Fin r → N.Gt, GtRelV W φ e wv v' vs := by
  choose g hg using fun j => exists_gt_over N (φ v'.b j)
  obtain ⟨u', hu'⟩ := hex g
  have hb : u'.b = v'.b := hT.2.1.1 (funext fun j => (hu'.1 j).trans (hg j))
  obtain ⟨t', ht'⟩ := (N'.exists_tor_iff (u'⁻¹ * v')).2 (by rw [NumD.Gt.mul_b, NumD.Gt.inv_b, hb, inv_mul_cancel])
  obtain ⟨ts, hts⟩ := tor_rel hT hdet t'
  have h := hmul u' (N'.tor t') g (fun j => N.tor (ts j)) hu' hts
  rw [ht', mul_inv_cancel_left] at h
  exact ⟨_, h⟩

end GlobalTheory.Mum.TensTor.Vonto
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusComponentsOfUnimodularTensor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

namespace GlobalTheory.Mum.TensTor

theorem gtRelV_onto (F : Type) [Field F] (N N' : NumD F) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (φ : N'.A → Fin r → N.A) (e : N'.X → Fin r → N.X) (wv : N'.A → F) (hT : TensFacts W φ e wv)
    (hdet : IsUnit (W + W.transpose).det) (v' : N'.Gt) : ∃ vs : Fin r → N.Gt, GtRelV W φ e wv v' vs :=
  Vonto.of_exist_mul hT hdet (VExist.gtRelV_exists F N N' W φ e wv hT)
    (gtRelV_mul F N N' W φ e wv hT) v'

end GlobalTheory.Mum.TensTor
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusComponentsOfUnimodularTensorStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torus_components_of_unimodular_tensor : ∀ (F : Type) [Field F] (N N' : NumD F) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (φ : N'.A → Fin r → N.A) (e : N'.X → Fin r → N.X) (wv : N'.A → F), TensFacts W φ e wv → IsUnit (W + W.transpose).det → ∀ v' : N'.Gt, ∃ vs : Fin r → N.Gt, GtRelV W φ e wv v' vs := by
  first | exact @GlobalTheory.Mum.TensTor.gtRelV_onto | exact GlobalTheory.Mum.TensTor.gtRelV_onto | (intros; apply GlobalTheory.Mum.TensTor.gtRelV_onto <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComponentTupleTensorTorsionUnimodular
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

noncomputable section

namespace GlobalTheory.Mum.TensTor

theorem gtRelV_npow_of_tensFacts {F : Type} [Field F] {N N' : NumD F} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
    {φ : N'.A → Fin r → N.A} {e : N'.X → Fin r → N.X} {wv : N'.A → F} (hf : TensFacts W φ e wv)
    {v' : N'.Gt} {vs : Fin r → N.Gt} (h : GtRelV W φ e wv v' vs) (k : ℕ) :
    GtRelV W φ e wv (v' ^ k) (vs ^ k) := by
  induction k with
  | zero =>
    have h0 := GlobalTheory.T.tensorTorusValueCorrespondence_period F N N' W φ e wv hf 0
    have he0 : ∀ j, e 0 j = 0 := fun j => by
      have := hf.2.2.1 0 0 j
      rw [add_zero] at this
      simpa using this
    have e1 : (1 : Fin r → N.Gt) = fun j => N.io (e 0 j) := funext fun j => by rw [he0, N.io_zero]; rfl
    rw [pow_zero, pow_zero, e1, ← N'.io_zero]
    exact h0
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact GlobalTheory.T.tensorTorusValueCorrespondence_mul F N N' W φ e wv hf _ _ _ _ ih h

theorem exists_components_of_unimodular : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N'), IsUnit (W + W.transpose).det → ∀ (k : ℕ) (p' : QkPt D'.toPre F k), ∃ ps : Fin r → QkPt D.toPre F k, PtRel T ν ν' p' ps := by
  intro R _ _ _ hB D D' r W T F _ _ _ N N' ν ν' hW k p'
  have hGt := GlobalTheory.Ex.GtValues.points_correspond
  have hf := GlobalTheory.T.tensorData_values_facts R hB D D' W T F N N' ν ν'
  obtain ⟨q', hq', -⟩ := ((hGt R D'.toPre D'.psi_even D'.tau_bimult F N' ν').2.2.2.2 k).1 p'
  obtain ⟨vs, hvs⟩ := GlobalTheory.T.exists_torus_components_of_unimodular_tensor F N N' W (cmp T ν ν') (chi T ν ν') (wv T ν ν') hf hW q'.1.2
  have hk := gtRelV_npow_of_tensFacts hf hvs k
  rw [N'.mem_QT.1 q'.2] at hk
  have hio := GlobalTheory.T.tensorTorusValueCorrespondence_period F N N' W (cmp T ν ν') (chi T ν ν') (wv T ν ν') hf q'.1.1.toAdd
  have hv := GlobalTheory.T.tensorTorusValueCorrespondence_unique_components F N N' W (cmp T ν ν') (chi T ν ν') (wv T ν ν') hf hW _ _ _ hk hio
  let qs : Fin r → N.QT k := fun j =>
    ⟨(Multiplicative.ofAdd (chi T ν ν' q'.1.1.toAdd j), vs j), N.mem_QT.2 (congrFun hv j)⟩
  choose ps hps using fun j => ((hGt R D.toPre D.psi_even D.tau_bimult F N ν).2.2.2.2 k).2.1 (qs j)
  exact ⟨ps, q', qs, hq', hps, fun _ => rfl, hvs⟩

end GlobalTheory.Mum.TensTor
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComponentTupleTensorTorsionUnimodularStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_component_tuple_tensor_torsion_unimodular : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N'), IsUnit (W + W.transpose).det → ∀ (k : ℕ) (p' : QkPt D'.toPre F k), ∃ ps : Fin r → QkPt D.toPre F k, PtRel T ν ν' p' ps := by
  first | exact @GlobalTheory.Mum.TensTor.exists_components_of_unimodular | exact GlobalTheory.Mum.TensTor.exists_components_of_unimodular | (intros; apply GlobalTheory.Mum.TensTor.exists_components_of_unimodular <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorTorsionPointOfComponentTuple
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorTorsionPointOfComponentTuple
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

noncomputable section

namespace GlobalTheory.Mum.TensTor

theorem gtRelV_pow {F : Type} [Field F] {N N' : NumD F} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
    {φ : N'.A → Fin r → N.A} {e : N'.X → Fin r → N.X} {wv : N'.A → F} (h : TensFacts W φ e wv)
    {v' : N'.Gt} {vs : Fin r → N.Gt} (hv : GtRelV W φ e wv v' vs) (k : ℕ) :
    GtRelV W φ e wv (v' ^ k) (vs ^ k) := by
  induction k with
  | zero =>
    have h0 := GlobalTheory.T.tensorTorusValueCorrespondence_period F N N' W φ e wv h 0
    have e0 : ∀ j, e 0 j = 0 := fun j => by
      have := h.2.2.1 0 0 j
      rw [add_zero] at this
      exact (add_eq_left.1 this.symm)
    simp only [e0, NumD.io_zero] at h0
    rw [pow_zero, pow_zero]
    exact h0
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact GlobalTheory.T.tensorTorusValueCorrespondence_mul F N N' W φ e wv h _ _ _ _ ih hv

theorem exists_ptRel : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N') (k : ℕ) (ps : Fin r → QkPt D.toPre F k), ∃ p' : QkPt D'.toPre F k, PtRel T ν ν' p' ps := by
  intro R _ _ _ hR D D' r W T F _ _ _ N N' ν ν' k ps
  have B := GlobalTheory.Ex.GtValues.points_correspond R D.toPre D.psi_even D.tau_bimult F N ν
  have B' := GlobalTheory.Ex.GtValues.points_correspond R D'.toPre D'.psi_even D'.tau_bimult F N' ν'
  have hT := GlobalTheory.T.tensorData_values_facts R hR D D' W T F N N' ν ν'
  choose qs hqs using fun i => ((B.2.2.2.2 k).1 (ps i)).exists
  obtain ⟨v', hv'⟩ := GlobalTheory.T.exists_tensorTorusPoint_of_componentTuple F N N' W (cmp T ν ν') (chi T ν ν') (wv T ν ν') hT fun j => (qs j).1.2
  obtain ⟨y', hy'⟩ := hT.2.2.2.1.2 fun i => (qs i).1.1.toAdd
  have hk : v' ^ k = N'.io y' := by
    refine GlobalTheory.T.tensorTorusValueCorrespondence_unique_point F N N' W (cmp T ν ν') (chi T ν ν') (wv T ν ν') hT _ _ (fun j => N.io (chi T ν ν' y' j))
      ?_ (GlobalTheory.T.tensorTorusValueCorrespondence_period F N N' W (cmp T ν ν') (chi T ν ν') (wv T ν ν') hT y')
    have hp := gtRelV_pow hT hv' k
    have e : ((fun j => (qs j).1.2) ^ k : Fin r → N.Gt) = fun j => N.io (chi T ν ν' y' j) := by
      funext j
      rw [Pi.pow_apply, hy']
      exact (qs j).2
    rwa [e] at hp
  let q' : N'.QT k := ⟨(Multiplicative.ofAdd y', v'), hk⟩
  obtain ⟨p', hp'⟩ := (B'.2.2.2.2 k).2.1 q'
  exact ⟨p', q', qs, hp', hqs, fun i => congrFun hy' i, hv'⟩

end GlobalTheory.Mum.TensTor
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorTorsionPointOfComponentTupleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tensor_torsion_point_of_component_tuple : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N') (k : ℕ) (ps : Fin r → QkPt D.toPre F k), ∃ p' : QkPt D'.toPre F k, PtRel T ν ν' p' ps := by
  first | exact @GlobalTheory.Mum.TensTor.exists_ptRel | exact GlobalTheory.Mum.TensTor.exists_ptRel | (intros; apply GlobalTheory.Mum.TensTor.exists_ptRel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorsionTowerNsmulComponentwise
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorsionTowerNsmulComponentwise
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

namespace GlobalTheory.Mum.TensTower

section Values
variable {F : Type} [Field F] {N N' : NumD F} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ} {φ : N'.A → Fin r → N.A}
  {e : N'.X → Fin r → N.X} {wv : N'.A → F}

theorem comp_nsmul (h : TensFacts W φ e wv) (k : ℕ) (χ : N'.X) (i : Fin r) : e (k • χ) i = k • e χ i :=
  (AddMonoidHom.mk' (fun χ => e χ i) fun a b => h.2.2.1 a b i).map_nsmul k χ

theorem rel_pow (h : TensFacts W φ e wv) {v' : N'.Gt} {vs : Fin r → N.Gt} (hv : GtRelV W φ e wv v' vs) (k : ℕ) :
    GtRelV W φ e wv (v' ^ k) (vs ^ k) := by
  induction k with
  | zero =>
    have h0 := GlobalTheory.T.tensorTorusValueCorrespondence_period F N N' W φ e wv h 0
    have e0 : ∀ j, e 0 j = 0 := fun j => by simpa using comp_nsmul h 0 0 j
    simp only [e0, NumD.io_zero] at h0
    rw [pow_zero, pow_zero]
    exact h0
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact GlobalTheory.T.tensorTorusValueCorrespondence_mul F N N' W φ e wv h _ _ _ _ ih hv

theorem tower_val (h : TensFacts W φ e wv) {n m : ℕ} {p' : N'.QT (n * m)} {ps : Fin r → N.QT (n * m)} {t' : N'.QT n}
    {ts : Fin r → N.QT n} (hp : QRelV W φ e wv p' ps) (ht : QRelV W φ e wv t' ts)
    (hz : ∀ i, ∃ z : N.X, (ts i).1.1.toAdd = (ps i).1.1.toAdd + n • z ∧ (ts i).1.2 = (ps i).1.2 ^ m * N.io z) :
    ∃ z' : N'.X, t'.1.1.toAdd = p'.1.1.toAdd + n • z' ∧ t'.1.2 = p'.1.2 ^ m * N'.io z' := by
  choose z hz1 hz2 using hz
  obtain ⟨z', rfl⟩ := h.2.2.2.1.2 z
  refine ⟨z', h.2.2.2.1.1 (funext fun i => ?_), ?_⟩
  · rw [h.2.2.1, comp_nsmul h, ht.1, hp.1, hz1]
  · refine GlobalTheory.T.tensorTorusValueCorrespondence_unique_point F N N' W φ e wv h _ _ _ ht.2 ?_
    have := GlobalTheory.T.tensorTorusValueCorrespondence_mul F N N' W φ e wv h _ _ _ _ (rel_pow h hp.2 m) (GlobalTheory.T.tensorTorusValueCorrespondence_period F N N' W φ e wv h z')
    have e1 : (fun j => (ts j).1.2) = (fun j => (ps j).1.2) ^ m * fun j => N.io (e z' j) := funext hz2
    rw [e1]
    exact this

end Values

theorem tower : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N') (n m : ℕ), 0 < n → 0 < m → ∀ (p' : QkPt D'.toPre F (n * m)) (ps : Fin r → QkPt D.toPre F (n * m)) (t' : QkPt D'.toPre F n) (ts : Fin r → QkPt D.toPre F n), PtRel T ν ν' p' ps → PtRel T ν ν' t' ts → (∀ i, ∃ q : QkPt D.toPre F n, q.y = (ps i).y ∧ GtPtF.IsNsmul m (ps i).g q.g ∧ QkPt.Equiv D.toPre F q (ts i)) → ∃ q' : QkPt D'.toPre F n, q'.y = p'.y ∧ GtPtF.IsNsmul m p'.g q'.g ∧ QkPt.Equiv D'.toPre F q' t' := by
  intro R _ _ _ hR D D' r W T F _ _ _ N N' ν ν' n m _ _ p' ps t' ts ⟨a', as, ha', has, ha⟩ ⟨b', bs, hb', hbs, hb⟩ H
  have hF := GlobalTheory.T.tensorData_values_facts R hR D D' W T F N N' ν ν'
  have B := (GtValues.points_correspond R D.toPre D.psi_even D.tau_bimult F N ν).2.2.2.2 n
  have B' := (GtValues.points_correspond R D'.toPre D'.psi_even D'.tau_bimult F N' ν').2.2.2.2 n
  obtain ⟨z', hz1, hz2⟩ := tower_val hF ha hb fun i => by
    obtain ⟨q, hy, hn, he⟩ := H i
    obtain ⟨c, hc⟩ := (B.1 q).exists
    obtain ⟨z, h1, h2⟩ := (B.2.2 q (ts i) c (bs i) hc (hbs i)).1 he
    refine ⟨z, ?_, ?_⟩
    · rw [h1, ν.eX.injective (hc.1.trans (hy.trans (has i).1.symm))]
    · rw [h2, (GtValues.isNsmul_val ν m (has i).2 hc.2).1 hn]
  let c' : N'.QT n := ⟨(a'.1.1, a'.1.2 ^ m), by
    rw [NumD.mem_QT, ← pow_mul, mul_comm m n]
    exact a'.2⟩
  obtain ⟨q', hq'⟩ := B'.2.1 c'
  exact ⟨q', hq'.1.symm.trans ha'.1, (GtValues.isNsmul_val ν' m ha'.2 hq'.2).2 rfl,
    (B'.2.2 q' t' c' b' hq' hb').2 ⟨z', hz1, hz2⟩⟩

end GlobalTheory.Mum.TensTower
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorsionTowerNsmulComponentwiseStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_torsion_tower_nsmul_componentwise : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N') (n m : ℕ), 0 < n → 0 < m → ∀ (p' : QkPt D'.toPre F (n * m)) (ps : Fin r → QkPt D.toPre F (n * m)) (t' : QkPt D'.toPre F n) (ts : Fin r → QkPt D.toPre F n), PtRel T ν ν' p' ps → PtRel T ν ν' t' ts → (∀ i, ∃ q : QkPt D.toPre F n, q.y = (ps i).y ∧ GtPtF.IsNsmul m (ps i).g q.g ∧ QkPt.Equiv D.toPre F q (ts i)) → ∃ q' : QkPt D'.toPre F n, q'.y = p'.y ∧ GtPtF.IsNsmul m p'.g q'.g ∧ QkPt.Equiv D'.toPre F q' t' := by
  first | exact @GlobalTheory.Mum.TensTower.tower | exact GlobalTheory.Mum.TensTower.tower | (intros; apply GlobalTheory.Mum.TensTower.tower <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorsionPointEquivIffComponentsEquiv
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorsionPointEquivIffComponentsEquiv
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

noncomputable section

namespace GlobalTheory.Mum.TensTor

theorem comp_nsmul {F : Type} [Field F] {N N' : NumD F} {r : ℕ} {e : N'.X → Fin r → N.X}
    (he : ∀ χ χ' i, e (χ + χ') i = e χ i + e χ' i) (k : ℕ) (z : N'.X) (i : Fin r) : e (k • z) i = k • e z i := by
  induction k with
  | zero =>
    have h := he 0 0 i
    rw [add_zero] at h
    simpa using h
  | succ k ih => rw [succ_nsmul, he, ih, succ_nsmul]

theorem qEq_iff_of_rel {F : Type} [Field F] {N N' : NumD F} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
    {φ : N'.A → Fin r → N.A} {e : N'.X → Fin r → N.X} {wv : N'.A → F} (hT : TensFacts W φ e wv)
    (hW : IsUnit (W + W.transpose).det) {k : ℕ} {a' b' : N'.QT k} {as bs : Fin r → N.QT k}
    (ha : QRelV W φ e wv a' as) (hb : QRelV W φ e wv b' bs) : N'.QEq a' b' ↔ ∀ i, N.QEq (as i) (bs i) := by
  have hadd := hT.2.2.1
  have he := hT.2.2.2.1
  constructor
  · rintro ⟨z, hy, hg⟩ i
    refine ⟨e z i, ?_, ?_⟩
    · rw [← hb.1 i, hy, hadd, comp_nsmul hadd, ha.1 i]
    · have h1 := GlobalTheory.T.tensorTorusValueCorrespondence_mul F N N' W φ e wv hT _ _ _ _ ha.2 (GlobalTheory.T.tensorTorusValueCorrespondence_period F N N' W φ e wv hT z)
      rw [← hg] at h1
      have h2 := congrFun (GlobalTheory.T.tensorTorusValueCorrespondence_unique_components F N N' W φ e wv hT hW _ _ _ hb.2 h1) i
      simpa using h2
  · intro h
    choose z hz using h
    obtain ⟨z', hz'⟩ := he.2 z
    refine ⟨z', ?_, ?_⟩
    · apply he.1
      funext i
      rw [hadd, comp_nsmul hadd, hz', ha.1 i, hb.1 i]
      exact (hz i).1
    · have h1 := GlobalTheory.T.tensorTorusValueCorrespondence_mul F N N' W φ e wv hT _ _ _ _ ha.2 (GlobalTheory.T.tensorTorusValueCorrespondence_period F N N' W φ e wv hT z')
      have h2 : ((fun j => (as j).1.2) * fun j => N.io (e z' j)) = fun j => (bs j).1.2 :=
        funext fun j => by rw [Pi.mul_apply, hz']; exact ((hz j).2).symm
      rw [h2] at h1
      exact GlobalTheory.T.tensorTorusValueCorrespondence_unique_point F N N' W φ e wv hT _ _ _ hb.2 h1

theorem qkPt_equiv_iff_components : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R →
    ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W)
    (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N)
    (ν' : NumOf D'.toPre F N'), IsUnit (W + W.transpose).det → ∀ (k : ℕ) (p' q' : QkPt D'.toPre F k)
    (ps qs : Fin r → QkPt D.toPre F k), PtRel T ν ν' p' ps → PtRel T ν ν' q' qs →
    (QkPt.Equiv D'.toPre F p' q' ↔ ∀ i, QkPt.Equiv D.toPre F (ps i) (qs i)) := by
  intro R _ _ _ hB D D' r W T F _ _ _ N N' ν ν' hW k p' q' ps qs hp hq
  obtain ⟨a', as, ha', has, ha⟩ := hp
  obtain ⟨b', bs, hb', hbs, hb⟩ := hq
  have hT := GlobalTheory.T.tensorData_values_facts R hB D D' W T F N N' ν ν'
  have G := GlobalTheory.Ex.GtValues.points_correspond
  rw [((G R D'.toPre D'.psi_even D'.tau_bimult F N' ν').2.2.2.2 k).2.2 p' q' a' b' ha' hb', qEq_iff_of_rel hT hW ha hb]
  exact forall_congr' fun i =>
    (((G R D.toPre D.psi_even D.tau_bimult F N ν).2.2.2.2 k).2.2 _ _ _ _ (has i) (hbs i)).symm

end GlobalTheory.Mum.TensTor
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorsionPointEquivIffComponentsEquivStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_torsion_point_equiv_iff_components_equiv : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N'), IsUnit (W + W.transpose).det → ∀ (k : ℕ) (p' q' : QkPt D'.toPre F k) (ps qs : Fin r → QkPt D.toPre F k), PtRel T ν ν' p' ps → PtRel T ν ν' q' qs → (QkPt.Equiv D'.toPre F p' q' ↔ ∀ i, QkPt.Equiv D.toPre F (ps i) (qs i)) := by
  first | exact @GlobalTheory.Mum.TensTor.qkPt_equiv_iff_components | exact GlobalTheory.Mum.TensTor.qkPt_equiv_iff_components | (intros; apply GlobalTheory.Mum.TensTor.qkPt_equiv_iff_components <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegenerationValuesAlgClosedField
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegenerationValuesAlgClosedField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

namespace GlobalTheory.MumValues

theorem exists_values : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F], ∃ N : NumD F, Nonempty (NumOf D.toPre F N) := by
  intro R _ _ _ hR D F _ _ _
  haveI : IsNoetherianRing R := hR.1.1
  obtain ⟨N, ν, -⟩ := GlobalTheory.ValuesExist.exists_integral_values GlobalTheory.allSixLaws.1 R D.toPre D.psi_even D.tau_bimult F ⊤
    (fun _ => trivial)
  exact ⟨N, ⟨ν⟩⟩

end GlobalTheory.MumValues
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegenerationValuesAlgClosedFieldStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_degenerationValues_algClosed_field : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F], ∃ N : NumD F, Nonempty (NumOf D.toPre F N) := by
  first | exact @GlobalTheory.MumValues.exists_values | exact GlobalTheory.MumValues.exists_values | (intros; apply GlobalTheory.MumValues.exists_values <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDegenerationDataTorsionIsometryOnto
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

noncomputable section

theorem GlobalTheory.Mum.TensTor.zpow_sum_tens {M κ : Type} [CommGroup M] (a : M) (s : Finset κ) (f : κ → ℤ) :
    a ^ (∑ i ∈ s, f i) = ∏ i ∈ s, a ^ f i := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro i t hi ih
    rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add, ih]

theorem GlobalTheory.Mum.TensTor.tate_tens : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsUnit (W + W.transpose).det → ∀ T : Tens D.toPre D'.toPre W, ∀ (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ), (∀ a, (ρ a).transpose * (W + W.transpose) = (W + W.transpose) * ρ (H.bar a)) → W = (W + W.transpose) * ρ H.w0 → ∀ [Module (𝓞 E) D'.toPre.X] (o : letI := H.starRing; D'.toPre.OAct (𝓞 E)), (letI := H.starRing; T.IsAct o ρ) → (letI := H.starRing; TraceFormTwistIso D'.toPre o H.w0) → ∀ (Dm : Datum H) (g : ℕ) (e : Dm.La ≃+ (Fin r → (Fin g → ℤ) × (Fin g → ℤ))), g = D.toPre.P.g + Module.finrank ℤ D.toPre.X → (∀ (a : 𝓞 E) x i, e (a • x) i = ∑ j, ρ a i j • e x j) → (∀ x y, Dm.EF x y = ∑ i, ∑ j, (W + W.transpose) i j * ((e x i).1 ⬝ᵥ (e y j).2 - (e x i).2 ⬝ᵥ (e y j).1)) → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (ζ : ℕ → Fˣ), (∀ n, 0 < n → IsPrimitiveRoot (ζ n) n) → (∀ n m, 0 < n → 0 < m → ζ (n * m) ^ m = ζ n) → ∀ ev : ∀ n : ℕ, ((Fin g → ℤ) × (Fin g → ℤ)) → QkPt D.toPre F n, (∀ n, 0 < n → ∀ a b, QkAdd (ev n a) (ev n b) (ev n (a + b))) → (∀ n, 0 < n → ∀ a b, QkPt.Equiv D.toPre F (ev n a) (ev n b) ↔ ∃ e, a = b + n • e) → (∀ n, 0 < n → ∀ p, ∃ a, QkPt.Equiv D.toPre F (ev n a) p) → (∀ n m, 0 < n → 0 < m → ∀ a, ∃ q : QkPt D.toPre F n, q.y = (ev (n * m) a).y ∧ GtPtF.IsNsmul m (ev (n * m) a).g q.g ∧ QkPt.Equiv D.toPre F q (ev n a)) → (∀ n, 0 < n → ∀ a b, WeilQkIs D.toPre F n (ev n a) (ev n b) ((ζ n ^ (a.1 ⬝ᵥ b.2 - a.2 ⬝ᵥ b.1) : Fˣ) : F)) → ∃ I : TateIsoQ Dm D'.toPre o F, I.ζ = ζ := by
  intro R _ _ _ hB E _ _ _ H D D' r W _ hdet T ρ hρ _ _ o hact _ Dm g e _ he hEF F _ _ _ ζ hprim hpow ev hadd hker
    honto htow hweil

  obtain ⟨N, ⟨ν⟩⟩ := GlobalTheory.T.exists_degenerationValues_algClosed_field R hB D F
  obtain ⟨N', ⟨ν'⟩⟩ := GlobalTheory.T.exists_degenerationValues_algClosed_field R hB D' F
  choose P hP using fun (n : ℕ) (a : Dm.La) =>
    GlobalTheory.T.exists_tensor_torsion_point_of_component_tuple R hB D D' W T F N N' ν ν' n (fun j => ev n (e a j))
  refine ⟨⟨ζ, hprim, hpow, P, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl⟩
  ·
    intro n hn a b
    have hs := hP n (a + b)
    simp only [map_add (f := _), Pi.add_apply] at hs
    exact GlobalTheory.T.tensor_torsion_add_componentwise R hB D D' W T F N N' ν ν' n (P n a) (P n b) (P n (a + b)) _ _ _ (hP n a) (hP n b) hs
      (fun i => hadd n hn (e a i) (e b i))
  ·
    intro n hn x a
    have hs := hP n (x • a)
    simp only [he] at hs
    exact GlobalTheory.T.tensorQuotientTorsion_orderAction_matrix R hB D D' W T F N N' ν ν' E H ρ hρ o hact g ev hadd hker n hn x (fun j => e a j)
      (P n a) (P n (x • a)) (hP n a) hs
  ·
    intro n hn a b
    rw [GlobalTheory.T.tensor_torsion_point_equiv_iff_components_equiv R hB D D' W T F N N' ν ν' hdet n (P n a) (P n b) _ _ (hP n a) (hP n b)]
    simp only [hker n hn]
    constructor
    · intro h
      choose c hc using h
      refine ⟨e.symm c, e.injective ?_⟩
      rw [map_add (f := _), map_nsmul, e.apply_symm_apply]
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, hc i]
    · rintro ⟨c, rfl⟩ i
      exact ⟨e c i, by simp only [map_add (f := _), map_nsmul, Pi.add_apply, Pi.smul_apply]⟩
  ·
    intro n hn p
    obtain ⟨ps, hps⟩ := GlobalTheory.T.exists_component_tuple_tensor_torsion_unimodular R hB D D' W T F N N' ν ν' hdet n p
    choose a ha using fun i => honto n hn (ps i)
    refine ⟨e.symm a, ?_⟩
    rw [GlobalTheory.T.tensor_torsion_point_equiv_iff_components_equiv R hB D D' W T F N N' ν ν' hdet n (P n (e.symm a)) p _ ps (hP n (e.symm a)) hps]
    intro i
    simpa only [e.apply_symm_apply] using ha i
  ·
    intro n m hn hm a
    exact GlobalTheory.T.tensor_torsion_tower_nsmul_componentwise R hB D D' W T F N N' ν ν' n m hn hm (P (n * m) a) _ (P n a) _ (hP (n * m) a) (hP n a)
      (fun i => htow n m hn hm (e a i))
  ·

    intro n hn a b
    have h := GlobalTheory.T.weil_pairing_tensor_torsion_eq_prod_components R hB D D' W T F N N' ν ν' n hn (P n a) (P n b) _ _ (hP n a) (hP n b)
      (fun i j => ζ n ^ ((e a i).1 ⬝ᵥ (e b j).2 - (e a i).2 ⬝ᵥ (e b j).1)) (fun i j => hweil n hn (e a i) (e b j))
    have key : (∏ i, ∏ j, (ζ n ^ ((e a i).1 ⬝ᵥ (e b j).2 - (e a i).2 ⬝ᵥ (e b j).1)) ^ (W + W.transpose) i j) =
        ζ n ^ Dm.EF a b := by
      rw [hEF a b, zpow_sum_tens]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [zpow_sum_tens]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [← zpow_mul, mul_comm ((W + W.transpose) i j)]
    beta_reduce at h
    rwa [key] at h
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDegenerationDataTorsionIsometryOntoStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorDegenerationData_torsion_isometry_onto : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E), ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsUnit (W + W.transpose).det → ∀ T : Tens D.toPre D'.toPre W, ∀ (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ), (∀ a, (ρ a).transpose * (W + W.transpose) = (W + W.transpose) * ρ (H.bar a)) → W = (W + W.transpose) * ρ H.w0 → ∀ [Module (𝓞 E) D'.toPre.X] (o : letI := H.starRing; D'.toPre.OAct (𝓞 E)), (letI := H.starRing; T.IsAct o ρ) → (letI := H.starRing; TraceFormTwistIso D'.toPre o H.w0) → ∀ (Dm : Datum H) (g : ℕ) (e : Dm.La ≃+ (Fin r → (Fin g → ℤ) × (Fin g → ℤ))), g = D.toPre.P.g + Module.finrank ℤ D.toPre.X → (∀ (a : 𝓞 E) x i, e (a • x) i = ∑ j, ρ a i j • e x j) → (∀ x y, Dm.EF x y = ∑ i, ∑ j, (W + W.transpose) i j * ((e x i).1 ⬝ᵥ (e y j).2 - (e x i).2 ⬝ᵥ (e y j).1)) → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (ζ : ℕ → Fˣ), (∀ n, 0 < n → IsPrimitiveRoot (ζ n) n) → (∀ n m, 0 < n → 0 < m → ζ (n * m) ^ m = ζ n) → ∀ ev : ∀ n : ℕ, ((Fin g → ℤ) × (Fin g → ℤ)) → QkPt D.toPre F n, (∀ n, 0 < n → ∀ a b, QkAdd (ev n a) (ev n b) (ev n (a + b))) → (∀ n, 0 < n → ∀ a b, QkPt.Equiv D.toPre F (ev n a) (ev n b) ↔ ∃ e, a = b + n • e) → (∀ n, 0 < n → ∀ p, ∃ a, QkPt.Equiv D.toPre F (ev n a) p) → (∀ n m, 0 < n → 0 < m → ∀ a, ∃ q : QkPt D.toPre F n, q.y = (ev (n * m) a).y ∧ GtPtF.IsNsmul m (ev (n * m) a).g q.g ∧ QkPt.Equiv D.toPre F q (ev n a)) → (∀ n, 0 < n → ∀ a b, WeilQkIs D.toPre F n (ev n a) (ev n b) ((ζ n ^ (a.1 ⬝ᵥ b.2 - a.2 ⬝ᵥ b.1) : Fˣ) : F)) → ∃ I : TateIsoQ Dm D'.toPre o F, I.ζ = ζ := by
  first | exact @GlobalTheory.Mum.TensTor.tate_tens | exact GlobalTheory.Mum.TensTor.tate_tens | (intros; apply GlobalTheory.Mum.TensTor.tate_tens <;> assumption)
end
