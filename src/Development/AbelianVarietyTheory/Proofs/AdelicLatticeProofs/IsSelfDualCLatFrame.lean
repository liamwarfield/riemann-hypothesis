module

public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.LinearIndependentWave
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsOpenNsmulCompletedHomLatticeFiniteAdelic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceModel

open GlobalTheory.DualPairCheck (cA_incA gram_star trace_cA star_purely_imaginary_eq_neg)
open GlobalTheory.WeilUnramifiedCompare (mem_hermitianStandardLattice_iff_pairing_integral hT_coord intAf_mul)

variable {D : D7} (S T : HSp D)

theorem hO_smul_left (a : AE D) (x y : WO S T) : hO S T (a • x) y = a * hO S T x y := by
  unfold hO
  simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun l _ => ?_
  ring

theorem hO_smul_right (a : AE D) (x y : WO S T) : hO S T x (a • y) = cA D a * hO S T x y := by
  unfold hO
  simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, map_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun l _ => ?_
  ring

theorem gram_inv_star (a b : Fin S.rank) : star (S.gram⁻¹ a b) = S.gram⁻¹ b a := by
  have h : S.gram.IsHermitian := Matrix.ext fun i j => gram_star S j i
  exact congrFun (congrFun h.inv b) a

theorem hO_herm (x y : WO S T) : cA D (hO S T x y) = hO S T y x := by
  unfold hO
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, cA_cA, cA_incA, gram_star, gram_inv_star]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring

theorem symplO_skew (x y : WO S T) : symplO S T y x = -symplO S T x y := by
  unfold symplO
  rw [← trace_cA, map_mul, cA_incA, star_purely_imaginary_eq_neg, hO_herm, map_neg, neg_mul, map_neg]

theorem symplO_add_left (x x' y : WO S T) : symplO S T (x + x') y = symplO S T x y + symplO S T x' y := by
  unfold symplO hO
  simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib, map_add (f := _)]

theorem symplO_add_right (x y y' : WO S T) : symplO S T x (y + y') = symplO S T x y + symplO S T x y' := by
  unfold symplO hO
  simp only [Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib, map_add (f := _)]

theorem symplO_smul (a : AE D) (x y : WO S T) : symplO S T (a • x) y = symplO S T x (cA D a • y) := by
  unfold symplO
  rw [hO_smul_left, hO_smul_right, cA_cA]

theorem symplO_zero_right (x : WO S T) : symplO S T x 0 = 0 := by
  simpa using symplO_add_right S T x 0 0

theorem symplO_zero_left (x : WO S T) : symplO S T 0 x = 0 := by
  simpa using symplO_add_left S T 0 0 x

theorem isBichar_symplO (ψ : AddChar (AF D.host.F) ℂ) : IsBichar fun x y : WO S T => ψ (symplO S T x y) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b y
    rw [symplO_add_left, AddChar.map_add_eq_mul]
  · intro a y z
    rw [symplO_add_right, AddChar.map_add_eq_mul]
  · intro y
    rw [symplO_zero_left, AddChar.map_zero_eq_one]
  · intro a
    rw [symplO_zero_right, AddChar.map_zero_eq_one]

def heisL (ψ : AddChar (AF D.host.F) ℂ) (w : WO S T) : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ) where
  toFun := heisO ψ S T w
  map_add' f g := by funext t; simp only [heisO, Pi.add_apply, mul_add]
  map_smul' c f := by funext t; simp only [heisO, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; exact mul_left_comm _ _ _

theorem heisL_heisL (ψ : AddChar (AF D.host.F) ℂ) (w w' : WO S T) (f : WO S T → ℂ) :
    heisL S T ψ w (heisL S T ψ w' f) = ψ (symplOH S T w w') • heisL S T ψ (w + w') f := by
  funext t
  change ψ (symplOH S T t w) * (ψ (symplOH S T (t + w) w') * f (t + w + w')) =
    ψ (symplOH S T w w') * (ψ (symplOH S T t (w + w')) * f (t + (w + w')))
  simp only [symplOH, symplO_add_left, symplO_add_right, mul_add, AddChar.map_add_eq_mul, add_assoc]
  ring

theorem heisL_comm (ψ : AddChar (AF D.host.F) ℂ) (w w' : WO S T) (f : WO S T → ℂ) :
    heisL S T ψ w (heisL S T ψ w' f) = ψ (symplO S T w w') • heisL S T ψ w' (heisL S T ψ w f) := by
  rw [heisL_heisL, heisL_heisL, smul_smul, ← AddChar.map_add_eq_mul, add_comm w' w]
  congr 2
  have h2 : algebraMap D.host.F (AF D.host.F) (1 / 2) * 2 = 1 := by
    rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul]
    norm_num
  rw [symplOH, symplOH, symplO_skew S T w w']
  linear_combination (symplO S T w w') * h2

def half (e : AE D) : AddSubgroup (WO S T) where
  carrier := {u | e • u = u}
  zero_mem' := smul_zero e
  add_mem' {a b} ha hb := by
    change e • (a + b) = a + b
    rw [smul_add, show e • a = a from ha, show e • b = b from hb]
  neg_mem' {a} ha := by
    change e • (-a) = -a
    rw [smul_neg, show e • a = a from ha]

theorem mem_half {e : AE D} {u : WO S T} : u ∈ half S T e ↔ e • u = u := Iff.rfl

theorem isHalf_iff {e : AE D} {u : WO S T} : IsHalf e u ↔ u ∈ half S T e :=
  ⟨fun h => Matrix.ext h, fun h i j => congrFun (congrFun h i) j⟩

theorem heisL_half (ψ : AddChar (AF D.host.F) ℂ) {e : AE D} (he : cA D e * e = 0) (x : WO S T) (hx : x ∈ half S T e)
    (x' : WO S T) (hx' : x' ∈ half S T e) (f : WO S T → ℂ) :
    heisL S T ψ x (heisL S T ψ x' f) = heisL S T ψ (x + x') f := by
  have : symplO S T x x' = 0 := by
    rw [← (mem_half S T).1 hx, ← (mem_half S T).1 hx', symplO_smul, smul_smul, he, zero_smul, symplO_zero_right]
  rw [heisL_heisL, symplOH, this, mul_zero, AddChar.map_zero_eq_one, one_smul]

theorem inv_smul_nsmul {k : ℕ} (hk : 0 < k) (t : WO S T) : incA D (k : D.host.E)⁻¹ • (k • t) = t := by
  have : (k : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  rw [← Nat.cast_smul_eq_nsmul (AE D), smul_smul, ← map_natCast (incA D), ← map_mul, inv_mul_cancel₀ this, map_one,
    one_smul]

theorem half_div (e : AE D) (k : ℕ) (hk : 0 < k) (x : WO S T) (hx : x ∈ half S T e) :
    ∃ x' ∈ half S T e, k • x' = x :=
  ⟨incA D (k : D.host.E)⁻¹ • x, by rw [mem_half, smul_comm, (mem_half S T).1 hx], by
    rw [smul_comm, inv_smul_nsmul S T hk]⟩

def latFrame : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E) :=
  S.L0.map (S.frame.equivFun.toLinearMap.restrictScalars (𝓞 D.host.E))

theorem mem_latFrame (y : Fin S.rank → D.host.E) : y ∈ latFrame S ↔ ∑ i, y i • S.frame i ∈ S.L0 := by
  rw [← S.frame.equivFun_symm_apply]
  constructor
  · rintro ⟨x, hx, rfl⟩
    change S.frame.equivFun.symm (S.frame.equivFun x) ∈ S.L0
    rwa [LinearEquiv.symm_apply_apply]
  · exact fun h => ⟨_, h, S.frame.equivFun.apply_symm_apply y⟩

theorem coe_latFrame : (latFrame S : Set (Fin S.rank → D.host.E)) = L0c D S :=
  Set.ext fun y => mem_latFrame S y

theorem isSelfDualC_latFrame : IsSelfDualC S (latFrame S) := by
  refine ⟨Submodule.IsLattice.of_fg D.host.E (S.standardTuple_isLattice.fg.map _), fun y => ?_⟩
  rw [mem_latFrame, mem_hermitianStandardLattice_iff_pairing_integral]
  constructor
  · intro h x hx
    rw [← hT_coord]
    exact h _ ((mem_latFrame S x).1 hx)
  · intro h x hx
    have := h (S.frame.equivFun x) ⟨x, hx, rfl⟩
    rwa [← hT_coord, S.frame.sum_equivFun] at this

variable {S T} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
  {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F}

theorem latO_le_top (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) : latO S T LS LT P ≤ latO S T LS LT fun _ => True :=
  AddSubgroup.closure_mono fun _ ⟨α, hα, _, h⟩ => ⟨α, hα, fun _ hv => absurd trivial hv, h⟩

theorem placeIdem_smul_mem (hε : IsPlaceIdem D v ε) {u : WO S T} (hu : u ∈ latO S T LS LT fun _ => True) :
    algebraMap (AF D.host.F) (AE D) ε • u ∈ latO S T LS LT fun w => w = v := by
  obtain ⟨β, rfl, h1, h0⟩ := hε
  have hβ : β ∈ intAf D.host.F := fun w => by
    by_cases hw : w = v
    · subst hw; rw [h1]; exact one_mem _
    · rw [h0 w hw]; exact zero_mem _
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨β * α, intAf_mul hβ hα, fun w hw => ?_, a, ha, s, hs, t, ht, ?_⟩
    · rw [map_mul, h0 w hw, zero_mul]
    · ext i j
      change (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 : D.host.E)) * (_ ⊗ₜ _) = _ ⊗ₜ _
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      congr 1
      exact Prod.ext (mul_zero _) rfl
  | zero => rw [smul_zero]; exact zero_mem _
  | add x x' _ _ h h' => rw [smul_add]; exact add_mem h h'
  | neg x _ h => rw [smul_neg]; exact neg_mem h

theorem idem_smul_mem (hε : IsPlaceIdem D v ε) {e : AE D} (he : e * e = e)
    (heε : algebraMap (AF D.host.F) (AE D) ε * e = e) {u : WO S T} (hu : u ∈ latO S T LS LT fun _ => True) :
    e • u ∈ (latO S T LS LT fun w => w = v) ⊓ half S T e := by
  refine AddSubgroup.mem_inf.2 ⟨?_, by rw [mem_half, smul_smul, he]⟩
  rw [← heε, mul_smul]
  exact placeIdem_smul_mem hε
    (GlobalTheory.LatticeStable.smul_mem_latO D S T LS LT _ e (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← map_mul, he])) u hu)

theorem infPart_half (hε : IsPlaceIdem D v ε) {e : AE D} (heε : algebraMap (AF D.host.F) (AE D) ε * e = e)
    {u : WO S T} (hu : u ∈ half S T e) : u.map (infPart D) = 0 := by
  obtain ⟨β, rfl, -⟩ := hε
  have h0 : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 β)) = 0 := TensorProduct.zero_tmul _ _
  ext i j
  rw [Matrix.map_apply, ← (isHalf_iff S T).2 hu i j, ← heε, map_mul, map_mul, h0, zero_mul, zero_mul]
  rfl

theorem halfInd_eq_ind (e : AE D) (Λ : AddSubgroup (WO S T)) : halfInd e Λ = ind (Λ ⊓ half S T e) := by
  funext t
  unfold halfInd ind
  by_cases h : t ∈ Λ ⊓ half S T e
  · rw [if_pos h, if_pos ⟨h.1, (isHalf_iff S T).2 h.2⟩]
  · rw [if_neg h, if_neg fun h' => h ⟨h'.1, (isHalf_iff S T).1 h'.2⟩]

theorem exists_placeModel (ψ : AddChar (AF D.host.F) ℂ) {e : AE D} (hec : e * cA D e = 0) (Λ : AddSubgroup (WO S T))
    (hLL' : ∀ u ∈ Λ ⊓ half S T e, ∀ y ∈ Λ ⊓ half S T (cA D e), ψ (symplO S T u y) = 1)
    (hX : ∀ x ∈ half S T e, (∀ y ∈ Λ ⊓ half S T (cA D e), ψ (symplO S T x y) = 1) → x ∈ Λ ⊓ half S T e)
    (hY : ∀ y ∈ half S T (cA D e), (∀ u ∈ Λ ⊓ half S T e, ψ (symplO S T u y) = 1) → y ∈ Λ ⊓ half S T (cA D e))
    (hfin : ∀ k : ℕ, 0 < k → ∃ R : Set (WO S T), R.Finite ∧
      ∀ t ∈ Λ ⊓ half S T e, ∃ r ∈ R, ∃ u ∈ Λ ⊓ half S T e, t = r + k • u)
    {c : ℂ} (hc : c ≠ 0) (f₀ : WO S T → ℂ) (hf : ∀ u ∈ Λ ⊓ half S T e, heisO ψ S T u f₀ = f₀)
    (hf' : ∀ u ∈ Λ ⊓ half S T (cA D e), heisO ψ S T u f₀ = f₀) :
    ∃ Tm, IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ c f₀ Tm := by
  have tf : ∀ k : ℕ, 0 < k → Function.Injective fun t : WO S T => k • t := fun k hk a b hab => by
    rw [← inv_smul_nsmul S T hk a, ← inv_smul_nsmul S T hk b]
    exact congrArg _ hab
  have c1 : cA D e * e = 0 := by rw [mul_comm, hec]
  have c2 : cA D (cA D e) * cA D e = 0 := by rw [cA_cA, hec]
  obtain ⟨Tm, h0, h1⟩ := exists_intertwiner (X := half S T e) (Y := half S T (cA D e)) (L := Λ ⊓ half S T e)
    (L' := Λ ⊓ half S T (cA D e)) (isBichar_symplO S T ψ) inf_le_right inf_le_right hLL' hX hY
    (half_div S T e) (half_div S T _) tf hfin (heisL S T ψ) (heisL_half S T ψ c1) (heisL_half S T ψ c2)
    (fun x _ y _ => heisL_comm S T ψ x y) f₀ hf hf'
  have h2 := fun Φ (hΦ : IsSBHalf e Λ Φ) =>
    h1 Φ (fun t ht => (isHalf_iff S T).1 (hΦ.1 t ht)) _ hΦ.2.choose_spec.1
      (fun u hu => hΦ.2.choose_spec.2.1 u hu.1 ((isHalf_iff S T).2 hu.2))
      fun t ht => ⟨hΦ.2.choose_spec.2.2 t ht, (half S T e).nsmul_mem ((isHalf_iff S T).1 (hΦ.1 t ht)) _⟩
  refine ⟨c⁻¹ • Tm, fun Φ hΦ x hx => ?_, fun Φ hΦ y hy => ?_, ?_⟩
  · rw [LinearMap.smul_apply, LinearMap.smul_apply, (h2 Φ hΦ).1 x ((isHalf_iff S T).1 hx)]
    exact ((heisL S T ψ x).map_smul _ _).symm
  · rw [LinearMap.smul_apply, LinearMap.smul_apply, (h2 Φ hΦ).2 y ((isHalf_iff S T).1 hy)]
    exact ((heisL S T ψ y).map_smul _ _).symm
  · rw [LinearMap.smul_apply, LinearMap.map_smul, halfInd_eq_ind, h0, smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem mem_of_dual {ψ : AddChar (AF D.host.F) ℂ} (hε : IsPlaceIdem D v ε)
    (hdual : ∀ u : WO S T, u.map (infPart D) = 0 → (u ∈ (latO S T LS LT fun _ => True) ↔
      ∀ u' ∈ (latO S T LS LT fun _ => True), ψ (symplO S T u u') = 1))
    {a : AE D} (ha : a * a = a) (h1 : algebraMap (AF D.host.F) (AE D) ε * a = a)
    (h2 : algebraMap (AF D.host.F) (AE D) ε * cA D a = cA D a) (x : WO S T) (hx : x ∈ half S T a)
    (h : ∀ y ∈ (latO S T LS LT fun w => w = v) ⊓ half S T (cA D a), ψ (symplO S T x y) = 1) :
    x ∈ (latO S T LS LT fun w => w = v) ⊓ half S T a := by
  have := idem_smul_mem hε ha h1 ((hdual x (infPart_half hε h1 hx)).2 fun u hu => by
    have := h _ (idem_smul_mem hε (by rw [← map_mul, ha]) h2 hu)
    rwa [← symplO_smul, (mem_half S T).1 hx] at this)
  rwa [(mem_half S T).1 hx] at this

end GlobalTheory.PlaceModel

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PureTensorLIntertwine
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace GlobalTheory.OrientedHeis

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem pureTensorL_intertwine {ι X : Type} (p : (X → ℂ) → Prop) (p0 : p 0) (padd : ∀ a b, p a → p b → p (a + b))
    (psmul : ∀ (c : ℂ) a, p a → p (c • a)) (A A' : ι → (X → ℂ) → (X → ℂ)) (Φ : Module.End ℂ (X → ℂ))
    (hA : ∀ i f, p f → p (A i f) ∧ Φ (A i f) = A' i (Φ f)) (f : X → ℂ) (hf : p f) (P : MvPolynomial ι ℂ) :
    p (pureTensorL A f P) ∧ Φ (pureTensorL A f P) = pureTensorL A' (Φ f) P := by
  have hl : ∀ l : List ι, p (l.foldr (fun i g => A i g) f) ∧
      Φ (l.foldr (fun i g => A i g) f) = l.foldr (fun i g => A' i g) (Φ f) := by
    intro l
    induction l with
    | nil => exact ⟨hf, rfl⟩
    | cons i l ih =>
      rw [List.foldr_cons, List.foldr_cons, ← ih.2]
      exact hA i _ ih.1
  have hm : ∀ (B : ι → (X → ℂ) → (X → ℂ)) (g : X → ℂ) (k : ι →₀ ℕ) (c : ℂ),
      pureTensorL B g (MvPolynomial.monomial k c) = c • opPow B k g := by
    intro B g k c
    have e : MvPolynomial.monomial k c = c • MvPolynomial.basisMonomials ι ℂ k := by
      rw [MvPolynomial.coe_basisMonomials, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [e, map_smul]
    unfold pureTensorL
    rw [Module.Basis.constr_basis]
  induction P using MvPolynomial.induction_on' with
  | monomial k c =>
    rw [hm, hm, map_smul]
    exact ⟨psmul c _ (hl _).1, congrArg (c • ·) (hl _).2⟩
  | add P Q hP hQ =>
    rw [map_add (f := _), map_add (f := _), map_add (f := _), hP.2, hQ.2]
    exact ⟨padd _ _ hP.1 hQ.1, rfl⟩

theorem cplxO_move {m n : ℕ} {sS sS' G G' : Matrix (Fin n) (Fin n) ℂ} {sT sT' H : Matrix (Fin m) (Fin m) ℂ}
    (hG : G * G' = 1) (hS : sS' * G = G * sS) (hT : sT' * H = H * sT) (z : Matrix (Fin m) (Fin n) ℂ) :
    cplxO sS' sT' (H * z * G') = H * cplxO sS sT z * G' := by
  have hG' : G' * G = 1 := mul_eq_one_comm.1 hG
  have e : G' * sS' = sS * G' := by
    calc G' * sS' = G' * (sS' * G) * G' := by rw [Matrix.mul_assoc, Matrix.mul_assoc, hG, Matrix.mul_one]
      _ = sS * G' := by rw [hS, ← Matrix.mul_assoc, hG', Matrix.one_mul]
  unfold cplxO
  rw [Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  calc sT' * (H * z * G') * sS' = (sT' * H) * z * (G' * sS') := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hT, e]; simp only [Matrix.mul_assoc]

theorem unitMap_move {m n : ℕ} {B G G' : Matrix (Fin n) (Fin n) ℂ} {B' H : Matrix (Fin m) (Fin m) ℂ}
    (hG : G * G' = 1) (i : Fin m) (j : Fin n) : unitMap (G * B) (H * B') i j = H * unitMap B B' i j * G' := by
  unfold unitMap
  rw [Matrix.mul_inv_rev, Matrix.inv_eq_right_inv hG]
  simp only [Matrix.mul_assoc]

theorem om_pureTensorO : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → ∀ (sS sS' BS BS' : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT sT' BT BT' : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (g : GA D S) (h : GA D T), (∀ τ, sS' τ * compAt θ τ (mt S g) = compAt θ τ (mt S g) * sS τ) → (∀ τ, sT' τ * compAt θ τ (mt T h) = compAt θ τ (mt T h) * sT τ) → (∀ τ, BS' τ = compAt θ τ (mt S g) * BS τ) → (∀ τ, BT' τ = compAt θ τ (mt T h) * BT τ) → ∀ f, IsThetaFunO ψ S T f → ∀ P, IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT f P) ∧ om (g, h) (pureTensorO ψ θ S T sS sT BS BT f P) = pureTensorO ψ θ S T sS' sT' BS' BT' (om (g, h) f) P := by
  intro D ψ θ S T χS χT om hom hθ sS sS' BS BS' sT sT' BT BT' g h h1 h2 h3 h4 f hf P
  refine pureTensorL_intertwine (IsThetaFunO ψ S T) theta_zero (fun _ _ => theta_add) (fun c _ => theta_smul c) _ _
    (om (g, h)) (fun k f hf => ?_) f hf P
  obtain ⟨τ, i, j⟩ := k
  have hG := compAt_mt_mul_inv (θ := θ) τ g
  refine ⟨theta_smul _ (theta_sub (theta_dRho hθ hom.std τ _ hf) (theta_smul _ (theta_dRho hθ hom.std τ _ hf))), ?_⟩
  simp only [aPlusAll, aPlus, crea]
  rw [map_smul, map_sub, map_smul, om_dRho hom hθ g h τ _ hf, om_dRho hom hθ g h τ _ hf, h3, h4, unitMap_move hG,
    cplxO_move hG (h1 τ) (h2 τ)]

end GlobalTheory.OrientedHeis

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SqNormIntegralFundamentalDomainEqL2NormSq
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace GlobalTheory.WeilVacMove

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {S T : HSp D}

theorem actO_two_nsmul (g : GA D S) (h : GA D T) (x : WO S T) : actO S T g h (2 • x) = 2 • actO S T g h x := by
  rw [two_nsmul, two_nsmul, actO_add]

theorem actO_inv_actO (g : GA D S) (h : GA D T) (x : WO S T) : actO S T g⁻¹ h⁻¹ (actO S T g h x) = x := by
  unfold actO
  rw [inv_inv, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← mt_mul, inv_mul_cancel, mt_one, Matrix.one_mul,
    Matrix.mul_assoc, ← mt_mul, inv_mul_cancel, mt_one, Matrix.mul_one]

theorem isHalf_actO (e : AE D) (g : GA D S) (h : GA D T) {x : WO S T} (hx : IsHalf e x) :
    IsHalf e (actO S T g h x) := by
  have e1 : e • x = x := Matrix.ext hx
  have e2 : e • actO S T g h x = actO S T g h x := by
    unfold actO
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, e1]
  exact fun i j => congrFun (congrFun e2 i) j

theorem sqNormIntegralFundamentalDomain_eq_l2Norm_sq (μ : Measure (WO S T)) (𝓕 : Set (WO S T)) {f : WO S T → ℂ} (hf : Continuous f) :
    nrm2 μ 𝓕 f = (∫⁻ w in 𝓕, ‖f w‖ₑ ^ 2 ∂μ).toReal := by
  have i6 : BorelSpace (WO S T) := ⟨rfl⟩
  unfold nrm2
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun w => sq_nonneg _)
    (hf.norm.pow 2).measurable.aestronglyMeasurable]
  congr 1
  refine lintegral_congr fun w => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]

theorem isVacO_om : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → ∀ (sS sS' : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT sT' : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (LS LS' : Set (Fin S.rank → D.host.E)) (LT LT' : Set (Fin T.rank → D.host.E)) (g : GA D S) (h : GA D T), (∀ τ, sS' τ * compAt θ τ (mt S g) = compAt θ τ (mt S g) * sS τ) → (∀ τ, sT' τ * compAt θ τ (mt T h) = compAt θ τ (mt T h) * sT τ) → (∀ u : WO S T, u ∈ (latO S T LS' LT' fun _ => True) ↔ ∃ u₀ ∈ (latO S T LS LT fun _ => True), u = actO S T g h u₀) → ∀ f, IsVacO ψ θ S T sS sT LS LT f → IsVacO ψ θ S T sS' sT' LS' LT' (om (g, h) f) := by
  intro D ψ θ S T χS χT om hW hθ sS sS' sT sT' LS LS' LT LT' g h hS hT hΛ f hf
  obtain ⟨hψ, -, hth, hlat, hfock, hnorm⟩ := hf
  refine ⟨hψ, hθ, hW.om_pres _ _ hth, ⟨fun u hu => ?_, fun e he u hu hh => ?_⟩, fun τ z => ?_, hnorm.1, fun p hp => ?_⟩
  · obtain ⟨u₀, hu₀, rfl⟩ := (hΛ u).1 hu
    rw [← actO_two_nsmul, ← hW.om_heis g h _ f hth, hlat.1 u₀ hu₀]
  · obtain ⟨u₀, hu₀, rfl⟩ := (hΛ u).1 hu
    have h0 : IsHalf e u₀ := by
      have := isHalf_actO e g⁻¹ h⁻¹ hh
      rwa [actO_inv_actO] at this
    rw [← hW.om_heis g h _ f hth, hlat.2 e he u₀ hu₀ h0]
  · obtain ⟨z₀, rfl⟩ : ∃ z₀ : Matrix (Fin T.rank) (Fin S.rank) ℂ, z = compAt θ τ (mt T h) * z₀ * compAt θ τ (mt S g⁻¹) := by
      refine ⟨compAt θ τ (mt T h⁻¹) * z * compAt θ τ (mt S g), ?_⟩
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, compAt_mt_mul_inv, Matrix.one_mul, Matrix.mul_assoc,
        compAt_mt_mul_inv, Matrix.mul_one]
    have h0 := congrArg (om (g, h)) (hfock τ z₀)
    unfold annih at h0 ⊢
    rw [map_add (f := _), map_smul, map_zero, om_dRho hW hθ g h τ _ hth, om_dRho hW hθ g h τ _ hth] at h0
    rw [cplxO_move θ τ g h (hS τ) (hT τ)]
    exact h0
  · show nrm2 p.1 p.2 (om (g, h) f) = 1
    rw [sqNormIntegralFundamentalDomain_eq_l2Norm_sq _ _ (hW.om_pres _ _ hth).cont, hW.om_unit p.1 p.2 hp.1 hp.2.1 _ f hth, ← sqNormIntegralFundamentalDomain_eq_l2Norm_sq _ _ hth.cont]
    exact hnorm.2 p hp

end GlobalTheory.WeilVacMove

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FockVacuumAnnihilationEquationRealCoordinates
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FockVacuumAnnihilationEquationRealCoordinates
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockCompare GlobalTheory.VacUnique

namespace GlobalTheory.VacUnique.Ann

theorem deriv_twisted_line {R : Type} [NormedAddCommGroup R] [NormedSpace ℝ R] (F : R → ℂ) (hF : Differentiable ℝ F)
    (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ) (w u : R) :
    deriv (fun t : ℝ => Complex.exp (-(Real.pi * Complex.I) * (om w (t • u) : ℂ)) * F (w + t • u)) 0 =
      fderiv ℝ F w u - Real.pi * Complex.I * (om w u : ℂ) * F w := by
  have h1 : HasDerivAt (fun t : ℝ => w + t • u) u 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add w
  have h2 : HasDerivAt (fun t : ℝ => F (w + t • u)) (fderiv ℝ F w u) 0 := by
    have h := (hF (w + (0 : ℝ) • u)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
    simpa [Function.comp_def] using h
  have h3 : HasDerivAt (fun t : ℝ => -(Real.pi * Complex.I) * (om w (t • u) : ℂ))
      (-(Real.pi * Complex.I) * (om w u : ℂ)) 0 := by
    have e : (fun t : ℝ => -(Real.pi * Complex.I) * (om w (t • u) : ℂ)) =
        fun t : ℝ => (t : ℂ) * (-(Real.pi * Complex.I) * (om w u : ℂ)) := by
      funext t
      rw [LinearMap.map_smul, smul_eq_mul, Complex.ofReal_mul]
      ring
    rw [e]
    simpa using (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const (-(Real.pi * Complex.I) * (om w u : ℂ))
  have h4 := (h3.cexp.mul h2).deriv
  refine Eq.trans h4 ?_
  simp only [zero_smul, map_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero, add_zero, one_mul]
  ring

variable {D : D7} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D}

open Classical in
theorem lineAt_eq (h : Chart θ σ) (S T : HSp D) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (t : ℝ) :
    lineAt θ τ z t = iotaW σ T S (t • (Pi.single τ z : RW T S)) := by
  have hL : IsLineAt θ τ z (lineAt θ τ z) :=
    Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ h.inf T.rank S.rank τ z)
  refine h.real_ext (V := T) (W := S) (hL.2.1 t) (h.real_iota T S _) ?_
  rw [h.pi_iota]
  funext τ'
  refine (hL.2.2 t τ').trans ?_
  by_cases e : τ' = τ
  · subst e
    have e1 : (Pi.single τ' z : RW T S) τ' = z := Pi.single_eq_same _ _
    rw [if_pos rfl, Pi.smul_apply, e1]
    funext i j
    show (t : ℂ) * z i j = t • z i j
    exact (Complex.real_smul).symm
  · have e1 : (Pi.single τ z : RW T S) τ' = 0 := Pi.single_eq_of_ne e _
    rw [if_neg e, Pi.smul_apply, e1, smul_zero]
    rfl

open Classical in
theorem dRho_eq (h : Chart θ σ) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D)
    (f : WO S T → ℂ) (hF : Differentiable ℝ fun z : RW T S => f (iotaW σ T S z)) (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (w : RW T S) :
    Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f (iotaW σ T S w) =
      fderiv ℝ (fun z : RW T S => f (iotaW σ T S z)) w (Pi.single τ z) -
        Real.pi * Complex.I * (omO S T w (Pi.single τ z) : ℂ) * f (iotaW σ T S w) := by
  refine Eq.trans ?_ (deriv_twisted_line _ hF (omO S T) w (Pi.single τ z))
  unfold Formalism.IndefR.Datum.dRho
  congr 1
  funext t
  rw [lineAt_eq h S T τ z t]
  unfold heisO
  rw [GlobalTheory.T.stdCharacter_halfSymplecticForm_realPoint D θ ψ h.inf hψ S T _ _ (Or.inl (h.real_iota T S w)), h.pi_iota, h.pi_iota,
    (iotaW σ T S).map_add]

open Classical in
theorem jO_single (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    jO S T sS sT (Pi.single τ z) = Pi.single τ (cplxO (sS τ) (sT τ) z) := by
  funext τ'
  rw [jO_apply]
  by_cases e : τ' = τ
  · subst e
    have e1 : ∀ y : Matrix (Fin T.rank) (Fin S.rank) ℂ, (Pi.single τ' y : RW T S) τ' = y :=
      fun _ => Pi.single_eq_same _ _
    rw [e1, e1]
  · have e1 : ∀ y : Matrix (Fin T.rank) (Fin S.rank) ℂ, (Pi.single τ y : RW T S) τ' = 0 :=
      fun _ => Pi.single_eq_of_ne e _
    rw [e1, e1]
    show Complex.I • (sT τ' * (0 : Matrix (Fin T.rank) (Fin S.rank) ℂ) * sS τ') = (0 : Matrix (Fin T.rank) (Fin S.rank) ℂ)
    rw [Matrix.mul_zero, Matrix.zero_mul, smul_zero]

theorem vacuum_annihilation : ∀ (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), Chart θ σ → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO S T → ℂ), IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → Differentiable ℝ (fun z : RW T S => f (iotaW σ T S z)) ∧ ∀ w z : RW T S, (fderiv ℝ (fun z : RW T S => f (iotaW σ T S z)) w z - Real.pi * Complex.I * (omO S T w z : ℂ) * f (iotaW σ T S w)) + Complex.I * (fderiv ℝ (fun z : RW T S => f (iotaW σ T S z)) w (jO S T sS sT z) - Real.pi * Complex.I * (omO S T w (jO S T sS sT z) : ℂ) * f (iotaW σ T S w)) = 0 := by
  classical
  intro D θ σ h ψ hψ S T sS sT f hf hv
  have hF : Differentiable ℝ (fun z : RW T S => f (iotaW σ T S z)) := by
    have h1 := ((smooth_iff_sm_and_real_lines D θ σ h T S).1 f).1 hf.smooth 0
    simp only [zero_add] at h1
    exact h1.differentiable (by simp)
  refine ⟨hF, fun w z => ?_⟩
  let A : RW T S →+ ℂ :=
    { toFun := fun z => fderiv ℝ (fun z : RW T S => f (iotaW σ T S z)) w z -
        Real.pi * Complex.I * (omO S T w z : ℂ) * f (iotaW σ T S w)
      map_zero' := by simp
      map_add' := fun x y => by
        rw [ContinuousLinearMap.map_add (f := _), LinearMap.map_add (f := _), Complex.ofReal_add]
        ring }
  show A z + Complex.I * A (jO S T sS sT z) = 0
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← Finset.univ_sum_single z, map_sum, map_sum, map_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun τ _ => ?_
  have h1 := congrFun (hv τ (z τ)) (iotaW σ T S w)
  have h2 : Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (z τ) f (iotaW σ T S w) +
      Complex.I * Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ) (z τ)) f (iotaW σ T S w) = 0 := h1
  have h3 := dRho_eq h hψ S T f hF τ (z τ) w
  have h4 := dRho_eq h hψ S T f hF τ (cplxO (sS τ) (sT τ) (z τ)) w
  have h5 := jO_single S T sS sT τ (z τ)
  have h6 : A (Pi.single τ (z τ)) + Complex.I * A (Pi.single τ (cplxO (sS τ) (sT τ) (z τ))) = 0 :=
    (congrArg₂ (fun a b : ℂ => a + Complex.I * b) h3 h4).symm.trans h2
  exact (congrArg (fun b => A (Pi.single τ (z τ)) + Complex.I * A b) h5).trans h6

end GlobalTheory.VacUnique.Ann
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FockVacuumAnnihilationEquationRealCoordinatesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockCompare GlobalTheory.VacUnique
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockVacuum_annihilation_equation_real_coordinates : ∀ (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), Chart θ σ → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO S T → ℂ), IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → Differentiable ℝ (fun z : RW T S => f (iotaW σ T S z)) ∧ ∀ w z : RW T S, (fderiv ℝ (fun z : RW T S => f (iotaW σ T S z)) w z - Real.pi * Complex.I * (omO S T w z : ℂ) * f (iotaW σ T S w)) + Complex.I * (fderiv ℝ (fun z : RW T S => f (iotaW σ T S z)) w (jO S T sS sT z) - Real.pi * Complex.I * (omO S T w (jO S T sS sT z) : ℂ) * f (iotaW σ T S w)) = 0 := by
  first | exact @GlobalTheory.VacUnique.Ann.vacuum_annihilation | exact GlobalTheory.VacUnique.Ann.vacuum_annihilation | (intros; apply GlobalTheory.VacUnique.Ann.vacuum_annihilation <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsSemicharacterCompletedSelfDualLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsSemicharacterCompletedSelfDualLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SemiChar

theorem exists_abstract {G R : Type} [AddCommGroup G] [AddCommGroup R] (ψ : AddChar R ℂ) (hψ : ∀ r, ‖ψ r‖ ≤ 1)
    (B : G → G → R) (hl : ∀ x y z, B (x + y) z = B x z + B y z) (hr : ∀ x y z, B x (y + z) = B x y + B x z)
    (ha : ∀ x, B x x = 0) (L : AddSubgroup G) (K : G → Prop) (K0 : K 0) (Ksub : ∀ x y, K x → K y → K (x - y))
    (hKL : ∀ l ∈ L, K l → l = 0) (hB : ∀ x, K x → ∀ l ∈ L, B x l = 0)
    (h2 : ∀ a ∈ L, ∀ u ∈ L, ψ (B a u + B a u) = 1)
    (p q : G → G) (padd : ∀ x y, p (x + y) = p x + p y) (pq : ∀ x, p x + q x = x)
    (adj : ∀ x y, B (p x) y = B x (q y)) (pL : ∀ l ∈ L, p l ∈ L) :
    ∃ χ : G → ℂ, (∀ x, (¬ ∃ l ∈ L, K (x - l)) → χ x = 0) ∧ (∀ x, ‖χ x‖ ≤ 1) ∧ χ 0 = 1 ∧
      (∀ x y, K y → χ (x + y) = χ x) ∧ (∀ u ∈ L, ∀ x, ψ (B x (2 • u)) * χ (x + 2 • u) = χ x) ∧
      ∀ u ∈ L, B (p u) u = 0 → ∀ x, ψ (B x u) * χ (x + u) = χ x := by
  classical
  have Kadd : ∀ x y, K x → K y → K (x + y) := fun x y hx hy => by
    have := Ksub x (0 - y) hx (Ksub 0 y K0 hy)
    rwa [zero_sub, sub_neg_eq_add] at this
  have skew : ∀ x y, B x y + B y x = 0 := fun x y => by
    have := ha (x + y)
    rwa [hl, hr, hr, ha, ha, zero_add, add_zero] at this
  let χ : G → ℂ := fun x => if h : ∃ l ∈ L, K (x - l) then ψ (B (p h.choose) h.choose) else 0
  have hn : ∀ x, (¬ ∃ l ∈ L, K (x - l)) → χ x = 0 := fun x h => dif_neg h
  have hy : ∀ x, ∀ l ∈ L, K (x - l) → χ x = ψ (B (p l) l) := fun x l hl' hk => by
    have h : ∃ l ∈ L, K (x - l) := ⟨l, hl', hk⟩
    have e : h.choose = l := by
      have h1 := Ksub _ _ hk h.choose_spec.2
      rw [sub_sub_sub_cancel_left] at h1
      exact sub_eq_zero.1 (hKL _ (L.sub_mem h.choose_spec.1 hl') h1)
    show dite _ _ _ = _
    rw [dite_eq_left h, e]
  have gen : ∀ u ∈ L, (∀ l ∈ L, ψ (B l u) * ψ (B (p (l + u)) (l + u)) = ψ (B (p l) l)) →
      ∀ x, ψ (B x u) * χ (x + u) = χ x := fun u hu H x => by
    by_cases h : ∃ l ∈ L, K (x - l)
    · obtain ⟨l, hl', hk⟩ := h
      have e : B x u = B l u := by
        have := hl (x - l) l u
        rwa [sub_add_cancel, hB _ hk u hu, zero_add] at this
      rw [hy x l hl' hk, hy (x + u) (l + u) (L.add_mem hl' hu) (by rwa [add_sub_add_right_eq_sub]), e, H l hl']
    · rw [hn x h, hn (x + u), mul_zero]
      rintro ⟨l, hl', hk⟩
      exact h ⟨l - u, L.sub_mem hl' hu, by rwa [← sub_add, sub_add_eq_add_sub]⟩
  refine ⟨χ, hn, fun x => ?_, ?_, fun x y hk => ?_, fun u hu => ?_, fun u hu h0 => ?_⟩
  · by_cases h : ∃ l ∈ L, K (x - l)
    · obtain ⟨l, hl', hk⟩ := h
      rw [hy x l hl' hk]; exact hψ _
    · rw [hn x h]; simp
  · rw [hy 0 0 L.zero_mem (by rwa [sub_zero])]
    have : B (p 0) 0 = 0 := by
      have := hr (p 0) 0 0
      rw [add_zero] at this
      exact left_eq_add.1 this
    rw [this, AddChar.map_zero_eq_one]
  · by_cases h : ∃ l ∈ L, K (x - l)
    · obtain ⟨l, hl', hk⟩ := h
      rw [hy x l hl' hk, hy (x + y) l hl' (by rw [← sub_add_eq_add_sub]; exact Kadd _ _ hk ‹_›)]
    · rw [hn x h, hn (x + y)]
      rintro ⟨l, hl', hk'⟩
      refine h ⟨l, hl', ?_⟩
      have := Ksub _ _ hk' hk
      rwa [show x + y - l - y = x - l by abel] at this
  · refine gen _ (L.nsmul_mem hu 2) fun l hl' => ?_
    have e : B (p (l + 2 • u)) (l + 2 • u) = B (p l) l + (B (p l) u + B (p l) u) +
        (B (p u) (l + 2 • u) + B (p u) (l + 2 • u)) := by
      conv_lhs => rw [padd, hl, hr, two_nsmul, hr, padd, hl]
      rw [two_nsmul]
    rw [e, two_nsmul, hr, h2 l hl' u hu, one_mul, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul,
      h2 _ (pL l hl') u hu, h2 _ (pL u hu) _ (L.add_mem hl' (L.add_mem hu hu)), mul_one, mul_one]
  · refine gen _ hu fun l hl' => ?_
    have e : B l u + B (p (l + u)) (l + u) = B (p l) l + (B (p l) u + B (p l) u) := by
      have e1 : B l u = B (p l) u + B (q l) u := by rw [← hl, pq]
      have e2 := skew u (q l)
      rw [padd, hl, hr, hr, h0, adj u l, e1]
      rw [← sub_eq_zero]
      refine Eq.trans ?_ e2
      abel
    rw [← AddChar.map_add_eq_mul, e, AddChar.map_add_eq_mul, h2 _ (pL l hl') u hu, mul_one]

variable {D : D7}

theorem latO_inf (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) : ∀ l ∈ latO S T LS LT P, l.map (infPart D) = 0 := by
  intro l hl
  induction hl using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, -, -, a, -, s, -, t, -, rfl⟩ := hw
    funext i j
    exact TensorProduct.zero_tmul _ _
  | zero => funext i j; exact (infPart D).map_zero
  | add x y _ _ hx hy =>
    funext i j
    have h1 : infPart D (x i j) = 0 := congrFun (congrFun hx i) j
    have h2 : infPart D (y i j) = 0 := congrFun (congrFun hy i) j
    show infPart D (x i j + y i j) = 0
    rw [RingHom.map_add (f := _), h1, h2, add_zero]
  | neg x _ hx =>
    funext i j
    have h1 : infPart D (x i j) = 0 := congrFun (congrFun hx i) j
    show infPart D (-x i j) = 0
    rw [RingHom.map_neg, h1, neg_zero]

theorem map_mul_add {m n : ℕ} (a : AE D) (x y : Mx D m n) :
    (x + y).map (fun z => a * z) = x.map (fun z => a * z) + y.map (fun z => a * z) := by
  funext i j; exact mul_add a (x i j) (y i j)

theorem latO_mul_int (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) (b : 𝓞 D.host.E) :
    ∀ l ∈ latO S T LS LT P, l.map (fun z => incA D (b : D.host.E) * z) ∈ latO S T LS LT P := by
  intro l hl
  induction hl using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, h1, h2, a, ha, s, hs, t, ht, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨α, h1, h2, b • a, Submodule.smul_mem (D.host.AA : Submodule (𝓞 D.host.E) D.host.E) b ha,
      s, hs, t, ht, ?_⟩
    funext i j
    show ((1 : AF D.host.F) ⊗ₜ[D.host.F] (b : D.host.E)) * (_ ⊗ₜ[D.host.F] _) = (_ ⊗ₜ[D.host.F] _)
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    congr 1
    show (b : D.host.E) * _ = (b : D.host.E) * a * _ * _
    ring
  | zero =>
    have : (0 : WO S T).map (fun z => incA D (b : D.host.E) * z) = 0 := by funext i j; exact mul_zero _
    rw [this]; exact AddSubgroup.zero_mem _
  | add x y _ _ hx hy => rw [map_mul_add]; exact AddSubgroup.add_mem _ hx hy
  | neg x _ hx =>
    have : (-x).map (fun z => incA D (b : D.host.E) * z) = -x.map (fun z => incA D (b : D.host.E) * z) := by
      funext i j; exact mul_neg _ _
    rw [this]; exact AddSubgroup.neg_mem _ hx

theorem exists_int_add_star (D : D7) : ∃ b : 𝓞 D.host.E, (b : D.host.E) + star (b : D.host.E) = 1 := by
  refine ⟨⟨(1 + D.host.sqrtMinusD) / 2,
    GlobalTheory.NormSum.isIntegral_half_one_add D.host.d D.host.hyp.2.2.2.1 _ (D.host.sqd_sq)⟩, ?_⟩
  have h2 : star (2 : D.host.E) = 2 := by
    have := star_natCast (R := D.host.E) 2
    exact_mod_cast this
  show (1 + D.host.sqrtMinusD) / 2 + star ((1 + D.host.sqrtMinusD) / 2) = 1
  rw [star_div₀, star_add, star_one, h2, GlobalTheory.FockCompare.RealChart.star_sqrtMinusD]
  ring

theorem exists_semichar : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → (∀ l ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), l.map (infPart D) = 0) ∧ ∃ χ : WO S T → ℂ, (∀ x, (¬ ∃ l ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), (x - l).map (finPart D) = 0) → χ x = 0) ∧ (∀ x, ‖χ x‖ ≤ 1) ∧ χ 0 = 1 ∧ (∀ x y, y.map (finPart D) = 0 → χ (x + y) = χ x) ∧ (∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), ∀ x, ψ (symplOH S T x (2 • u)) * χ (x + 2 • u) = χ x) ∧ ∀ e, IsSplitIdem D e → ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), IsHalf e u → ∀ x, ψ (symplOH S T x u) * χ (x + u) = χ x := by
  intro D S T ΛS ΛT ψ hψ hS hT
  have hinf := latO_inf S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True
  refine ⟨hinf, ?_⟩
  obtain ⟨f1, f2, f3, f4, -, -, f7, f8, f9⟩ := GlobalTheory.T.homSymplecticHalfForm_algebraic_laws_continuous D S T
  have g := (GlobalTheory.T.self_dual_lattice_pairing_dual D ψ S T ΛS ΛT hψ hS hT).1
  obtain ⟨b, hb⟩ := exists_int_add_star D
  obtain ⟨χ, c1, c2, c3, c4, c5, c6⟩ := exists_abstract ψ (fun r => (hψ.1.2.1 r).le) (symplOH S T) f1 f2 f3
    (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)
    (fun x => x.map (finPart D) = 0) (by funext i j; exact (finPart D).map_zero)
    (fun x y hx hy => by
      funext i j
      have h1 : finPart D (x i j) = 0 := congrFun (congrFun hx i) j
      have h2 : finPart D (y i j) = 0 := congrFun (congrFun hy i) j
      show finPart D (x i j - y i j) = 0
      rw [RingHom.map_sub, h1, h2, sub_zero])
    (fun l hl hk => by
      funext i j
      exact GlobalTheory.FockCompare.RealChart.adele_tensor_ext (l i j) (congrFun (congrFun (hinf l hl) i) j)
        (congrFun (congrFun hk i) j))
    (fun x hx l hl => f9 x l hx (hinf l hl))
    (fun a ha u hu => by rw [f4]; exact (g a (hinf a ha)).1 ha u hu)
    (fun x => x.map fun z => incA D (b : D.host.E) * z) (fun x => x.map fun z => cA D (incA D (b : D.host.E)) * z)
    (map_mul_add _)
    (fun x => by
      funext i j
      show incA D (b : D.host.E) * x i j + incA D (star (b : D.host.E)) * x i j = x i j
      rw [← add_mul, ← RingHom.map_add (f := _), hb, RingHom.map_one, one_mul])
    (f7 _) (latO_mul_int S T _ _ _ b)
  exact ⟨χ, c1, c2, c3, c4, c5, fun e he u hu hh => c6 u hu (f8 e _ u he.2.1 hh)⟩

end GlobalTheory.SemiChar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsSemicharacterCompletedSelfDualLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_semicharacter_completedSelfDualLattice : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → (∀ l ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), l.map (infPart D) = 0) ∧ ∃ χ : WO S T → ℂ, (∀ x, (¬ ∃ l ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), (x - l).map (finPart D) = 0) → χ x = 0) ∧ (∀ x, ‖χ x‖ ≤ 1) ∧ χ 0 = 1 ∧ (∀ x y, y.map (finPart D) = 0 → χ (x + y) = χ x) ∧ (∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), ∀ x, ψ (symplOH S T x (2 • u)) * χ (x + 2 • u) = χ x) ∧ ∀ e, IsSplitIdem D e → ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), IsHalf e u → ∀ x, ψ (symplOH S T x u) * χ (x + u) = χ x := by
  first | exact @GlobalTheory.SemiChar.exists_semichar | exact GlobalTheory.SemiChar.exists_semichar | (intros; apply GlobalTheory.SemiChar.exists_semichar <;> assumption)
end
end
