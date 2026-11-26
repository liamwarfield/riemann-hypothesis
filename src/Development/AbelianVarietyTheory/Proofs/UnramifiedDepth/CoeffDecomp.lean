module

public import ReciprocityTheory.DualLattices.SubMemOfCompat

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ZmodPrimeSqLocal
noncomputable section
open IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Be2 TrivSqZeroExt

namespace GlobalTheory.WModel

def mkL (R : Type) [CommRing R] [IsLocalRing R] : LAlg ℤ :=
  { carrier := R, alg := Ring.toIntAlgebra R }

def mkH {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S] (f : R →+* S)
    (hf : Function.Surjective f) : LHom (mkL R) (mkL S) :=
  ⟨f.toIntAlgHom, TowerExample.isLocalHom_of_surj _ hf⟩

instance dualLocal (A : Type) [CommRing A] [IsLocalRing A] : IsLocalRing (DualNumber A) := by
  haveI : Nontrivial (DualNumber A) := (inl_injective (R := A) (M := A)).nontrivial
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
  rw [isUnit_iff_isUnit_fst, isUnit_iff_isUnit_fst]
  simpa using IsLocalRing.isUnit_or_isUnit_one_sub_self x.fst

def fstR (A : Type) [CommRing A] : DualNumber A →+* A := (fstHom A A A).toRingHom

lemma fstR_surj (A : Type) [CommRing A] : Function.Surjective (fstR A) := fun r => ⟨inl r, rfl⟩

lemma ker_fstR (A : Type) [CommRing A] :
    RingHom.ker (fstR A) = Ideal.span {(DualNumber.eps : DualNumber A)} := by
  ext x
  rw [Ideal.mem_span_singleton']
  change fst x = 0 ↔ _
  constructor
  · intro hx
    refine ⟨inl x.snd, ?_⟩
    ext
    · simpa [snd_mul, DualNumber.snd_eps, DualNumber.fst_eps] using hx.symm
    · simp
  · rintro ⟨a, rfl⟩
    simp

lemma ann_eps (A : Type) [CommRing A] (a : DualNumber A) (ha : a * DualNumber.eps = 0) :
    a ∈ Ideal.span {(DualNumber.eps : DualNumber A)} := by
  rw [← ker_fstR]
  change fst a = 0
  have h := congrArg snd ha
  simpa [snd_mul, DualNumber.snd_eps, DualNumber.fst_eps] using h

lemma char_D (A : Type) [CommRing A] (k : ℕ) (h : (k : A) = 0) : (k : DualNumber A) = 0 := by
  ext
  · simpa using h
  · simp

def mapD {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) : DualNumber A →+* DualNumber B where
  toFun x := inl (f x.fst) + inr (f x.snd)
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp
  map_mul' x y := by ext <;> simp [snd_mul, mul_comm]

lemma mapD_surj {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (hf : Function.Surjective f) :
    Function.Surjective (mapD f) := fun y => by
  obtain ⟨a, ha⟩ := hf y.fst
  obtain ⟨b, hb⟩ := hf y.snd
  refine ⟨inl a + inr b, ?_⟩
  ext <;> simp [mapD, ha, hb]

def evD {A : Type} [CommRing A] (t : A) (ht : t * t = 0) : DualNumber A →+* A where
  toFun x := x.fst + t * x.snd
  map_one' := by simp
  map_zero' := by simp
  map_add' x y := by simp; ring
  map_mul' x y := by
    simp [snd_mul]
    linear_combination (-(x.snd * y.snd)) * ht

variable (p : ℕ) [hp : Fact p.Prime]

instance : NeZero (p ^ 2) := ⟨pow_ne_zero _ hp.out.ne_zero⟩

instance : Fact (1 < p ^ 2) := ⟨Nat.one_lt_pow two_ne_zero hp.out.one_lt⟩

instance zmod_prime_sq_local : IsLocalRing (ZMod (p ^ 2)) :=
  IsLocalRing.of_surjective' (PadicInt.toZModPow (p := p) 2) (ZMod.ringHom_surjective _)

def red : ZMod (p ^ 2) →+* ZMod p := ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p)

lemma red_surj : Function.Surjective (red p) := ZMod.ringHom_surjective _

lemma psq : (p : ZMod (p ^ 2)) ^ 2 = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_self]

lemma red_eq_zero (a : ZMod (p ^ 2)) : red p a = 0 ↔ (p : ZMod (p ^ 2)) ∣ a := by
  obtain ⟨k, rfl⟩ := ZMod.natCast_zmod_surjective a
  constructor
  · intro h
    rw [map_natCast, ZMod.natCast_eq_zero_iff] at h
    exact Nat.cast_dvd_cast h
  · rintro ⟨c, hc⟩
    rw [hc, map_mul, map_natCast, ZMod.natCast_self, zero_mul]

lemma ann_p (a : ZMod (p ^ 2)) : (p : ZMod (p ^ 2)) * a = 0 ↔ red p a = 0 := by
  constructor
  · intro h
    obtain ⟨k, rfl⟩ := ZMod.natCast_zmod_surjective a
    rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff, sq] at h
    rw [map_natCast, ZMod.natCast_eq_zero_iff]
    exact Nat.dvd_of_mul_dvd_mul_left hp.out.pos h
  · intro h
    obtain ⟨c, rfl⟩ := (red_eq_zero p a).1 h
    rw [← mul_assoc, ← sq, psq, zero_mul]

lemma pow_congr (x y : ZMod (p ^ 2)) (h : red p x = red p y) : x ^ p = y ^ p := by
  have h1 : (p : ZMod (p ^ 2)) ∣ x - y := (red_eq_zero p _).1 (by rw [map_sub, h, sub_self])
  have h2 := dvd_sub_pow_of_dvd_sub h1 1
  rw [pow_one, show (1 + 1 : ℕ) = 2 from rfl, psq, zero_dvd_iff, sub_eq_zero] at h2
  exact h2

def sec (a : ZMod p) : ZMod (p ^ 2) := (a.val : ℕ)

lemma red_sec (a : ZMod p) : red p (sec p a) = a := by
  rw [sec, map_natCast, ZMod.natCast_zmod_val]

def teich : ZMod p →* ZMod (p ^ 2) where
  toFun a := sec p a ^ p
  map_one' := by
    rw [pow_congr p _ 1 (by rw [red_sec, map_one]), one_pow]
  map_mul' a b := by
    rw [← mul_pow]
    exact pow_congr p _ _ (by rw [map_mul, red_sec, red_sec, red_sec])

lemma teich_red (x : ZMod (p ^ 2)) : teich p (red p x) = x ^ p :=
  pow_congr p _ _ (red_sec p _)

lemma red_teich (a : ZMod p) : red p (teich p a) = a := by
  change red p (sec p a ^ p) = a
  rw [map_pow, red_sec, ZMod.pow_card]

lemma wS_spec (n : ℕ) : (p : MvPolynomial (Fin n) ℤ) * wS p n =
    (∑ j, (MvPolynomial.X j) ^ p) - (∑ j, MvPolynomial.X j) ^ p := by
  set q : MvPolynomial (Fin n) ℤ := (∑ j, (MvPolynomial.X j) ^ p) - (∑ j, MvPolynomial.X j) ^ p with hq
  have hd : MvPolynomial.C (p : ℤ) ∣ q := by
    rw [MvPolynomial.C_dvd_iff_zmod, hq]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sub, map_sum, map_pow, MvPolynomial.map_X]
    rw [sum_pow_char, sub_self]
  rw [MvPolynomial.C_dvd_iff_dvd_coeff] at hd
  conv_rhs => rw [q.as_sum]
  change _ * ∑ m ∈ q.support, MvPolynomial.monomial m (q.coeff m / (p : ℤ)) = _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← map_natCast (MvPolynomial.C : ℤ →+* _), MvPolynomial.C_mul_monomial,
    Int.mul_ediv_cancel' (hd m)]

lemma witt_add (n : ℕ) (a : Fin n → ZMod p) : ∑ j, teich p (a j) =
    teich p (∑ j, a j) + p * teich p (MvPolynomial.eval₂ (Int.castRingHom (ZMod p))
      (fun j => (frobeniusEquiv (ZMod p) p).symm (a j)) (wS p n)) := by
  have hf : ∀ x : ZMod p, (frobeniusEquiv (ZMod p) p).symm x = x := fun x => by
    rw [RingEquiv.symm_apply_eq, frobeniusEquiv_apply, frobenius_def, ZMod.pow_card]
  have h := congrArg (MvPolynomial.eval₂Hom (Int.castRingHom (ZMod (p ^ 2))) (fun j => sec p (a j)))
    (wS_spec p n)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_mul, map_natCast, map_sub, map_sum, map_pow, MvPolynomial.eval₂Hom_X'] at h
  have h1 : teich p (∑ j, a j) = (∑ j, sec p (a j)) ^ p := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← teich_red, map_sum (red p)]
    simp only [red_sec]
  set c := MvPolynomial.eval₂ (Int.castRingHom (ZMod p))
      (fun j => (frobeniusEquiv (ZMod p) p).symm (a j)) (wS p n) with hc
  have h2 : (p : ZMod (p ^ 2)) * (teich p c - MvPolynomial.eval₂Hom (Int.castRingHom (ZMod (p ^ 2)))
      (fun j => sec p (a j)) (wS p n)) = 0 := by
    rw [ann_p, map_sub, red_teich, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_comp_left, sub_eq_zero, hc]
    congr 1
    · exact RingHom.ext_int _ _
    · funext j
      rw [hf, Function.comp_apply, red_sec]
  have h3 : ∑ j, teich p (a j) = ∑ j, sec p (a j) ^ p := rfl
  rw [h3, h1]
  linear_combination -h - h2

def lev : ℕ → LAlg ℤ
  | 0 => mkL (ZMod p)
  | _ + 1 => mkL (ZMod (p ^ 2))

def lev' : ℕ → LAlg ℤ
  | 0 => mkL (DualNumber (ZMod p))
  | _ + 1 => mkL (DualNumber (ZMod (p ^ 2)))

lemma pk (n : ℕ) : ((p ^ (n + 1 + 1) : ℕ) : ZMod (p ^ 2)) = 0 := by
  rw [ZMod.natCast_eq_zero_iff]
  exact pow_dvd_pow p (by omega)

def tower : ATowerL ℤ p where
  O := mkL (ZMod (p ^ 2))
  R' := lev' p
  R := lev p
  π | 0 => mkH (fstR _) (fstR_surj _)
    | _ + 1 => mkH (fstR _) (fstR_surj _)
  q | 0 => mkH (red p) (red_surj p)
    | _ + 1 => LHom.id _
  ξ | 0 => (DualNumber.eps : DualNumber (ZMod p))
    | _ + 1 => (DualNumber.eps : DualNumber (ZMod (p ^ 2)))
  surj | 0 => fstR_surj _
       | _ + 1 => fstR_surj _
  ker_eq | 0 => ker_fstR _
         | _ + 1 => ker_fstR _
  ξ_sq | 0 => DualNumber.eps_mul_eps (R := ZMod p)
       | _ + 1 => DualNumber.eps_mul_eps (R := ZMod (p ^ 2))
  ann | 0 => ann_eps _
      | _ + 1 => ann_eps _
  char | 0 => char_D (ZMod p) _ (by simp)
       | n + 1 => char_D (ZMod (p ^ 2)) _ (pk p n)
  sep a ha := ha 1
  c := 0
  cp _ := 0
  cp_spec _ := (map_zero _).trans (map_zero _).symm
  zh _ := 1
  zh_pow _ := by rw [Units.val_one, one_pow, zero_mul, add_zero]
  ζ _ := 1
  ζ_spec _ := (map_one _).trans (map_one _).symm
  r' | 0 => mkH (mapD (red p)) (mapD_surj _ (red_surj p))
     | _ + 1 => LHom.id _
  r | 0 => mkH (red p) (red_surj p)
    | _ + 1 => LHom.id _
  r_π | 0 => fun x => by
          change red p (fst x) = fst (inl (red p (fst x)) + inr (red p (snd x)) : DualNumber (ZMod p))
          simp
      | _ + 1 => fun _ => rfl
  r_q | 0 => fun _ => rfl
      | _ + 1 => fun _ => rfl
  r'_ξ | 0 => by
          change mapD (red p) DualNumber.eps = DualNumber.eps
          ext <;> simp [mapD]
       | _ + 1 => rfl
  complete x hx := ⟨x 1, fun n => by
    cases n with
    | zero => exact hx 0
    | succ n =>
      induction n with
      | zero => rfl
      | succ n ih => exact ih.trans (hx (n + 1)).symm⟩

def wModel : WData (tower p) (mkL (ZMod p)) where
  W := mkL (ZMod (p ^ 2))
  ρW := mkH (red p) (red_surj p)
  ρ1 := LHom.id _
  ψ := mkH (evD (p : ZMod (p ^ 2)) (by rw [← sq, psq])) fun a => ⟨inl a, by simp [evD]⟩
  πW := mkH (red p) (red_surj p)
  πW_surj := red_surj p
  ρW_eq := rfl
  p_sq := psq p
  ker_πW := by
    ext a
    exact (red_eq_zero p a).trans Ideal.mem_span_singleton.symm
  ann_p := ann_p p
  compat a := by
    change red p (fst a + p * snd a) = red p (fst a)
    rw [map_add (f := _), map_mul, map_natCast, ZMod.natCast_self, zero_mul, add_zero]
  b := 1
  ξ_img := by
    change fst (DualNumber.eps : DualNumber (ZMod (p ^ 2))) + (p : ZMod (p ^ 2)) * snd (DualNumber.eps : DualNumber (ZMod (p ^ 2))) = (p : ZMod (p ^ 2)) * 1
    simp
  Rb := ZMod p
  T := teich p
  decomp (w : ZMod (p ^ 2)) := by
    obtain ⟨c, hc⟩ := (red_eq_zero p (w - teich p (red p w))).1 (by rw [map_sub, red_teich, sub_self])
    exact ⟨red p w, c, sub_eq_iff_eq_add'.1 hc⟩
  witt_add := witt_add p
  T_kill c h := by
    have h1 : c = 0 := (red_teich p c).symm.trans h
    subst h1
    have := teich_red p 0
    rw [map_zero, zero_pow hp.out.ne_zero] at this
    exact this

end GlobalTheory.WModel
end
end

noncomputable section

open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2

namespace GlobalTheory.WFrob

variable {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {Tw : ATowerL R₀ p} {K : LAlg R₀}

private lemma pow_add_sqz {A : Type*} [CommRing A] (u v : A) (hv : v * v = 0) (n : ℕ) :
    (u + v) ^ (n + 1) = u ^ (n + 1) + ((n : A) + 1) * u ^ n * v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih]
    push_cast
    linear_combination ((n : A) + 1) * u ^ n * hv

private lemma p_ker (wd : WData Tw K) : wd.πW.1 (p : (wd.W : Type)) = 0 := by
  have : (p : (wd.W : Type)) ∈ RingHom.ker wd.πW.1 := by
    rw [wd.ker_πW]; exact Ideal.subset_span rfl
  exact this

private lemma π_pmul (wd : WData Tw K) (x : (wd.W : Type)) : wd.πW.1 (p * x) = 0 := by
  rw [map_mul, p_ker, zero_mul]

private lemma T_zero (wd : WData Tw K) : wd.T 0 = 0 := by
  have h := wd.witt_add 0 Fin.elim0
  rw [Finset.univ_eq_empty, Finset.sum_empty, Finset.sum_empty] at h
  apply wd.T_kill
  have h2 := congrArg wd.πW.1 h
  rw [map_zero, map_add (f := _), π_pmul, add_zero] at h2
  exact h2.symm

private lemma πT_add (wd : WData Tw K) (a b : wd.Rb) :
    wd.πW.1 (wd.T (a + b)) = wd.πW.1 (wd.T a) + wd.πW.1 (wd.T b) := by
  have h := wd.witt_add 2 ![a, b]
  rw [Fin.sum_univ_two, Fin.sum_univ_two] at h
  have h2 := congrArg wd.πW.1 h
  rw [map_add (f := _), map_add (f := _), π_pmul, add_zero] at h2
  simpa using h2.symm

private def φW (wd : WData Tw K) : wd.Rb →+* (Tw.R 0 : Type) where
  toFun c := wd.πW.1 (wd.T c)
  map_one' := by rw [map_one, map_one]
  map_mul' a b := by rw [map_mul, map_mul]
  map_zero' := by rw [T_zero, map_zero]
  map_add' := πT_add wd

private lemma φW_apply (wd : WData Tw K) (c : wd.Rb) : φW wd c = wd.πW.1 (wd.T c) := rfl

private lemma pmul_congr (wd : WData Tw K) (a b : (wd.W : Type)) (h : wd.πW.1 a = wd.πW.1 b) :
    (p : (wd.W : Type)) * a = p * b := by
  have := (wd.ann_p (a - b)).2 (by rw [map_sub, h, sub_self])
  rw [mul_sub, sub_eq_zero] at this
  exact this

private lemma pow_p_teich (wd : WData Tw K) (u s : (wd.W : Type)) :
    (u + p * s) ^ p = u ^ p := by
  obtain ⟨k, hk⟩ : ∃ k, p = k + 1 := ⟨p - 1, (Nat.sub_add_cancel (Fact.out : p.Prime).one_le).symm⟩
  have hv : (p * s) * (p * s) = 0 := by
    have : (p : (wd.W : Type)) * p * (s * s) = 0 := by rw [← sq, wd.p_sq, zero_mul]
    linear_combination this
  have := pow_add_sqz u (p * s) hv k
  rw [← hk] at this
  rw [this]
  have hk' : ((k : (wd.W : Type)) + 1) = p := by
    have := congrArg (Nat.cast : ℕ → (wd.W : Type)) hk
    rw [this]; push_cast; ring
  rw [hk']
  have : (p : (wd.W : Type)) * u ^ k * (p * s) = (p : (wd.W : Type)) ^ 2 * (u ^ k * s) := by ring
  rw [this, wd.p_sq, zero_mul, add_zero]

private lemma coeff_decomp (wd : WData Tw K) {g : ℕ} (G : MvPolynomial (Fin g) (wd.W : Type))
    (hG : ∀ m, (∃ i, ¬ p ∣ m i) →
      AddMonoidAlgebra.coeff G m ∈ Ideal.span {(p : (wd.W : Type))}) (m : Fin g →₀ ℕ) :
    ∃ d : wd.Rb, ∃ e : (wd.W : Type), AddMonoidAlgebra.coeff G m = wd.T d + p * e ∧
      (d = 0 ∨ ∀ i, p ∣ m i) := by
  by_cases h : ∃ i, ¬ p ∣ m i
  · obtain ⟨e, he⟩ := Ideal.mem_span_singleton'.1 (hG m h)
    exact ⟨0, e, by rw [T_zero, zero_add, ← he, mul_comm], Or.inl rfl⟩
  · obtain ⟨d, e, he⟩ := wd.decomp (AddMonoidAlgebra.coeff G m)
    refine ⟨d, e, he, Or.inr fun i => ?_⟩
    by_contra hi
    exact h ⟨i, hi⟩

private lemma teich_term (wd : WData Tw K) {g : ℕ} (m : Fin g →₀ ℕ) (d : wd.Rb)
    (hd : d = 0 ∨ ∀ i, p ∣ m i) (η : Fin g → wd.Rb) (s : Fin g → (wd.W : Type)) :
    wd.T d * ∏ i, (wd.T (η i) + p * s i) ^ m i = wd.T (d * ∏ i, η i ^ m i) := by
  rcases hd with rfl | hd
  · rw [zero_mul, T_zero, zero_mul]
  · rw [map_mul, map_prod]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    obtain ⟨k, hk⟩ := hd i
    rw [map_pow, hk, pow_mul, pow_p_teich, ← pow_mul]

private lemma root_term (wd : WData Tw K) {g : ℕ} (m : Fin g →₀ ℕ) (d : wd.Rb)
    (hd : d = 0 ∨ ∀ i, p ∣ m i) (η : Fin g → wd.Rb) :
    (frobeniusEquiv wd.Rb p).symm (d * ∏ i, η i ^ m i) =
      (frobeniusEquiv wd.Rb p).symm d * ∏ i, η i ^ (m i / p) := by
  rcases hd with rfl | hd
  · rw [zero_mul, map_zero, zero_mul]
  · rw [map_mul, map_prod]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [RingEquiv.symm_apply_eq, frobeniusEquiv_apply, frobenius_def, ← pow_mul,
      Nat.div_mul_cancel (hd i)]

theorem wFrob :
    (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {Tw : ATowerL R₀ p} {K : LAlg R₀}
      (wd : WData Tw K) (g : ℕ), WFrobStatement wd g) := by
  intro R₀ _ p _ Tw K wd g G hG
  classical
  choose d e hde hd using coeff_decomp wd G hG
  set n := G.support.card with hn
  let μ : Fin n → (Fin g →₀ ℕ) := fun j => (G.support.equivFin.symm j : Fin g →₀ ℕ)
  have hsum : ∀ (f : (Fin g →₀ ℕ) → (wd.W : Type)), ∑ m ∈ G.support, f m = ∑ j, f (μ j) := by
    intro f
    rw [← Finset.sum_coe_sort G.support f]
    exact (Equiv.sum_comp G.support.equivFin.symm (fun x => f x)).symm
  refine ⟨MvPolynomial.eval₂ (Int.castRingHom _)
      (fun j => MvPolynomial.C (φW wd ((frobeniusEquiv wd.Rb p).symm (d (μ j)))) *
        ∏ i, MvPolynomial.X i ^ (μ j i / p)) (wS p n) +
      ∑ j, MvPolynomial.C (wd.πW.1 (e (μ j))) * ∏ i, MvPolynomial.X i ^ (μ j i), ?_⟩
  intro y hy a ha
  choose η s hy' using fun i => wd.decomp (y i)
  have hπy : ∀ i, wd.πW.1 (y i) = φW wd (η i) := fun i => by
    rw [hy' i, map_add (f := _), π_pmul, add_zero, φW_apply]
  have hw := wd.witt_add n (fun j => d (μ j) * ∏ i, η i ^ μ j i)
  have hev : MvPolynomial.eval y G = ∑ j, wd.T (d (μ j) * ∏ i, η i ^ μ j i) +
      p * ∑ j, e (μ j) * ∏ i, y i ^ μ j i := by
    rw [MvPolynomial.eval_eq', hsum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hde, add_mul, ← teich_term wd (μ j) (d (μ j)) (hd _) η s, mul_assoc]
    simp only [← hy']
  rw [hw, add_assoc, ← mul_add] at hev
  have h0 : wd.T (∑ j, d (μ j) * ∏ i, η i ^ μ j i) = 0 := by
    apply wd.T_kill
    have h1 : wd.πW.1 (MvPolynomial.eval y G) = 0 := by
      rw [← wd.ker_πW] at hy
      exact hy
    rw [hev, map_add (f := _), π_pmul, add_zero] at h1
    exact h1
  rw [hev, h0, zero_add]
  apply pmul_congr
  rw [ha, map_add (f := _), map_add (f := _), ← φW_apply, MvPolynomial.eval₂_comp_left,
    MvPolynomial.eval₂_comp_left]
  congr 1
  · congr 1
    · exact RingHom.ext_int _ _
    · funext j
      rw [Function.comp_apply, Function.comp_apply, root_term wd (μ j) (d (μ j)) (hd _) η]
      simp only [map_mul, map_prod, map_pow, MvPolynomial.eval_C, MvPolynomial.eval_X, hπy]
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [map_sum, map_mul, map_prod, map_pow, MvPolynomial.eval_C, MvPolynomial.eval_X]

end GlobalTheory.WFrob
