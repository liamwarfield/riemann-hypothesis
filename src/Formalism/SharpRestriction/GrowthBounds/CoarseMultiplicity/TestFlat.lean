module

public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.RestBlockForm
public import Formalism.LocalToGlobal.GroupLattices.FockModels.FlatModels.LetterWtAnti

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.MulMatQOne
section -- merged from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.LaTwInvT
section -- merged from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.FockRAddRight
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.ColumnSystems.Pf.TF

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility
open Formalism.L2.G.Model (Lin Th0 Aa Lin_comp Lin_one Lin_Pol Th0_inj mem_tens_nabla mem_tens_dw map_Pol mem_Pol VS)
open Formalism.L2.G.Model.TS

def kapFl (p k : ℕ) {S : Type} [Fintype S] (d : S → ℕ) : ℕ := ∑ s, k * Nat.log p (d s)

def MultDiv (O : Type) [CommRing O] (p κ : ℕ) {S : Type} [Fintype S] {k : ℕ} (d : S → ℕ) : Prop :=
  ∀ α : S × Fin k →₀ ℕ, (∀ s, multideg α s = d s) →
    (((∏ s, (d s).factorial : ℕ) : ℕ) : O) ∣ (p : O) ^ κ * ((expFact α : ℕ) : O)

theorem mem_scale {O Kf X : Type*} [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup X] [Module Kf X] [Module O X]
    [IsScalarTower O Kf X] {c : Kf} {M : Submodule O X} {x : X} : x ∈ scale c M ↔ ∃ y ∈ M, c • y = x := by
  unfold scale
  rw [Submodule.mem_map]
  rfl

section Contra

variable {S : Type} [Fintype S] [DecidableEq S] {R : Type} [CommRing R] {k : ℕ}

theorem fock_eq_fockR {τ : Type} (F G : MvPolynomial τ R) : fock F G = fockR F G := rfl

theorem Lin_X (N : S → Matrix (Fin k) (Fin k) R) (v : S × Fin k) :
    Lin N (X v) = ∑ b : Fin k, C (N v.1 v.2 b) * X (v.1, b) := by
  simp [Lin]

theorem Lin_coeff_zero (N : S → Matrix (Fin k) (Fin k) R) (h : MvPolynomial (S × Fin k) R) :
    AddMonoidAlgebra.coeff (Lin N h) 0 = AddMonoidAlgebra.coeff h 0 := by
  induction h using MvPolynomial.induction_on with
  | C a => simp [Lin]
  | add p q hp hq => simp only [map_add (f := _), MvPolynomial.coeff_add, hp, hq]
  | mul_X p v hp =>
    have e1 : AddMonoidAlgebra.coeff (p * X v) 0 = 0 := by
      rw [← constantCoeff_eq]; simp
    have e2 : AddMonoidAlgebra.coeff (Lin N (p * X v)) 0 = 0 := by
      rw [map_mul, Lin_X, ← constantCoeff_eq]; simp
    rw [e1, e2]

theorem Lin_chain (N : S → Matrix (Fin k) (Fin k) R) (s : S) (b : Fin k) (h : MvPolynomial (S × Fin k) R) :
    pderiv (s, b) (Lin N h) = ∑ a : Fin k, N s a b • Lin N (pderiv (s, a) h) := by
  classical
  induction h using MvPolynomial.induction_on with
  | C a => simp [Lin]
  | add p q hp hq => simp only [map_add (f := _), hp, hq, smul_add, Finset.sum_add_distrib]
  | mul_X p v hp =>
    obtain ⟨t, c⟩ := v
    have hL : pderiv (s, b) (∑ d : Fin k, C (N t c d) * X (t, d) : MvPolynomial (S × Fin k) R)
        = if t = s then C (N t c b) else 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp only [pderiv_C_mul, pderiv_X, Pi.single_apply, Prod.mk.injEq]
      by_cases hts : t = s
      · subst hts
        simp [eq_comm]
      · have hts' : ¬ s = t := fun h => hts h.symm
        simp [hts, hts']
    have hR : ∑ a : Fin k, N s a b • (Lin N p * Lin N (pderiv (s, a) (X (t, c))))
        = Lin N p * (if t = s then C (N t c b) else 0) := by
      simp only [pderiv_X, Pi.single_apply, Prod.mk.injEq]
      by_cases hts : t = s
      · subst hts
        simp [apply_ite, Finset.sum_ite_eq, smul_eq_C_mul, mul_comm]
      · have hts' : ¬ s = t := fun h => hts h.symm
        simp [hts, hts']
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add (f := _), Lin_X, hL, hp]
    simp only [smul_add, Finset.sum_add_distrib]
    rw [hR]
    simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm]

theorem fockR_Lin (N : S → Matrix (Fin k) (Fin k) R) (P : MvPolynomial (S × Fin k) R) :
    ∀ Q : MvPolynomial (S × Fin k) R, fockR (Lin N P) Q = fockR P (Lin (fun s => (N s).transpose) Q) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    intro Q
    have h1 : Lin N (C a : MvPolynomial (S × Fin k) R) = C a := by simp [Lin]
    rw [h1, C_apply, tsact_monomial_left, tsact_monomial_left, Lin_coeff_zero]
  | add p q hp hq =>
    intro Q
    rw [map_add (f := _), tsact_add_left, tsact_add_left, hp, hq]
  | mul_X p v hp =>
    intro Q
    rw [map_mul, Lin_X, Finset.mul_sum, tsact_sum_left, tsact_X_mul, Lin_chain, tsact_sum_right]
    refine Finset.sum_congr rfl fun b _ => ?_
    have e : Lin N p * (C (N v.1 v.2 b) * X (v.1, b)) = N v.1 v.2 b • (Lin N p * X (v.1, b)) := by
      rw [smul_eq_C_mul]; ring
    rw [e, tsact_smul_left, tsact_X_mul, hp, tsact_smul_right, Matrix.transpose_apply]

theorem fockR_Lin_dual (A B : S → Matrix (Fin k) (Fin k) R) (h : ∀ s, B s * (A s).transpose = 1)
    (P Q : MvPolynomial (S × Fin k) R) : fockR (Lin A P) (Lin B Q) = fockR P Q := by
  rw [fockR_Lin, Lin_comp]
  simp only [h]
  rw [Lin_one]

end Contra

theorem Aa_dual {K : Type} [Field K] {m : ℕ} (vec : Bool) (M : Matrix (Fin (m + 1)) (Fin (m + 1)) K)
    (hM : IsUnit M.det) : Aa vec ((M⁻¹).transpose)⁻¹ * (Aa vec M⁻¹).transpose = 1 := by
  have hMi : IsUnit (M⁻¹).det := by rw [Matrix.det_nonsing_inv]; exact hM.ringInverse
  have hMt : IsUnit ((M⁻¹).transpose).det := by rw [Matrix.det_transpose]; exact hMi
  cases vec
  · simp only [Aa, Bool.false_eq_true, if_false]
    rw [Matrix.nonsing_inv_nonsing_inv _ hMt, Matrix.nonsing_inv_nonsing_inv _ hM, Matrix.transpose_transpose,
      Matrix.transpose_transpose, Matrix.nonsing_inv_mul _ hM]
  · simp only [Aa, if_true]
    exact Matrix.nonsing_inv_mul _ hMt

theorem multDiv_kapFl (O : Type) [CommRing O] [IsLocalRing O] (p : ℕ) [hp : Fact p.Prime]
    (hpO : (p : O) ∈ IsLocalRing.maximalIdeal O) {S : Type} [Fintype S] {k : ℕ} (d : S → ℕ) :
    MultDiv O p (kapFl p k d) (k := k) d := by
  intro α hα

  have h1 : ∀ s, (d s).factorial = Nat.multinomial Finset.univ (fun c : Fin k => α (s, c)) *
      ∏ c : Fin k, (α (s, c)).factorial := by
    intro s
    rw [mul_comm, Nat.multinomial_spec, ← hα s]
    rfl
  have h2 : expFact α = ∏ s : S, ∏ c : Fin k, (α (s, c)).factorial := by
    unfold expFact
    rw [Finsupp.prod_fintype _ _ (fun _ => rfl), Fintype.prod_prod_type]
  set Mn : ℕ := ∏ s : S, Nat.multinomial Finset.univ (fun c : Fin k => α (s, c)) with hMn
  have h3 : (∏ s, (d s).factorial) = Mn * expFact α := by
    rw [h2, hMn, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun s _ => h1 s
  have hMn0 : Mn ≠ 0 := Finset.prod_ne_zero_iff.2 fun s _ => (Nat.multinomial_pos _ _).ne'
  have h4 : padicValNat p Mn ≤ kapFl p k d := by
    rw [hMn, Formalism.CountingSumsFrames.fock_val_prod p _ _ (fun s _ => (Nat.multinomial_pos _ _).ne')]
    unfold kapFl
    refine Finset.sum_le_sum fun s _ => ?_
    have := Formalism.CountingSumsFrames.fock_mult_val_le p (fun c : Fin k => α (s, c)) Finset.univ
    rw [Finset.card_univ, Fintype.card_fin] at this
    have e : ∑ c : Fin k, α (s, c) = d s := hα s
    rw [e] at this
    exact this

  have hdv : p ^ padicValNat p Mn ∣ Mn := (_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat _ _))
  have hnd : ¬ p ^ (padicValNat p Mn + 1) ∣ Mn := by
    rw [Nat.padicValNat_def]
    exact pow_succ_multiplicity_not_dvd hMn0
  generalize padicValNat p Mn = v at h4 hdv hnd
  obtain ⟨u, hu⟩ := hdv
  have hpu : ¬ p ∣ u := by
    intro hd
    apply hnd
    rw [hu, pow_succ]
    exact Nat.mul_dvd_mul_left _ hd
  have huO : IsUnit ((u : ℕ) : O) := by
    have hco : Nat.Coprime u p := ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hpu).symm
    by_contra hnu
    have hm : ((u : ℕ) : O) ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 hnu
    have hb := Nat.gcd_eq_gcd_ab u p
    rw [hco] at hb
    have h5 : (1 : O) = (u : O) * ((Nat.gcdA u p : ℤ) : O) + (p : O) * ((Nat.gcdB u p : ℤ) : O) := by
      have := congrArg (fun z : ℤ => (z : O)) hb
      push_cast at this
      exact this
    have h6 : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
      rw [h5]
      exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hm) (Ideal.mul_mem_right _ _ hpO)
    exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 h6)
  obtain ⟨uu, huu⟩ := huO
  refine ⟨(p : O) ^ (kapFl p k d - v) * (↑uu⁻¹ : O), ?_⟩
  rw [h3, hu]
  push_cast
  rw [← huu]
  have e1 : (p : O) ^ kapFl p k d = (p : O) ^ v * (p : O) ^ (kapFl p k d - v) := by
    rw [← pow_add]
    congr 1
    omega
  rw [e1]
  have e2 : (uu : O) * (↑uu⁻¹ : O) = 1 := Units.mul_inv uu
  linear_combination (-(p : O) ^ v * (p : O) ^ (kapFl p k d - v) * (expFact α : O)) * e2

def fockL {τ K : Type} [CommRing K] (Q : MvPolynomial τ K) : MvPolynomial τ K →ₗ[K] K where
  toFun P := fockR P Q
  map_add' a b := tsact_add_left a b Q
  map_smul' c a := by simpa using tsact_smul_left c a Q

theorem fockR_add_right {τ K : Type} [CommRing K] (g f f' : MvPolynomial τ K) :
    fockR g (f + f') = fockR g f + fockR g f' := by
  rw [tsact_symm, tsact_add_left, tsact_symm f, tsact_symm f']

section Pair

variable {O Kf : Type} [CommRing O] [IsDomain O] [Field Kf] [Algebra O Kf] {S : Type} [Fintype S] [DecidableEq S] {m : ℕ}

def LatM (O : Type) {Kf : Type} [CommRing O] [Field Kf] [Algebra O Kf] {S : Type} [Fintype S] {m : ℕ} (vec : S → Bool)
    (d : S → ℕ) (M : S → Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) :
    Submodule O (MvPolynomial (S × (Fin (m + 1) × Fin (m + 1))) Kf) :=
  tensorLat O Kf (fun s => nablaLTw O Kf m (letterWt m (d s) (vec s)) (M s))

theorem exists_thK (Kf : Type) [Field Kf] {S : Type} [Fintype S] [DecidableEq S] {m : ℕ} (hm : 1 ≤ m) (vec : S → Bool)
    (d : S → ℕ) :
    ∃ thK : ↥(Pol Kf (ι := S) (m + 1) d) ≃ₗ[Kf] ↥(VS Kf m vec d),
      ∀ P, ((thK P : ↥(VS Kf m vec d)) : MvPolynomial (S × (Fin (m + 1) × Fin (m + 1))) Kf) =
        Th0 Kf m vec (P : MvPolynomial (S × Fin (m + 1)) Kf) := by
  let f : ↥(Pol Kf (ι := S) (m + 1) d) →ₗ[Kf] ↥(VS Kf m vec d) :=
    LinearMap.codRestrict (VS Kf m vec d)
      ((Th0 Kf m vec).toLinearMap.comp (Pol Kf (ι := S) (m + 1) d).subtype)
      (fun P => (mem_tens_dw Kf m hm vec d _).2 ⟨P.1, P.2, rfl⟩)
  have hinj : Function.Injective f := by
    intro P Q hPQ
    apply Subtype.ext
    exact Th0_inj Kf m hm vec d _ _ P.2 Q.2 (congrArg Subtype.val hPQ)
  have hsurj : Function.Surjective f := by
    intro y
    have hy : (y : MvPolynomial (S × (Fin (m + 1) × Fin (m + 1))) Kf) ∈ VS Kf m vec d := y.2
    obtain ⟨F, hF, hyF⟩ := (mem_tens_dw Kf m hm vec d _).1 hy
    exact ⟨⟨F, hF⟩, Subtype.ext hyF.symm⟩
  exact ⟨LinearEquiv.ofBijective f ⟨hinj, hsurj⟩, fun P => rfl⟩

variable {vec : S → Bool} {d : S → ℕ} (thK : ↥(Pol Kf (ι := S) (m + 1) d) ≃ₗ[Kf] ↥(VS Kf m vec d))

def TY (c : Kf) : ↥(VS Kf m vec d) →ₗ[Kf] Module.Dual Kf ↥(VS Kf m vec d) where
  toFun y := c • ((fockL ((thK.symm y : ↥(Pol Kf (ι := S) (m + 1) d)) :
      MvPolynomial (S × Fin (m + 1)) Kf)).comp
    ((Pol Kf (ι := S) (m + 1) d).subtype.comp thK.symm.toLinearMap))
  map_add' y y' := by
    ext u
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.add_apply, fockL, LinearMap.coe_mk,
      AddHom.coe_mk, map_add, Submodule.coe_add, smul_eq_mul]
    rw [fockR_add_right, mul_add]
  map_smul' a y := by
    ext u
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, fockL, LinearMap.coe_mk, AddHom.coe_mk, map_smul,
      Submodule.coe_smul, smul_eq_mul, RingHom.id_apply]
    rw [tsact_smul_right]
    ring

theorem TY_apply (c : Kf) (P Q : ↥(Pol Kf (ι := S) (m + 1) d)) :
    TY thK c (thK Q) (thK P) = c * fockR (P : MvPolynomial (S × Fin (m + 1)) Kf)
      (Q : MvPolynomial (S × Fin (m + 1)) Kf) := by
  simp [TY, fockL]

theorem int_pair (p κ : ℕ) (hMD : MultDiv O p κ (k := m + 1) d) (G : MvPolynomial (S × Fin (m + 1)) O)
    (hG : G ∈ Pol O (m + 1) d) (E : MvPolynomial (S × Fin (m + 1)) O) :
    ∃ z : O, ((p : Kf) ^ κ / (((∏ s, (d s).factorial : ℕ) : ℕ) : Kf)) *
      fockR (map (algebraMap O Kf) G) (map (algebraMap O Kf) E) = algebraMap O Kf z := by
  by_cases hD : (((∏ s, (d s).factorial : ℕ) : ℕ) : Kf) = 0
  · exact ⟨0, by rw [hD, div_zero, zero_mul, map_zero]⟩
  have hdvd : (((∏ s, (d s).factorial : ℕ) : ℕ) : O) ∣ (p : O) ^ κ * fockR G E := by
    unfold fockR
    rw [Finset.mul_sum]
    apply Finset.dvd_sum
    intro α hα
    obtain ⟨q, hq⟩ := hMD α (mem_Pol.1 hG α hα)
    have hq' : (p : O) ^ κ * ((∏ k ∈ α.support, (α k).factorial : ℕ) : O) =
        (((∏ s, (d s).factorial : ℕ) : ℕ) : O) * q := hq
    exact ⟨AddMonoidAlgebra.coeff G α * AddMonoidAlgebra.coeff E α * q, by linear_combination (AddMonoidAlgebra.coeff G α * AddMonoidAlgebra.coeff E α) * hq'⟩
  obtain ⟨z, hz⟩ := hdvd
  refine ⟨z, ?_⟩
  rw [fockR_map, div_mul_eq_mul_div, div_eq_iff hD]
  have := congrArg (algebraMap O Kf) hz
  simp only [map_mul, map_pow, map_natCast] at this
  rw [this]
  ring

theorem sandwich (hm : 1 ≤ m)
    (hthK : ∀ P, ((thK P : ↥(VS Kf m vec d)) : MvPolynomial (S × (Fin (m + 1) × Fin (m + 1))) Kf) =
      Th0 Kf m vec (P : MvPolynomial (S × Fin (m + 1)) Kf))
    (p κ : ℕ) (hMD : MultDiv O p κ (k := m + 1) d)
    (M : S → Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (hM : ∀ s, IsUnit (M s).det)
    (u y : ↥(VS Kf m vec d))
    (hu : (u : MvPolynomial (S × (Fin (m + 1) × Fin (m + 1))) Kf) ∈ LatM O vec d M)
    (hy : (y : MvPolynomial (S × (Fin (m + 1) × Fin (m + 1))) Kf) ∈ LatM O vec d (fun s => ((M s)⁻¹).transpose)) :
    TY thK ((p : Kf) ^ κ / (((∏ s, (d s).factorial : ℕ) : ℕ) : Kf)) y u ∈ Set.range (algebraMap O Kf) := by
  have hMt : ∀ s, IsUnit (((M s)⁻¹).transpose).det := by
    intro s
    rw [Matrix.det_transpose, Matrix.det_nonsing_inv]
    exact (hM s).ringInverse
  obtain ⟨G, hG, hu'⟩ := (mem_tens_nabla O Kf m hm vec d M hM _).1 hu
  obtain ⟨G', hG', hy'⟩ := (mem_tens_nabla O Kf m hm vec d _ hMt _).1 hy
  let P : ↥(Pol Kf (ι := S) (m + 1) d) :=
    ⟨Lin (fun s => Aa (vec s) (M s)⁻¹) (map (algebraMap O Kf) G), Lin_Pol _ _ (map_Pol _ G hG)⟩
  let Q : ↥(Pol Kf (ι := S) (m + 1) d) :=
    ⟨Lin (fun s => Aa (vec s) (((M s)⁻¹).transpose)⁻¹) (map (algebraMap O Kf) G'), Lin_Pol _ _ (map_Pol _ G' hG')⟩
  have eu : u = thK P := Subtype.ext (by rw [hthK, hu'])
  have ey : y = thK Q := Subtype.ext (by rw [hthK, hy'])
  rw [eu, ey, TY_apply]
  show _ * fockR (Lin _ _) (Lin _ _) ∈ _
  rw [fockR_Lin_dual _ _ (fun s => Aa_dual (vec s) (M s) (hM s))]
  obtain ⟨z, hz⟩ := int_pair (Kf := Kf) p κ hMD G hG G'
  exact ⟨z, hz.symm⟩

end Pair

end Formalism.MainNotions.ColumnSystems.Pf.TF
end
end

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.ColumnSystems.Pf.TF

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility
open Formalism.MainNotions.G.LatticeSystems (la_tw lb_D la_tw_det lb_D_det H0_eq_twisted_nabla la_indep)
open Formalism.L2.G.Model (Lin Th0 Aa Lin_comp Lin_one Lin_Pol Lin_smul Th0_inj mem_tens_nabla mem_tens_dw map_Pol mem_Pol VS
  letterWt_anti tensor_lattice_twist_eq edgeLat_of la_tw_mul la_tw_transpose la_tw_inv dE invT_mul_D dual_edgeBasis w_ne p_eq
  pQ_ne kapR kapR_alg lift_eq Bm Bm_eq Mx Mx_det Avec pol_iff thF)
open Formalism.L2.G.Model.TS

section

variable {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
  [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O} {m : ℕ} {TT : Finset (Fin n')} {aT bT : Fin n' → ℕ}

abbrev vecH (TT : Finset (Fin n')) : TT × Bool → Bool := fun x => x.2

theorem HHL_iff (hS : HidaSetting p n' W Qq O Kf ι σ j w) (ℓ : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (hℓ : IsUnit ℓ.det)
    (u : ↥(VHH (m := m) Kf TT aT bT)) :
    u ∈ HHL (O := O) ι σ TT aT bT (colSpan W ℓ) ↔
      (u : MvPolynomial ((TT × Bool) × (Fin (m + 1) × Fin (m + 1))) Kf) ∈
        LatM O (vecH TT) (hhDegs TT aT bT) (fun x => la_tw ι σ x.1.val.val ℓ) := by
  have e := tensor_lattice_twist_eq hS m (vecH TT) (hhDegs TT aT bT) (fun x => x.1.val) ℓ hℓ
  unfold LatM
  rw [← e]
  rfl

theorem HHLe_iff (hS : HidaSetting p n' W Qq O Kf ι σ j w) (r : ℕ) (e : Edge W Qq (m + 1))
    (b : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (hb : IsEdgeBasis p r e b) (u : ↥(VHH (m := m) Kf TT aT bT)) :
    u ∈ HHLe p ι σ w TT aT bT e ↔
      (u : MvPolynomial ((TT × Bool) × (Fin (m + 1) × Fin (m + 1))) Kf) ∈
        LatM O (vecH TT) (hhDegs TT aT bT) (fun x => la_tw ι σ x.1.val.val b * lb_D (m + 1) r (algebraMap O Kf w)) := by
  have := hS.frac_O
  have e1 : (fun x : TT × Bool => H0 O m (letterWt m (hhDegs TT aT bT x) (vecH TT x)) (LeAt p ι σ w x.1.val.val e)) =
      fun x => nablaLTw O Kf m (letterWt m (hhDegs TT aT bT x) (vecH TT x))
        (la_tw ι σ x.1.val.val b * lb_D (m + 1) r (algebraMap O Kf w)) := by
    funext x
    rw [(edgeLat_of hS m r e b hb).2.1, H0_eq_twisted_nabla (la_indep (IsFractionRing.injective O Kf)) _ _ (letterWt_anti _ _ _) _
      (by rw [Matrix.det_mul]; exact (la_tw_det _ _ _ _ hb.1).mul (lb_D_det _ _ _ (w_ne hS)))]
  unfold LatM
  rw [← e1]
  rfl

theorem la_tw_invT (s : ℕ) (b : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (hb : IsUnit b.det) :
    la_tw ι σ s ((b⁻¹).transpose) = ((la_tw ι σ s b)⁻¹).transpose := by
  rw [la_tw_transpose, la_tw_inv _ _ hb]

theorem la_tw_dE (s r : ℕ) : la_tw ι σ s (dE (m + 1) r ((p : ℕ) : Qq)) = dE (m + 1) r ((p : ℕ) : Kf) := by
  ext a c
  simp only [la_tw, dE, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem dualM (hS : HidaSetting p n' W Qq O Kf ι σ j w) (s r : ℕ) (b : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq)
    (hb : IsUnit b.det) :
    la_tw ι σ s ((b⁻¹).transpose * dE (m + 1) r ((p : ℕ) : Qq)) * lb_D (m + 1) r (algebraMap O Kf w) =
      ((la_tw ι σ s b * lb_D (m + 1) r (algebraMap O Kf w))⁻¹).transpose := by
  have hω := w_ne hS
  have hp : ((p : ℕ) : Kf) = (algebraMap O Kf w) ^ 2 := by rw [← map_pow, hS.w_sq, map_natCast]
  rw [la_tw_mul, la_tw_invT s b hb, la_tw_dE, Matrix.mul_inv_rev, Matrix.transpose_mul, mul_assoc]
  congr 1
  simp only [dE, lb_D, Matrix.diagonal_mul_diagonal, Matrix.inv_diagonal, Matrix.diagonal_transpose]
  congr 1
  funext a
  have hu : IsUnit (fun a : Fin (m + 1) => if a.val < r then (algebraMap O Kf w)⁻¹ else (1 : Kf)) := by
    rw [Pi.isUnit_iff]
    intro a
    split_ifs
    · exact isUnit_iff_ne_zero.mpr (inv_ne_zero hω)
    · exact isUnit_one
  have hinv := congrFun (Ring.inverse_mul_cancel _ hu) a
  rw [Pi.mul_apply, Pi.one_apply] at hinv
  rw [eq_inv_of_mul_eq_one_left hinv]
  split_ifs with h
  · rw [inv_inv, hp]; field_simp
  · simp

variable (thK : ↥(Pol Kf (ι := TT × Bool) (m + 1) (hhDegs TT aT bT)) ≃ₗ[Kf] ↥(VHH (m := m) Kf TT aT bT))

def XiH (c : Kf) : ↥(VHH (m := m) Kf TT aT bT) →ₗ[Kf] Module.Dual Kf ↥(VHH (m := m) Kf TT aT bT) :=
  TY (vec := vecH TT) (d := hhDegs TT aT bT) thK c

theorem XiH_apply (c : Kf) (P Q : ↥(Pol Kf (ι := TT × Bool) (m + 1) (hhDegs TT aT bT))) :
    XiH thK c (thK Q) (thK P) = c * fockR (P : MvPolynomial ((TT × Bool) × Fin (m + 1)) Kf)
      (Q : MvPolynomial ((TT × Bool) × Fin (m + 1)) Kf) :=
  TY_apply (vec := vecH TT) (d := hhDegs TT aT bT) thK c P Q

abbrev zK (Kf : Type) [Field Kf] (p κ : ℕ) (TT : Finset (Fin n')) (aT bT : Fin n' → ℕ) : Kf :=
  (p : Kf) ^ κ / (((∏ x : TT × Bool, (hhDegs TT aT bT x).factorial : ℕ) : ℕ) : Kf)

theorem FD_edge (hS : HidaSetting p n' W Qq O Kf ι σ j w) (hm : 1 ≤ m)
    (hthK : ∀ P, ((thK P : ↥(VHH (m := m) Kf TT aT bT)) : MvPolynomial ((TT × Bool) × (Fin (m + 1) × Fin (m + 1))) Kf) =
      Th0 Kf m (vecH TT) (P : MvPolynomial ((TT × Bool) × Fin (m + 1)) Kf))
    (κ : ℕ) (hMD : MultDiv O p κ (k := m + 1) (hhDegs TT aT bT)) (r : ℕ) (e : Edge W Qq (m + 1))
    (b : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (hb : IsEdgeBasis p r e b) (c : Kf)
    (y : ↥(VHH (m := m) Kf TT aT bT))
    (hy : y ∈ scale c (ReHH p ι σ w TT aT bT e.dual)) :
    XiH thK (zK Kf p κ TT aT bT) y ∈ scale c (ReHH' p ι σ w TT aT bT e) := by
  obtain ⟨y1, hy1, rfl⟩ := mem_scale.1 hy
  obtain ⟨y0, hy0, rfl⟩ := mem_scale.1 hy1
  refine mem_scale.2 ⟨_, mem_scale.2 ⟨XiH thK (zK Kf p κ TT aT bT) y0, ?_, rfl⟩, ?_⟩
  · intro u hu
    refine sandwich (vec := vecH TT) (d := hhDegs TT aT bT) thK hm hthK p κ hMD
      (fun x => la_tw ι σ x.1.val.val b * lb_D (m + 1) r (algebraMap O Kf w))
      (fun x => by rw [Matrix.det_mul]; exact (la_tw_det _ _ _ _ hb.1).mul (lb_D_det _ _ _ (w_ne hS))) u y0
      ((HHLe_iff hS r e b hb u).1 hu) ?_
    have h1 := (HHLe_iff hS r e.dual _ (dual_edgeBasis p r (pQ_ne hS) e b hb) y0).1 hy0
    have e1 : (fun x : TT × Bool => la_tw ι σ x.1.val.val ((b⁻¹).transpose * dE (m + 1) r ((p : ℕ) : Qq)) *
        lb_D (m + 1) r (algebraMap O Kf w)) =
        fun x => ((la_tw ι σ x.1.val.val b * lb_D (m + 1) r (algebraMap O Kf w))⁻¹).transpose :=
      funext fun x => dualM hS x.1.val.val r b hb.1
    rw [e1] at h1
    exact h1
  · rw [map_smul, map_smul]

theorem FD_HL (hS : HidaSetting p n' W Qq O Kf ι σ j w) (hm : 1 ≤ m)
    (hthK : ∀ P, ((thK P : ↥(VHH (m := m) Kf TT aT bT)) : MvPolynomial ((TT × Bool) × (Fin (m + 1) × Fin (m + 1))) Kf) =
      Th0 Kf m (vecH TT) (P : MvPolynomial ((TT × Bool) × Fin (m + 1)) Kf))
    (κ : ℕ) (hMD : MultDiv O p κ (k := m + 1) (hhDegs TT aT bT))
    (ℓ : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (hℓ : IsUnit ℓ.det) (c : Kf)
    (y : ↥(VHH (m := m) Kf TT aT bT))
    (hy : y ∈ scale c (HHL (O := O) ι σ TT aT bT (colSpan W ((ℓ⁻¹).transpose)))) :
    XiH thK (zK Kf p κ TT aT bT) y ∈ scale c (dualLat O Kf (HHL (O := O) ι σ TT aT bT (colSpan W ℓ))) := by
  obtain ⟨y0, hy0, rfl⟩ := mem_scale.1 hy
  refine mem_scale.2 ⟨XiH thK (zK Kf p κ TT aT bT) y0, ?_, by rw [map_smul]⟩
  intro u hu
  refine sandwich (vec := vecH TT) (d := hhDegs TT aT bT) thK hm hthK p κ hMD (fun x => la_tw ι σ x.1.val.val ℓ)
    (fun x => la_tw_det _ _ _ _ hℓ) u y0 ((HHL_iff hS ℓ hℓ u).1 hu) ?_
  have hℓt : IsUnit ((ℓ⁻¹).transpose).det := Formalism.L2.G.Model.det_invT ℓ hℓ
  have h1 := (HHL_iff hS _ hℓt y0).1 hy0
  have e1 : (fun x : TT × Bool => la_tw ι σ x.1.val.val ((ℓ⁻¹).transpose)) =
      fun x => ((la_tw ι σ x.1.val.val ℓ)⁻¹).transpose :=
    funext fun x => la_tw_invT x.1.val.val ℓ hℓ
  rw [e1] at h1
  exact h1

end

end Formalism.MainNotions.ColumnSystems.Pf.TF
end
end

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.ColumnSystems.Pf.TF

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility
open Formalism.MainNotions.G.LatticeSystems (la_tw lb_D la_tw_det lb_D_det H0_eq_twisted_nabla la_indep)
open Formalism.L2.G.Model (Lin Th0 Aa Lin_comp Lin_one Lin_Pol Lin_smul Th0_inj mem_tens_nabla mem_tens_dw map_Pol mem_Pol VS
  letterWt_anti tensor_lattice_twist_eq tens_Le edgeLat_of la_tw_mul la_tw_transpose la_tw_inv dE invT_mul_D dual_edgeBasis w_ne p_eq
  pQ_ne kapR kapR_alg lift_eq Bm Bm_eq Mx Mx_det Avec pol_iff thF gen_equiv gen_A gen_R mem_scale2 edgePlane)
open Formalism.L2.G.Model.TS

section

variable {p n' : ℕ} [Fact p.Prime] {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
  [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {jO : W →+* O} {w : O}

theorem Avec_eq {m : ℕ} (TT : Finset (Fin n')) (aT bT : Fin n' → ℕ) :
    (Avec (vecH TT) (hhDegs TT aT bT) : ℤ) = AHH TT aT bT := by
  unfold Avec AHH
  push_cast
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, vecH, hhDegs, if_true, Bool.false_eq_true, if_false, add_zero]
  exact Finset.sum_coe_sort TT (fun s => (hhDeg aT bT s true : ℤ))

theorem flatTheta (hS : HidaSetting p n' W Qq O Kf ι σ jO w) (φ : WF p n' ≃+* W) (hφ : IsWittIdent σ φ) (m : ℕ)
    (TT : Finset (Fin n')) (aT bT : Fin n' → ℕ) (hm : 1 ≤ m) (h : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq)
    (hh : IsUnit h.det) :
    ∃ Θ : ↥((Pol (KK O) (ι := TT × Bool) (m + 1) (hhDegs TT aT bT)).restrictScalars O) ≃ₗ[O]
        ↥(VHH (m := m) Kf TT aT bT),
      IsFlatTheta ι σ jO w φ TT aT bT h Θ ∧
      ∀ F, ((Θ F : ↥(VHH (m := m) Kf TT aT bT)) : MvPolynomial ((TT × Bool) × (Fin (m + 1) × Fin (m + 1))) Kf) =
        thF hS m (vecH TT) (fun x => la_tw ι σ x.1.val.val h) F.1 := by
  letI : Algebra (WF p n') O := algOfIdent jO φ
  have hw := w_ne hS
  obtain ⟨Θ0, hΘ0⟩ := gen_equiv hS m hm (fun x : TT × Bool => x.2) (Formalism.MainNotions.ColumnSystems.hhDegs TT aT bT)
    (fun x => la_tw ι σ x.1.val.val h) (fun x => la_tw_det _ _ _ _ hh)
  have hV : VS Kf m (fun x : TT × Bool => x.2) (Formalism.MainNotions.ColumnSystems.hhDegs TT aT bT) = VHH (m := m) Kf TT aT bT := rfl
  let Θ : ↥((Pol (KK O) (ι := TT × Bool) (m + 1) (Formalism.MainNotions.ColumnSystems.hhDegs TT aT bT)).restrictScalars O) ≃ₗ[O]
      ↥(VHH (m := m) Kf TT aT bT) := Θ0.trans ((LinearEquiv.ofEq _ _ hV).restrictScalars O)
  have hΘ : ∀ F, ((Θ F : ↥(VHH (m := m) Kf TT aT bT)) :
      MvPolynomial ((TT × Bool) × (Fin (m + 1) × Fin (m + 1))) Kf) =
      thF hS m (fun x : TT × Bool => x.2) (fun x => la_tw ι σ x.1.val.val h) F.1 := fun F => hΘ0 F
  refine ⟨Θ, ⟨?_, ?_, ?_⟩, hΘ⟩
  · intro F
    rw [gen_A hS m hm (fun x : TT × Bool => x.2) (Formalism.MainNotions.ColumnSystems.hhDegs TT aT bT)
      (fun x => la_tw ι σ x.1.val.val h) (fun x => la_tw_det _ _ _ _ hh) F.1 F.2, ← hΘ F,
      ← tensor_lattice_twist_eq hS m (fun x : TT × Bool => x.2) (Formalism.MainNotions.ColumnSystems.hhDegs TT aT bT) (fun x => x.1.val) h hh]
    rfl
  · intro g hg e he F i
    have h1 : InWjRg p n' O w 1 (Formalism.MainNotions.ColumnSystems.hhLetters TT) g F.1 i ↔
        ∃ y ∈ tensorLat O Kf (fun s : TT × Bool => nablaLTw O Kf m
            (letterWt m (Formalism.MainNotions.ColumnSystems.hhDegs TT aT bT s) s.2) (Mx ι σ w φ 1 (fun x : TT × Bool => x.1.val) h g s)),
          thF hS m (fun x : TT × Bool => x.2) (fun x => la_tw ι σ x.1.val.val h) F.1 =
            (algebraMap O Kf w ^ ((i : ℤ) -
              (Avec (fun x : TT × Bool => x.2) (Formalism.MainNotions.ColumnSystems.hhDegs TT aT bT) : ℤ))) • y :=
      gen_R hS φ hφ m hm 1 (Formalism.MainNotions.ColumnSystems.hhLetters TT) (fun x => x.1.val) (fun _ => rfl)
        (Formalism.MainNotions.ColumnSystems.hhDegs TT aT bT) h hh g hg F.1 F.2 i
    rw [h1, ← hΘ F, ← tens_Le hS φ m 1 (fun x : TT × Bool => x.2) (Formalism.MainNotions.ColumnSystems.hhDegs TT aT bT) (fun x => x.1.val)
      h hh g hg e he]
    have hA : (Avec (fun x : TT × Bool => x.2) (Formalism.MainNotions.ColumnSystems.hhDegs TT aT bT) : ℤ) = AHH TT aT bT :=
      Avec_eq (m := m) TT aT bT
    have h2 := mem_scale2 (O := O) (VHH (m := m) Kf TT aT bT)
      (HHten O TT aT bT fun s => LeAt p ι σ w s.val e) (algebraMap O Kf w ^ (i : ℤ))
      (algebraMap O Kf w ^ (-AHH TT aT bT)) (zpow_ne_zero _ hw) (zpow_ne_zero _ hw) (Θ F)
    have e1 : algebraMap O Kf w ^ (i : ℤ) * algebraMap O Kf w ^ (-AHH TT aT bT) = algebraMap O Kf w ^
        ((i : ℤ) - (Avec (fun x : TT × Bool => x.2) (Formalism.MainNotions.ColumnSystems.hhDegs TT aT bT) : ℤ)) := by
      rw [← zpow_add₀ hw, ← sub_eq_add_neg, ← hA]
    rw [e1] at h2
    exact h2.symm
  · intro e he hsrc
    exact (edgePlane p n' W Qq O Kf ι σ jO w hS φ hφ m 1 h hh).1 e he hsrc

theorem matQ_one (φ : WF p n' ≃+* W) (k : ℕ) : matQ (Qq := Qq) φ (1 : Matrix (Fin k) (Fin k) (WF p n')) = 1 := by
  ext a b
  simp only [matQ, Matrix.one_apply]
  split_ifs <;> simp

theorem mul_matQ_one (φ : WF p n' ≃+* W) {k : ℕ} (h : Matrix (Fin k) (Fin k) Qq) :
    h * ((matQ φ (1 : Matrix (Fin k) (Fin k) (WF p n')))⁻¹).transpose = h := by
  rw [matQ_one]
  simp

theorem isGLW_one (k : ℕ) : IsGLW (1 : Matrix (Fin k) (Fin k) (WF p n')) := by
  simp [IsGLW]

theorem Aa_dual' {K : Type} [Field K] {m : ℕ} (vec : Bool) (M : Matrix (Fin (m + 1)) (Fin (m + 1)) K)
    (hM : IsUnit M.det) : Aa vec ((M⁻¹).transpose) * (Aa vec M).transpose = 1 := by
  cases vec
  · simp [Aa, Matrix.transpose_nonsing_inv, Matrix.nonsing_inv_nonsing_inv _ hM, Matrix.mul_nonsing_inv _ hM]
  · simp [Aa, ← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hM]

theorem lift_Pol (hS : HidaSetting p n' W Qq O Kf ι σ jO w) (φ : WF p n' ≃+* W) (hφ : IsWittIdent σ φ) (m : ℕ)
    (TT : Finset (Fin n')) (aT bT : Fin n' → ℕ) (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n')) (hg : IsGLW g)
    (F : MvPolynomial ((TT × Bool) × Fin (m + 1)) (KK O)) (hF : F ∈ Pol (KK O) (m + 1) (hhDegs TT aT bT)) :
    letI : Algebra (WF p n') O := algOfIdent jO φ
    liftSubst p n' O w 1 (hhLetters TT) g F ∈ Pol (KK O) (m + 1) (hhDegs TT aT bT) := by
  letI : Algebra (WF p n') O := algOfIdent jO φ
  rw [pol_iff hS, lift_eq hS φ hφ 1 (hhLetters TT) (fun x => x.1.val) (fun _ => rfl) g hg F]
  exact Lin_Pol _ _ ((pol_iff hS _ _ _).1 hF)

theorem lift_one (hS : HidaSetting p n' W Qq O Kf ι σ jO w) (φ : WF p n' ≃+* W) (hφ : IsWittIdent σ φ) (m : ℕ)
    (TT : Finset (Fin n')) (aT bT : Fin n' → ℕ) (h : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (hh : IsUnit h.det)
    (F : MvPolynomial ((TT × Bool) × Fin (m + 1)) (KK O)) (hF : F ∈ Pol (KK O) (m + 1) (hhDegs TT aT bT)) :
    letI : Algebra (WF p n') O := algOfIdent jO φ
    map (kapR hS) (liftSubst p n' O w 1 (hhLetters TT) (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n')) F) =
      (algebraMap O Kf w ^ Avec (vecH TT) (hhDegs TT aT bT)) •
        Lin (fun x : TT × Bool => Aa x.2 (la_tw ι σ x.1.val.val h * lb_D (m + 1) 1 (algebraMap O Kf w)))
          (Lin (fun x : TT × Bool => Aa x.2 (la_tw ι σ x.1.val.val h)⁻¹) (map (kapR hS) F)) := by
  letI : Algebra (WF p n') O := algOfIdent jO φ
  have hw := w_ne hS
  set c := algebraMap O Kf w with hc
  have hF' := (pol_iff hS _ _ _).1 hF
  rw [lift_eq hS φ hφ 1 (hhLetters TT) (fun x => x.1.val) (fun _ => rfl) 1 (isGLW_one _) F]
  have hB : Bm ι σ w φ 1 (hhLetters TT).vec (fun x : TT × Bool => x.1.val) (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n')) =
      fun x => (if (hhLetters TT).vec x then c else 1) •
      (Aa ((hhLetters TT).vec x) (la_tw ι σ x.1.val.val h)⁻¹ *
        Aa ((hhLetters TT).vec x) (Mx ι σ w φ 1 (fun x : TT × Bool => x.1.val) h 1 x)) :=
    funext fun x => Bm_eq hw φ 1 (hhLetters TT).vec (fun x : TT × Bool => x.1.val) h hh 1 (isGLW_one _) x
  rw [hB, Lin_smul _ _ _ hF', Lin_comp]
  have hprod : ∏ x : TT × Bool, (if (hhLetters TT).vec x then c else 1) ^ hhDegs TT aT bT x =
      c ^ Avec (vecH TT) (hhDegs TT aT bT) := by
    unfold Avec
    rw [← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_congr rfl
    intro x _
    show (if x.2 = true then c else 1) ^ _ = c ^ (if x.2 = true then _ else 0)
    split_ifs <;> simp
  rw [hprod]
  have hfun : (fun x : TT × Bool => Aa ((hhLetters TT).vec x) (la_tw ι σ x.1.val.val h)⁻¹ *
        Aa ((hhLetters TT).vec x) (Mx ι σ w φ 1 (fun x : TT × Bool => x.1.val) h 1 x)) =
      fun x : TT × Bool => Aa x.2 (la_tw ι σ x.1.val.val h)⁻¹ * Aa x.2 (la_tw ι σ x.1.val.val h * lb_D (m + 1) 1 c) := by
    funext x
    unfold Mx
    rw [mul_matQ_one]
    rfl
  rw [hfun]

end

end Formalism.MainNotions.ColumnSystems.Pf.TF
end
end

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.ColumnSystems.Pf.TF

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility
open Formalism.MainNotions.G.LatticeSystems (la_tw lb_D la_tw_det lb_D_det H0_eq_twisted_nabla la_indep)
open Formalism.L2.G.Model (Lin Th0 Aa Lin_comp Lin_one Lin_Pol Lin_smul Th0_inj mem_tens_nabla mem_tens_dw map_Pol mem_Pol VS
  letterWt_anti tensor_lattice_twist_eq tens_Le edgeLat_of la_tw_mul la_tw_transpose la_tw_inv dE invT_mul_D dual_edgeBasis w_ne p_eq
  pQ_ne kapR kapR_alg lift_eq Bm Bm_eq Mx Mx_det Avec pol_iff thF edgeBasis dual_edge latDual_colSpan)
open Formalism.L2.G.Model.TS

section

variable {p n' : ℕ} [Fact p.Prime] {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
  [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {jO : W →+* O} {w : O} {m : ℕ} {TT : Finset (Fin n')} {aT bT : Fin n' → ℕ}

variable (thK : ↥(Pol Kf (ι := TT × Bool) (m + 1) (hhDegs TT aT bT)) ≃ₗ[Kf] ↥(VHH (m := m) Kf TT aT bT))

theorem Xi_CC (hS : HidaSetting p n' W Qq O Kf ι σ jO w) (hm : 1 ≤ m)
    (hthK : ∀ P, ((thK P : ↥(VHH (m := m) Kf TT aT bT)) : MvPolynomial ((TT × Bool) × (Fin (m + 1) × Fin (m + 1))) Kf) =
      Th0 Kf m (vecH TT) (P : MvPolynomial ((TT × Bool) × Fin (m + 1)) Kf))
    (κ : ℕ) (hMD : MultDiv O p κ (k := m + 1) (hhDegs TT aT bT)) (e : Edge W Qq (m + 1)) (he : IsEdge p n' 1 e)
    (t c : ℕ) (v : ↥(VHH (m := m) Kf TT aT bT)) (hv : v ∈ CCe p ι σ w TT aT bT t c e.dual) :
    XiH thK (zK Kf p κ TT aT bT) v ∈ CCe' p ι σ w TT aT bT t c e := by
  have hs1 : ∀ M : Submodule O (VHH (m := m) Kf TT aT bT), scale (1 : Kf) M = M := by
    intro M
    ext x
    simp [scale, Submodule.mem_map]
  have hs1' : ∀ M : Submodule O (Module.Dual Kf (VHH (m := m) Kf TT aT bT)), scale (1 : Kf) M = M := by
    intro M
    ext x
    simp [scale, Submodule.mem_map]
  simp only [CCe, CCe', Submodule.mem_inf, Submodule.mem_iInf] at hv ⊢
  obtain ⟨⟨hv1, hv2⟩, hv3⟩ := hv
  obtain ⟨g, hg⟩ := edgeBasis hS m 1 e he
  have hpQ : ((p : ℕ) : Qq) ≠ 0 := by
    haveI := hS.frac_alt
    intro h0
    apply hS.p_unif.ne_zero
    apply IsFractionRing.injective W Qq
    rw [map_natCast, h0, map_zero]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have hℓu : IsUnit (g * Matrix.diagonal fun c : Fin (m + 1) =>
        if c.val < 1 then ((p : Qq))⁻¹ else 1).det := by
      rw [Matrix.det_mul, Matrix.det_diagonal]
      refine hg.1.mul (isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun c _ => ?_))
      split_ifs
      · exact inv_ne_zero hpQ
      · exact one_ne_zero
    have htgt := hg.2.2
    have hsrc : e.dual.src = colSpan W ((g * Matrix.diagonal fun c : Fin (m + 1) =>
        if c.val < 1 then ((p : Qq))⁻¹ else 1)⁻¹).transpose := by
      show latDual e.tgt = _
      rw [htgt, latDual_colSpan _ hℓu]
    rw [hsrc] at hv1
    have h1 := FD_HL thK hS hm hthK κ hMD _ hℓu _ v hv1
    rwa [← htgt] at h1
  · have h1 := FD_edge thK hS hm hthK κ hMD 1 e g hg 1 v (by rw [hs1]; exact hv2)
    rwa [hs1'] at h1
  · intro e'' he''
    have hd := dual_edge hS m 1 e'' he''.1
    have hsrc : e''.dual.src = e.dual.src := by
      show latDual e''.tgt = latDual e.tgt
      rw [he''.2.1]
    have hne : e''.dual ≠ e.dual := fun heq =>
      he''.2.2 (by rw [← hd.2, heq, (dual_edge hS m 1 e he).2])
    have hv3' := hv3 e''.dual ⟨hd.1, hsrc, hne⟩
    obtain ⟨b, hb⟩ := edgeBasis hS m 1 e'' he''.1
    exact FD_edge thK hS hm hthK κ hMD 1 e'' b hb _ v hv3'

theorem kapR_zTen (hS : HidaSetting p n' W Qq O Kf ι σ jO w) :
    kapR hS (zTen (KK O) p m TT aT bT) = zK Kf p (kapZ p m TT aT bT) TT aT bT := by
  simp [zTen, zK, map_div₀, map_pow, map_natCast, map_prod, Nat.cast_prod]

theorem pairing (hS : HidaSetting p n' W Qq O Kf ι σ jO w) (φ : WF p n' ≃+* W) (hφ : IsWittIdent σ φ)
    (hthK : ∀ P, ((thK P : ↥(VHH (m := m) Kf TT aT bT)) : MvPolynomial ((TT × Bool) × (Fin (m + 1) × Fin (m + 1))) Kf) =
      Th0 Kf m (vecH TT) (P : MvPolynomial ((TT × Bool) × Fin (m + 1)) Kf))
    (b : Matrix (Fin (m + 1)) (Fin (m + 1)) Qq) (hb : IsUnit b.det)
    (hb' : IsUnit ((b⁻¹).transpose * dE (m + 1) 1 ((p : ℕ) : Qq)).det)
    (Θ Θ' : ↥((Pol (KK O) (ι := TT × Bool) (m + 1) (hhDegs TT aT bT)).restrictScalars O) ≃ₗ[O]
        ↥(VHH (m := m) Kf TT aT bT))
    (hΘ : ∀ F, ((Θ F : ↥(VHH (m := m) Kf TT aT bT)) : MvPolynomial ((TT × Bool) × (Fin (m + 1) × Fin (m + 1))) Kf) =
        thF hS m (vecH TT) (fun x => la_tw ι σ x.1.val.val b) F.1)
    (hΘ' : ∀ F, ((Θ' F : ↥(VHH (m := m) Kf TT aT bT)) : MvPolynomial ((TT × Bool) × (Fin (m + 1) × Fin (m + 1))) Kf) =
        thF hS m (vecH TT) (fun x => la_tw ι σ x.1.val.val ((b⁻¹).transpose * dE (m + 1) 1 ((p : ℕ) : Qq))) F.1)
    (F F' : ↥((Pol (KK O) (ι := TT × Bool) (m + 1) (hhDegs TT aT bT)).restrictScalars O)) (y : O) :
    letI : Algebra (WF p n') O := algOfIdent jO φ
    zTen (KK O) p m TT aT bT *
        fock (liftSubst p n' O w 1 (hhLetters TT) (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n'))
            (F : MvPolynomial ((TT × Bool) × Fin (m + 1)) (KK O)))
          (liftSubst p n' O w 1 (hhLetters TT) (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) (WF p n'))
            (F' : MvPolynomial ((TT × Bool) × Fin (m + 1)) (KK O))) = algebraMap O (KK O) y →
    beHH (m := m) p TT aT bT (Θ F) (XiH thK (zK Kf p (kapZ p m TT aT bT) TT aT bT) (Θ' F')) = algebraMap O Kf y := by
  letI : Algebra (WF p n') O := algOfIdent jO φ
  intro hy
  have hw := w_ne hS
  set c := algebraMap O Kf w with hc
  have hF0 := (pol_iff hS _ _ _).1 F.2
  have hF0' := (pol_iff hS _ _ _).1 F'.2
  let P : ↥(Pol Kf (ι := TT × Bool) (m + 1) (hhDegs TT aT bT)) :=
    ⟨Lin (fun x : TT × Bool => Aa x.2 (la_tw ι σ x.1.val.val b)⁻¹) (map (kapR hS) F.1), Lin_Pol _ _ hF0⟩
  let Q : ↥(Pol Kf (ι := TT × Bool) (m + 1) (hhDegs TT aT bT)) :=
    ⟨Lin (fun x : TT × Bool => Aa x.2 (la_tw ι σ x.1.val.val ((b⁻¹).transpose * dE (m + 1) 1 ((p : ℕ) : Qq)))⁻¹)
      (map (kapR hS) F'.1), Lin_Pol _ _ hF0'⟩
  have hP : Θ F = thK P := Subtype.ext (by rw [hΘ, hthK]; rfl)
  have hQ : Θ' F' = thK Q := Subtype.ext (by rw [hΘ', hthK]; rfl)
  have hk := congrArg (kapR hS) hy
  rw [map_mul, kapR_alg, kapR_zTen, fock_eq_fockR, ← fockR_map,
    lift_one hS φ hφ m TT aT bT b hb F.1 F.2, lift_one hS φ hφ m TT aT bT _ hb' F'.1 F'.2,
    tsact_smul_left, tsact_smul_right] at hk
  have hdual : ∀ x : TT × Bool,
      Aa x.2 (la_tw ι σ x.1.val.val ((b⁻¹).transpose * dE (m + 1) 1 ((p : ℕ) : Qq)) * lb_D (m + 1) 1 c) *
        (Aa x.2 (la_tw ι σ x.1.val.val b * lb_D (m + 1) 1 c)).transpose = 1 := by
    intro x
    rw [hc, dualM hS x.1.val.val 1 b hb]
    exact Aa_dual' x.2 _ (by rw [Matrix.det_mul]; exact (la_tw_det _ _ _ _ hb).mul (lb_D_det _ _ _ hw))
  rw [fockR_Lin_dual _ _ hdual] at hk
  unfold beHH
  rw [hP, hQ, map_smul, XiH_apply, smul_eq_mul, ← hk]
  have hpA : (p : Kf) ^ AHH TT aT bT = c ^ Avec (vecH TT) (hhDegs TT aT bT) * c ^ Avec (vecH TT) (hhDegs TT aT bT) := by
    rw [← Avec_eq (m := m), zpow_natCast, p_eq hS]
    ring
  rw [hpA]
  show _ = _ * (_ * (_ * fockR P.1 Q.1))
  ring

end

end Formalism.MainNotions.ColumnSystems.Pf.TF

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility TF
open Formalism.L2.G.Model (dE dual_edgeBasis pQ_ne edgeBasis dual_edge Th0)

end Formalism.MainNotions.ColumnSystems.Pf
