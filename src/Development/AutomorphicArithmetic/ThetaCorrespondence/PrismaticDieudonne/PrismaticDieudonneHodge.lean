module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasPeriodIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WindowLiftToFontaineAinfMatrices
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivisibleGroupDatumOfConnectedDualConnected
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrismaticDieudonneHodgeOfHodgeTateDatum

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.TemperedRepresentationTheory.FarguesExactness.FarguesExactOfPrismatic
noncomputable section

open TensorProduct GlobalTheory GlobalTheory.PDivGroup

namespace PositivityTheory.Tls2.Jfarg

theorem exists_factor {O M N : Type} [CommRing O] [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N]
    (f : M →ₗ[O] N) (φ : M →ₗ[O] O) (h : ∀ y, f y = 0 → φ y = 0) (κ : O)
    (hκ : ∀ w, κ • w ∈ LinearMap.range f) : ∃ l : N →ₗ[O] O, ∀ y, κ * φ y = l (f y) := by
  have hle : LinearMap.ker f ≤ LinearMap.ker φ := fun y hy => h y hy
  let g : LinearMap.range f →ₗ[O] O :=
    ((LinearMap.ker f).liftQ φ hle).comp f.quotKerEquivRange.symm.toLinearMap
  let c : N →ₗ[O] LinearMap.range f :=
    LinearMap.codRestrict (LinearMap.range f) (κ • LinearMap.id) (fun w => by simpa using hκ w)
  refine ⟨g.comp c, fun y => ?_⟩
  have hc : c (f y) = ⟨f (κ • y), LinearMap.mem_range_self f _⟩ := Subtype.ext (by simp [c])
  rw [LinearMap.comp_apply, hc]
  show κ * φ y = (LinearMap.ker f).liftQ φ hle
    (f.quotKerEquivRange.symm ⟨f (κ • y), LinearMap.mem_range_self f _⟩)
  rw [LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply,
    map_smul, smul_eq_mul]

theorem primitive {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] {ζ : ℕ → O} (h0 : ζ 0 = 1)
    (h : ∀ n, ζ (n + 1) ^ p = ζ n) (h1 : ζ 1 ≠ 1) (n : ℕ) : IsPrimitiveRoot (ζ n) (p ^ n) := by
  have key : ∀ k m, ζ (m + k) ^ (p ^ k) = ζ m := by
    intro k
    induction k with
    | zero => intro m; simp
    | succ k ih =>
      intro m
      rw [pow_succ', pow_mul, ← Nat.add_assoc, h, ih]
  cases n with
  | zero => simpa [h0] using (IsPrimitiveRoot.one : IsPrimitiveRoot (1 : O) 1)
  | succ m =>
    have hfin : ζ (m + 1) ^ p ^ (m + 1) = 1 := by
      have := key (m + 1) 0
      simpa [h0] using this
    have hnot : ¬ ζ (m + 1) ^ p ^ m = 1 := by
      have := key m 1
      rw [show 1 + m = m + 1 by omega] at this
      rw [this]
      exact h1
    have ho := orderOf_eq_prime_pow hnot hfin
    rw [← ho]
    exact IsPrimitiveRoot.orderOf _

theorem farguesExact_of_hodge (hP : GlobalTheory.Published.PrismaticDieudonneHodge) : GlobalTheory.CompanionTheory.Ar.HT.FarguesExact := by
  intro p _ C _ _ _ v O _ _ _ hv hp hO G ζ h0 h h1 B hB x
  haveI : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  haveI : Fact ¬IsUnit (p : O) := ⟨fun hu => by
    have := hv.one_of_isUnit hu
    rw [map_natCast] at this
    exact hp.ne this⟩
  have hp0 : (p : O) ≠ 0 := fun h => by
    have h5 : algebraMap O C (p : O) = 0 := by rw [h, map_zero]
    rw [map_natCast] at h5
    exact Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero h5
  obtain ⟨ε, hε₁⟩ := ReciprocityTheory.PGsh.exists_eps (p := p) C _ O hv
  have hε : GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.IsPrimitiveSystem ε := GlobalTheory.PrismModel.isPrimitiveSystem_of_one hε₁
  have hS := GlobalTheory.T.hodgeTateSandwich_of_prismaticDieudonne hP p C v O hv ε hε
  have hζ : Function.Bijective fun a : ℤ_[p] => a • muTate O ζ h0 h :=
    smul_muTate_bijective ζ h0 h (primitive h0 h h1)
  obtain ⟨B₀, hB₀, -, -⟩ := GlobalTheory.PointGroup.exists_form hv G _ hζ
  have hk := (GlobalTheory.DetInv.HTKer.ker_hodgeTateLinear p C v O ε hε hS G _ B₀ hv hζ hB₀).1 x
  obtain ⟨-, -, hc⟩ := GlobalTheory.T.pDivGroup_omega_finite_free_and_p_sq_mem_dlog_span p C v O ε hε hv hS G
  have hBB : ∀ (z : O ⊗[ℤ_[p]] G.Tate) (χ : G.dual.Tate),
      (TensorProduct.rid ℤ_[p] O) ((B₀.flip χ).baseChange O z) = B z (1 ⊗ₜ χ) := fun z χ => by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), LinearMap.add_apply, ha, hb]
    | tmul c t =>
      obtain ⟨a, ha, hb⟩ := hB t χ
      have e : B₀ t χ = a := hζ.1 ((hB₀ t χ).symm.trans ha)
      have h4 : (c ⊗ₜ t : O ⊗[ℤ_[p]] G.Tate) = c • (1 ⊗ₜ t) := by rw [smul_tmul', smul_eq_mul, mul_one]
      rw [LinearMap.baseChange_tmul, LinearMap.flip_apply, TensorProduct.rid_tmul, e, h4, map_smul,
        LinearMap.smul_apply, hb, Algebra.smul_def, smul_eq_mul, mul_comm]
  simp only [hBB] at hk
  rw [hk]
  constructor
  · rintro ⟨c, l, hc0, hl⟩ y hy
    have h2 : ∀ z, c * B x z = l (dlogLinear G z) := fun z => by
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => simp only [map_add (f := _), mul_add, ha, hb]
      | tmul d χ =>
        have h5 : (d ⊗ₜ χ : O ⊗[ℤ_[p]] G.dual.Tate) = d • (1 ⊗ₜ χ) := by
          rw [smul_tmul', smul_eq_mul, mul_one]
        rw [dlogLinear_tmul, map_smul, ← hl, h5, map_smul, smul_eq_mul, smul_eq_mul, mul_left_comm]
    have h3 := h2 y
    rw [hy, map_zero] at h3
    exact (mul_eq_zero.1 h3).resolve_left hc0
  · intro hx
    have hle : Submodule.span O (Set.range (dlog G)) ≤ LinearMap.range (dlogLinear G) :=
      Submodule.span_le.2 (by
        rintro _ ⟨χ, rfl⟩
        exact ⟨1 ⊗ₜ χ, by rw [dlogLinear_tmul, one_smul]⟩)
    obtain ⟨l, hl⟩ := exists_factor (dlogLinear G) (B x) hx ((p : O) ^ 2) fun w => hle (hc w)
    exact ⟨(p : O) ^ 2, l, pow_ne_zero _ hp0, fun χ => by rw [hl, dlogLinear_tmul, one_smul]⟩

end PositivityTheory.Tls2.Jfarg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfEqZero
set_option autoImplicit false
noncomputable section
open Polynomial WittVector GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta

namespace GlobalTheory.BRing

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]

theorem frob_congr (x : Ainf p O) : ∃ z, frobenius x = x ^ p + (p : Ainf p O) * z := by
  have h : frobenius x - x ^ p ∈ Ideal.span {(p : Ainf p O)} := by
    rw [← WittVector.ker_constantCoeff, RingHom.mem_ker, map_sub, map_pow,
      WittVector.constantCoeff_apply, WittVector.constantCoeff_apply, coeff_frobenius_charP, sub_self]
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp h
  exact ⟨y, by linear_combination -hy⟩

theorem frob_teich (r : PreTilt O p) :
    frobenius (teichmuller p r : Ainf p O) = teichmuller p (r ^ p) := by
  rw [frobenius_eq_map_frobenius, map_teichmuller, frobenius_def]

theorem frob_nu (ε : PreTilt O p) : frobenius (nu ε) = mu ε := by
  rw [nu, mu, map_sub, map_one, frob_teich, root, frobeniusEquiv_symm_pow_p]

theorem frob_mu (ε : PreTilt O p) : frobenius (mu ε) = mu ε * frobenius (xi ε) := by
  rw [show frobenius (mu ε) = frobenius (xi ε * nu ε) by rw [xi_mul_nu], map_mul, frob_nu,
    mul_comm]

theorem frob_xi (ε : PreTilt O p) : ∃ d, frobenius (xi ε) = p + mu ε * d := by
  have h : frobenius (xi ε) = ∑ i ∈ Finset.range p, (teichmuller p ε : Ainf p O) ^ i := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [xi, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_pow, frob_teich, root, frobeniusEquiv_symm_pow_p]
  have hd : ∀ i : ℕ, mu ε ∣ (teichmuller p ε : Ainf p O) ^ i - 1 := fun i => by
    rw [mu]; simpa using sub_dvd_pow_sub_pow (teichmuller p ε : Ainf p O) 1 i
  choose d hd using hd
  refine ⟨∑ i ∈ Finset.range p, d i, ?_⟩
  rw [h, Finset.mul_sum, ← Finset.sum_congr rfl fun i _ => hd i]
  simp [Finset.sum_sub_distrib]

theorem theta_mu {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) :
    fontaineTheta O p (mu ε) = 0 := by
  rw [mu, map_sub, fontaineTheta_teichmuller, map_one, sub_eq_zero]
  exact hε.zeta_zero

variable (ε : PreTilt O p)

def rel : Ideal (Ainf p O)[X] := Ideal.span {C (p : Ainf p O) * X - C (mu ε), X ^ 2}

abbrev BR : Type := (Ainf p O)[X] ⧸ rel ε

def a : Ainf p O →+* BR ε := (Ideal.Quotient.mk (rel ε)).comp C

def τ : BR ε := Ideal.Quotient.mk (rel ε) X

theorem p_τ : (p : BR ε) * τ ε = a ε (mu ε) := by
  rw [τ, a, RingHom.comp_apply, ← map_natCast (Ideal.Quotient.mk (rel ε)), ← map_mul,
    ← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem, ← map_natCast C]
  exact Ideal.subset_span (Set.mem_insert _ _)

theorem τ_sq : τ ε * τ ε = 0 := by
  rw [τ, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, ← sq]
  exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)

theorem a_natCast (n : ℕ) : a ε n = n := map_natCast _ n

def θ {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) : BR ε →+* O :=
  Ideal.Quotient.lift (rel ε) (eval₂RingHom (fontaineTheta O p) 0) (fun f hf => by
    have h : rel ε ≤ RingHom.ker (eval₂RingHom (fontaineTheta O p) 0) := by
      refine Ideal.span_le.2 ?_
      rintro g (rfl | rfl) <;> simp [theta_mu hε]
    exact (RingHom.mem_ker).1 (h hf))

theorem θ_a {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) (x : Ainf p O) :
    θ hε (a ε x) = fontaineTheta O p x := by
  rw [θ, a, RingHom.comp_apply, Ideal.Quotient.lift_mk]; simp

theorem θ_τ {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) : θ hε (τ ε) = 0 := by
  rw [θ, τ, Ideal.Quotient.lift_mk]; simp

def σ : BR ε →+* BR ε :=
  Ideal.Quotient.lift (rel ε) (eval₂RingHom ((a ε).comp frobenius) (τ ε * a ε (frobenius (xi ε))))
    (fun f hf => by
      have h : rel ε ≤ RingHom.ker (eval₂RingHom ((a ε).comp frobenius)
          (τ ε * a ε (frobenius (xi ε)))) := by
        refine Ideal.span_le.2 ?_
        rintro g (rfl | rfl)
        · simp only [SetLike.mem_coe, RingHom.mem_ker, coe_eval₂RingHom, eval₂_sub, eval₂_mul,
            eval₂_C, eval₂_X, eval₂_natCast, RingHom.comp_apply, map_natCast]
          rw [frob_mu, map_mul, ← p_τ]; ring
        · simp only [SetLike.mem_coe, RingHom.mem_ker, coe_eval₂RingHom, eval₂_X_pow]
          rw [mul_pow, sq (τ ε), τ_sq, zero_mul]
      exact (RingHom.mem_ker).1 (h hf))

theorem σ_a (x : Ainf p O) : σ ε (a ε x) = a ε (frobenius x) := by
  simp [σ, a, Ideal.Quotient.lift_mk]

theorem σ_τ : σ ε (τ ε) = τ ε * a ε (frobenius (xi ε)) := by
  simp [σ, τ, Ideal.Quotient.lift_mk]

abbrev BQ : Type := Localization.Away (p : BR ε)

def s : BQ ε →+* BQ ε :=
  IsLocalization.map (M := Submonoid.powers (p : BR ε)) (T := Submonoid.powers (p : BR ε))
    (BQ ε) (σ ε) (by
      rintro _ ⟨n, rfl⟩
      exact ⟨n, by rw [map_pow, map_natCast]⟩)

theorem s_alg (b : BR ε) : s ε (algebraMap (BR ε) (BQ ε) b) = algebraMap (BR ε) (BQ ε) (σ ε b) :=
  IsLocalization.map_eq _ _

theorem gen (b : BR ε) : ∃ x y, b = a ε x + τ ε * a ε y := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective b
  refine ⟨f.coeff 0, f.divX.coeff 0, ?_⟩
  have h1 := divX_mul_X_add f
  have h2 := divX_mul_X_add f.divX
  have hX : Ideal.Quotient.mk (rel ε) (X ^ 2) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
  conv_lhs => rw [← h1, ← h2]
  simp only [map_add (f := _), map_mul, a, τ, RingHom.comp_apply]
  have : Ideal.Quotient.mk (rel ε) f.divX.divX * Ideal.Quotient.mk (rel ε) X *
      Ideal.Quotient.mk (rel ε) X = 0 := by
    rw [mul_assoc, ← map_mul, ← sq, hX, mul_zero]
  linear_combination this

section Faithful

variable {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C NNReal} [Algebra O C]
  {ε : PreTilt O p}

theorem prim (hε : IsPrimitiveSystem ε) : IsPrimitiveRoot (root ε).untilt p := by
  simpa [zeta] using hε 1

theorem eps_ne (hv : v.Integers O) (hε : IsPrimitiveSystem ε) : ε - 1 ≠ 0 := by
  rw [← GlobalTheory.MuDivides.constantCoeff_mu, WittVector.constantCoeff_apply]
  exact (GlobalTheory.DetInv.mu_coeff_zero_ne_zero p C v O hv ε (prim hε)).1

theorem mu_ne (hv : v.Integers O) (hε : IsPrimitiveSystem ε) : mu ε ≠ 0 :=
  (GlobalTheory.DetInv.mu_coeff_zero_ne_zero p C v O hv ε (prim hε)).2.1

theorem mu_dvd (hv : v.Integers O) (hε : IsPrimitiveSystem ε) (w : Ainf p O)
    (h : mu ε ∣ (p : Ainf p O) * w) : mu ε ∣ w :=
  GlobalTheory.MuDivides.dvd_of_dvd_p_mul hv ε (eps_ne hv hε) w h

theorem mu_sq_dvd (hv : v.Integers O) (hε : IsPrimitiveSystem ε) (w : Ainf p O)
    (h : mu ε ^ 2 ∣ (p : Ainf p O) * w) : mu ε ^ 2 ∣ w := by
  haveI := GlobalTheory.AinfXi.isDomain_ainf (p := p) hv
  obtain ⟨w', rfl⟩ := mu_dvd hv hε w (dvd_trans (dvd_pow_self _ two_ne_zero) h)
  rw [sq, mul_left_comm] at h
  rw [sq]
  exact mul_dvd_mul_left _ (mu_dvd hv hε w' ((mul_dvd_mul_iff_left (mu_ne hv hε)).1 h))

theorem dvd_of_eq_zero (x y : Ainf p O) (h : a ε x + τ ε * a ε y = 0) :
    mu ε ^ 2 ∣ (p : Ainf p O) * x + mu ε * y := by
  have hm : C x + C y * X ∈ rel ε := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← h, map_add (f := _), map_mul, mul_comm]; rfl
  obtain ⟨h1, h2, he⟩ := Ideal.mem_span_pair.1 hm
  have he' : C x + C y * X = h1 * C (p : Ainf p O) * X - h1 * C (mu ε) + h2 * X ^ 2 := by
    rw [← he]; ring
  have e0 := congrArg (fun f => _root_.AddMonoidAlgebra.coeff (M := ℕ) f 0) he'
  have e1 := congrArg (fun f => _root_.AddMonoidAlgebra.coeff (M := ℕ) f 1) he'
  simp only [coeff_add, coeff_sub, coeff_C_zero, coeff_mul_X_zero, coeff_mul_C,
    coeff_mul_X_pow', coeff_C_succ] at e0 e1
  rw [show (1 : ℕ) = 0 + 1 from rfl, coeff_mul_X, coeff_mul_X, coeff_mul_C, coeff_C_zero] at e1
  simp only [coeff_C_succ, zero_add, Nat.one_lt_ofNat, if_neg (by norm_num : ¬ (2 ≤ 1)),
    if_neg (by norm_num : ¬ (2 ≤ 0)), add_zero, zero_sub] at e0 e1
  refine ⟨-(h1.coeff 1), ?_⟩
  rw [e0, e1]; ring

theorem eq_zero_of_dvd (hv : v.Integers O) (hε : IsPrimitiveSystem ε) (x y : Ainf p O)
    (h : mu ε ^ 2 ∣ (p : Ainf p O) * x + mu ε * y) : a ε x + τ ε * a ε y = 0 := by
  haveI := GlobalTheory.AinfXi.isDomain_ainf (p := p) hv
  obtain ⟨z, hz⟩ := h
  obtain ⟨x', rfl⟩ := mu_dvd hv hε x ⟨-y + mu ε * z, by linear_combination hz⟩
  have hy : y = mu ε * z - p * x' := by
    have : mu ε * (y - (mu ε * z - p * x')) = 0 := by linear_combination hz
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left (mu_ne hv hε))
  subst hy
  have h1 := p_τ ε
  have h2 := τ_sq ε
  simp only [map_mul, map_sub, map_natCast]
  rw [← h1]
  linear_combination (↑p * a ε z) * h2

theorem torsion_free (hv : v.Integers O) (hε : IsPrimitiveSystem ε) (b : BR ε)
    (h : (p : BR ε) * b = 0) : b = 0 := by
  obtain ⟨x, y, rfl⟩ := gen ε b
  refine eq_zero_of_dvd hv hε x y (mu_sq_dvd hv hε _ ?_)
  have := dvd_of_eq_zero (ε := ε) (p * x) (p * y) (by
    rw [map_mul, map_mul, a_natCast]; linear_combination h)
  rw [show (p : Ainf p O) * (p * x + mu ε * y) = p * (p * x) + mu ε * (p * y) by ring]
  exact this

end Faithful

end GlobalTheory.BRing
end
end

set_option autoImplicit false
noncomputable section
open Polynomial WittVector GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta

namespace GlobalTheory.BRing

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]
  {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C NNReal} [Algebra O C]
  {ε : PreTilt O p}

theorem tau_mul (hv : v.Integers O) (hε : IsPrimitiveSystem ε) (y : Ainf p O) :
    τ ε * a ε y = 0 ↔ mu ε ∣ y := by
  haveI := GlobalTheory.AinfXi.isDomain_ainf (p := p) hv
  constructor
  · intro h
    have := dvd_of_eq_zero (ε := ε) 0 y (by rw [map_zero, zero_add]; exact h)
    rw [mul_zero, zero_add, sq] at this
    exact (mul_dvd_mul_iff_left (mu_ne hv hε)).1 this
  · rintro ⟨z, rfl⟩
    rw [map_mul, ← p_τ]
    linear_combination (↑p * a ε z) * τ_sq ε

theorem tau_dvd (hv : v.Integers O) (hε : IsPrimitiveSystem ε) (x : Ainf p O) :
    τ ε ∣ a ε x ↔ mu ε ∣ x := by
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨u, w, rfl⟩ := gen ε b
    have h := dvd_of_eq_zero (ε := ε) x (-u) (by
      rw [hb, map_neg]; linear_combination (a ε w) * τ_sq ε)
    exact mu_dvd hv hε x (by
      have h2 : mu ε ∣ mu ε * -u := dvd_mul_right _ _
      have h3 := (dvd_pow_self (mu ε) two_ne_zero).trans h
      simpa using (dvd_add_left h2).1 h3)
  · rintro ⟨c, rfl⟩
    exact ⟨p * a ε c, by rw [map_mul, ← p_τ]; ring⟩

theorem sat (hv : v.Integers O) (b : O) (h : (p : O) * b = 0) : b = 0 := by
  have hp : (p : O) ≠ 0 := fun h0 => by
    have := congrArg (algebraMap O C) h0
    rw [map_natCast, map_zero] at this
    exact (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) this
  haveI : IsDomain O := (algebraMap O C).domain_nontrivial |> fun _ =>
    Function.Injective.isDomain (algebraMap O C) hv.hom_inj
  exact (mul_eq_zero.1 h).resolve_left hp

theorem smod_iff {R : Type} [CommRing R] (q : R) (n : ℕ) (x y : R) :
    x ≡ y [SMOD (Ideal.span {q}) ^ n • (⊤ : Submodule R R)] ↔ q ^ n ∣ x - y := by
  rw [SModEq.sub_mem, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top,
    Ideal.mem_span_singleton]

theorem lim_series (u0 : Ainf p O) (u : ℕ → Ainf p O) : ∃ L : Ainf p O, ∀ n,
    (p : Ainf p O) ^ n ∣ (u0 + ∑ k ∈ Finset.range n, (p : Ainf p O) ^ k * u k) - L := by
  haveI : IsAdicComplete (Ideal.span {(p : Ainf p O)}) (Ainf p O) :=
    WittVector.isAdicCompleteIdealSpanP
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {(p : Ainf p O)})
    (fun N => u0 + ∑ k ∈ Finset.range N, (p : Ainf p O) ^ k * u k) (by
      intro m n hmn
      rw [smod_iff, ← dvd_neg, neg_sub]
      induction n, hmn using Nat.le_induction with
      | base => simp
      | succ n hmn ih =>
        rw [Finset.sum_range_succ, show ∀ s t w : Ainf p O, u0 + (s + t) - w = (u0 + s - w) + t
          from fun _ _ _ => by ring]
        exact dvd_add ih (Dvd.dvd.mul_right (pow_dvd_pow _ hmn) _))
  exact ⟨L, fun n => (smod_iff _ _ _ _).1 (hL n)⟩

theorem complete (hv : v.Integers O) (hε : IsPrimitiveSystem ε) :
    IsAdicComplete (Ideal.span {(p : BR ε)}) (BR ε) := by
  haveI : IsAdicComplete (Ideal.span {(p : Ainf p O)}) (Ainf p O) :=
    WittVector.isAdicCompleteIdealSpanP
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    have hx' : ∀ n, (p : BR ε) ^ n ∣ x := fun n => by simpa using (smod_iff _ n x 0).1 (hx n)
    obtain ⟨u, w, rfl⟩ := gen ε x
    refine eq_zero_of_dvd hv hε u w (GlobalTheory.MuDivides.dvd_of_step (p : Ainf p O) (mu ε ^ 2)
      (fun z => ∀ n, ∃ s t, z = (p : Ainf p O) ^ n * s + mu ε ^ 2 * t) ?_ _ ?_)
    · intro z hz
      obtain ⟨s, t, hst⟩ := hz 1
      refine ⟨t, s, by rw [hst]; ring, fun n => ?_⟩
      obtain ⟨s', t', hst'⟩ := hz (n + 1)
      obtain ⟨e, he⟩ := mu_sq_dvd hv hε (s - p ^ n * s') ⟨t' - t, by
        linear_combination hst' - hst⟩
      exact ⟨s', e, by linear_combination he⟩
    · intro n
      obtain ⟨c, hc⟩ := hx' n
      obtain ⟨s', t', rfl⟩ := gen ε c
      obtain ⟨e, he⟩ := dvd_of_eq_zero (ε := ε) (u - p ^ n * s') (w - p ^ n * t') (by
        simp only [map_sub, map_mul, map_pow, map_natCast]
        linear_combination hc)
      exact ⟨p * s' + mu ε * t', e, by linear_combination he⟩
  · intro f hf
    have hstep : ∀ n, ∃ c, f (n + 1) - f n = (p : BR ε) ^ n * c := fun n => by
      obtain ⟨c, hc⟩ := (smod_iff _ n (f n) (f (n + 1))).1 (hf (Nat.le_succ n))
      exact ⟨-c, by linear_combination -hc⟩
    choose c hc using hstep
    choose u w huw using fun n => gen ε (c n)
    obtain ⟨u0, w0, h0⟩ := gen ε (f 0)
    obtain ⟨LX, hX⟩ := lim_series u0 u
    obtain ⟨LY, hY⟩ := lim_series w0 w
    have hf' : ∀ N, f N = a ε (u0 + ∑ k ∈ Finset.range N, (p : Ainf p O) ^ k * u k) +
        τ ε * a ε (w0 + ∑ k ∈ Finset.range N, (p : Ainf p O) ^ k * w k) := by
      intro N
      induction N with
      | zero => simpa using h0
      | succ N ih =>
        have := hc N
        rw [huw N] at this
        simp only [Finset.sum_range_succ, map_add (f := _), map_mul, map_pow, map_natCast] at ih ⊢
        linear_combination this + ih
    refine ⟨a ε LX + τ ε * a ε LY, fun n => (smod_iff _ _ _ _).2 ?_⟩
    obtain ⟨e1, he1⟩ := hX n
    obtain ⟨e2, he2⟩ := hY n
    refine ⟨a ε e1 + τ ε * a ε e2, ?_⟩
    rw [hf' n]
    have h1 := congrArg (a ε) he1
    have h2 := congrArg (a ε) he2
    simp only [map_sub, map_mul, map_pow, map_natCast, map_add (f := _)] at h1 h2 ⊢
    linear_combination h1 + τ ε * h2

theorem sqz_pow {R : Type} [CommRing R] (s t : R) (ht : t * t = 0) (n : ℕ) :
    (s + t) ^ (n + 1) = s ^ (n + 1) + (n + 1) * s ^ n * t := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih]; push_cast
    linear_combination ((n + 1 : R) * s ^ n) * ht

theorem pow_gen (x y : Ainf p O) : (a ε x + τ ε * a ε y) ^ p =
    a ε x ^ p + p * a ε x ^ (p - 1) * (τ ε * a ε y) := by
  have hsq : (τ ε * a ε y) * (τ ε * a ε y) = 0 := by
    linear_combination (a ε y * a ε y) * τ_sq ε
  have h := sqz_pow (a ε x) (τ ε * a ε y) hsq (p - 1)
  have h1 : p - 1 + 1 = p := Nat.sub_add_cancel (Fact.out : p.Prime).one_le
  have h2 : ((p - 1 : ℕ) : BR ε) + 1 = p := by rw [← Nat.cast_add_one, h1]
  rwa [h1, h2] at h

theorem σ_pow (b : BR ε) : (p : BR ε) ∣ σ ε b - b ^ p := by
  obtain ⟨x, y, rfl⟩ := gen ε b
  obtain ⟨z, hz⟩ := frob_congr x
  obtain ⟨d, hd⟩ := frob_xi ε
  rw [pow_gen, map_add (f := _), map_mul, σ_a, σ_a, σ_τ, hz, hd]
  refine ⟨a ε z + τ ε * a ε (frobenius y) - a ε x ^ (p - 1) * (τ ε * a ε y), ?_⟩
  simp only [map_add (f := _), map_mul, map_pow, map_natCast]
  linear_combination (-(τ ε * a ε d * a ε (frobenius y))) * p_τ ε +
    ((p : BR ε) * a ε d * a ε (frobenius y)) * τ_sq ε

theorem pd (hv : v.Integers O) (hε : IsPrimitiveSystem ε) (x : BR ε) (hx : θ hε x = 0) :
    ∃ y, θ hε y = 0 ∧ x ^ p = p * y := by
  suffices h : (p : BR ε) ∣ x ^ p by
    obtain ⟨y, hy⟩ := h
    refine ⟨y, sat (p := p) hv _ ?_, hy⟩
    have := congrArg (θ hε) hy
    rw [map_pow, hx, zero_pow (Fact.out : p.Prime).ne_zero, map_mul, map_natCast] at this
    exact this.symm
  obtain ⟨u, w, rfl⟩ := gen ε x
  have hu : fontaineTheta O p u = 0 := by
    rw [map_add (f := _), map_mul, θ_a, θ_a, θ_τ, zero_mul, add_zero] at hx; exact hx
  obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1
    (by rw [← GlobalTheory.AinfXi.ker_theta hv ε (prim hε)]; exact hu)
  obtain ⟨z, hz⟩ := frob_congr (xi ε)
  obtain ⟨d, hd⟩ := frob_xi ε
  have hxi : a ε (xi ε) ^ p = p + p * τ ε * a ε d - p * a ε z := by
    rw [← map_pow, show xi ε ^ p = frobenius (xi ε) - p * z by rw [hz]; ring, hd]
    simp only [map_add (f := _), map_sub, map_mul, map_natCast]
    rw [← p_τ]
  rw [pow_gen]
  refine ⟨a ε c ^ p * (1 + τ ε * a ε d - a ε z) + a ε (c * xi ε) ^ (p - 1) * (τ ε * a ε w), ?_⟩
  rw [map_mul, mul_pow, hxi]
  ring

theorem unit_coprime (n : ℕ) (h : Nat.Coprime n p) : IsUnit (n : BR ε) := by
  rw [← a_natCast ε]
  refine IsUnit.map _ (GlobalTheory.AinfXi.witt_isUnit _ ?_)
  rw [map_natCast]
  have hu : IsUnit (n : ZMod p) := by
    have := (ZMod.unitOfCoprime n h).isUnit
    rwa [ZMod.coe_unitOfCoprime] at this
  simpa using hu.map (ZMod.castHom (dvd_refl p) (PreTilt O p))

theorem isFrame (hv : v.Integers O) (hε : IsPrimitiveSystem ε) : QLog.IsFrame p (BQ ε) (θ hε) := by
  refine {
    surj := ?_
    inj := ?_
    denom := ?_
    unit_p := ?_
    unit_coprime := unit_coprime
    pd := pd hv hε
    sat := sat hv
    complete := complete hv hε }
  · intro y
    obtain ⟨x, rfl⟩ := (GlobalTheory.AinfXi.ainf_local_xi_order p C v O hv ε (prim hε)).2.2.2.1 y
    exact ⟨a ε x, θ_a hε x⟩
  · exact IsLocalization.injective (M := Submonoid.powers (p : BR ε)) _ (Submonoid.powers_le.2
      (mem_nonZeroDivisors_iff.2 ⟨fun x hx => torsion_free hv hε x hx,
        fun x hx => torsion_free hv hε x (by rw [mul_comm]; exact hx)⟩))
  · intro q
    obtain ⟨⟨b, ⟨_, k, rfl⟩⟩, hq⟩ := IsLocalization.surj (Submonoid.powers (p : BR ε)) q
    exact ⟨k, b, by rw [← hq, map_pow, map_natCast, mul_comm]⟩
  ·
    have := IsLocalization.Away.algebraMap_isUnit (S := BQ ε) (p : BR ε)
    rwa [map_natCast] at this

theorem exists_bFrame : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O →
    ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), Nonempty (QLog.BFrame ε) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε
  exact ⟨QLog.BFrame.mk (BR ε) (BQ ε) (a ε) (θ hε) (σ ε) (s ε) (τ ε) (isFrame hv hε) (θ_a hε)
    (σ_a ε) (s_alg ε) σ_pow (p_τ ε) (τ_sq ε) (gen ε) (tau_mul hv hε) (tau_dvd hv hε)⟩

end GlobalTheory.BRing
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSumEpsPairingSmul
set_option autoImplicit false
noncomputable section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.DatumOfMatrices

def sumIdx {d k h : ℕ} (hdk : d + k = h) : Fin d ⊕ Fin k ≃ Fin h :=
  finSumFinEquiv.trans (finCongr hdk)

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]

def datumOf (ε : PreTilt O p) {d k h : ℕ} (hdk : d + k = h)
    (Fa : Matrix (Fin d ⊕ Fin k) (Fin h) (Ainf p O)) (Ga : Matrix (Fin h) (Fin d ⊕ Fin k) (Ainf p O))
    (Ψ Ψ' : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O))
    (hGF : Ga * Fa = Sandwich.mu ε • (1 : Matrix (Fin h) (Fin h) (Ainf p O)))
    (hF : Fa = Ψ * Fa.map (phiInv p O))
    (hΨ : Ψ * Ψ' = xi ε • (1 : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O))) :
    Datum ε h ℤ_[p] where
  F := Fa.submatrix (sumIdx hdk).symm id
  G := Ga.submatrix id (sumIdx hdk).symm
  Ψ := Ψ.submatrix (sumIdx hdk).symm (sumIdx hdk).symm
  Ψ' := Ψ'.submatrix (sumIdx hdk).symm (sumIdx hdk).symm
  ρT := Algebra.ofId _ _
  ρM := (RingHom.mapMatrix (ofPadic p O)).comp (algebraMap _ _)
  G_mul_F := by
    rw [Matrix.submatrix_mul_equiv, hGF]
    rfl
  F_eq := by
    calc Fa.submatrix (sumIdx hdk).symm id
        = (Ψ * Fa.map (phiInv p O)).submatrix (sumIdx hdk).symm id :=
          congrArg (fun M => M.submatrix (sumIdx hdk).symm id) hF
      _ = Ψ.submatrix (sumIdx hdk).symm (sumIdx hdk).symm *
            (Fa.map (phiInv p O)).submatrix (sumIdx hdk).symm id :=
          (Matrix.submatrix_mul_equiv _ _ _ _ _).symm
      _ = _ := by rw [Matrix.submatrix_map]
  Ψ_mul := by
    rw [Matrix.submatrix_mul_equiv, hΨ]
    refine Matrix.ext fun i j => ?_
    simp [Matrix.one_apply]
  F_act := by
    intro a
    refine Matrix.ext fun i j => ?_
    simp [Algebra.ofId_apply, Matrix.algebraMap_matrix_apply, Matrix.mul_apply, Matrix.one_apply,
      apply_ite (ofPadic p O), mul_ite, ite_mul, mul_comm]

end GlobalTheory.DatumOfMatrices

namespace GlobalTheory.DatumOfMatrices

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O]

theorem eq_sum_epsPairing_smul {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) (C : Type) [Field C]
    [Algebra O C] [IsIntegrallyClosedIn O C] [IsAlgClosed C] [CharZero C] (G : PDivGroup p O)
    (tb : Module.Basis (Fin G.height) ℤ_[p] G.Tate) (χ : Fin G.height → G.dual.Tate)
    (hpair : ∀ m m', epsPairing hε G (tb m) (χ m') = if m = m' then 1 else 0)
    (χ0 : G.dual.Tate) : χ0 = ∑ m', epsPairing hε G (tb m') χ0 • χ m' := by
  classical
  apply (G.pairing_flip_bijective C).1
  refine tb.ext fun m => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [LinearMap.flip_apply, LinearMap.flip_apply, map_sum]
  have hlin : ∀ (t : G.Tate) (c : ℤ_[p]) (ψ : G.dual.Tate),
      epsPairing hε G t (c • ψ) = c * epsPairing hε G t ψ := by
    intro t c ψ
    simp [epsPairing, map_smul]
  simp only [← epsPairing_smul hε, hlin, hpair, mul_ite, mul_one, mul_zero, ite_smul, zero_smul]
  simp

end GlobalTheory.DatumOfMatrices

namespace GlobalTheory.DatumOfMatrices

theorem hasDatum_of_matrices : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ (G : PDivGroup p O) (d k : ℕ), d + k = G.height → ∀ (tb : Module.Basis (Fin G.height) ℤ_[p] G.Tate) (χ : Fin G.height → G.dual.Tate) (w : Module.Basis (Fin d) O G.omega) (lb : Module.Basis (Fin k) O G.dual.Lie) (Fa : Matrix (Fin d ⊕ Fin k) (Fin G.height) (Ainf p O)) (Ga : Matrix (Fin G.height) (Fin d ⊕ Fin k) (Ainf p O)) (Ψ Ψ' : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)), Ga * Fa = Sandwich.mu ε • (1 : Matrix (Fin G.height) (Fin G.height) (Ainf p O)) → Fa = Ψ * Fa.map (phiInv p O) → Ψ * Ψ' = xi ε • (1 : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)) → (∀ m m', epsPairing hε G (tb m) (χ m') = if m = m' then 1 else 0) → (∀ i m, WittVector.fontaineTheta O p (Fa (Sum.inl i) m) = 0) → (∀ j m, WittVector.fontaineTheta O p (Fa (Sum.inr j) m) = lb j (hodgeTate G (tb m))) → (∀ m j, WittVector.fontaineTheta O p (Ga m (Sum.inr j)) = 0) → (∀ m, dlog G (χ m) = ∑ i, WittVector.fontaineTheta O p (Ga m (Sum.inl i)) • w i) → HasDatum hε G := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε G d k hdk tb χ w lb Fa Ga Ψ Ψ' hGF hF hΨ hpair hθl hθr
    hGr hdlog
  classical
  have := hv.isFractionRing
  have := hv.isIntegrallyClosed
  have : IsIntegrallyClosedIn O C :=
    (isIntegrallyClosed_iff_isIntegrallyClosedIn C).1 inferInstance
  obtain ⟨hfin, hproj⟩ := GlobalTheory.PDiv.omega_finite_projective p C v O hv G.dual
  haveI := hfin
  haveI := hproj
  have hζ : IsPrimitiveRoot (root ε).untilt p := by simpa [zeta] using hε 1
  set σ := sumIdx hdk with hσ
  set D := datumOf ε hdk Fa Ga Ψ Ψ' hGF hF hΨ with hD
  have hal : ∀ y a, D.al y (σ a) = ∑ m, WittVector.fontaineTheta O p (Fa a m) * y m := by
    intro y a
    simp [D, datumOf, Datum.al, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, σ]
  have hbb : ∀ y m', D.bb y m' =
      ∑ i, WittVector.fontaineTheta O p (Ga m' (Sum.inl i)) * y (σ (Sum.inl i)) := by
    intro y m'
    have h1 : D.bb y m' = ∑ a, WittVector.fontaineTheta O p (Ga m' a) * y (σ a) := by
      simp only [D, datumOf, Datum.bb, Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
        Matrix.map_apply, Matrix.submatrix_apply, id]
      rw [← Equiv.sum_comp σ]
      simp [σ]
    rw [h1, Fintype.sum_sum_type]
    simp [hGr]

  have hbC : ∀ z : Fin G.height → O, GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.bC C D (fun l => algebraMap O C (z l)) =
      fun m' => algebraMap O C (D.bb z m') := by
    intro z
    funext m'
    set_option synthInstance.maxHeartbeats 100000 in
      simp [GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.bC, GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.redC, Datum.bb, Matrix.toLin'_apply, Matrix.mulVec,
      dotProduct, map_sum, map_mul]
  have halC : ∀ (y : Fin G.height → C) a, GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.alC C D y (σ a) =
      ∑ m, algebraMap O C (WittVector.fontaineTheta O p (Fa a m)) * y m := by
    intro y a
    simp [GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.alC, GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.redC, D, datumOf, Matrix.toLin'_apply,
      Matrix.mulVec, dotProduct, σ]
  let projL : (Fin G.height → O) →ₗ[O] (Fin d → O) := LinearMap.funLeft O O (σ ∘ Sum.inl)
  let projR : (Fin G.height → O) →ₗ[O] (Fin k → O) := LinearMap.funLeft O O (σ ∘ Sum.inr)
  have hFil : D.Fil = LinearMap.ker projL := by
    ext m
    change D.bb m = 0 ↔ projL m = 0
    constructor
    · intro hm
      have hker : (fun l => algebraMap O C (m l)) ∈ LinearMap.ker (GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps.bC C D) := by
        rw [LinearMap.mem_ker, hbC, hm]
        funext m'
        simp
      rw [(GlobalTheory.DetInv.ker_bC_eq_range_alC_and_ker_alC_eq_range_bC p C v O hv ε hζ ℤ_[p]
        G.height D).1] at hker
      obtain ⟨y, hy⟩ := hker
      funext i
      apply hv.hom_inj
      have h1 := congrFun hy (σ (Sum.inl i))
      rw [halC] at h1
      simp only [hθl, map_zero, zero_mul, Finset.sum_const_zero] at h1
      simpa [projL] using h1.symm
    · intro hm
      funext m'
      rw [hbb]
      have h2 : ∀ i, m (σ (Sum.inl i)) = 0 := fun i => congrFun hm i
      simp [h2]

  let coordE : G.dual.omega ≃ₗ[O] (Fin k → O) :=
    Module.evalEquiv O G.dual.omega ≪≫ₗ lb.dualBasis.equivFun
  have hcoordE : ∀ x j, coordE x j = lb j x := by
    intro x j
    simp [coordE]
  let incl : (Fin k → O) →ₗ[O] (Fin G.height → O) :=
    { toFun := fun c l => Sum.elim (0 : Fin d → O) c (σ.symm l)
      map_add' := by
        intro a b
        funext l
        rcases h : σ.symm l with i | j <;> simp [h]
      map_smul' := by
        intro r a
        funext l
        rcases h : σ.symm l with i | j <;> simp [h] }
  have hincl : ∀ c a, incl c (σ a) = Sum.elim (0 : Fin d → O) c a := by
    intro c a
    simp [incl]
  have hinclF : ∀ c, incl c ∈ D.Fil := by
    intro c
    rw [hFil, LinearMap.mem_ker]
    funext i
    simp [projL, hincl]
  let filE : (Fin k → O) ≃ₗ[O] D.Fil :=
    { toFun := fun c => ⟨incl c, hinclF c⟩
      map_add' := by intro a b; ext1; simp
      map_smul' := by intro r a; ext1; simp
      invFun := fun m => projR m
      left_inv := by
        intro c
        funext j
        simp [projR, hincl]
      right_inv := by
        intro m
        ext1
        funext l
        obtain ⟨a, rfl⟩ := σ.surjective l
        have hFil' : ∀ y, y ∈ D.Fil ↔ projL y = 0 := fun y => by rw [hFil, LinearMap.mem_ker]
        have hm : projL (m : Fin G.height → O) = 0 := (hFil' _).1 m.2
        rcases a with i | j
        · simp only [hincl, Sum.elim_inl, Pi.zero_apply]
          exact (congrFun hm i).symm
        · simp [hincl, projR] }
  let fil : G.dual.omega ≃ₗ[O] D.Fil := coordE ≪≫ₗ filE
  have hfil : ∀ x a, (fil x : Fin G.height → O) (σ a) =
      Sum.elim (0 : Fin d → O) (fun j => lb j x) a := by
    intro x a
    change incl (coordE x) (σ a) = _
    rw [hincl]
    congr 1
    funext j
    exact hcoordE x j
  have hsurjL : Function.Surjective projL := by
    intro c
    refine ⟨fun l => Sum.elim c (0 : Fin k → O) (σ.symm l), ?_⟩
    funext i
    simp [projL]
  let lie : ((Fin G.height → O) ⧸ D.Fil) ≃ₗ[O] G.Lie :=
    Submodule.quotEquivOfEq _ _ hFil ≪≫ₗ projL.quotKerEquivOfSurjective hsurjL ≪≫ₗ
      w.dualBasis.equivFun.symm
  have hlie : ∀ m i, lie (D.Fil.mkQ m) (w i) = m (σ (Sum.inl i)) := by
    intro m i
    change (w.dualBasis.equivFun.symm (projL.quotKerEquivOfSurjective hsurjL
      (Submodule.quotEquivOfEq _ _ hFil (D.Fil.mkQ m)))) (w i) = _
    rw [← Module.Basis.dualBasis_equivFun, LinearEquiv.apply_symm_apply]
    rfl

  have hexpHT : ∀ j t, lb j (hodgeTate G t) =
      ∑ m, lb j (hodgeTate G (tb m)) * padicToO p O (tb.repr t m) := by
    intro j t
    conv_lhs => rw [← tb.sum_repr t]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum (hodgeTate G), map_sum (lb j)]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hodgeTate_smul (padicToO p O), map_smul, smul_eq_mul, mul_comm]
  have hχexp : ∀ χ0 : G.dual.Tate, χ0 = ∑ m', epsPairing hε G (tb m') χ0 • χ m' :=
    eq_sum_epsPairing_smul hε C G tb χ hpair
  have he : ∀ i, (tb.equivFun).symm (Pi.single i 1) = tb i := by
    intro i
    simp
  refine ⟨D, tb.equivFun, fil, lie, fun t => ?_, fun x χ0 => ?_⟩
  · funext l
    obtain ⟨a, rfl⟩ := σ.surjective l
    rw [hal, hfil]
    rcases a with i | j
    · simp [hθl]
    · simp only [Sum.elim_inr, hθr, toO, Module.Basis.equivFun_apply]
      rw [hexpHT j t]
  · obtain ⟨m, hm⟩ := D.Fil.mkQ_surjective (lie.symm x)
    have hx : x = lie (D.Fil.mkQ m) := by rw [hm, LinearEquiv.apply_symm_apply]
    subst hx
    rw [LinearEquiv.symm_apply_apply]
    have hbq : bQuot D (D.Fil.mkQ m) = D.bb m := rfl
    rw [hbq]
    have hbbx : ∀ m', D.bb m m' = lie (D.Fil.mkQ m) (dlog G (χ m')) := by
      intro m'
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hbb, hdlog, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, hlie, smul_eq_mul]
    rw [pairingO]
    simp only [hbbx, he]
    conv_rhs => rw [hχexp χ0]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum (dlog G), map_sum]
    refine Finset.sum_congr rfl fun m' _ => ?_
    rw [dlog_smul (padicToO p O), map_smul, smul_eq_mul, mul_comm]

end GlobalTheory.DatumOfMatrices
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDatumBiconnOf
set_option autoImplicit false
noncomputable section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.PDivLat

theorem hasDatum_biconn_of (hfr : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), Nonempty (BFrame ε))
    (hmat : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ G : PDivGroup p O, IsConn G → IsConn G.dual → ∀ F : BFrame ε, ∃ (d k : ℕ) (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) (Y : Matrix (Fin d ⊕ Fin k) (Fin G.height) F.B) (Gm : Matrix (Fin G.height) (Fin d ⊕ Fin k) F.B) (tb : Module.Basis (Fin G.height) ℤ_[p] G.Tate) (χ : Fin G.height → G.dual.Tate) (w : Module.Basis (Fin d) O G.omega) (lb : Module.Basis (Fin k) O G.dual.Lie), d + k = G.height ∧ IsUnit U ∧ Y.map F.σ = blk d k (p : F.B) 1 * U.transpose * Y ∧ U * blk d k (p : F.B) 1 * (Gm.transpose.map F.σ) = (p : F.B) • Gm.transpose ∧ Gm * Y = F.a (Sandwich.mu ε) • (1 : Matrix (Fin G.height) (Fin G.height) F.B) ∧ (∀ i m, F.θ (Y (Sum.inl i) m) = 0) ∧ (∀ m j, F.θ (Gm m (Sum.inr j)) = 0) ∧ IsNil F.θ F.σ (U * blk d k (p : F.B) 1) ∧ IsNil F.θ F.σ (U.transpose⁻¹ * blk d k 1 (p : F.B)) ∧ (∀ m m', epsPairing hε G (tb m) (χ m') = if m = m' then 1 else 0) ∧ (∀ j m, F.θ (Y (Sum.inr j) m) = lb j (hodgeTate G (tb m))) ∧ ∀ m, dlog G (χ m) = ∑ i, F.θ (Gm m (Sum.inl i)) • w i)
    (hlift : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k h : ℕ) (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) (Y : Matrix (Fin d ⊕ Fin k) (Fin h) F.B) (Gm : Matrix (Fin h) (Fin d ⊕ Fin k) F.B), IsUnit U ∧ Y.map F.σ = blk d k (p : F.B) 1 * U.transpose * Y ∧ U * blk d k (p : F.B) 1 * (Gm.transpose.map F.σ) = (p : F.B) • Gm.transpose ∧ Gm * Y = F.a (Sandwich.mu ε) • (1 : Matrix (Fin h) (Fin h) F.B) ∧ (∀ i m, F.θ (Y (Sum.inl i) m) = 0) ∧ (∀ m j, F.θ (Gm m (Sum.inr j)) = 0) ∧ IsNil F.θ F.σ (U * blk d k (p : F.B) 1) ∧ IsNil F.θ F.σ (U.transpose⁻¹ * blk d k 1 (p : F.B)) → ∃ (Fa : Matrix (Fin d ⊕ Fin k) (Fin h) (Ainf p O)) (Ga : Matrix (Fin h) (Fin d ⊕ Fin k) (Ainf p O)) (Ψ Ψ' : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)), Ga * Fa = Sandwich.mu ε • (1 : Matrix (Fin h) (Fin h) (Ainf p O)) ∧ Fa = Ψ * Fa.map (phiInv p O) ∧ Ψ * Ψ' = xi ε • (1 : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)) ∧ (∀ i m, WittVector.fontaineTheta O p (Fa i m) = F.θ (Y i m)) ∧ ∀ m i, WittVector.fontaineTheta O p (Ga m i) = F.θ (Gm m i))
    (hfin : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ (G : PDivGroup p O) (d k : ℕ), d + k = G.height → ∀ (tb : Module.Basis (Fin G.height) ℤ_[p] G.Tate) (χ : Fin G.height → G.dual.Tate) (w : Module.Basis (Fin d) O G.omega) (lb : Module.Basis (Fin k) O G.dual.Lie) (Fa : Matrix (Fin d ⊕ Fin k) (Fin G.height) (Ainf p O)) (Ga : Matrix (Fin G.height) (Fin d ⊕ Fin k) (Ainf p O)) (Ψ Ψ' : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)), Ga * Fa = Sandwich.mu ε • (1 : Matrix (Fin G.height) (Fin G.height) (Ainf p O)) → Fa = Ψ * Fa.map (phiInv p O) → Ψ * Ψ' = xi ε • (1 : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) (Ainf p O)) → (∀ m m', epsPairing hε G (tb m) (χ m') = if m = m' then 1 else 0) → (∀ i m, WittVector.fontaineTheta O p (Fa (Sum.inl i) m) = 0) → (∀ j m, WittVector.fontaineTheta O p (Fa (Sum.inr j) m) = lb j (hodgeTate G (tb m))) → (∀ m j, WittVector.fontaineTheta O p (Ga m (Sum.inr j)) = 0) → (∀ m, dlog G (χ m) = ∑ i, WittVector.fontaineTheta O p (Ga m (Sum.inl i)) • w i) → HasDatum hε G) :
    ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ G : PDivGroup p O, IsConn G → IsConn G.dual → HasDatum hε G := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε G hG hD
  obtain ⟨F⟩ := hfr p C v O hv ε hε
  obtain ⟨d, k, U, Y, Gm, tb, χ, w, lb, hdk, hU, hY, hGm, hGY, hY0, hG0, hn1, hn2, hpair, hYl, hdl⟩ :=
    hmat p C v O hv ε hε G hG hD F
  obtain ⟨Fa, Ga, Ψ, Ψ', h1, h2, h3, h4, h5⟩ :=
    hlift p C v O hv ε hε F d k G.height U Y Gm ⟨hU, hY, hGm, hGY, hY0, hG0, hn1, hn2⟩
  refine hfin p C v O hv ε hε G d k hdk tb χ w lb Fa Ga Ψ Ψ' h1 h2 h3 hpair
    (fun i m => (h4 _ _).trans (hY0 i m)) (fun j m => (h4 _ _).trans (hYl j m))
    (fun m j => (h5 _ _).trans (hG0 m j)) (fun m => ?_)
  rw [hdl m]
  exact Finset.sum_congr rfl fun i _ => by rw [h5]

end GlobalTheory.PDivLat
end
end

set_option autoImplicit false

noncomputable section

open GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace UpperTheory.Lit

theorem prismaticDieudonneHodge : GlobalTheory.Published.PrismaticDieudonneHodge := by
  intro p _ C _ _ _ v O _ _ hv _ _ ε hε
  haveI : IsDomain O := hv.hom_inj.isDomain (algebraMap O C)
  have hs : IsPrimitiveSystem ε := fun n => GlobalTheory.Dieudonne.isPrimitiveRoot_untilt_root hε n
  exact GlobalTheory.T.prismaticDieudonneHodge_of_hodgeTateDatum p C v O hv ε hs (GlobalTheory.T.pDivisibleGroup_datum_of_connected_dual_connected p C v O hv ε hs
    (hasDatum_biconn_of GlobalTheory.BRing.exists_bFrame GlobalTheory.QLog.WindowMat.window_matrices GlobalTheory.T.window_lift_to_fontaineAinf_matrices
      GlobalTheory.DatumOfMatrices.hasDatum_of_matrices p C v O hv ε hs))

theorem farguesExact : GlobalTheory.CompanionTheory.Ar.HT.FarguesExact :=
  PositivityTheory.Tls2.Jfarg.farguesExact_of_hodge prismaticDieudonneHodge

end UpperTheory.Lit

end
