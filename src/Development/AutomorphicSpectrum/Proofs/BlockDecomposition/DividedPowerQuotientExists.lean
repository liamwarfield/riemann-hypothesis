module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.GapAbsOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JpUnif
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.EmbeddedFrames.PfD
public import Formalism.RealPlaceAnalysis.Complexify
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelL2RowsColumns

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerQuotientExists
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerStructureExists
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.PdTF

theorem natCast_mul_cancel {S : Type} [CommRing S] (hS : TF (S := S)) {n : ℕ} (hn : n ≠ 0) {a b : S}
    (e : (n : S) * a = (n : S) * b) : a = b := by
  have h0 : (n : S) * (a - b) = 0 := by rw [mul_sub, e, sub_self]
  have := (mem_nonZeroDivisors_iff.mp (hS n hn)).1 _ h0
  exact sub_eq_zero.mp this

theorem exists_dividedPowers {S : Type} [CommRing S] (hS : TF (S := S)) (I : Ideal S) (hI : PdI I) :
    ∃ δ : DividedPowers I, IsPd (RingHom.id S) I δ := by
  classical
  have ex : ∀ (k : ℕ) (x : S), ∃ y : S,
      (x ∈ I → (k.factorial : S) * y = x ^ k ∧ (k ≠ 0 → y ∈ I)) ∧ (x ∉ I → y = 0) := by
    intro k x
    by_cases hx : x ∈ I
    · by_cases hk : k = 0
      · subst hk
        exact ⟨1, fun _ => ⟨by simp, fun h => absurd rfl h⟩, fun h => absurd hx h⟩
      · obtain ⟨y, hy, e⟩ := hI x hx k hk
        exact ⟨y, fun _ => ⟨e, fun _ => hy⟩, fun h => absurd hx h⟩
    · exact ⟨0, fun h => absurd h hx, fun _ => rfl⟩
  choose d hd using ex
  have spec : ∀ (k : ℕ) {x : S}, x ∈ I → (k.factorial : S) * d k x = x ^ k :=
    fun k x hx => ((hd k x).1 hx).1
  have hmem : ∀ {k : ℕ} {x : S}, k ≠ 0 → x ∈ I → d k x ∈ I :=
    fun {k x} hk hx => ((hd k x).1 hx).2 hk
  have fne : ∀ k : ℕ, k.factorial ≠ 0 := Nat.factorial_ne_zero
  refine ⟨{ dpow := d
            dpow_null := fun {n x} hx => (hd n x).2 hx
            dpow_zero := fun {x} hx => ?_
            dpow_one := fun {x} hx => ?_
            dpow_mem := fun {n x} hn hx => hmem hn hx
            dpow_add := fun {n x y} hx hy => ?_
            dpow_mul := fun {n a x} hx => ?_
            mul_dpow := fun {m n x} hx => ?_
            dpow_comp := fun {m n x} hn hx => ?_ }, (Ideal.map_id I).symm, ?_⟩
  · have := spec 0 hx
    simpa using this
  · have := spec 1 hx
    simpa using this
  · apply natCast_mul_cancel hS (fne n)
    rw [spec n (I.add_mem hx hy), (Commute.all x y).add_pow', Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    obtain ⟨i, j⟩ := p
    have hij : i + j = n := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    subst hij
    have hf : (((i + j).factorial : ℕ) : S)
        = ((i + j).choose i : S) * (i.factorial : S) * (j.factorial : S) := by
      rw [← Nat.add_choose_mul_factorial_mul_factorial, Nat.choose_symm_add]
      push_cast
      ring
    simp only
    rw [hf, nsmul_eq_mul, ← spec i hx, ← spec j hy]
    ring
  · apply natCast_mul_cancel hS (fne n)
    rw [spec n (I.mul_mem_left a hx), mul_pow, ← spec n hx]
    ring
  · apply natCast_mul_cancel hS (Nat.mul_ne_zero (fne m) (fne n))
    have hf : (((m + n).factorial : ℕ) : S)
        = ((m + n).choose m : S) * (m.factorial : S) * (n.factorial : S) := by
      rw [← Nat.add_choose_mul_factorial_mul_factorial, Nat.choose_symm_add]
      push_cast
      ring
    have h1 : ((m.factorial * n.factorial : ℕ) : S) * (d m x * d n x) = x ^ (m + n) := by
      push_cast
      rw [pow_add, ← spec m hx, ← spec n hx]
      ring
    have h2 : ((m.factorial * n.factorial : ℕ) : S) * (((m + n).choose m : S) * d (m + n) x)
        = x ^ (m + n) := by
      rw [← spec (m + n) hx, hf]
      push_cast
      ring
    rw [h1, h2]
  · by_cases hm : m = 0
    · subst hm
      have h0 := spec 0 (hmem hn hx)
      have h1 := spec 0 hx
      simp only [Nat.factorial_zero, Nat.cast_one, one_mul, pow_zero] at h0 h1
      simp [h0, h1, Nat.uniformBell_zero_left]
    · apply natCast_mul_cancel hS (Nat.mul_ne_zero (fne m) (pow_ne_zero m (fne n)))
      have hdx : d n x ∈ I := hmem hn hx
      have hb : ((Nat.uniformBell m n : ℕ) : S) * ((n.factorial : S) ^ m) * (m.factorial : S)
          = ((m * n).factorial : S) := by
        rw [← Nat.uniformBell_mul_eq _ hn]
        push_cast
        ring
      have h1 : ((m.factorial * n.factorial ^ m : ℕ) : S) * d m (d n x) = x ^ (m * n) := by
        push_cast
        calc (m.factorial : S) * (n.factorial : S) ^ m * d m (d n x)
            = (n.factorial : S) ^ m * ((m.factorial : S) * d m (d n x)) := by ring
          _ = ((n.factorial : S) * d n x) ^ m := by rw [spec m hdx, mul_pow]
          _ = x ^ (m * n) := by rw [spec n hx, ← pow_mul, mul_comm]
      have h2 : ((m.factorial * n.factorial ^ m : ℕ) : S)
          * (((Nat.uniformBell m n : ℕ) : S) * d (m * n) x) = x ^ (m * n) := by
        rw [← spec (m * n) hx, ← hb]
        push_cast
        ring
      rw [h1, h2]
  · intro k x y hx e
    apply natCast_mul_cancel hS (fne k)
    simp only [RingHom.id_apply]
    rw [spec k hx, e]

end GlobalTheory.CompanionTheory.PdTF
end

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.PdTF

theorem exists_dividedPowers_map_quotient {S : Type} [CommRing S] (hS : TF (S := S)) (I J : Ideal S)
    (hI : PdI I)
    (hJ : ∀ x ∈ I, x ∈ J → ∀ k : ℕ, k ≠ 0 → ∀ y : S, (k.factorial : S) * y = x ^ k → y ∈ J) :
    ∃ δ : DividedPowers (I.map (Ideal.Quotient.mk J)), IsPd (Ideal.Quotient.mk J) I δ := by
  obtain ⟨δ₀, -, hδ₀⟩ := exists_dividedPowers hS I hI
  have hsub : DividedPowers.IsSubDPIdeal δ₀ (J ⊓ I) :=
    { isSubideal := inf_le_right
      dpow_mem := fun n hn j hj =>
        ⟨hJ j hj.2 hj.1 n hn _ (δ₀.factorial_mul_dpow_eq_pow hj.2),
          δ₀.dpow_mem hn hj.2⟩ }
  refine ⟨DividedPowers.Quotient.dividedPowers δ₀ hsub, rfl, fun k x y hx e => ?_⟩
  rw [DividedPowers.Quotient.dpow_apply δ₀ hsub hx]
  exact congrArg _ (hδ₀ k x y hx e)

end GlobalTheory.CompanionTheory.PdTF
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemRiemannRochSpaceIffRegularAtEverywhere
noncomputable section

open Matrix Classical PositivityTheory.Rg.Rs

namespace GlobalTheory.CompanionTheory.GLFirstBasisOrbit

variable {k : Type} [Field k] {n : ℕ}

theorem mem_gmap {N : ℕ} (g : GL (Fin N) k) (M : Submodule k (Fin N → k)) (x : Fin N → k) :
    x ∈ gmap g M ↔ (g⁻¹).val *ᵥ x ∈ M := by
  unfold gmap
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]
    exact hz
  · intro h
    refine ⟨_, h, ?_⟩
    rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec]

theorem smul_mem_gmap {N : ℕ} (g : GL (Fin N) k) (M : Submodule k (Fin N → k)) (x : Fin N → k) :
    g.val *ᵥ x ∈ gmap g M ↔ x ∈ M := by
  rw [mem_gmap, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem gmap_mul {N : ℕ} (g h : GL (Fin N) k) (M : Submodule k (Fin N → k)) :
    gmap (g * h) M = gmap g (gmap h M) := by
  ext x
  rw [mem_gmap, mem_gmap, mem_gmap, Matrix.mulVec_mulVec, ← Units.val_mul, _root_.mul_inv_rev]

theorem gmap_one {N : ℕ} (M : Submodule k (Fin N → k)) : gmap (1 : GL (Fin N) k) M = M := by
  ext x
  rw [mem_gmap, inv_one, Units.val_one, Matrix.one_mulVec]

theorem gmap_top {N : ℕ} (g : GL (Fin N) k) : gmap g ⊤ = ⊤ := by
  ext x
  simp [mem_gmap]

def gmapEquiv {N : ℕ} (g : GL (Fin N) k) : Submodule k (Fin N → k) ≃ Submodule k (Fin N → k) where
  toFun := gmap g
  invFun := gmap g⁻¹
  left_inv M := by rw [← gmap_mul, inv_mul_cancel, gmap_one]
  right_inv M := by rw [← gmap_mul, mul_inv_cancel, gmap_one]

theorem finrank_gmap {N : ℕ} (g : GL (Fin N) k) (M : Submodule k (Fin N → k)) :
    Module.finrank k (gmap g M) = Module.finrank k M := by
  have hinj : Function.Injective (Matrix.toLin' g.val) := by
    intro x y h
    have := congrArg (fun z => (g⁻¹).val *ᵥ z) h
    simpa [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← Units.val_mul] using this
  exact (Submodule.equivMapOfInjective _ hinj M).finrank_eq.symm

theorem first_basis_ne_zero : e0 k n ≠ 0 := by
  intro h
  have := congrFun h 0
  simp [e0] at this

theorem star_e0_dotProduct (x : Fin (n + 1) → k) : e0 k n ⬝ᵥ x = x 0 := by
  simp [e0]

theorem mem_riemannRochSpace_iff_regularAt_everywhere (x : Fin (n + 1) → k) : x ∈ H0 k n ↔ x 0 = 0 := by
  simp [H0]

theorem exists_GL_first_basis_eq (x : Fin (n + 1) → k) (hx : x ≠ 0) :
    ∃ g : GL (Fin (n + 1)) k, g.val *ᵥ e0 k n = x := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
  let A : Matrix (Fin (n + 1)) (Fin (n + 1)) k := (1 : Matrix _ _ k).updateCol i x
  have hA : A.det = x i := by
    have := Matrix.cramer_apply (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) x i
    rw [← show (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k).updateCol i x = A from rfl, ← this]
    simp
  let G : Matrix (Fin (n + 1)) (Fin (n + 1)) k := A.submatrix id (Equiv.swap 0 i)
  have hG : G.det ≠ 0 := by
    have := Matrix.det_permute' (Equiv.swap 0 i) A
    rw [show G = A.submatrix id (Equiv.swap 0 i) from rfl, this, hA]
    refine mul_ne_zero ?_ hi
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.swap (0 : Fin (n + 1)) i)) with h | h <;> rw [h] <;> simp
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero G hG, ?_⟩
  ext a
  simp [Matrix.GeneralLinearGroup.mkOfDetNeZero, e0, G, A]

theorem exists_gl_cov (a : Fin (n + 1) → k) (ha : a ≠ 0) :
    ∃ g : GL (Fin (n + 1)) k, ∀ x, a ⬝ᵥ (g.val *ᵥ x) = x 0 := by
  obtain ⟨h, hh⟩ := exists_GL_first_basis_eq a ha
  have hd : (h.val)ᵀ.det ≠ 0 := by
    rw [Matrix.det_transpose]
    exact (Matrix.isUnits_det_units h).ne_zero
  let T : GL (Fin (n + 1)) k := Matrix.GeneralLinearGroup.mkOfDetNeZero (h.val)ᵀ hd
  refine ⟨T⁻¹, fun x => ?_⟩
  have hT : T.val = (h.val)ᵀ := rfl
  have h1 : a = e0 k n ᵥ* T.val := by rw [hT, Matrix.vecMul_transpose, hh]
  rw [Matrix.dotProduct_mulVec, h1, Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel,
    Units.val_one, Matrix.vecMul_one, star_e0_dotProduct]

theorem mem_GL_image_hyperplane_iff (g : GL (Fin (n + 1)) k) (a : Fin (n + 1) → k)
    (h : ∀ x, a ⬝ᵥ (g.val *ᵥ x) = x 0) (z : Fin (n + 1) → k) :
    z ∈ gmap g (H0 k n) ↔ a ⬝ᵥ z = 0 := by
  rw [mem_gmap, mem_riemannRochSpace_iff_regularAt_everywhere, ← h ((g⁻¹).val *ᵥ z), Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.one_mulVec]

theorem exists_scalar_stabilizer_line (g : GL (Fin (n + 1)) k)
    (h : gmap g (Submodule.span k {e0 k n}) = Submodule.span k {e0 k n}) :
    ∃ s : k, s ≠ 0 ∧ g.val *ᵥ e0 k n = s • e0 k n := by
  have h1 : g.val *ᵥ e0 k n ∈ Submodule.span k {e0 k n} := by
    rw [← h, smul_mem_gmap]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp h1
  refine ⟨s, ?_, hs.symm⟩
  rintro rfl
  have h2 : g.val *ᵥ e0 k n = 0 := by rw [← hs, zero_smul]
  have h3 := congrArg (fun z => (g⁻¹).val *ᵥ z) h2
  simp only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec,
    Matrix.mulVec_zero] at h3
  exact first_basis_ne_zero h3

section Lat

variable {V Γ : Type} [AddCommGroup V] [Module ℂ V] [Group Γ]

def stabV (red : Γ →* GL (Fin (n + 1)) k) (ρ : Γ →* Module.End ℂ V) : Submodule ℂ V where
  carrier := {y | ∀ γ, gmap (red γ) (Submodule.span k {e0 k n}) = Submodule.span k {e0 k n} → ρ γ y = y}
  add_mem' := by
    intro a b ha hb γ h
    rw [map_add (f := _), ha γ h, hb γ h]
  zero_mem' := by
    intro γ _
    simp
  smul_mem' := by
    intro c a ha γ h
    rw [map_smul, ha γ h]

theorem mem_stabV (red : Γ →* GL (Fin (n + 1)) k) (ρ : Γ →* Module.End ℂ V) (y : V) :
    y ∈ stabV red ρ ↔
      ∀ γ, gmap (red γ) (Submodule.span k {e0 k n}) = Submodule.span k {e0 k n} → ρ γ y = y := Iff.rfl

variable [Fintype k]

def zx (v : Submodule k (Fin (n + 1) → k) → V) (x : Fin (n + 1) → k) (j : ℕ) : V :=
  ∑ M ∈ Finset.univ.filter (fun M : Submodule k (Fin (n + 1) → k) => x ∈ M ∧ Module.finrank k M + j = n + 1), v M

def IsCov (red : Γ →* GL (Fin (n + 1)) k) (gam : (Fin (n + 1) → k) → Γ) : Prop :=
  ∀ a, a ≠ 0 → ∀ x, a ⬝ᵥ ((red (gam a)).val *ᵥ x) = x 0

def uop (ρ : Γ →* Module.End ℂ V) (t : Module.End ℂ V) (gam : (Fin (n + 1) → k) → Γ) : Module.End ℂ V :=
  ∑ a ∈ Finset.univ.filter (fun a : Fin (n + 1) → k => a ⬝ᵥ e0 k n = 1), ρ (gam a) * t

end Lat

end GlobalTheory.CompanionTheory.GLFirstBasisOrbit
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MonomialCoefficientComparison
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MonomialCoefficientComparison
open Finset GlobalTheory.CompanionTheory.CoefId

namespace GlobalTheory.CompanionTheory.CoefId

theorem unitCircle_infinite : {z : ℂ | ‖z‖ = 1}.Infinite := by
  have hinj : Function.Injective (fun k : ℕ => ((1 + (k : ℂ) * Complex.I) / (1 - (k : ℂ) * Complex.I))) := by
    intro s t hst
    have h1 : ∀ k : ℕ, (1 - (k : ℂ) * Complex.I) ≠ 0 := by
      intro k h0
      have := congrArg Complex.re h0
      simp at this
    have h2 := (div_eq_div_iff (h1 s) (h1 t)).mp hst
    have h3 := congrArg Complex.im h2
    simp at h3
    have h4 : (s : ℝ) = t := by linarith
    exact_mod_cast h4
  refine Set.infinite_of_injective_forall_mem hinj fun k => ?_
  have h5 : ‖(1 + (k : ℂ) * Complex.I)‖ = ‖(1 - (k : ℂ) * Complex.I)‖ := by
    rw [← Complex.norm_conj (1 + (k : ℂ) * Complex.I)]
    simp [sub_eq_add_neg]
  have h6 : ‖(1 - (k : ℂ) * Complex.I)‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    intro h0
    have := congrArg Complex.re h0
    simp at this
  simp only [Set.mem_ofPred_eq, norm_div, h5]
  exact div_self h6

theorem poly_zero_of_torus {n : ℕ} (p : MvPolynomial (Fin n) ℂ)
    (h : ∀ z : Fin n → ℂ, (∀ a, ‖z a‖ = 1) → Function.Injective (fun a => z a ^ 2) →
      MvPolynomial.eval z p = 0) : p = 0 := by
  classical
  set D : MvPolynomial (Fin n) ℂ :=
    ∏ q ∈ prs n, (MvPolynomial.X q.1 ^ 2 - MvPolynomial.X q.2 ^ 2) with hD
  have hD0 : D ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun q hq => ?_
    have hlt : q.1 < q.2 := (mem_filter.mp hq).2
    intro h0
    have h1 : (MvPolynomial.X q.1 ^ 2 : MvPolynomial (Fin n) ℂ) = MvPolynomial.X q.2 ^ 2 :=
      sub_eq_zero.mp h0
    have := congrArg (MvPolynomial.eval (fun a => if a = q.1 then (1 : ℂ) else 0)) h1
    simp [hlt.ne'] at this
  have hz : p * D = 0 := by
    apply MvPolynomial.funext_set (fun _ => {z : ℂ | ‖z‖ = 1}) (fun _ => unitCircle_infinite)
    intro x hx
    have hx' : ∀ a, ‖x a‖ = 1 := fun a => hx a (Set.mem_univ a)
    rw [map_mul, map_zero]
    by_cases hi : Function.Injective (fun a => x a ^ 2)
    · rw [h x hx' hi, zero_mul]
    · obtain ⟨a, b, hab, hne⟩ : ∃ a b, x a ^ 2 = x b ^ 2 ∧ a ≠ b := by
        simpa [Function.Injective] using hi
      have : MvPolynomial.eval x D = 0 := by
        rw [hD, map_prod]
        rcases lt_or_gt_of_ne hne with hlt | hlt
        · exact Finset.prod_eq_zero (i := (a, b)) (by simp [prs, hlt]) (by simp [hab])
        · exact Finset.prod_eq_zero (i := (b, a)) (by simp [prs, hlt]) (by simp [hab])
      rw [this, mul_zero]
  exact (mul_eq_zero.mp hz).resolve_right hD0

theorem coeff_zero_of_torus {n : ℕ} (S : Finset (Fin n → ℤ)) (h : (Fin n → ℤ) → ℂ)
    (H : ∀ z : Fin n → ℂ, (∀ a, ‖z a‖ = 1) → Function.Injective (fun a => z a ^ 2) →
      ∑ m ∈ S, h m * mon m z = 0) : ∀ m ∈ S, h m = 0 := by
  classical
  set N : ℕ := ∑ m ∈ S, ∑ a, (m a).natAbs with hNdef
  have hN : ∀ m ∈ S, ∀ a, 0 ≤ m a + (N : ℤ) := by
    intro m hm a
    have h1 : (m a).natAbs ≤ ∑ a, (m a).natAbs :=
      Finset.single_le_sum (f := fun a => (m a).natAbs) (fun _ _ => Nat.zero_le _) (mem_univ a)
    have h2 : ∑ a, (m a).natAbs ≤ N :=
      Finset.single_le_sum (f := fun m : Fin n → ℤ => ∑ a, (m a).natAbs)
        (fun _ _ => Nat.zero_le _) hm
    have h3 : ((m a).natAbs : ℤ) ≤ N := by exact_mod_cast h1.trans h2
    have h4 : -((m a).natAbs : ℤ) ≤ m a := by
      have := abs_nonneg (m a)
      rw [Int.natCast_natAbs]
      exact neg_abs_le (m a)
    linarith
  let s : (Fin n → ℤ) → (Fin n →₀ ℕ) := fun m =>
    Finsupp.equivFunOnFinite.symm (fun a => (m a + (N : ℤ)).toNat)
  have hs : ∀ m ∈ S, ∀ a, ((s m a : ℕ) : ℤ) = m a + N := by
    intro m hm a
    simp only [s, Finsupp.equivFunOnFinite_symm_apply_apply]
    exact Int.toNat_of_nonneg (hN m hm a)
  have hinj : ∀ m ∈ S, ∀ m' ∈ S, s m = s m' → m = m' := by
    intro m hm m' hm' hss
    funext a
    have h1 := hs m hm a
    have h2 := hs m' hm' a
    rw [hss] at h1
    linarith
  have hp : (∑ m ∈ S, MvPolynomial.monomial (s m) (h m) : MvPolynomial (Fin n) ℂ) = 0 := by
    refine poly_zero_of_torus _ fun z hz hi => ?_
    have hz0 : ∀ a, z a ≠ 0 := by
      intro a h0
      have := hz a
      simp [h0] at this
    have hterm : ∀ m ∈ S, MvPolynomial.eval z (MvPolynomial.monomial (s m) (h m)) =
        (∏ a, z a ^ N) * (h m * mon m z) := by
      intro m hm
      rw [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), mon]
      have : ∀ a, z a ^ (s m a) = z a ^ N * z a ^ (m a) := by
        intro a
        rw [← zpow_natCast, hs m hm a, ← zpow_natCast, ← zpow_add₀ (hz0 a), add_comm]
      simp only [this, Finset.prod_mul_distrib]
      ring
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_congr rfl hterm, ← Finset.mul_sum, H z hz hi, mul_zero]
  intro m hm
  have h1 := congrArg (AddMonoidAlgebra.coeff · (s m)) hp
  rw [MvPolynomial.coeff_sum, Finset.sum_eq_single m] at h1
  · simpa [MvPolynomial.coeff_monomial] using h1
  · intro b hb hne
    rw [MvPolynomial.coeff_monomial, if_neg fun e => hne (hinj b hb m hm e)]
  · exact fun h' => absurd hm h'

theorem laurent_indep_torus {n : ℕ} {ι κ : Type} (I : Finset ι) (J : Finset κ) (f : ι → ℂ)
    (g : κ → ℂ) (e : ι → Fin n → ℤ) (e' : κ → Fin n → ℤ)
    (H : ∀ z : Fin n → ℂ, (∀ a, ‖z a‖ = 1) → Function.Injective (fun a => z a ^ 2) →
      ∑ i ∈ I, f i * mon (e i) z = ∑ j ∈ J, g j * mon (e' j) z) (m : Fin n → ℤ) :
    ∑ i ∈ I.filter (fun i => e i = m), f i = ∑ j ∈ J.filter (fun j => e' j = m), g j := by
  classical
  set S : Finset (Fin n → ℤ) := insert m (I.image e ∪ J.image e') with hS
  set h : (Fin n → ℤ) → ℂ := fun m => ∑ i ∈ I.filter (fun i => e i = m), f i -
    ∑ j ∈ J.filter (fun j => e' j = m), g j with hh
  have hI : ∀ i ∈ I, e i ∈ S := fun i hi =>
    mem_insert_of_mem (mem_union_left _ (mem_image_of_mem e hi))
  have hJ : ∀ j ∈ J, e' j ∈ S := fun j hj =>
    mem_insert_of_mem (mem_union_right _ (mem_image_of_mem e' hj))
  have key := coeff_zero_of_torus S h (fun z hz hi => by
    have h1 : ∑ i ∈ I, f i * mon (e i) z =
        ∑ m ∈ S, (∑ i ∈ I.filter (fun i => e i = m), f i) * mon m z := by
      rw [← Finset.sum_fiberwise_of_maps_to hI]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [(mem_filter.mp hi).2]
    have h2 : ∑ j ∈ J, g j * mon (e' j) z =
        ∑ m ∈ S, (∑ j ∈ J.filter (fun j => e' j = m), g j) * mon m z := by
      rw [← Finset.sum_fiberwise_of_maps_to hJ]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [(mem_filter.mp hj).2]
    simp only [hh, sub_mul, Finset.sum_sub_distrib]
    rw [← h1, ← h2, H z hz hi, sub_self]) m (mem_insert_self _ _)
  exact sub_eq_zero.mp key

end GlobalTheory.CompanionTheory.CoefId
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MonomialCoefficientComparisonStatement
open Finset GlobalTheory.CompanionTheory.CoefId
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monomial_coefficient_comparison : ∀ {n : ℕ} {ι κ : Type} (I : Finset ι) (J : Finset κ) (f : ι → ℂ) (g : κ → ℂ) (e : ι → Fin n → ℤ) (e' : κ → Fin n → ℤ), (∀ z : Fin n → ℂ, (∀ a, ‖z a‖ = 1) → Function.Injective (fun a => z a ^ 2) → ∑ i ∈ I, f i * mon (e i) z = ∑ j ∈ J, g j * mon (e' j) z) → ∀ m : Fin n → ℤ, ∑ i ∈ I.filter (fun i => e i = m), f i = ∑ j ∈ J.filter (fun j => e' j = m), g j := by
  first | exact @GlobalTheory.CompanionTheory.CoefId.laurent_indep_torus | exact GlobalTheory.CompanionTheory.CoefId.laurent_indep_torus | (intros; apply GlobalTheory.CompanionTheory.CoefId.laurent_indep_torus <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentiableAffLine
noncomputable section

open Filter Topology PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.RgEisGal

def aff (α β γ : ℝ) (l : ℂ × ℂ) : ℂ := (α : ℂ) * l.1 + (β : ℂ) * l.2 + (γ : ℂ)

def affR (α β γ : ℝ) (x : ℝ × ℝ) : ℝ := α * x.1 + β * x.2 + γ

def chg (α₁ β₁ γ₁ α₂ β₂ γ₂ : ℝ) (l : ℂ × ℂ) : ℂ × ℂ := (aff α₁ β₁ γ₁ l, aff α₂ β₂ γ₂ l)

def chgR (α₁ β₁ γ₁ α₂ β₂ γ₂ : ℝ) (x : ℝ × ℝ) : ℝ × ℝ := (affR α₁ β₁ γ₁ x, affR α₂ β₂ γ₂ x)

lemma aff_re (α β γ : ℝ) (l : ℂ × ℂ) : (aff α β γ l).re = affR α β γ (l.1.re, l.2.re) := by
  simp [aff, affR]

lemma aff_line (α β γ : ℝ) (p v : ℂ × ℂ) (τ : ℂ) :
    aff α β γ (p + τ • v) = aff α β γ p + τ * ((α : ℂ) * v.1 + (β : ℂ) * v.2) := by
  simp only [aff, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

lemma continuous_aff (α β γ : ℝ) : Continuous (aff α β γ) := by
  unfold aff; fun_prop

lemma continuous_affR (α β γ : ℝ) : Continuous (affR α β γ) := by
  unfold affR; fun_prop

lemma continuous_chg (α₁ β₁ γ₁ α₂ β₂ γ₂ : ℝ) : Continuous (chg α₁ β₁ γ₁ α₂ β₂ γ₂) :=
  (continuous_aff _ _ _).prodMk (continuous_aff _ _ _)

lemma continuous_chgR (α₁ β₁ γ₁ α₂ β₂ γ₂ : ℝ) : Continuous (chgR α₁ β₁ γ₁ α₂ β₂ γ₂) :=
  (continuous_affR _ _ _).prodMk (continuous_affR _ _ _)

lemma differentiable_aff_line (α β γ : ℝ) (p v : ℂ × ℂ) :
    Differentiable ℂ fun τ : ℂ => aff α β γ (p + τ • v) := by
  simp only [aff_line]
  fun_prop

lemma mem_tube_chg {Ω : Set (ℝ × ℝ)} {α₁ β₁ γ₁ α₂ β₂ γ₂ : ℝ} {l : ℂ × ℂ} :
    l ∈ tube (chgR α₁ β₁ γ₁ α₂ β₂ γ₂ ⁻¹' Ω) ↔ chg α₁ β₁ γ₁ α₂ β₂ γ₂ l ∈ tube Ω := by
  simp only [tube, Set.mem_setOf_eq, Set.mem_preimage, chg, chgR, aff_re]

lemma chg_line (α₁ β₁ γ₁ α₂ β₂ γ₂ : ℝ) (p v : ℂ × ℂ) (τ : ℂ) :
    chg α₁ β₁ γ₁ α₂ β₂ γ₂ (p + τ • v) = chg α₁ β₁ γ₁ α₂ β₂ γ₂ p +
      τ • ((α₁ : ℂ) * v.1 + (β₁ : ℂ) * v.2, (α₂ : ℂ) * v.1 + (β₂ : ℂ) * v.2) := by
  simp only [chg, aff_line]
  rfl

section Good

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

lemma lineHol_chg {F : ℂ × ℂ → X} {Ω : Set (ℝ × ℝ)} (hF : LineHol F (tube Ω))
    (α₁ β₁ γ₁ α₂ β₂ γ₂ : ℝ) :
    LineHol (fun l => F (chg α₁ β₁ γ₁ α₂ β₂ γ₂ l)) (tube (chgR α₁ β₁ γ₁ α₂ β₂ γ₂ ⁻¹' Ω)) := by
  intro p v
  have h := hF (chg α₁ β₁ γ₁ α₂ β₂ γ₂ p)
    ((α₁ : ℂ) * v.1 + (β₁ : ℂ) * v.2, (α₂ : ℂ) * v.1 + (β₂ : ℂ) * v.2)
  simp only [mem_tube_chg, chg_line]
  exact h

theorem TubeGood_chg {T : Type} [TopologicalSpace T] {F : ℂ × ℂ → T → X} {Ω : Set (ℝ × ℝ)}
    (hF : TubeGood F Ω) (α₁ β₁ γ₁ α₂ β₂ γ₂ : ℝ) :
    TubeGood (fun l g => F (chg α₁ β₁ γ₁ α₂ β₂ γ₂ l) g) (chgR α₁ β₁ γ₁ α₂ β₂ γ₂ ⁻¹' Ω) := by
  refine ⟨fun g => lineHol_chg (hF.hol g) _ _ _ _ _ _, ?_, ?_⟩
  · have hc : Continuous fun y : (ℂ × ℂ) × T => (chg α₁ β₁ γ₁ α₂ β₂ γ₂ y.1, y.2) :=
      ((continuous_chg _ _ _ _ _ _).comp continuous_fst).prodMk continuous_snd
    refine hF.cont.comp hc.continuousOn ?_
    rintro ⟨l, g⟩ ⟨hl, -⟩
    exact ⟨mem_tube_chg.1 hl, Set.mem_univ _⟩
  · intro C hC hCc g
    obtain ⟨U, hU, M, hM⟩ := hF.bdd (chgR α₁ β₁ γ₁ α₂ β₂ γ₂ '' C)
      (by rintro _ ⟨x, hx, rfl⟩; exact hC hx) (hCc.image (continuous_chgR _ _ _ _ _ _)) g
    refine ⟨U, hU, M, fun l hl g' hg' => hM _ ?_ g' hg'⟩
    have : (l.1.re, l.2.re) ∈ C := hl
    refine ⟨_, this, ?_⟩
    simp only [chg, chgR, aff_re]

lemma TubeGood_mono {T : Type} [TopologicalSpace T] {F : ℂ × ℂ → T → X} {Ω Ω' : Set (ℝ × ℝ)}
    (hF : TubeGood F Ω) (h : Ω' ⊆ Ω) : TubeGood F Ω' := by
  have ht : tube Ω' ⊆ tube Ω := fun l hl => h hl
  refine ⟨fun g p v => ?_, hF.cont.mono (Set.prod_mono ht subset_rfl),
    fun C hC => hF.bdd C (hC.trans h)⟩
  exact (hF.hol g p v).mono fun τ hτ => ht hτ

structure Fac (A : ℂ × ℂ → X) (Ω : Set (ℝ × ℝ)) : Prop where
  hol : LineHol A (tube Ω)
  cont : ContinuousOn A (tube Ω)
  bdd : ∀ C ⊆ Ω, IsCompact C → ∃ M : ℝ, ∀ l ∈ tube C, ‖A l‖ ≤ M

lemma exists_bounds {C : Set (ℝ × ℝ)} (hC : IsCompact C) (hne : C.Nonempty) (f : ℝ × ℝ → ℝ)
    (hf : Continuous f) : ∃ x ∈ C, ∃ y ∈ C, ∀ u ∈ C, f x ≤ f u ∧ f u ≤ f y := by
  obtain ⟨x, hx, hx'⟩ := hC.exists_isMinOn hne hf.continuousOn
  obtain ⟨y, hy, hy'⟩ := hC.exists_isMaxOn hne hf.continuousOn
  exact ⟨x, hx, y, hy, fun u hu => ⟨hx' hu, hy' hu⟩⟩

theorem Fac_left {f : ℂ → X} {a : ℝ} (hf : LeftGood f a) (α β γ : ℝ) {Ω : Set (ℝ × ℝ)}
    (h : ∀ x ∈ Ω, affR α β γ x < a) : Fac (fun l => f (aff α β γ l)) Ω := by
  have hre : ∀ l ∈ tube Ω, (aff α β γ l).re < a := fun l hl => by
    rw [aff_re]; exact h _ hl
  refine ⟨fun p v => ?_, ?_, fun C hC hCc => ?_⟩
  · refine hf.1.comp (differentiable_aff_line α β γ p v).differentiableOn ?_
    intro τ hτ
    exact hre _ hτ
  · exact hf.1.continuousOn.comp (continuous_aff _ _ _).continuousOn fun l hl => hre l hl
  · rcases C.eq_empty_or_nonempty with rfl | hne
    · exact ⟨0, fun l hl => hl.elim⟩
    · obtain ⟨x, -, y, hy, hxy⟩ := exists_bounds hCc hne _ (continuous_affR α β γ)
      obtain ⟨M, hM⟩ := hf.2 (affR α β γ x) (affR α β γ y) (h y (hC hy))
      refine ⟨M, fun l hl => hM _ ?_ ?_⟩
      · rw [aff_re]; exact (hxy _ hl).1
      · rw [aff_re]; exact (hxy _ hl).2

theorem Fac_strip {f : ℂ → X} (hf : StripEntire f) (α β γ : ℝ) (Ω : Set (ℝ × ℝ)) :
    Fac (fun l => f (aff α β γ l)) Ω := by
  refine ⟨fun p v => ?_, ?_, fun C _ hCc => ?_⟩
  · exact (hf.1.comp (differentiable_aff_line α β γ p v)).differentiableOn
  · exact (hf.1.continuous.comp (continuous_aff _ _ _)).continuousOn
  · rcases C.eq_empty_or_nonempty with rfl | hne
    · exact ⟨0, fun l hl => hl.elim⟩
    · obtain ⟨x, -, y, -, hxy⟩ := exists_bounds hCc hne _ (continuous_affR α β γ)
      obtain ⟨M, hM⟩ := hf.2 (affR α β γ x) (affR α β γ y)
      refine ⟨M, fun l hl => hM _ ?_ ?_⟩
      · rw [aff_re]; exact (hxy _ hl).1
      · rw [aff_re]; exact (hxy _ hl).2

theorem Fac_smul {f : ℂ × ℂ → ℂ} {A : ℂ × ℂ → X} {Ω : Set (ℝ × ℝ)} (hf : Fac f Ω) (hA : Fac A Ω) :
    Fac (fun l => f l • A l) Ω := by
  refine ⟨fun p v => (hf.hol p v).smul (hA.hol p v), hf.cont.smul hA.cont, fun C hC hCc => ?_⟩
  obtain ⟨M₁, h₁⟩ := hf.bdd C hC hCc
  obtain ⟨M₂, h₂⟩ := hA.bdd C hC hCc
  refine ⟨|M₁| * |M₂|, fun l hl => ?_⟩
  rw [norm_smul]
  exact mul_le_mul ((h₁ l hl).trans (le_abs_self _)) ((h₂ l hl).trans (le_abs_self _))
    (norm_nonneg _) (abs_nonneg _)

theorem Fac_mul {f f' : ℂ × ℂ → ℂ} {Ω : Set (ℝ × ℝ)} (hf : Fac f Ω) (hf' : Fac f' Ω) :
    Fac (fun l => f l * f' l) Ω :=
  Fac_smul hf hf'

theorem TubeGood_smul {T : Type} [TopologicalSpace T] {F : ℂ × ℂ → T → X} {Ω : Set (ℝ × ℝ)}
    {f : ℂ × ℂ → ℂ} (hf : Fac f Ω) (hF : TubeGood F Ω) :
    TubeGood (fun l g => f l • F l g) Ω := by
  refine ⟨fun g p v => (hf.hol p v).smul (hF.hol g p v), ?_, fun C hC hCc g => ?_⟩
  · refine ContinuousOn.smul (hf.cont.comp continuousOn_fst ?_) hF.cont
    rintro ⟨l, g⟩ ⟨hl, -⟩
    exact hl
  · obtain ⟨M₁, h₁⟩ := hf.bdd C hC hCc
    obtain ⟨U, hU, M₂, h₂⟩ := hF.bdd C hC hCc g
    refine ⟨U, hU, |M₁| * |M₂|, fun l hl g' hg' => ?_⟩
    rw [norm_smul]
    exact mul_le_mul ((h₁ l hl).trans (le_abs_self _)) ((h₂ l hl g' hg').trans (le_abs_self _))
      (norm_nonneg _) (abs_nonneg _)

end Good

section Comp

variable {E₁ E₂ E₃ : Type} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [NormedAddCommGroup E₂]
  [NormedSpace ℂ E₂] [NormedAddCommGroup E₃] [NormedSpace ℂ E₃]

theorem Fac_comp {A : ℂ × ℂ → E₂ →L[ℂ] E₃} {B : ℂ × ℂ → E₁ →L[ℂ] E₂} {Ω : Set (ℝ × ℝ)}
    (hA : Fac A Ω) (hB : Fac B Ω) : Fac (fun l => (A l).comp (B l)) Ω := by
  refine ⟨fun p v => (hA.hol p v).clm_comp (hB.hol p v), hA.cont.clm_comp hB.cont,
    fun C hC hCc => ?_⟩
  obtain ⟨M₁, h₁⟩ := hA.bdd C hC hCc
  obtain ⟨M₂, h₂⟩ := hB.bdd C hC hCc
  refine ⟨|M₁| * |M₂|, fun l hl => (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_⟩
  exact mul_le_mul ((h₁ l hl).trans (le_abs_self _)) ((h₂ l hl).trans (le_abs_self _))
    (norm_nonneg _) (abs_nonneg _)

theorem TubeGood_comp {T : Type} [TopologicalSpace T] {F : ℂ × ℂ → T → E₂ →L[ℂ] E₃}
    {A : ℂ × ℂ → E₁ →L[ℂ] E₂} {Ω : Set (ℝ × ℝ)} (hF : TubeGood F Ω) (hA : Fac A Ω) :
    TubeGood (fun l g => (F l g).comp (A l)) Ω := by
  refine ⟨fun g p v => (hF.hol g p v).clm_comp (hA.hol p v), ?_, fun C hC hCc g => ?_⟩
  · refine ContinuousOn.clm_comp hF.cont (hA.cont.comp continuousOn_fst ?_)
    rintro ⟨l, g⟩ ⟨hl, -⟩
    exact hl
  · obtain ⟨U, hU, M₁, h₁⟩ := hF.bdd C hC hCc g
    obtain ⟨M₂, h₂⟩ := hA.bdd C hC hCc
    refine ⟨U, hU, |M₁| * |M₂|, fun l hl g' hg' =>
      (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_⟩
    exact mul_le_mul ((h₁ l hl g' hg').trans (le_abs_self _)) ((h₂ l hl).trans (le_abs_self _))
      (norm_nonneg _) (abs_nonneg _)

end Comp

end GlobalTheory.CompanionTheory.RgEisGal
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommutatorCoerciveOnAnnihilator
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommutatorCoerciveOnAnnihilator
open Finset Matrix PositivityTheory.RgHe.Frame

namespace GlobalTheory.CompanionTheory.RgHeFrame

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

theorem hs_eq_frobenius_sq {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) :
    Formalism.REAL.hs A = ‖A‖ ^ 2 := by
  have h0 : 0 ≤ ∑ i, ∑ j, ‖A i j‖ ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity
  rw [Matrix.frobenius_norm_def]
  simp only [Real.rpow_two]
  rw [← Real.sqrt_eq_rpow, Real.sq_sqrt h0]
  rfl

theorem hs_le_commutator {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) (v : Fin m → ℂ)
    (h : ∀ A : Matrix (Fin m) (Fin m) ℂ, A * X = X * A → A *ᵥ v = 0 → A = 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ A : Matrix (Fin m) (Fin m) ℂ, A *ᵥ v = 0 →
      Formalism.REAL.hs A ≤ c * Formalism.REAL.hs (A * X - X * A) := by
  let Φ : Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ × (Fin m → ℂ) :=
    { toFun := fun A => (A * X - X * A, A *ᵥ v)
      map_add' := fun A B => by
        ext1
        · simp only [Prod.fst_add, add_mul, mul_add]; abel
        · simp only [Prod.snd_add, Matrix.add_mulVec]
      map_smul' := fun a A => by
        ext1
        · simp [smul_sub]
        · simp [Matrix.smul_mulVec] }
  have hker : LinearMap.ker Φ = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro A hA
    have h1 : A * X - X * A = 0 := congrArg Prod.fst hA
    have h2 : A *ᵥ v = 0 := congrArg Prod.snd hA
    exact h A (sub_eq_zero.mp h1) h2
  obtain ⟨K, hK, hanti⟩ := LinearMap.exists_antilipschitzWith Φ hker
  refine ⟨(K : ℝ) ^ 2, by positivity, fun A hA => ?_⟩
  have hle : ‖A‖ ≤ K * ‖A * X - X * A‖ := by
    have h3 := hanti.le_mul_dist A 0
    rw [map_zero, dist_zero_right, dist_zero_right] at h3
    have h4 : ‖Φ A‖ = ‖A * X - X * A‖ := by
      change ‖((A * X - X * A, A *ᵥ v) : Matrix (Fin m) (Fin m) ℂ × (Fin m → ℂ))‖ = _
      rw [hA, Prod.norm_def]
      simp
    rwa [h4] at h3
  rw [hs_eq_frobenius_sq, hs_eq_frobenius_sq, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) hle 2

end GlobalTheory.CompanionTheory.RgHeFrame
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CommutatorCoerciveOnAnnihilatorStatement
open Finset Matrix PositivityTheory.RgHe.Frame
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commutator_coercive_on_annihilator : ∀ {m : ℕ} (X : Matrix (Fin m) (Fin m) ℂ) (v : Fin m → ℂ), (∀ A : Matrix (Fin m) (Fin m) ℂ, A * X = X * A → A *ᵥ v = 0 → A = 0) → ∃ c : ℝ, 0 < c ∧ ∀ A : Matrix (Fin m) (Fin m) ℂ, A *ᵥ v = 0 → Formalism.REAL.hs A ≤ c * Formalism.REAL.hs (A * X - X * A) := by
  first | exact @GlobalTheory.CompanionTheory.RgHeFrame.hs_le_commutator | exact GlobalTheory.CompanionTheory.RgHeFrame.hs_le_commutator | (intros; apply GlobalTheory.CompanionTheory.RgHeFrame.hs_le_commutator <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoeFnSumAe
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsTailRest
theorem UpperTheory.Reformulated.B.Yxa1.main :
    ∀ {α : Type} [inst : MeasurableSpace α] {ν : MeasureTheory.Measure α} {ι : Type} (s : Finset ι)
      (g : ι → ↥(MeasureTheory.Lp ℂ (2 : ENNReal) ν)),
      (↑(↑(∑ j ∈ s, g j) : α →ₘ[ν] ℂ) : α → ℂ) =ᵐ[ν] fun (x : α) ↦ ∑ j ∈ s, (↑(↑(g j) : α →ₘ[ν] ℂ) : α → ℂ) x := by
  intro α _ ν ι s g
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact MeasureTheory.Lp.coeFn_zero ℂ 2 ν
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    filter_upwards [MeasureTheory.Lp.coeFn_add (g a) (∑ j ∈ s, g j), ih] with x hx hx'
    rw [hx, Pi.add_apply, hx']
end

open MeasureTheory
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.OpEx

open PositivityTheory.Rg.BcB.E1

theorem coeFn_sum_ae {α : Type} [MeasurableSpace α] {ν : Measure α} {ι : Type} (s : Finset ι)
    (g : ι → Lp ℂ 2 ν) :
    ((∑ j ∈ s, g j : Lp ℂ 2 ν) : α → ℂ) =ᵐ[ν] fun x => ∑ j ∈ s, (g j : α → ℂ) x :=
  _root_.UpperTheory.Reformulated.B.Yxa1.main s g

theorem opExA : KerBasic → RowInt → SchurOp → OpExA := by
  intro hK hR hS X ι _ Φ hΦ
  classical
  haveI : SFinite X.ν := by unfold Ctx.ν; infer_instance
  have hex : ∀ i j, ∃ T : Lp ℂ 2 X.ν →L[ℂ] Lp ℂ 2 X.ν, ∀ f, (T f : X.G → ℂ) =ᵐ[X.ν]
      fun x => ∫ y, ker X.Γ (Φ i j) x y * (f : X.G → ℂ) y ∂X.ν := by
    intro i j
    obtain ⟨A, hA, h1, h2⟩ := hR X (Φ i j) (hΦ i j)
    have hc := (hK X (Φ i j) (hΦ i j)).2.1
    exact hS X.G X.ν (ker X.Γ (Φ i j)) A hc.measurable hA h1 h2
  choose S hSop using hex
  let T : X.Hs ι →L[ℂ] X.Hs ι :=
    ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : ι => Lp ℂ 2 X.ν)).symm :
        (ι → Lp ℂ 2 X.ν) →L[ℂ] X.Hs ι) ∘L
      ContinuousLinearMap.pi fun i => ∑ j, (S i j).comp (PiLp.proj 2 (fun _ : ι => Lp ℂ 2 X.ν) j)
  have hT : ∀ f i, T f i = ∑ j, S i j (f j) := by
    intro f i
    simp [T, ContinuousLinearMap.sum_apply]
  have hIs : X.IsOp Φ T := by
    intro f i
    rw [hT]
    have hall : ∀ᵐ x ∂X.ν, ∀ j, (S i j (f j) : X.G → ℂ) x =
        ∫ y, ker X.Γ (Φ i j) x y * (f j : X.G → ℂ) y ∂X.ν :=
      ae_all_iff.2 fun j => hSop i j (f j)
    filter_upwards [coeFn_sum_ae Finset.univ (fun j => S i j (f j)), hall] with x h1 h2
    rw [h1]
    exact Finset.sum_congr rfl fun j _ => h2 j
  refine ⟨T, hIs, ?_⟩
  intro T' hT'
  ext f : 1
  refine PiLp.ext fun i => Lp.ext ?_
  exact (hT' f i).trans (hIs f i).symm

end GlobalTheory.CompanionTheory.OpEx
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueUpperUnipotentLift
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueUpperUnipotentLift
open Matrix GlobalTheory.CompanionTheory.Jp

namespace GlobalTheory.CompanionTheory.Jp

theorem tauM_val_blocks {L : Type} [Field L] {n : ℕ} (w : Lˣ) :
    ((tauM (n := n) w : GL (Ix n) L) : Matrix (Ix n) (Ix n) L) =
      fromBlocks 1 0 0 ((w : L) • (1 : Matrix (Fin n) (Fin n) L)) := by
  ext i k
  rcases i with i | i <;> rcases k with k | k <;>
    simp [tauM, pM, scM, Matrix.one_apply, Matrix.diagonal_apply]

theorem twist_low : ∀ (O L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field L] [Algebra O L] [IsFractionRing O L]
    (n : ℕ) (ϖ : O), Irreducible ϖ → ∀ w : Lˣ, (w : L) = algebraMap O L ϖ →
    ∀ x : GL (Ix n) (IsLocalRing.ResidueField O), x.1.toBlocks₁₂ = 0 →
      ∃ j j' : GL (Ix n) O, inL j * tauM w = tauM w * inL j' ∧ resK j' = x := by
  intro O L _ _ _ _ _ _ n ϖ hϖ w hw x hx
  classical
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : IsLocalRing.ResidueField O → O, ∀ a, IsLocalRing.residue O (ℓ a) = a :=
    ⟨Function.surjInv IsLocalRing.residue_surjective, Function.surjInv_eq _⟩
  have hmapℓ : ∀ B : Matrix (Fin n) (Fin n) (IsLocalRing.ResidueField O),
      (B.map ℓ).map (IsLocalRing.residue O) = B := by
    intro B
    ext i k
    simp [hℓ]
  obtain ⟨A, hA⟩ : ∃ A, A = x.1.toBlocks₁₁.map ℓ := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C, C = x.1.toBlocks₂₁.map ℓ := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D, D = x.1.toBlocks₂₂.map ℓ := ⟨_, rfl⟩
  have hred : (fromBlocks A 0 C D).map (IsLocalRing.residue O) = x.1 := by
    rw [Matrix.fromBlocks_map, hA, hC, hD, hmapℓ, hmapℓ, hmapℓ,
      Matrix.map_zero _ (map_zero _), ← hx, Matrix.fromBlocks_toBlocks]
  have hdet : IsUnit (A.det * D.det) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    have h1 : IsLocalRing.residue O (A.det * D.det) = x.1.det := by
      rw [← Matrix.det_fromBlocks_zero₁₂ A C D, RingHom.map_det, RingHom.mapMatrix_apply, hred]
    rw [h1]
    exact ((Matrix.isUnit_iff_isUnit_det _).mp x.isUnit).ne_zero
  let j' : GL (Ix n) O := Matrix.nonsingInvUnit (fromBlocks A 0 C D)
    (by rw [Matrix.det_fromBlocks_zero₁₂]; exact hdet)
  let j : GL (Ix n) O := Matrix.nonsingInvUnit (fromBlocks A 0 (ϖ • C) D)
    (by rw [Matrix.det_fromBlocks_zero₁₂]; exact hdet)
  refine ⟨j, j', ?_, ?_⟩
  · apply Units.ext
    rw [Units.val_mul, Units.val_mul, tauM_val_blocks]
    show (fromBlocks A 0 (ϖ • C) D).map (algebraMap O L) * _ =
      _ * (fromBlocks A 0 C D).map (algebraMap O L)
    rw [Matrix.fromBlocks_map, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply]
    congr 1
    · simp
    · simp
    · ext i k
      simp [hw, Matrix.map_apply, Matrix.smul_apply]
      rw [Algebra.smul_def]
    · ext i k
      simp [hw]
  · apply Units.ext
    exact hred

end GlobalTheory.CompanionTheory.Jp
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ResidueUpperUnipotentLiftStatement
open Matrix GlobalTheory.CompanionTheory.Jp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residue_upper_unipotent_lift : ∀ (O L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field L] [Algebra O L] [IsFractionRing O L]
    (n : ℕ) (ϖ : O), Irreducible ϖ → ∀ w : Lˣ, (w : L) = algebraMap O L ϖ →
    ∀ x : GL (Ix n) (IsLocalRing.ResidueField O), x.1.toBlocks₁₂ = 0 →
      ∃ j j' : GL (Ix n) O, inL j * tauM w = tauM w * inL j' ∧ resK j' = x := by
  first | exact @GlobalTheory.CompanionTheory.Jp.twist_low | exact GlobalTheory.CompanionTheory.Jp.twist_low | (intros; apply GlobalTheory.CompanionTheory.Jp.twist_low <;> assumption)
end
end
