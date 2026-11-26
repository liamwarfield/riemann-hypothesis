module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralWittLatticeBasis
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotentialPhiSub

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaThroughOfPoly
noncomputable section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

namespace GlobalTheory.PassPoly

theorem aeval_mem_of_stable {L M : Type} [Field L] [AddCommGroup M] [Module L M] (f : Module.End L M)
    (D : Submodule L M) (hD : ∀ x ∈ D, f x ∈ D) (p : L[X]) : ∀ x ∈ D, Polynomial.aeval f p x ∈ D := by
  induction p using Polynomial.induction_on with
  | C a => intro x hx; simpa [Module.algebraMap_end_apply] using D.smul_mem a hx
  | add p q hp hq => intro x hx; simpa using D.add_mem (hp x hx) (hq x hx)
  | monomial n a ih =>
    intro x hx
    have := ih _ (hD x hx)
    rw [pow_succ, ← mul_assoc, map_mul, Module.End.mul_apply, Polynomial.aeval_X]
    exact this

section
variable {G : Type} [Group G] {Qp K₀ K K₀' K' : Type} [Field Qp] [Field K₀] [Field K]
    [Field K₀'] [Field K']
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    [Algebra Qp K₀'] [Algebra Qp K'] [Algebra K₀' K'] [IsScalarTower Qp K₀' K']
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra K₀' B] [IsScalarTower Qp K₀' B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    [Algebra K₀' BdR] [Algebra K' BdR] [IsScalarTower Qp K' BdR]
    [IsScalarTower K₀' K' BdR] [IsScalarTower Qp K₀' BdR]
    (PC : PotCrysData G Qp K₀ K K₀' K' B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem actVB_mul' (g h : G) (x : V ⊗[Qp] B) :
    actVB PC.PD ρ (g * h) x = actVB PC.PD ρ g (actVB PC.PD ρ h x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem actVB_one' (x : V ⊗[Qp] B) : actVB PC.PD ρ 1 x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem actVB_resH (h : PC.H) (x : V ⊗[Qp] B) :
    actVB PC.PD' (PC.resH ρ) h x = actVB PC.PD ρ (h : G) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB, PotCrysData.resH, PC.actB_eq]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem mem_Dpcris_iff (x : V ⊗[Qp] B) :
    x ∈ PC.Dpcris ρ ↔ ∀ g ∈ PC.H, actVB PC.PD ρ g x = x := by
  simp only [PotCrysData.Dpcris, Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.id_apply, sub_eq_zero, actVB_resH, Subtype.forall]

theorem Dpcris_stable (g : G) : ∀ x ∈ PC.Dpcris ρ, actVB PC.PD ρ g x ∈ PC.Dpcris ρ := by
  intro x hx
  rw [mem_Dpcris_iff] at hx ⊢
  intro h hh
  have h1 : g⁻¹ * h * g ∈ PC.H := by simpa using PC.normal.conj_mem h hh g⁻¹
  rw [← actVB_mul', show h * g = g * (g⁻¹ * h * g) by group, actVB_mul', hx _ h1]

end

end GlobalTheory.PassPoly

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaThroughOfPolyPow
noncomputable section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module TensorProduct GlobalTheory.Pass

namespace GlobalTheory.PassPolyPow

theorem aeval_mul_apply {L M : Type} [Field L] [AddCommGroup M] [Module L M] (f : Module.End L M)
    (p q : L[X]) (x : M) : Polynomial.aeval f (p * q) x = Polynomial.aeval f p (Polynomial.aeval f q x) := by
  rw [map_mul, Module.End.mul_apply]

theorem eigen_of_pow_of_separable {L M : Type} [Field L] [AddCommGroup M] [Module L M] (f : Module.End L M)
    (c : L) (m : ℕ) (r : L[X]) (hr : r.Separable) (x : M)
    (h1 : Polynomial.aeval f ((X - C c) ^ m) x = 0) (h2 : Polynomial.aeval f r x = 0) :
    Polynomial.aeval f (X - C c) x = 0 := by
  obtain ⟨t, hrt, hnd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd r hr.ne_zero c
  have hle := Polynomial.rootMultiplicity_le_one_of_separable hr c
  have hcop : IsCoprime ((X - C c) ^ m) t :=
    ((Polynomial.irreducible_X_sub_C c).coprime_iff_not_dvd.2 hnd).pow_left
  obtain ⟨A, B', hAB⟩ := hcop
  have hs : ∃ s : L[X], (X - C c) * t = s * r := by
    interval_cases hj : r.rootMultiplicity c
    · exact ⟨X - C c, by rw [hrt]; ring⟩
    · exact ⟨1, by rw [hrt]; ring⟩
  obtain ⟨s, hs⟩ := hs
  have : (X - C c) = (A * (X - C c)) * (X - C c) ^ m + (B' * s) * r := by
    rw [mul_assoc (B') s r, ← hs]
    linear_combination (-(X - C c)) * hAB
  rw [this, map_add (f := _), LinearMap.add_apply, aeval_mul_apply, h1, map_zero, aeval_mul_apply, h2, map_zero, add_zero]

theorem mem_iSup_eigen_pow {L M ι : Type} [Field L] [AddCommGroup M] [Module L M] (f : Module.End L M)
    (D : Submodule L M) (hD : ∀ x ∈ D, f x ∈ D) (r : L[X]) (hr : r.Separable)
    (hrD : ∀ x ∈ D, Polynomial.aeval f r x = 0) (c : ι → L) (m : ℕ) (s : Finset ι) :
    (∀ a ∈ s, ∀ b ∈ s, c a = c b → a = b) → ∀ d ∈ D,
      Polynomial.aeval f ((∏ a ∈ s, (X - C (c a))) ^ m) d = 0 →
      d ∈ ⨆ a ∈ s, (D ⊓ LinearMap.ker (f - c a • LinearMap.id)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro _ d _ h
    simp at h
    simp [h]
  | insert a t hat ih =>
    intro hinj d hd h
    rw [Finset.prod_insert hat, mul_pow] at h
    have hcop : IsCoprime ((X - C (c a)) ^ m) ((∏ b ∈ t, (X - C (c b))) ^ m) := by
      refine IsCoprime.pow (IsCoprime.prod_right fun b hb => ?_)
      refine Polynomial.isCoprime_X_sub_C_of_isUnit_sub (IsUnit.mk0 _ (sub_ne_zero.2 fun e => hat ?_))
      rw [hinj a (Finset.mem_insert_self _ _) b (Finset.mem_insert_of_mem hb) e]
      exact hb
    obtain ⟨u, v, huv⟩ := hcop
    set Q := (∏ b ∈ t, (X - C (c b))) ^ m with hQ
    have hdec : d = Polynomial.aeval f (u * (X - C (c a)) ^ m) d + Polynomial.aeval f (v * Q) d := by
      rw [← LinearMap.add_apply, ← map_add (f := _), huv, map_one, Module.End.one_apply]
    rw [Finset.iSup_insert, hdec, add_comm]
    refine Submodule.add_mem_sup ?_ ?_
    · have hmem := GlobalTheory.PassPoly.aeval_mem_of_stable f D hD (v * Q) d hd
      refine ⟨hmem, ?_⟩
      have h1 : Polynomial.aeval f ((X - C (c a)) ^ m) (Polynomial.aeval f (v * Q) d) = 0 := by
        rw [← aeval_mul_apply, show (X - C (c a)) ^ m * (v * Q) = v * ((X - C (c a)) ^ m * Q) by ring,
          aeval_mul_apply, h, map_zero]
      have := eigen_of_pow_of_separable f (c a) m r hr _ h1 (hrD _ hmem)
      simpa [Module.algebraMap_end_apply] using this
    · refine ih (fun x hx y hy => hinj x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy)) _
        (GlobalTheory.PassPoly.aeval_mem_of_stable f D hD _ d hd) ?_
      rw [← aeval_mul_apply, show Q * (u * (X - C (c a)) ^ m) = u * ((X - C (c a)) ^ m * Q) by ring,
        aeval_mul_apply, h, map_zero]

section
variable {G : Type} [Group G] {Qp K₀ K K₀' K' : Type} [Field Qp] [Field K₀] [Field K]
    [Field K₀'] [Field K']
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    [Algebra Qp K₀'] [Algebra Qp K'] [Algebra K₀' K'] [IsScalarTower Qp K₀' K']
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra K₀' B] [IsScalarTower Qp K₀' B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    [Algebra K₀' BdR] [Algebra K' BdR] [IsScalarTower Qp K' BdR]
    [IsScalarTower K₀' K' BdR] [IsScalarTower Qp K₀' BdR]
    (PC : PotCrysData G Qp K₀ K K₀' K' B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem actVB_pow (g : G) (n : ℕ) (x : V ⊗[Qp] B) :
    (actVB PC.PD ρ g ^ n) x = actVB PC.PD ρ (g ^ n) x := by
  induction n generalizing x with
  | zero => simp [GlobalTheory.PassPoly.actVB_one']
  | succ n ih => rw [pow_succ, Module.End.mul_apply, ih, pow_succ, GlobalTheory.PassPoly.actVB_mul']

theorem aeval_index_kill (g : G) : ∀ x ∈ PC.Dpcris ρ,
    Polynomial.aeval (actVB PC.PD ρ g) (X ^ PC.H.index - C (1 : LL)) x = 0 := by
  intro x hx
  haveI := PC.normal
  have hg : g ^ PC.H.index ∈ PC.H := Subgroup.pow_index_mem PC.H g
  simp only [map_sub, map_pow, Polynomial.aeval_X, map_one, LinearMap.sub_apply, Module.End.one_apply]
  rw [actVB_pow, (GlobalTheory.PassPoly.mem_Dpcris_iff PC ρ x).1 hx _ hg, sub_self]

theorem separable_index [CharZero LL] : (X ^ PC.H.index - C (1 : LL)).Separable := by
  haveI := PC.finiteIndex
  exact Polynomial.separable_X_pow_sub_C 1 (Nat.cast_ne_zero.2 Subgroup.FiniteIndex.index_ne_zero) one_ne_zero

theorem inertiaThrough_of_poly_pow [CharZero LL] (Sig : Finset (PC.Iner →* LLˣ))
    (h1 : ∀ a ∈ Sig, ∀ g : PC.Iner, (g : G) ∈ PC.H → a g = 1)
    (h2 : ∀ a ∈ Sig, Nat.Coprime (orderOf a) PC.PD.p)
    (h3 : ∀ (g : PC.Iner), ∃ m : ℕ, ∀ d ∈ PC.Dpcris ρ, (Polynomial.aeval (actVB PC.PD ρ (g : G))
      ((∏ a ∈ Sig, (X - C ((a g : LLˣ) : LL))) ^ m)) d = 0)
    (h4 : ∃ γ : PC.Iner, (∀ a ∈ Sig, ∀ b ∈ Sig, a γ = b γ → a = b) ∧
      ∀ g : PC.Iner, ∃ (n : ℕ) (u : PC.Iner), (∀ a ∈ Sig, a u = 1) ∧ g = γ ^ n * u) :
    PC.InertiaThrough ρ Sig := by

  have htriv : ∀ u : PC.Iner, (∀ a ∈ Sig, a u = 1) → ∀ x ∈ PC.Dpcris ρ,
      actVB PC.PD ρ (u : G) x = x := by
    intro u hu x hx
    obtain ⟨m, hm⟩ := h3 u
    have hprod : (∏ a ∈ Sig, (X - C ((a u : LLˣ) : LL))) ^ m = (X - C (1 : LL)) ^ (Sig.card * m) := by
      rw [Finset.prod_congr rfl (fun a ha => by rw [hu a ha, Units.val_one]), Finset.prod_const, pow_mul]
    have hk := hm x hx
    rw [hprod] at hk
    have := eigen_of_pow_of_separable _ 1 _ _ (separable_index PC) x hk (aeval_index_kill PC ρ _ x hx)
    simpa [Module.algebraMap_end_apply, sub_eq_zero] using this
  refine ⟨h1, h2, le_antisymm ?_ ?_⟩
  · obtain ⟨γ, hsep, hgen⟩ := h4
    intro d hd
    obtain ⟨m, hm⟩ := h3 γ
    have := mem_iSup_eigen_pow (actVB PC.PD ρ (γ : G)) (PC.Dpcris ρ) (GlobalTheory.PassPoly.Dpcris_stable PC ρ γ)
      _ (separable_index PC) (aeval_index_kill PC ρ _)
      (fun a : PC.Iner →* LLˣ => ((a γ : LLˣ) : LL)) m Sig
      (fun a ha b hb e => hsep a ha b hb (Units.ext e)) d hd (hm d hd)
    refine (iSup₂_mono (fun a ha => ?_) : _ ≤ ⨆ a ∈ Sig, PC.Eig ρ PC.Iner a) this
    rintro x ⟨hx, hx'⟩
    refine ⟨hx, ?_⟩
    have hγ : actVB PC.PD ρ (γ : G) x = ((a γ : LLˣ) : LL) • x := by
      simpa [sub_eq_zero] using hx'
    have hn : ∀ n : ℕ, actVB PC.PD ρ ((γ : G) ^ n) x = ((a γ : LLˣ) : LL) ^ n • x := by
      intro n
      induction n with
      | zero => simp [GlobalTheory.PassPoly.actVB_one']
      | succ n ih => rw [pow_succ, GlobalTheory.PassPoly.actVB_mul', hγ, map_smul, ih, smul_smul, pow_succ, mul_comm]
    simp only [Submodule.coe_iInf, Set.mem_iInter, SetLike.mem_coe, LinearMap.mem_ker,
      LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    intro g
    obtain ⟨n, u, hu, rfl⟩ := hgen g
    rw [map_mul, hu a ha, mul_one, map_pow, Subgroup.coe_mul, Subgroup.coe_pow, GlobalTheory.PassPoly.actVB_mul',
      htriv u hu x hx, hn, Units.val_pow_eq_pow_val]
  · exact iSup₂_le fun a _ => inf_le_left

end

theorem main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K K' LL : FinExt l) (h : K.1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : ↥(GK K)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (P.PD K).actB g (algebraMap ↥(K0 K') P.R.B c) = algebraMap ↥(K0 K') P.R.B c') (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (Sig : Finset ((pc P h hN hF hS).Iner →* (↥LL.1)ˣ)), (∀ a ∈ Sig, ∀ g : (pc P h hN hF hS).Iner, (g : ↥(GK K)) ∈ (pc P h hN hF hS).H → a g = 1) → (∀ a ∈ Sig, Nat.Coprime (orderOf a) l) → (∀ (g : (pc P h hN hF hS).Iner), ∃ m : ℕ, ∀ d ∈ (pc P h hN hF hS).Dpcris ρ, (Polynomial.aeval (actVB (P.PD K) ρ (g : ↥(GK K))) ((∏ a ∈ Sig, (X - C ((a g : (↥LL.1)ˣ) : ↥LL.1))) ^ m)) d = 0) → (∃ γ : (pc P h hN hF hS).Iner, (∀ a ∈ Sig, ∀ b ∈ Sig, a γ = b γ → a = b) ∧ ∀ g : (pc P h hN hF hS).Iner, ∃ (n : ℕ) (u : (pc P h hN hF hS).Iner), (∀ a ∈ Sig, a u = 1) ∧ g = γ ^ n * u) → (pc P h hN hF hS).InertiaThrough ρ Sig := by
  intro l _ P K K' LL h hN hF hS V _ _ _ _ ρ Sig h1 h2 h3 h4
  haveI : CharZero ↥LL.1 := charZero_of_injective_algebraMap (algebraMap ℚ_[l] ↥LL.1).injective
  refine inertiaThrough_of_poly_pow (pc P h hN hF hS) ρ Sig h1 ?_ h3 h4
  have hp : (pc P h hN hF hS).PD.p = l := P.PD_p K
  rw [hp]
  exact h2

end GlobalTheory.PassPolyPow

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRootsOfUnityCharacterHom
namespace GlobalTheory

theorem exists_rootsOfUnity_character_hom : ∀ {Γ F O LL : Type} [Group Γ] [Field F] [CommRing O] [Field LL] (n : ℕ), 0 < n → ∀ (f : F → Γ → ℂ), (∀ x, x ≠ 0 → f x 1 = 1) → (∀ x, x ≠ 0 → ∀ σ σ', f x (σ * σ') = f x σ * f x σ') → (∀ x y, x ≠ 0 → y ≠ 0 → ∀ σ, f (x * y) σ = f x σ * f y σ) → ∀ (ι : O →+* ℂ), Function.Injective ι → ∀ (ζ : O), IsPrimitiveRoot ζ n → ∀ (t : O →+* LL), ∃ Ψ : ↥(rootsOfUnity n F) →* (Γ →* LLˣ), ∀ (u : ↥(rootsOfUnity n F)) (σ : Γ), ∃ o : O, ι o = f (((u : Fˣ)) : F) σ ∧ ((Ψ u σ : LLˣ) : LL) = t o := by
  intro Γ F O LL _ _ _ _ n hn f hone hmul hx ι hι ζ hζ t
  haveI : NeZero n := ⟨hn.ne'⟩
  have h1 : ∀ σ, f 1 σ = 1 := by
    intro σ
    have hne : f 1 σ ≠ 0 := by
      intro h
      have := hmul 1 one_ne_zero σ σ⁻¹
      rw [mul_inv_cancel, hone 1 one_ne_zero, h, zero_mul] at this
      exact one_ne_zero this
    have := hx 1 1 one_ne_zero one_ne_zero σ
    rw [mul_one] at this
    exact (mul_left_cancel₀ hne (by rw [mul_one]; exact this)).symm
  have hpow : ∀ x, x ≠ 0 → ∀ σ (k : ℕ), f (x ^ k) σ = f x σ ^ k := by
    intro x hx0 σ k
    induction k with
    | zero => simp [h1]
    | succ k ih => rw [pow_succ, hx _ _ (pow_ne_zero k hx0) hx0, ih, pow_succ]
  have hex : ∀ (u : rootsOfUnity n F) (σ : Γ), ∃ o : O, ι o = f ((u : Fˣ) : F) σ := by
    intro u σ
    have hu : (((u : Fˣ) : F)) ^ n = 1 := by
      have := u.2
      rw [mem_rootsOfUnity'] at this
      exact this
    have h2 : f ((u : Fˣ) : F) σ ^ n = 1 := by
      rw [← hpow _ (Units.ne_zero _), hu, h1]
    obtain ⟨j, -, hj⟩ := (hζ.map_of_injective hι).eq_pow_of_pow_eq_one h2
    exact ⟨ζ ^ j, by rw [map_pow, hj]⟩
  choose o ho using hex
  let g : rootsOfUnity n F → (Γ →* LL) := fun u =>
    { toFun := fun σ => t (o u σ)
      map_one' := by
        have : o u 1 = 1 := hι (by rw [ho, map_one, hone _ (Units.ne_zero _)])
        rw [this, map_one]
      map_mul' := by
        intro a b
        have : o u (a * b) = o u a * o u b :=
          hι (by rw [map_mul, ho, ho, ho, hmul _ (Units.ne_zero _)])
        rw [this, map_mul] }
  refine ⟨MonoidHom.mk' (fun u => (g u).toHomUnits) ?_, fun u σ => ⟨o u σ, ho u σ, rfl⟩⟩
  intro u v
  ext σ
  have : o (u * v) σ = o u σ * o v σ :=
    hι (by
      rw [map_mul, ho, ho, ho, Subgroup.coe_mul, Units.val_mul,
        hx _ _ (Units.ne_zero _) (Units.ne_zero _)])
  show t (o (u * v) σ) = t (o u σ) * t (o v σ)
  rw [this, map_mul]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsExtendCharacterTrivialOnNormal
namespace GlobalTheory

private lemma char_eq_of_same_coset {G M : Type} [Group G] [CommGroup M]
    (Ik H : Subgroup G) (ψ : ↥Ik →* M) (hψ : ∀ s : ↥Ik, (s : G) ∈ H → ψ s = 1)
    (g s t : G) (hs : s ∈ Ik) (ht : t ∈ Ik) (h1 : s⁻¹ * g ∈ H) (h2 : t⁻¹ * g ∈ H) :
    ψ ⟨s, hs⟩ = ψ ⟨t, ht⟩ := by
  have hmem : ((⟨s, hs⟩⁻¹ * ⟨t, ht⟩ : ↥Ik) : G) ∈ H := by
    have h3 : s⁻¹ * t = (s⁻¹ * g) * (t⁻¹ * g)⁻¹ := by group
    have h5 : s⁻¹ * t ∈ H := by
      rw [h3]
      exact H.mul_mem h1 (H.inv_mem h2)
    exact h5
  have h4 := hψ _ hmem
  rw [map_mul, map_inv, inv_mul_eq_one] at h4
  exact h4

theorem exists_extend_character_trivial_on_normal {G M : Type} [Group G] [CommGroup M]
    (I Ik H : Subgroup G) (hH : H.Normal) (hdec : ∀ g ∈ I, ∃ s ∈ Ik, s⁻¹ * g ∈ H)
    (ψ : ↥Ik →* M) (hψ : ∀ s : ↥Ik, (s : G) ∈ H → ψ s = 1) :
    ∃ χ : ↥I →* M, ∀ (g : ↥I) (s : G) (hs : s ∈ Ik), s⁻¹ * (g : G) ∈ H → χ g = ψ ⟨s, hs⟩ := by
  classical
  choose f hfIk hfH using hdec
  have key := char_eq_of_same_coset Ik H ψ hψ
  refine ⟨{ toFun := fun g => ψ ⟨f g g.2, hfIk g g.2⟩, map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · show ψ ⟨f _ _, _⟩ = 1
    rw [key _ _ 1 _ Ik.one_mem (hfH _ _) (by simp)]
    exact map_one ψ
  · intro a b
    show ψ ⟨f _ _, _⟩ = ψ ⟨f _ _, _⟩ * ψ ⟨f _ _, _⟩
    have hab : (f a a.2 * f b b.2)⁻¹ * ((a * b : ↥I) : G) ∈ H := by
      show (f a a.2 * f b b.2)⁻¹ * ((a : G) * b) ∈ H
      have hc := hH.conj_mem _ (hfH a a.2) (f b b.2)⁻¹
      have he : (f a a.2 * f b b.2)⁻¹ * ((a : G) * b)
          = ((f b b.2)⁻¹ * ((f a a.2)⁻¹ * a) * (f b b.2)⁻¹⁻¹) * ((f b b.2)⁻¹ * b) := by group
      rw [he]
      exact H.mul_mem hc (hfH b b.2)
    rw [key ((a * b : ↥I) : G) _ (f a a.2 * f b b.2) _ (Ik.mul_mem (hfIk a a.2) (hfIk b b.2))
      (hfH _ _) hab]
    exact map_mul ψ ⟨f a a.2, hfIk a a.2⟩ ⟨f b b.2, hfIk b b.2⟩
  · intro g s hs hsg
    exact key g _ s _ hs (hfH g g.2) hsg

theorem extend_characters_and_generator : ∀ {G F LL : Type} [Group G] [Field F] [Field LL] (I Ik H : Subgroup G), H.Normal → Ik ≤ I → (∀ g ∈ I, ∃ s ∈ Ik, s⁻¹ * g ∈ H) → ∀ (n : ℕ), 0 < n → ∀ (Ψ : ↥(rootsOfUnity n F) →* (↥Ik →* LLˣ)) (Y : Set F), (∀ y ∈ Y, ∃ u : ↥(rootsOfUnity n F), ((u : Fˣ) : F) = y) → (∀ u : ↥(rootsOfUnity n F), ((u : Fˣ) : F) ∈ Y → ∀ s : ↥Ik, (s : G) ∈ H → Ψ u s = 1) → ∃ ch : F → (↥I →* LLˣ), (∀ u : ↥(rootsOfUnity n F), ((u : Fˣ) : F) ∈ Y → ∀ (g : ↥I) (s : G) (hs : s ∈ Ik), s⁻¹ * (g : G) ∈ H → ch ((u : Fˣ) : F) g = Ψ u ⟨s, hs⟩) ∧ ∃ c : ↥I →* LLˣ, (∀ g, c g ^ n = 1) ∧ ∀ y ∈ Y, ∃ k : ℕ, ∀ g, ch y g = c g ^ k := by
  intro G F LL _ _ _ I Ik H hH _ hdec n hn Ψ Y hY hΨ
  classical
  have : NeZero n := ⟨hn.ne'⟩
  let K : Subgroup ↥(rootsOfUnity n F) :=
    { carrier := {u | ∀ s : ↥Ik, (s : G) ∈ H → Ψ u s = 1}
      mul_mem' := fun {a b} ha hb s hs => by
        simp only [Set.mem_ofPred_eq] at ha hb
        rw [map_mul, MonoidHom.mul_apply, ha s hs, hb s hs, mul_one]
      one_mem' := fun s _ => by rw [map_one, MonoidHom.one_apply]
      inv_mem' := fun {a} ha s hs => by
        simp only [Set.mem_ofPred_eq] at ha
        rw [map_inv, MonoidHom.inv_apply, ha s hs, inv_one] }
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := ↥K)
  obtain ⟨c, hc⟩ := exists_extend_character_trivial_on_normal I Ik H hH hdec
    (Ψ (ζ : ↥(rootsOfUnity n F))) (fun s hs => ζ.2 s hs)
  have hk : ∀ y ∈ Y, ∃ k : ℕ, ∀ u : ↥(rootsOfUnity n F), ((u : Fˣ) : F) = y →
      (ζ : ↥(rootsOfUnity n F)) ^ k = u := by
    intro y hy
    obtain ⟨u₀, hu₀⟩ := hY y hy
    have hK : u₀ ∈ K := hΨ u₀ (hu₀ ▸ hy)
    obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers (x := ζ) (y := ⟨u₀, hK⟩)).mpr (hζ _)
    refine ⟨k, fun u hu => ?_⟩
    have hu' : u = u₀ := Subtype.ext (Units.ext (hu.trans hu₀.symm))
    rw [hu']
    have := congrArg (fun v : ↥K => (v : ↥(rootsOfUnity n F))) hk
    simpa using this
  choose! kk hkk using hk
  have hpow : (ζ : ↥(rootsOfUnity n F)) ^ n = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, OneMemClass.coe_one]
    exact (mem_rootsOfUnity n _).mp (ζ : ↥(rootsOfUnity n F)).2
  refine ⟨fun y => c ^ kk y, ?_, c, ?_, ?_⟩
  · intro u hu g s hs hsg
    show (c ^ kk ((u : Fˣ) : F)) g = Ψ u ⟨s, hs⟩
    rw [MonoidHom.pow_apply, hc g s hs hsg, ← MonoidHom.pow_apply, ← map_pow,
      hkk _ hu u rfl]
  · intro g
    obtain ⟨s, hs, hsg⟩ := hdec g g.2
    rw [hc g s hs hsg, ← MonoidHom.pow_apply, ← map_pow, hpow, map_one, MonoidHom.one_apply]
  · intro y _
    exact ⟨kk y, fun g => MonoidHom.pow_apply c (kk y) g⟩

end GlobalTheory
end

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
open Formalism.MainNotions.PairedCharacterCondition Polynomial

noncomputable section
namespace GlobalTheory.InertiaChars

theorem IK_le_iner : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K K' : FinExt l) (h : K.1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : ↥(GK K)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (P.PD K).actB g (algebraMap ↥(K0 K') P.R.B c) = algebraMap ↥(K0 K') P.R.B c'), IK K ≤ (pc P h hN hF hS).Iner := by
  intro l _ P K K' h hN hF hS g hg c
  have hfix := GlobalTheory.BKGal.UnitModel.fix_Kur hg
  have hc : (c : Om l) ∈ MaximalUnramifiedExtension l := (IntermediateField.mem_inf.1 c.2).2
  show (P.PD K).actB g (algebraMap ↥(K0 K') P.R.B c) = algebraMap ↥(K0 K') P.R.B c
  rw [P.PD_actB]
  exact P.actQ_Kur (g : GQ l) ⟨c, hc⟩ ⟨c, hc⟩ ((IntermediateField.mem_fixingSubgroup_iff _ _).1 hfix c hc)

theorem coprime_orderOf : ∀ (l : ℕ) [Fact l.Prime] {F : Type} [Field F] [CharP F l] (y : Fˣ) (n : ℕ), 0 < n → y ^ n = 1 → Nat.Coprime (orderOf y) l := by
  intro l hl F _ _ y n hn hy
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hl.out]
  rintro ⟨M, hM⟩
  have hpos : 0 < orderOf y := orderOf_pos_iff.2 (isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, hy⟩)
  have hz : (y ^ M) ^ l = 1 := by rw [← pow_mul, mul_comm, ← hM, pow_orderOf_eq_one]
  have h1 : ((y ^ M : Fˣ) : F) ^ l = 1 := by rw [← Units.val_pow_eq_pow_val, hz, Units.val_one]
  have h2 : (((y ^ M : Fˣ) : F) - 1) ^ l = 0 := by rw [sub_pow_char, h1, one_pow, sub_self]
  have h3 : ((y ^ M : Fˣ) : F) = 1 := sub_eq_zero.1 (pow_eq_zero_iff hl.out.ne_zero |>.1 h2)
  have hz1 : y ^ M = 1 := Units.ext h3
  have hMpos : 0 < M := Nat.pos_of_mul_pos_left (hM ▸ hpos)
  have hdvd := Nat.le_of_dvd hMpos (orderOf_dvd_of_pow_eq_one hz1)
  have hl2 := hl.out.two_le
  rw [hM] at hdvd
  nlinarith

theorem exists_gen : ∀ {G F : Type} [Group G] [Field F] (I : Subgroup G) (c : ↥I →* Fˣ) (n : ℕ), 0 < n → (∀ g, c g ^ n = 1) → ∀ (Sig : Finset (↥I →* Fˣ)), (∀ a ∈ Sig, ∃ k : ℕ, ∀ g, a g = c g ^ k) → ∃ γ : ↥I, (∀ a ∈ Sig, ∀ b ∈ Sig, a γ = b γ → a = b) ∧ ∀ g : ↥I, ∃ (m : ℕ) (u : ↥I), (∀ a ∈ Sig, a u = 1) ∧ g = γ ^ m * u := by
  intro G F _ _ I c n hn hc Sig hSig
  haveI : NeZero n := ⟨hn.ne'⟩
  have hle : c.range ≤ rootsOfUnity n F := by
    rintro _ ⟨g, rfl⟩
    rw [mem_rootsOfUnity]
    exact hc g
  haveI : Finite c.range := Finite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  haveI : IsCyclic c.range := isCyclic_of_injective_ringHom ((Units.coeHom F).comp c.range.subtype)
    (fun x y hxy => Subtype.ext (Units.ext hxy))
  obtain ⟨x, hx⟩ := IsCyclic.exists_monoid_generator (α := c.range)
  obtain ⟨γ, hγ⟩ := x.2
  have hgen : ∀ g, ∃ m : ℕ, c g = c γ ^ m := by
    intro g
    obtain ⟨m, hm⟩ := Submonoid.mem_powers_iff _ _ |>.1 (hx ⟨c g, g, rfl⟩)
    refine ⟨m, ?_⟩
    have := congrArg Subtype.val hm
    rw [SubmonoidClass.coe_pow, ← hγ] at this
    exact this.symm
  refine ⟨γ, fun a ha b hb hab => ?_, fun g => ?_⟩
  · obtain ⟨ka, hka⟩ := hSig a ha
    obtain ⟨kb, hkb⟩ := hSig b hb
    ext1 g
    obtain ⟨m, hm⟩ := hgen g
    rw [hka g, hkb g, hm, ← pow_mul, ← pow_mul, mul_comm m ka, mul_comm m kb, pow_mul, pow_mul, ← hka γ,
      ← hkb γ, hab]
  · obtain ⟨m, hm⟩ := hgen g
    refine ⟨m, (γ ^ m)⁻¹ * g, fun a ha => ?_, by rw [mul_inv_cancel_left]⟩
    obtain ⟨k, hk⟩ := hSig a ha
    rw [hk, map_mul, map_inv, map_pow, hm, inv_mul_cancel, one_pow]

open TensorProduct

section Helpers
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem actVB_mul (g g' : G) (x : V ⊗[Qp] B) :
    actVB PD ρ (g * g') x = actVB PD ρ g (actVB PD ρ g' x) := by
  induction x using TensorProduct.inductionOn with
  | tmul v b => simp [actVB]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem actVB_one (x : V ⊗[Qp] B) : actVB PD ρ 1 x = x := by
  induction x using TensorProduct.inductionOn with
  | tmul v b => simp [actVB]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem actVB_pow (g : G) (n : ℕ) (x : V ⊗[Qp] B) :
    actVB PD ρ (g ^ n) x = (actVB PD ρ g ^ n) x := by
  induction n with
  | zero => simp [actVB_one]
  | succ n ih => rw [pow_succ', actVB_mul, ih, pow_succ', mul_apply_eq_comp]

theorem aeval_actVB (g : G) (q : LL[X]) {N : ℕ} (hN : q.natDegree < N) (x : V ⊗[Qp] B) :
    (aeval (actVB PD ρ g) q) x = ∑ n ∈ Finset.range N, q.coeff n • actVB PD ρ (g ^ n) x := by
  rw [aeval_eq_sum_range' hN, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [LinearMap.smul_apply, actVB_pow]

end Helpers

theorem aeval_eq_of_mem_Dpcris {G : Type} [Group G] {Qp K₀ K K₀' K' : Type} [Field Qp] [Field K₀] [Field K]
    [Field K₀'] [Field K']
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    [Algebra Qp K₀'] [Algebra Qp K'] [Algebra K₀' K'] [IsScalarTower Qp K₀' K']
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra K₀' B] [IsScalarTower Qp K₀' B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    [Algebra K₀' BdR] [Algebra K' BdR] [IsScalarTower Qp K' BdR]
    [IsScalarTower K₀' K' BdR] [IsScalarTower Qp K₀' BdR]
    (PC : PotCrysData G Qp K₀ K K₀' K' B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V) (g s : G) (hgs : s⁻¹ * g ∈ PC.H) (q : LL[X]) (x : V ⊗[Qp] B)
    (hx : x ∈ PC.Dpcris ρ) :
    (aeval (actVB PC.PD ρ g) q) x = (aeval (actVB PC.PD ρ s) q) x := by
  have hpow : ∀ n : ℕ, actVB PC.PD ρ (g ^ n) x = actVB PC.PD ρ (s ^ n) x ∧
      actVB PC.PD ρ (s ^ n) x ∈ PC.Dpcris ρ := by
    intro n
    induction n with
    | zero => exact ⟨by rw [pow_zero, pow_zero], by rw [pow_zero, actVB_one]; exact hx⟩
    | succ n ih =>
      have hy := ih.2
      have e1 : actVB PC.PD ρ g (actVB PC.PD ρ (s ^ n) x) = actVB PC.PD ρ s (actVB PC.PD ρ (s ^ n) x) := by
        rw [show g = s * (s⁻¹ * g) by group, actVB_mul,
          (GlobalTheory.PassPoly.mem_Dpcris_iff PC ρ _).1 hy _ hgs]
      refine ⟨?_, ?_⟩
      · rw [pow_succ', actVB_mul, ih.1, e1, ← actVB_mul, ← pow_succ']
      · rw [pow_succ', actVB_mul]
        exact GlobalTheory.PassPoly.Dpcris_stable PC ρ s _ hy
  rw [aeval_actVB PC.PD ρ g q (Nat.lt_succ_self _), aeval_actVB PC.PD ρ s q (Nat.lt_succ_self _)]
  exact Finset.sum_congr rfl fun n _ => by rw [(hpow n).1]

theorem prod_dvd_pow {R α β : Type} [CommRing R] [DecidableEq β] (M : Multiset α) (Sig : Finset β)
    (f : α → R) (v : β → R) (h : ∀ y ∈ M, ∃ a ∈ Sig, f y = v a) :
    (M.map fun y => X - C (f y)).prod ∣ (∏ a ∈ Sig, (X - C (v a))) ^ Multiset.card M := by
  induction M using Multiset.induction_on with
  | empty => simp
  | cons y M ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ']
    obtain ⟨a, ha, hya⟩ := h y (Multiset.mem_cons_self y M)
    refine mul_dvd_mul ?_ (ih fun z hz => h z (Multiset.mem_cons_of_mem hz))
    rw [hya]
    exact Finset.dvd_prod_of_mem (fun a => X - C (v a)) ha


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 200000 in
open Classical in
theorem main : ∀ (D : D7) (P : Pend D), TieInePoly D → InertEq D → ∀ (i : D.nd.Loc) (k : Fin 2), D.nd.l i = D.host.g k →
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (Y : Finset (Fb (D.host.g k) (D.host.g_prime k))), (∀ y ∈ Y, y ≠ 0 ∧ y ^ D.what₂.restRowsFiniteGroupCard = 1) →
  ∀ (K' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).Kw.1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex)
    (hS : ∀ (g : ↥(GK (D.nbr i w hw).Kw)) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'),
      ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).actB g (algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c) =
        algebraMap ↥(K0 K') (D.loc (D.nd.l i)).R.B c'),
  (∀ y ∈ Y, ∀ g ∈ GKin h,
      (((D.nbr i w hw).e.symm g : Gw D.nd w) : GE D.nd) ∈ Ine (F := D.host.E) (D.nd.plOm.1 w) →
        P.om k w y (((D.nbr i w hw).e.symm g : Gw D.nd w) : GE D.nd) = 1) →
  ∃ ch : Fb (D.host.g k) (D.host.g_prime k) → ((pc (D.loc (D.nd.l i)) h hN hF hS).Iner →* (Br.LL D.nbr i w hw)ˣ),
    ∀ S : Finset (Fb (D.host.g k) (D.host.g_prime k)), S ⊆ Y → ∀ (m : ℕ) (R : GE D.nd →* GL (Fin m) (D.nd.O i)),
      Continuous (fun g => ((R g : GL (Fin m) (D.nd.O i)) : Matrix (Fin m) (Fin m) (D.nd.O i))) →
      (pc (D.loc (D.nd.l i)) h hN hF hS).IsPotCrys ((D.nbr i w hw).rep (R.comp (decS D.nd w))) →
      ∀ M : Multiset (Fb (D.host.g k) (D.host.g_prime k)), (∀ y ∈ M, y ∈ S) →
      (∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w),
        D.naut.inePol (D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) R) w) σ =
          (M.map fun y => X - C (P.om k w y σ)).prod) →
      (pc (D.loc (D.nd.l i)) h hN hF hS).InertiaThrough ((D.nbr i w hw).rep (R.comp (decS D.nd w))) (S.image ch) := by
  intro D P hTie hIE i k hik w hw Y hY K' h hN hF hS hH
  have hn : 0 < D.what₂.restRowsFiniteGroupCard := D.what₂.restRowsFiniteGroupCard_pos
  haveI : NeZero D.what₂.restRowsFiniteGroupCard := ⟨hn.ne'⟩
  have hιinj : Function.Injective (iotaO D.nd D.naut i) :=
    (((D.naut.iotaQC i).toRingHom.comp (D.naut.iotaQ i)).injective).comp
      (IsFractionRing.injective (D.nd.O i) (FractionRing (D.nd.O i)))
  obtain ⟨ζ, hζ⟩ := P.zetaPrimitiveRoot i

  let ιg : ↥(GK (D.nbr i w hw).Kw) →* GE D.nd := (decS D.nd w).comp (D.nbr i w hw).e.symm.toMonoidHom
  have hιg : ∀ s, ιg s = (((D.nbr i w hw).e.symm s : Gw D.nd w) : GE D.nd) := fun s => rfl
  have hIne : ∀ s ∈ IK (D.nbr i w hw).Kw, ιg s ∈ Ine (F := D.host.E) (D.nd.plOm.1 w) := by
    intro s hs
    rw [← hIE i w hw] at hs
    exact hs
  obtain ⟨Ψ, hΨ⟩ := GlobalTheory.exists_rootsOfUnity_character_hom (Γ := ↥(IK (D.nbr i w hw).Kw)) (F := Fb (D.host.g k) (D.host.g_prime k))
    (LL := ↥(D.nbr i w hw).LL.1) D.what₂.restRowsFiniteGroupCard hn (fun x s => P.om k w x (ιg s))
    (fun x hx => by simpa using P.om_one k w x hx)
    (fun x hx s s' => by
      simpa using P.om_mul k w x hx _ (hIne s s.2) _ (hIne s' s'.2))
    (fun x y hx hy s => P.tameInertiaChar_mul_root k w x y hx hy _ (hIne s s.2))
    (iotaO D.nd D.naut i) hιinj ζ hζ (D.nbr i w hw).toLL

  have hdec : ∀ g ∈ (pc (D.loc (D.nd.l i)) h hN hF hS).Iner, ∃ s ∈ IK (D.nbr i w hw).Kw, s⁻¹ * g ∈ GKin h :=
    fun g hg => GlobalTheory.InertiaDecomp.iner_decomp _ (D.loc (D.nd.l i)) _ K' h hN hF hS g hg
  have hYu : ∀ y ∈ (Y : Set (Fb (D.host.g k) (D.host.g_prime k))),
      ∃ u : ↥(rootsOfUnity D.what₂.restRowsFiniteGroupCard (Fb (D.host.g k) (D.host.g_prime k))),
        ((u : (Fb (D.host.g k) (D.host.g_prime k))ˣ) : Fb (D.host.g k) (D.host.g_prime k)) = y := by
    intro y hy
    obtain ⟨hy0, hyn⟩ := hY y hy
    refine ⟨⟨Units.mk0 y hy0, ?_⟩, rfl⟩
    rw [mem_rootsOfUnity]; exact Units.ext (by simpa using hyn)
  have hYH : ∀ u : ↥(rootsOfUnity D.what₂.restRowsFiniteGroupCard (Fb (D.host.g k) (D.host.g_prime k))),
      ((u : (Fb (D.host.g k) (D.host.g_prime k))ˣ) : Fb (D.host.g k) (D.host.g_prime k)) ∈
        (Y : Set (Fb (D.host.g k) (D.host.g_prime k))) →
      ∀ s : ↥(IK (D.nbr i w hw).Kw), (s : ↥(GK (D.nbr i w hw).Kw)) ∈ GKin h → Ψ u s = 1 := by
    intro u hu s hs
    obtain ⟨o, ho, ho'⟩ := hΨ u s
    have h1 : P.om k w ((u : (Fb (D.host.g k) (D.host.g_prime k))ˣ) : Fb (D.host.g k) (D.host.g_prime k)) (ιg s) = 1 :=
      hH _ hu s hs (hIne s s.2)
    have h2 : o = 1 := hιinj (by rw [ho, map_one]; exact h1)
    exact Units.ext (by rw [ho', h2, map_one]; rfl)
  have X8 := GlobalTheory.extend_characters_and_generator (G := ↥(GK (D.nbr i w hw).Kw)) (F := Fb (D.host.g k) (D.host.g_prime k)) (LL := ↥(D.nbr i w hw).LL.1) (pc (D.loc (D.nd.l i)) h hN hF hS).Iner (IK (D.nbr i w hw).Kw) (GKin h) hN (IK_le_iner _ (D.loc (D.nd.l i)) _ K' h hN hF hS) hdec D.what₂.restRowsFiniteGroupCard hn Ψ (Y : Set (Fb (D.host.g k) (D.host.g_prime k))) hYu hYH
  obtain ⟨ch, hch, c, hc, hck⟩ := X8
  refine ⟨ch, fun S hSY m R hcont hpot M hMS hPol => ?_⟩
  have hSu : ∀ y ∈ S, ∃ u : ↥(rootsOfUnity D.what₂.restRowsFiniteGroupCard (Fb (D.host.g k) (D.host.g_prime k))),
      ((u : (Fb (D.host.g k) (D.host.g_prime k))ˣ) : Fb (D.host.g k) (D.host.g_prime k)) = y ∧
      ((u : (Fb (D.host.g k) (D.host.g_prime k))ˣ) : Fb (D.host.g k) (D.host.g_prime k)) ∈
        (Y : Set (Fb (D.host.g k) (D.host.g_prime k))) := by
    intro y hy
    obtain ⟨u, hu⟩ := hYu y (hSY hy)
    exact ⟨u, hu, hu ▸ hSY hy⟩

  have G1 : ∀ a ∈ S.image ch, ∀ g : (pc (D.loc (D.nd.l i)) h hN hF hS).Iner,
      (g : ↥(GK (D.nbr i w hw).Kw)) ∈ (pc (D.loc (D.nd.l i)) h hN hF hS).H → a g = 1 := by
    intro a ha g hg
    refine Exists.elim (Finset.mem_image.1 ha) fun y hy => ?_
    refine Exists.elim (hSu y hy.1) fun u hu => ?_
    rw [← hy.2, ← hu.1, hch u hu.2 g 1 (IK (D.nbr i w hw).Kw).one_mem (by rw [inv_one, one_mul]; exact hg)]
    exact map_one (Ψ u)
  have G2 : ∀ a ∈ S.image ch, Nat.Coprime (orderOf a) (D.nd.l i) := by
    intro a ha
    refine Exists.elim (Finset.mem_image.1 ha) fun y hy => ?_
    refine Exists.elim (hSu y hy.1) fun u hu => ?_
    have hu1 : u ^ orderOf (u : (Fb (D.host.g k) (D.host.g_prime k))ˣ) = 1 :=
      Subtype.ext (by rw [SubmonoidClass.coe_pow, pow_orderOf_eq_one]; rfl)
    have hpow : a ^ orderOf (u : (Fb (D.host.g k) (D.host.g_prime k))ˣ) = 1 := by
      ext g
      refine Exists.elim (hdec g g.2) fun s hs => ?_
      rw [MonoidHom.pow_apply, ← hy.2, ← hu.1, hch u hu.2 g s hs.1 hs.2, ← MonoidHom.pow_apply, ← map_pow, hu1,
        map_one]
      rfl
    have hchar : CharP (Fb (D.host.g k) (D.host.g_prime k)) (D.host.g k) := by
      haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      infer_instance
    have hcop := @coprime_orderOf (D.host.g k) ⟨D.host.g_prime k⟩ _ _ hchar
      (u : (Fb (D.host.g k) (D.host.g_prime k))ˣ) D.what₂.restRowsFiniteGroupCard hn ((mem_rootsOfUnity _ _).1 u.2)
    have hc2 := Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hpow) hcop
    rwa [← hik] at hc2

  have G4 := exists_gen (G := ↥(GK (D.nbr i w hw).Kw)) (F := ↥(D.nbr i w hw).LL.1) (pc (D.loc (D.nd.l i)) h hN hF hS).Iner c D.what₂.restRowsFiniteGroupCard hn hc (S.image ch) (fun a ha => by
    refine Exists.elim (Finset.mem_image.1 ha) fun y hy => ?_
    rw [← hy.2]
    exact hck y (hSY hy.1))
  have G3 : ∀ g : (pc (D.loc (D.nd.l i)) h hN hF hS).Iner, ∃ m' : ℕ,
      ∀ d ∈ (pc (D.loc (D.nd.l i)) h hN hF hS).Dpcris ((D.nbr i w hw).rep (R.comp (decS D.nd w))),
        (aeval (actVB ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw) ((D.nbr i w hw).rep (R.comp (decS D.nd w)))
          (g : ↥(GK (D.nbr i w hw).Kw)))
          ((∏ a ∈ S.image ch, (X - C ((a g : (↥(D.nbr i w hw).LL.1)ˣ) : ↥(D.nbr i w hw).LL.1))) ^ m')) d = 0 := by
    intro g
    refine ⟨Multiset.card M, fun d hd => ?_⟩
    refine Exists.elim (hdec g g.2) fun s hs => ?_
    have hσ := hIne s hs.1
    have hO : ∀ y ∈ M, ∃ o : D.nd.O i, iotaO D.nd D.naut i o = P.om k w y (ιg s) ∧
        ((ch y g : (↥(D.nbr i w hw).LL.1)ˣ) : ↥(D.nbr i w hw).LL.1) = (D.nbr i w hw).toLL o := by
      intro y hy
      refine Exists.elim (hSu y (hMS y hy)) fun u hu => ?_
      refine Exists.elim (hΨ u ⟨s, hs.1⟩) fun o ho => ?_
      refine ⟨o, by rw [ho.1, hu.1], ?_⟩
      rw [← hu.1, hch u hu.2 g s hs.1 hs.2, ho.2]
    choose! o ho using hO
    have hpmap : ((M.map fun y => X - C (o y)).prod).map (iotaO D.nd D.naut i) =
        D.naut.inePol (D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) R) w) (ιg s) := by
      rw [hPol _ hσ, Polynomial.map_multiset_prod, Multiset.map_map]
      congr 1
      refine Multiset.map_congr rfl fun y hy => ?_
      simp only [Function.comp_apply, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, (ho y hy).1]
    have hT := hTie i w hw K' h hN hF hS m R hcont hpot ((D.nbr i w hw).e.symm s) hσ _ hpmap d hd
    have hq : ((M.map fun y => X - C (o y)).prod).map (D.nbr i w hw).toLL =
        (M.map fun y => X - C ((ch y g : (↥(D.nbr i w hw).LL.1)ˣ) : ↥(D.nbr i w hw).LL.1)).prod := by
      rw [Polynomial.map_multiset_prod, Multiset.map_map]
      congr 1
      refine Multiset.map_congr rfl fun y hy => ?_
      simp only [Function.comp_apply, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, (ho y hy).2]
    have hkill : (aeval (actVB (pc (D.loc (D.nd.l i)) h hN hF hS).PD ((D.nbr i w hw).rep (R.comp (decS D.nd w))) s)
        (((M.map fun y => X - C (o y)).prod).map (D.nbr i w hw).toLL)) d = 0 := by
      rw [aeval_actVB _ _ s _ (lt_of_le_of_lt Polynomial.natDegree_map_le (Nat.lt_succ_self _))]
      refine Eq.trans (Finset.sum_congr rfl fun n _ => ?_) hT
      rw [Polynomial.coeff_map, map_pow, MulEquiv.apply_symm_apply]
      try rfl
    obtain ⟨r, hr⟩ := prod_dvd_pow M (S.image ch) (fun y => ((ch y g : (↥(D.nbr i w hw).LL.1)ˣ) : ↥(D.nbr i w hw).LL.1))
      (fun a => ((a g : (↥(D.nbr i w hw).LL.1)ˣ) : ↥(D.nbr i w hw).LL.1))
      (fun y hy => ⟨ch y, Finset.mem_image_of_mem ch (hMS y hy), rfl⟩)
    refine (aeval_eq_of_mem_Dpcris (pc (D.loc (D.nd.l i)) h hN hF hS) _ _ s hs.2 _ d hd).trans ?_
    rw [hr, mul_comm, map_mul, mul_apply_eq_comp, ← hq, hkill, map_zero]
  exact GlobalTheory.PassPolyPow.main (D.nd.l i) (D.loc (D.nd.l i)) (D.nbr i w hw).Kw K' (D.nbr i w hw).LL h hN hF hS _ _
    (S.image ch) G1 G2 G3 G4
end GlobalTheory.InertiaChars
