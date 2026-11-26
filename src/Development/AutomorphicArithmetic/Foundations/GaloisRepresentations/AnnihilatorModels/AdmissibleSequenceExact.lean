module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPstAtOfIsSstAt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.LocFacts

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AevalComm
theorem UpperTheory.Reformulated.B.Qk66.aeval_comm :
    ∀ {L M N : Type} [inst : Field L]
    [inst_1 : AddCommGroup M] [inst_2 : _root_.Module L M] [inst_3 : AddCommGroup N] [inst_4 : _root_.Module L N]
    (φ : M →ₗ[L] N) (A : Module.End L M) (A' : Module.End L N),
    (∀ (y : M), (φ : M → N) ((A : M → M) y) = (A' : N → N) ((φ : M → N) y)) →
      ∀ (Q : Polynomial L) (y : M),
        (φ : M → N) (((Polynomial.aeval A : Polynomial L → Module.End L M) Q : M → M) y) =
          ((Polynomial.aeval A' : Polynomial L → Module.End L N) Q : N → N) ((φ : M → N) y) := by
  intro L M N _ _ _ _ _ φ A A' h Q
  induction Q using Polynomial.induction_on with
  | C a =>
    intro y
    simp [Module.algebraMap_end_apply]
  | add p q hp hq =>
    intro y
    simp only [map_add (f := _), LinearMap.add_apply, hp, hq]
  | monomial n a ih =>
    intro y
    rw [pow_succ, ← mul_assoc, map_mul (Polynomial.aeval A), map_mul (Polynomial.aeval A'),
      Polynomial.aeval_X, Polynomial.aeval_X, Module.End.mul_apply, Module.End.mul_apply, ih, h]
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AevalInterAlt
theorem UpperTheory.Reformulated.B.Qi58.aeval_inter :
    ∀ {L M N : Type} [inst : Field L]
    [inst_1 : AddCommGroup M] [inst_2 : _root_.Module L M] [inst_3 : AddCommGroup N] [inst_4 : _root_.Module L N]
    (c : M →ₗ[L] N) (f : Module.End L M) (g : Module.End L N),
    (∀ (x : M), (c : M → N) ((f : M → M) x) = (g : N → N) ((c : M → N) x)) →
      ∀ (Q : Polynomial L) (x : M),
        (c : M → N) (((Polynomial.aeval f : Polynomial L → Module.End L M) Q : M → M) x) =
          ((Polynomial.aeval g : Polynomial L → Module.End L N) Q : N → N) ((c : M → N) x) := by
  intro L M N _ _ _ _ _ c f g h Q x
  have hp : ∀ (n : ℕ) (y : M), c ((f ^ n) y) = (g ^ n) (c y) := by
    intro n
    induction n with
    | zero => intro y; simp
    | succ n ih =>
      intro y
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h]
  induction Q using Polynomial.induction_on' with
  | add p q hp' hq' => simp only [map_add (f := _), LinearMap.add_apply, hp', hq']
  | monomial n a =>
    simp only [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      map_smul, hp]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PStOfCr
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

private theorem boundQ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K : FinExt l) :
    Bound (σSt P K) ℚ_[l] (finrank ℚ_[l] ↥(K0 K)) := by
  intro U _ m₁ m₂ hts _ ρ
  have hm : m₂ = m₁ := by
    refine Module.ext' _ _ fun a u => ?_
    have h := hts.smul_assoc a (1 : ℚ_[l]) u
    rw [smul_eq_mul, mul_one, @one_smul ℚ_[l] U _ m₁.toDistribMulAction.toMulAction] at h
    exact h.symm
  subst hm
  obtain ⟨hfin, hb⟩ := GlobalTheory.CrysSst.finrank_Dst_le P AI T ρ
  rw [dinv_σSt]
  exact ⟨hfin, by rw [mul_comm]; exact hb⟩

private theorem pow_C {l : ℕ} [Fact l.Prime] (P : LocPrime l) (f : ℕ) (b : P.R.B) :
    (Polynomial.C ((ψCr P f) b) : Bst P) = (ψSt P f) (Polynomial.C b) := by
  induction f generalizing b with
  | zero => simp [ψCr, ψSt]
  | succ f ih =>
    simp only [ψCr, ψSt, pow_succ', Module.End.mul_apply] at ih ⊢
    rw [← ih]
    simp

theorem UpperTheory.Gal.crystallineComparison.stOfCr_of :
    AnnPer → BoundSt → StOfCr := by
  intro hP _ l _ P AI hT K V _ _ _ ρ hA
  obtain ⟨T⟩ := hT
  have hB := boundQ P AI T K
  have key : ∀ f : ℕ, _ := fun f => hP ℚ_[l] ↥(GK K) P.R.B (Bst P) (σCr P K) (ψCr P f) (σSt P K) (ψSt P f)
    (Polynomial.CAlgHom : P.R.B →ₐ[ℚ_[l]] Bst P).toLinearMap Polynomial.C_injective
    (fun g b => (actSt_C P (g : GQ l) b).symm) (fun b => pow_C P f b) ℚ_[l] _ hB V ρ hA
  exact ⟨(key 0).1, fun f q n T' h => (key f).2 q n T' h⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PBoundSt
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.boundSt_of :
    BoundSt := by
  intro l _ P AI hT K LL
  obtain ⟨T⟩ := hT
  refine ⟨?_, fun f g => ?_⟩
  · intro U _ _ _ _ _ ρ
    rw [dinv_σSt]
    haveI := LL.2
    haveI : FiniteDimensional ℚ_[l] U := Module.Finite.trans ↥LL.1 U
    obtain ⟨hfin, hb⟩ := GlobalTheory.CrysSst.finrank_Dst_le P AI T (GlobalTheory.PstCoeff.resQ ρ)
    have hD : Dst P (GlobalTheory.PstCoeff.resQ ρ) = (Dst P ρ).restrictScalars ℚ_[l] := by
      ext x
      simp [mem_Dst, GlobalTheory.PstCoeff.stRep_resQ]
    have e : finrank ℚ_[l] ↥(Dst P (GlobalTheory.PstCoeff.resQ ρ)) =
        finrank ℚ_[l] ↥LL.1 * finrank ↥LL.1 ↥(Dst P ρ) := by
      rw [hD, finrank_mul_finrank]
      rfl
    have hfin' : FiniteDimensional ℚ_[l] ↥((Dst P ρ).restrictScalars ℚ_[l]) := hD ▸ hfin
    haveI : Module.Finite ℚ_[l] ↥(Dst P ρ) := hfin'
    haveI hL : FiniteDimensional ↥LL.1 ↥(Dst P ρ) :=
      Module.Finite.of_restrictScalars_finite ℚ_[l] ↥LL.1 ↥(Dst P ρ)
    refine ⟨hL, ?_⟩
    have hV : finrank ℚ_[l] U = finrank ℚ_[l] ↥LL.1 * finrank ↥LL.1 U :=
      (finrank_mul_finrank ℚ_[l] ↥LL.1 U).symm
    rw [e, hV] at hb
    refine Nat.le_of_mul_le_mul_left ?_ (finrank_pos (R := ℚ_[l]) (M := ↥LL.1))
    calc finrank ℚ_[l] ↥LL.1 * finrank ↥LL.1 ↥(Dst P ρ)
        ≤ finrank ℚ_[l] ↥LL.1 * finrank ↥LL.1 U * finrank ℚ_[l] ↥(K0 K) := hb
      _ = finrank ℚ_[l] ↥LL.1 * (finrank ℚ_[l] ↥(K0 K) * finrank ↥LL.1 U) := by ring
  · refine Commute.pow_right ?_ f
    exact LinearMap.ext fun p => (phiSt_actSt P (g : GQ l) p).symm
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PNilRho
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.GalOfCusp TensorProduct Module
open UpperTheory.Gal.crystallineComparison

private theorem nil_transfer {R S M W : Type} [CommRing R] [CommRing S] [AddCommGroup M] [Module R M]
    [AddCommGroup W] [Module S W] (φ : R →+* S) (mk : M → W) (hzero : mk 0 = 0)
    (hadd : ∀ x y, mk (x + y) = mk x + mk y) (hsmul : ∀ (a : R) x, mk (a • x) = φ a • mk x)
    (hext : ∀ f g : End S W, (∀ x, f (mk x) = g (mk x)) → f = g)
    (T : End S W) (D : End R M) (hTD : ∀ x, T (mk x) = mk (D x)) (Q : Polynomial R)
    (hQ : IsNilpotent (Polynomial.aeval D Q)) : IsNilpotent (Polynomial.aeval T (Q.map φ)) := by
  obtain ⟨N, hN⟩ := hQ
  have hpow : ∀ (n : ℕ) x, (T ^ n) (mk x) = mk ((D ^ n) x) := by
    intro n
    induction n with
    | zero => intro x; rfl
    | succ n ih =>
      intro x
      rw [pow_succ, pow_succ, End.mul_apply, End.mul_apply, hTD, ih]
  have key : ∀ (R' : Polynomial R) x,
      Polynomial.aeval T (R'.map φ) (mk x) = mk (Polynomial.aeval D R' x) := by
    intro R' x
    induction R' using Polynomial.induction_on' with
    | add p q hp hq =>
      simp only [Polynomial.map_add (f := _), map_add (f := _), LinearMap.add_apply, hp, hq, hadd]
    | monomial n a =>
      rw [Polynomial.map_monomial, Polynomial.aeval_monomial, Polynomial.aeval_monomial,
        End.mul_apply, End.mul_apply, hpow, Module.algebraMap_end_apply,
        Module.algebraMap_end_apply, hsmul]
  refine ⟨N, hext _ _ fun x => ?_⟩
  rw [← map_pow, ← Polynomial.map_pow, key, map_pow, hN]
  simp [hzero]

theorem UpperTheory.Gal.crystallineComparison.nilRho_of :
    NilRho := by
  intro l _ P ι E Ω _ _ _ _ _ A w h O _ _ _ Bw hj LL V _ _ _ _ _ ρ hV Q g
  haveI := hV.finite
  exact nil_transfer (ι.toRingHom.comp (algebraMap ↥LL.1 (Om l))) (wdMk P ι ρ) (wdMk_zero P ι ρ)
    (wdMk_add P ι ρ) (wdMk_smul P ι ρ) (fun _ _ => wd_ext P ι ρ) _ _
    (wdRho_mk P ι Bw h hj ρ g) Q
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PNilAnn
open TensorProduct Module
open UpperTheory.Gal.crystallineComparison

section
variable {F B : Type} [Field F] [AddCommGroup B] [Module F B]
  {L : Type} [Field L] [Algebra F L] {V : Type} [AddCommGroup V] [Module L V] [Module F V] [IsScalarTower F L V]

end

private theorem commute_tensorMap_of_commute {F B L V : Type} [Field F] [AddCommGroup B] [Module F B] [Field L]
    [Algebra F L] [AddCommGroup V] [Module L V] [Module F V] [IsScalarTower F L V]
    {f₁ f₂ : Module.End L V} {g₁ g₂ : Module.End F B} (hf : Commute f₁ f₂) (hg : Commute g₁ g₂) :
    Commute (AlgebraTensorModule.map f₁ g₁ : Module.End L (V ⊗[F] B)) (AlgebraTensorModule.map f₂ g₂) := by
  unfold Commute SemiconjBy
  rw [← AlgebraTensorModule.map_mul, ← AlgebraTensorModule.map_mul, hf.eq, hg.eq]

private theorem tensorMap_pow {F B L V : Type} [Field F] [AddCommGroup B] [Module F B] [Field L]
    [Algebra F L] [AddCommGroup V] [Module L V] [Module F V] [IsScalarTower F L V]
    (f : Module.End L V) (g : Module.End F B) (k : ℕ) :
    (AlgebraTensorModule.map f g : Module.End L (V ⊗[F] B)) ^ k = AlgebraTensorModule.map (f ^ k) (g ^ k) := by
  induction k with
  | zero => simp only [pow_zero, AlgebraTensorModule.map_one]
  | succ k ih =>
    rw [pow_succ, ih, ← AlgebraTensorModule.map_mul, ← pow_succ, ← pow_succ]

private theorem isNilpotent_tensorMap_of_isNilpotent {F B L V : Type} [Field F] [AddCommGroup B] [Module F B] [Field L]
    [Algebra F L] [AddCommGroup V] [Module L V] [Module F V] [IsScalarTower F L V]
    {f : Module.End L V} (g : Module.End F B) (hf : IsNilpotent f) :
    IsNilpotent (AlgebraTensorModule.map f g : Module.End L (V ⊗[F] B)) := by
  have h : (AlgebraTensorModule.map f g : Module.End L (V ⊗[F] B)) =
      AlgebraTensorModule.map f 1 * AlgebraTensorModule.map 1 g := by
    rw [← AlgebraTensorModule.map_mul, mul_one, one_mul]
  rw [h]
  apply Commute.isNilpotent_mul_right (commute_tensorMap_of_commute (Commute.one_right f) (Commute.one_left g))
  obtain ⟨k, hk⟩ := hf
  refine ⟨k, ?_⟩
  rw [tensorMap_pow, hk, one_pow]
  apply TensorProduct.AlgebraTensorModule.ext
  intro v b
  simp

theorem UpperTheory.Gal.crystallineComparison.nilAnn_of :
    NilOfAnn := by
  intro F G B _ _ _ _ σ ψ hσψ L _ _ V _ _ _ _ ρ q n T θ hTρ hTT hnil hann
  let c : ℕ → ℤ := fun j => (-1) ^ j * (q : ℤ) ^ j.choose 2
  let P : Module.End L (V ⊗[F] B) :=
    ∑ j ∈ Finset.range (n + 1), c j • AlgebraTensorModule.map (T j) (ψ ^ (n - j))
  let E : Module.End L (V ⊗[F] B) :=
    ∑ j ∈ Finset.range (n + 1), c j • AlgebraTensorModule.map (T j - θ j • 1) (ψ ^ (n - j))
  have hQ : Polynomial.aeval (onPer ψ L V) (heckePol q n θ) = P - E := by
    rw [← Finset.sum_sub_distrib]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [heckePol, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    apply TensorProduct.AlgebraTensorModule.ext
    intro v b
    simp only [onPer, tensorMap_pow, map_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow,
      Module.End.mul_apply, Module.algebraMap_end_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      AlgebraTensorModule.map_tmul, ← smul_sub, ← sub_tmul]
    simp [c, smul_tmul', sub_sub_cancel, smul_smul]
    rw [← Int.cast_smul_eq_zsmul L, smul_smul]
    congr 2
    push_cast
    ring
  have hP : ∀ x ∈ Dinv σ ρ, P x = 0 := by
    intro x hx
    simp only [P, LinearMap.sum_apply, LinearMap.smul_apply]
    exact hann x hx
  have hM : ∀ i j : ℕ, ∀ f : Module.End L V, Commute (T i) f →
      Commute (c i • AlgebraTensorModule.map (T i) (ψ ^ (n - i)) : Module.End L (V ⊗[F] B))
        (c j • AlgebraTensorModule.map f (ψ ^ (n - j))) := by
    intro i j f hf
    have h0 : Commute (AlgebraTensorModule.map (T i) (ψ ^ (n - i)) : Module.End L (V ⊗[F] B))
        (AlgebraTensorModule.map f (ψ ^ (n - j))) :=
      commute_tensorMap_of_commute hf (Commute.pow_pow_self ψ _ _)
    exact (h0.smul_left (c i)).smul_right (c j)
  have hPE : Commute P E := by
    refine Commute.sum_left _ _ _ fun i _ => Commute.sum_right _ _ _ fun j _ => ?_
    exact hM i j _ ((hTT i j).sub_right ((Commute.one_right (T i)).smul_right (θ j)))
  have hE : IsNilpotent E := by
    refine Commute.isNilpotent_sum (fun j hj => (isNilpotent_tensorMap_of_isNilpotent _ (hnil j ?_)).smul (c j)) ?_
    · exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    · intro i j _ _
      have hf : Commute (T i - θ i • 1) (T j - θ j • 1) := by
        refine ((hTT i j).sub_right ((Commute.one_right (T i)).smul_right (θ j))).sub_left ?_
        exact ((Commute.one_left (T j)).smul_left (θ i)).sub_right
          (((Commute.one_right _).smul_left (θ i)).smul_right (θ j))
      have h0 : Commute (AlgebraTensorModule.map (T i - θ i • 1) (ψ ^ (n - i)) : Module.End L (V ⊗[F] B))
          (AlgebraTensorModule.map (T j - θ j • 1) (ψ ^ (n - j))) :=
        commute_tensorMap_of_commute hf (Commute.pow_pow_self ψ _ _)
      exact (h0.smul_left (c i)).smul_right (c j)
  obtain ⟨N, hN⟩ := hE
  refine ⟨N, fun x hx => ?_⟩
  have key : ∀ (k : ℕ) (y : V ⊗[F] B), P y = 0 → ((P - E) ^ k) y = ((-E) ^ k) y := by
    intro k
    induction k with
    | zero => intro y _; simp
    | succ k ih =>
      intro y hy
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply]
      have h1 : (P - E) y = (-E) y := by simp [hy]
      rw [h1]
      apply ih
      rw [← Module.End.mul_apply, hPE.neg_right.eq, Module.End.mul_apply, hy, map_zero]
  rw [hQ, key N x (hP x hx), neg_pow, hN]
  simp
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PDinvExact
open TensorProduct Module
open UpperTheory.Gal.crystallineComparison

private lemma UpperTheory.Gal.crystallineComparison.map_id_eq_rTensor {F B L U V : Type} [Field F] [AddCommGroup B] [Module F B]
    [Field L] [Algebra F L] [AddCommGroup U] [Module L U] [Module F U] [IsScalarTower F L U]
    [AddCommGroup V] [Module L V] [Module F V] [IsScalarTower F L V] (f : U →ₗ[L] V) (x : U ⊗[F] B) :
    AlgebraTensorModule.map f (LinearMap.id : B →ₗ[F] B) x = LinearMap.rTensor B (f.restrictScalars F) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul u b => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

private lemma UpperTheory.Gal.crystallineComparison.inter_map {F G B L U V : Type} [Field F] [Group G] [AddCommGroup B] [Module F B]
    (σ : G → End F B) [Field L] [Algebra F L] [AddCommGroup U] [Module L U] [Module F U] [IsScalarTower F L U]
    [AddCommGroup V] [Module L V] [Module F V] [IsScalarTower F L V]
    {ρ : Representation L G U} {ρ' : Representation L G V} {f : U →ₗ[L] V} (hf : Inter ρ ρ' f) (g : G) (x : U ⊗[F] B) :
    AlgebraTensorModule.map f (LinearMap.id : B →ₗ[F] B) (AlgebraTensorModule.map (ρ g) (σ g) x) =
      AlgebraTensorModule.map (ρ' g) (σ g) (AlgebraTensorModule.map f (LinearMap.id : B →ₗ[F] B) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul u b => simp [hf g u]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem UpperTheory.Gal.crystallineComparison.dinvExact_of :
    DinvExact := by
  intro F G B _ _ _ _ σ L _ _ U V W _ _ _ _ _ _ _ _ _ _ _ _ ρU ρV ρW i p hi hp hinj hex hfin
  have hI : Function.Injective (AlgebraTensorModule.map i (LinearMap.id : B →ₗ[F] B)) := by
    have h := Module.Flat.rTensor_preserves_injective_linearMap (M := B) (i.restrictScalars F) hinj
    intro x y hxy
    apply h
    rw [← map_id_eq_rTensor, ← map_id_eq_rTensor]
    exact hxy
  have hE : Function.Exact (AlgebraTensorModule.map i (LinearMap.id : B →ₗ[F] B))
      (AlgebraTensorModule.map p (LinearMap.id : B →ₗ[F] B)) := by
    have h := Module.Flat.rTensor_exact (f := i.restrictScalars F) (g := p.restrictScalars F) B hex
    have e1 : (AlgebraTensorModule.map i (LinearMap.id : B →ₗ[F] B) : U ⊗[F] B → V ⊗[F] B) =
        LinearMap.rTensor B (i.restrictScalars F) := funext (map_id_eq_rTensor i)
    have e2 : (AlgebraTensorModule.map p (LinearMap.id : B →ₗ[F] B) : V ⊗[F] B → W ⊗[F] B) =
        LinearMap.rTensor B (p.restrictScalars F) := funext (map_id_eq_rTensor p)
    rw [e1, e2]
    exact h
  have key : (Dinv σ ρU).map (AlgebraTensorModule.map i (LinearMap.id : B →ₗ[F] B)) =
      Dinv σ ρV ⊓ LinearMap.ker (AlgebraTensorModule.map p (LinearMap.id : B →ₗ[F] B)) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨?_, ?_⟩
      · refine (mem_Dinv σ).2 fun g => ?_
        rw [← inter_map σ hi, (mem_Dinv σ).1 hx g]
      · exact (hE _).2 ⟨x, rfl⟩
    · rintro ⟨hy, hk⟩
      obtain ⟨x, rfl⟩ := (hE y).1 hk
      refine ⟨x, (mem_Dinv σ).2 fun g => hI ?_, rfl⟩
      rw [inter_map σ hi, (mem_Dinv σ).1 hy g]
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    refine (mem_Dinv σ).2 fun g => ?_
    rw [← inter_map σ hp, (mem_Dinv σ).1 hx g]
  · have h1 := LinearMap.finrank_range_add_finrank_ker
      ((AlgebraTensorModule.map p (LinearMap.id : B →ₗ[F] B)).domRestrict (Dinv σ ρV))
    rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at h1
    have h2 : finrank L (Submodule.comap (Dinv σ ρV).subtype
        (LinearMap.ker (AlgebraTensorModule.map p (LinearMap.id : B →ₗ[F] B)))) =
        finrank L (Dinv σ ρU) := by
      rw [← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype, ← key]
      exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hI _)).symm
    rw [h2] at h1
    omega
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PAnnSub
open TensorProduct Module
open UpperTheory.Gal.crystallineComparison

private theorem algebraTensorModule_map_map_id_right_comm_of_comm {F L U V B : Type} [Field F] [Field L] [Algebra F L]
    [AddCommGroup U] [Module L U] [Module F U] [IsScalarTower F L U]
    [AddCommGroup V] [Module L V] [Module F V] [IsScalarTower F L V]
    [AddCommGroup B] [Module F B]
    (i : U →ₗ[L] V) (f : U →ₗ[L] U) (f' : V →ₗ[L] V) (u : B →ₗ[F] B)
    (h : ∀ a, i (f a) = f' (i a)) (x : U ⊗[F] B) :
    AlgebraTensorModule.map f' u (AlgebraTensorModule.map i (LinearMap.id : B →ₗ[F] B) x) =
      AlgebraTensorModule.map i (LinearMap.id : B →ₗ[F] B) (AlgebraTensorModule.map f u x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [h]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

set_option maxHeartbeats 800000 in
theorem UpperTheory.Gal.crystallineComparison.annSub_of :
    AnnSub := by
  intro F G B _ _ _ _ σ ψ L _ _ U V _ _ _ _ _ _ _ _ ρU ρ i hI hi q n TU T hT hAnn
  unfold Inter at hI
  unfold AnnD at hAnn ⊢
  let M : U ⊗[F] B →ₗ[L] V ⊗[F] B := AlgebraTensorModule.map i LinearMap.id
  have hM_inj : Function.Injective M := by
    have h1 : ⇑M = ⇑(LinearMap.rTensor B (i.restrictScalars F)) := by
      funext x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a b => simp [M]
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
    rw [h1]
    exact Module.Flat.rTensor_preserves_injective_linearMap (i.restrictScalars F) hi
  have hpow : ∀ k, ∀ b, (LinearMap.id : B →ₗ[F] B) ((ψ ^ k) b) = (ψ ^ k) ((LinearMap.id : B →ₗ[F] B) b) :=
    fun _ _ => rfl
  intro x hx
  have hmx : M x ∈ Dinv σ ρ := by
    simp only [Dinv, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero] at hx ⊢
    intro g
    exact (algebraTensorModule_map_map_id_right_comm_of_comm i (ρU g) (ρ g) (σ g) (hI g) x).trans (congrArg M (hx g))
  apply hM_inj
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_zero, ← hAnn (M x) hmx, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearMap.map_smul_of_tower]
  congr 1
  exact (algebraTensorModule_map_map_id_right_comm_of_comm i (TU j) (T j) (ψ ^ (n - j)) (hT j) x).symm
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PNilSubq
open TensorProduct Module
open UpperTheory.Gal.crystallineComparison

private theorem pow_inter {L M N : Type} [Field L] [AddCommGroup M] [Module L M] [AddCommGroup N] [Module L N]
    (c : M →ₗ[L] N) (f : End L M) (g : End L N) (h : ∀ x, c (f x) = g (c x)) (n : ℕ) (x : M) :
    c ((f ^ n) x) = (g ^ n) (c x) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h]

private theorem aeval_inter {L M N : Type} [Field L] [AddCommGroup M] [Module L M] [AddCommGroup N] [Module L N]
    (c : M →ₗ[L] N) (f : End L M) (g : End L N) (h : ∀ x, c (f x) = g (c x)) (Q : Polynomial L) (x : M) :
    c (Polynomial.aeval f Q x) = Polynomial.aeval g Q (c x) :=
  _root_.UpperTheory.Reformulated.B.Qi58.aeval_inter c f g h Q x

theorem UpperTheory.Gal.crystallineComparison.nilSubq_of :
    AdmExact → NilEmb → NilSubq := by
  intro hA hE F G B _ _ _ _ σ ψ L _ _ e hB V W _ _ _ _ _ _ _ _ _ ρ ρ' hS hAdm
  obtain ⟨U, _, _, ρU, i, p, hi, hinj, hp, hsurj⟩ := hS
  letI : Module F U := Module.compHom U (algebraMap F L)
  haveI : IsScalarTower F L U := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : Module.Finite L U := Module.Finite.of_injective i hinj
  haveI : Module.Finite L W := Module.Finite.of_surjective p hsurj
  have hU : admitted σ e ρU := (hA F G B σ L e hB U V ρU ρ i hi).1 hinj hAdm
  obtain ⟨hW, hmap⟩ := (hA F G B σ L e hB U W ρU ρ' p hp).2 hsurj hU
  refine ⟨hW, fun Q hQ => ?_⟩
  obtain ⟨N, hN⟩ : NilD σ ψ ρU Q :=
    hE F G B σ ψ L U ρU Unit (fun _ => V) (fun _ => ρ) (fun _ => i) (fun _ => hi)
      (fun v h => hinj (by simpa using h ())) Q (fun _ => hQ)
  refine ⟨N, fun y hy => ?_⟩
  rw [← hmap] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  have h1 : ∀ z : U ⊗[F] B, AlgebraTensorModule.map p (LinearMap.id : B →ₗ[F] B) (onPer ψ L U z) =
      onPer ψ L W (AlgebraTensorModule.map p (LinearMap.id : B →ₗ[F] B) z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul u b => simp [onPer]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  rw [← pow_inter _ _ _ (fun z => aeval_inter _ _ _ h1 Q z) N x, hN x hx, map_zero]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PAdmExact
open TensorProduct Module
open UpperTheory.Gal.crystallineComparison

private theorem admissible_exact_sequence (hD : DinvExact) {F G B : Type} [Field F] [Group G] [AddCommGroup B] [Module F B]
    (σ : G → End F B) {L : Type} [Field L] [Algebra F L] {e : ℕ} (hB : Bound σ L e)
    {U V W : Type} [AddCommGroup U] [Module L U] [Module F U] [IsScalarTower F L U] [Module.Finite L U]
    [AddCommGroup V] [Module L V] [Module F V] [IsScalarTower F L V] [Module.Finite L V]
    [AddCommGroup W] [Module L W] [Module F W] [IsScalarTower F L W] [Module.Finite L W]
    (ρU : Representation L G U) (ρV : Representation L G V) (ρW : Representation L G W)
    (i : U →ₗ[L] V) (p : V →ₗ[L] W) (hi : Inter ρU ρV i) (hp : Inter ρV ρW p)
    (inj : Function.Injective i) (ex : Function.Exact i p) (surj : Function.Surjective p)
    (hA : admitted σ e ρV) :
    admitted σ e ρU ∧ admitted σ e ρW ∧
      (Dinv σ ρV).map (AlgebraTensorModule.map p (LinearMap.id : B →ₗ[F] B)) = Dinv σ ρW := by
  obtain ⟨fU, bU⟩ := hB U ρU
  obtain ⟨fV, -⟩ := hB V ρV
  obtain ⟨fW, bW⟩ := hB W ρW
  obtain ⟨hle, hdim⟩ := hD F G B σ L U V W ρU ρV ρW i p hi hp inj ex fV
  have hmono := Submodule.finrank_mono hle
  have hrank : finrank L V = finrank L U + finrank L W := by
    have h1 := LinearMap.finrank_range_add_finrank_ker p
    rw [LinearMap.range_eq_top.mpr surj, finrank_top, LinearMap.exact_iff.mp ex,
      LinearMap.finrank_range_of_inj inj] at h1
    omega
  unfold admitted at hA ⊢
  rw [hrank, mul_add] at hA
  have h2 : finrank L (Dinv σ ρU) = e * finrank L U := by omega
  have h3 : finrank L (Dinv σ ρW) = e * finrank L W := by omega
  refine ⟨h2, h3, Submodule.eq_of_le_of_finrank_eq hle ?_⟩
  omega

theorem UpperTheory.Gal.crystallineComparison.admissibleExact_of_dualInvariantExact :
    DinvExact → AdmExact := by
  intro hD
  unfold AdmExact
  intro F G B _ _ _ _ σ L _ _ e hB V W _ _ _ _ _ _ _ _ _ _ ρ ρ' f hf
  refine ⟨fun inj hA => ?_, fun surj hA => ?_⟩
  · let ρQ : Representation L G (W ⧸ LinearMap.range f) :=
      { toFun := fun g => (LinearMap.range f).mapQ (LinearMap.range f) (ρ' g) (by
          rintro _ ⟨v, rfl⟩
          exact ⟨ρ g v, hf g v⟩)
        map_one' := by
          ext w
          simp
        map_mul' := by
          intro g h
          ext w
          simp [map_mul] }
    have hQ : UpperTheory.Gal.crystallineComparison.Inter ρ' ρQ (LinearMap.range f).mkQ := fun g w => rfl
    exact (admissible_exact_sequence hD σ hB ρ ρ' ρQ f (LinearMap.range f).mkQ hf hQ inj
      (LinearMap.exact_map_mkQ_range f) (Submodule.mkQ_surjective _) hA).1
  · have hK : ∀ (g : G) (x : LinearMap.ker f), ρ g x ∈ LinearMap.ker f := by
      intro g x
      rw [LinearMap.mem_ker, hf g x, LinearMap.mem_ker.mp x.2, map_zero]
    let ρK : Representation L G (LinearMap.ker f) :=
      { toFun := fun g => LinearMap.codRestrict (LinearMap.ker f)
          ((ρ g).comp (LinearMap.ker f).subtype) (hK g)
        map_one' := by
          ext x
          simp
        map_mul' := by
          intro g h
          ext x
          simp only [map_mul, Module.End.mul_apply]
          rfl }
    have hKi : UpperTheory.Gal.crystallineComparison.Inter ρK ρ (LinearMap.ker f).subtype := fun g x => rfl
    obtain ⟨-, hW, hmap⟩ := admissible_exact_sequence hD σ hB ρK ρ ρ' (LinearMap.ker f).subtype f hKi hf
      (LinearMap.ker f).injective_subtype (LinearMap.exact_subtype_ker_map f) surj hA
    exact ⟨hW, hmap⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PNilEmb
noncomputable section

open TensorProduct Module

namespace UpperTheory.Gal.crystallineComparison

section Comm
variable {L M N : Type} [Field L] [AddCommGroup M] [Module L M] [AddCommGroup N] [Module L N]

private theorem pow_comm (φ : M →ₗ[L] N) (A : End L M) (A' : End L N) (h : ∀ y, φ (A y) = A' (φ y)) (n : ℕ) (y : M) :
    φ ((A ^ n) y) = (A' ^ n) (φ y) := by
  induction n generalizing y with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h]

private theorem aeval_comm (φ : M →ₗ[L] N) (A : End L M) (A' : End L N) (h : ∀ y, φ (A y) = A' (φ y)) (Q : Polynomial L) (y : M) :
    φ (Polynomial.aeval A Q y) = Polynomial.aeval A' Q (φ y) :=
  _root_.UpperTheory.Reformulated.B.Qk66.aeval_comm φ A A' h Q y

end Comm

section
variable {F G B : Type} [Field F] [Group G] [AddCommGroup B] [Module F B] (σ : G → End F B) (ψ : End F B)
  {L : Type} [Field L] [Algebra F L] {V W : Type} [AddCommGroup V] [Module L V] [Module F V] [IsScalarTower F L V]
  [AddCommGroup W] [Module L W] [Module F W] [IsScalarTower F L W]

private def ext1 (B : Type) [AddCommGroup B] [Module F B] (f : V →ₗ[L] W) : V ⊗[F] B →ₗ[L] W ⊗[F] B :=
  AlgebraTensorModule.map f (LinearMap.id : B →ₗ[F] B)

private theorem scalar_extension_tmul (f : V →ₗ[L] W) (v : V) (b : B) : ext1 (F := F) B f (v ⊗ₜ b) = f v ⊗ₜ b := by
  simp [ext1]

private theorem typeCharacterExtension_mem_range_coefficientRing {ρ : Representation L G V} {ρ' : Representation L G W} {f : V →ₗ[L] W} (h : Inter ρ ρ' f)
    {x : V ⊗[F] B} (hx : x ∈ Dinv σ ρ) : ext1 B f x ∈ Dinv σ ρ' := by
  rw [mem_Dinv] at hx ⊢
  intro g
  have key : ∀ y : V ⊗[F] B, AlgebraTensorModule.map (ρ' g) (σ g) (ext1 B f y) =
      ext1 B f (AlgebraTensorModule.map (ρ g) (σ g) y) := by
    intro y
    induction y with
    | tmul v b => simp [scalar_extension_tmul, h g v]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  rw [key, hx]

private theorem scalar_extension_period_action (f : V →ₗ[L] W) (y : V ⊗[F] B) :
    ext1 B f (onPer ψ L V y) = onPer ψ L W (ext1 B f y) := by
  induction y with
  | tmul v b => simp [scalar_extension_tmul, onPer]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]

private theorem scalar_extension_basis_coord {κ : Type} [DecidableEq κ] (b : Basis κ F B) (f : V →ₗ[L] W) (y : V ⊗[F] B) (k : κ) :
    TensorProduct.equivFinsuppOfBasisRight b (ext1 B f y) k = f (TensorProduct.equivFinsuppOfBasisRight b y k) := by
  induction y with
  | tmul v c =>
    rw [scalar_extension_tmul, TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply,
      TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply, LinearMap.map_smul_of_tower]
  | add a c ha hc => simp only [map_add (f := _), Finsupp.add_apply, ha, hc]

end

theorem nilEmb_of : NilEmb := by
  intro F G B _ _ _ _ σ ψ L _ _ V _ _ _ _ ρ I _ W _ _ _ _ ρ' f hI hinj Q hQ
  classical
  cases nonempty_fintype I
  choose N hN using hQ
  refine ⟨∑ i, N i, fun x hx => ?_⟩
  set A := Polynomial.aeval (onPer ψ L V) Q with hA
  have hzero : ∀ i, ext1 B (f i) ((A ^ ∑ i, N i) x) = 0 := by
    intro i
    have hle : N i ≤ ∑ i, N i := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    rw [pow_comm (ext1 B (f i)) A (Polynomial.aeval (onPer ψ L (W i)) Q)
      (aeval_comm _ _ _ (scalar_extension_period_action ψ (f i)) Q), ← Nat.sub_add_cancel hle, pow_add, Module.End.mul_apply,
      hN i _ (typeCharacterExtension_mem_range_coefficientRing σ (hI i) hx), map_zero]
  apply (TensorProduct.equivFinsuppOfBasisRight (Basis.ofVectorSpace F B)).injective
  ext k
  rw [map_zero, Finsupp.zero_apply]
  refine hinj _ fun i => ?_
  rw [← scalar_extension_basis_coord, hzero i, map_zero, Finsupp.zero_apply]

end UpperTheory.Gal.crystallineComparison
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PAnnPer
open TensorProduct Module
open UpperTheory.Gal.crystallineComparison

private theorem algebraTensorModule_map_map_id_left_comm_of_comm {F L V B B' : Type} [Field F] [Field L] [Algebra F L]
    [AddCommGroup V] [Module L V] [Module F V] [IsScalarTower F L V]
    [AddCommGroup B] [Module F B] [AddCommGroup B'] [Module F B']
    (c : B →ₗ[F] B') (f : V →ₗ[L] V) (u : B →ₗ[F] B) (u' : B' →ₗ[F] B')
    (h : ∀ b, c (u b) = u' (c b)) (x : V ⊗[F] B) :
    AlgebraTensorModule.map f u' (AlgebraTensorModule.map (LinearMap.id : V →ₗ[L] V) c x) =
      AlgebraTensorModule.map (LinearMap.id : V →ₗ[L] V) c (AlgebraTensorModule.map f u x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [h]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

set_option maxHeartbeats 800000 in
theorem UpperTheory.Gal.crystallineComparison.annPer_of :
    AnnPer := by
  intro F G B B' _ _ _ _ _ _ σ ψ σ' ψ' c hc hσ hψ L _ _ e hB V _ _ _ _ _ ρ hA
  unfold Bound at hB
  unfold admitted at hA ⊢
  have hpow : ∀ k b, c ((ψ ^ k) b) = (ψ' ^ k) (c b) := by
    intro k
    induction k with
    | zero => intro b; simp
    | succ k ih =>
      intro b
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, hψ]
  let m : V ⊗[F] B →ₗ[L] V ⊗[F] B' := AlgebraTensorModule.map LinearMap.id c
  have hm_inj : Function.Injective m := by
    have h1 : ⇑m = ⇑(LinearMap.lTensor V c) := by
      funext x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul v b => simp [m]
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
    rw [h1]
    exact Module.Flat.lTensor_preserves_injective_linearMap c hc
  have hmaps : ∀ x ∈ Dinv σ ρ, m x ∈ Dinv σ' ρ := by
    intro x hx
    simp only [Dinv, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero] at hx ⊢
    intro g
    exact (algebraTensorModule_map_map_id_left_comm_of_comm c (ρ g) (σ g) (σ' g) (hσ g) x).trans (congrArg m (hx g))
  let φ : Dinv σ ρ →ₗ[L] Dinv σ' ρ := m.restrict hmaps
  have hφ : Function.Injective φ := by
    intro a b hab
    apply Subtype.ext
    apply hm_inj
    exact congrArg Subtype.val hab
  obtain ⟨hfin', hle⟩ := hB V ρ
  haveI : Module.Finite L (Dinv σ ρ) := Module.Finite.of_injective φ hφ
  have hge : finrank L (Dinv σ ρ) ≤ finrank L (Dinv σ' ρ) :=
    LinearMap.finrank_le_finrank_of_injective hφ
  have heq : finrank L (Dinv σ ρ) = finrank L (Dinv σ' ρ) := by omega
  have hsurj : Function.Surjective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).mp hφ
  refine ⟨by omega, ?_⟩
  intro q n T hT
  unfold AnnD at hT ⊢
  intro x hx
  obtain ⟨y, hy⟩ := hsurj ⟨x, hx⟩
  have hxy : x = m y.1 := (congrArg Subtype.val hy).symm
  have key : ∀ j, (AlgebraTensorModule.map (T j) (ψ' ^ (n - j))) (m y.1) =
      m ((AlgebraTensorModule.map (T j) (ψ ^ (n - j))) y.1) :=
    fun j => algebraTensorModule_map_map_id_left_comm_of_comm c (T j) (ψ ^ (n - j)) (ψ' ^ (n - j)) (hpow (n - j)) y.1
  have h0 := congrArg m (hT y.1 y.2)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_zero, map_sum] at h0
  rw [hxy, ← h0]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [key j]
  exact (LinearMap.map_smul_of_tower m _ _).symm
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PAnnExt
open TensorProduct Module
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.annExt_of :
    DinvExt → AnnExt := by
  intro h F G B _ _ _ _ σ ψ L _ _ V _ _ ρ
  have hD := h F G B σ L V ρ
  have hinj : Function.Injective ((Dinv σ ρ).subtype.baseChange L) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ (Dinv σ ρ).injective_subtype
  refine ⟨fun e hadm => ?_, fun q n T hA x hx => ?_⟩
  · unfold admitted at hadm ⊢
    rw [← LinearEquiv.finrank_map_eq (AlgebraTensorModule.assoc F F L L V B), hD, Module.finrank_baseChange]
    rw [← hadm]
    change Module.finrank L (LinearMap.range ((Dinv σ ρ).subtype.baseChange L)) = _
    rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_baseChange]
  · unfold AnnD at hA
    dsimp only
    have comm : ∀ (f : V →ₗ[F] V) (g : B →ₗ[F] B) (y : (L ⊗[F] V) ⊗[F] B),
        AlgebraTensorModule.assoc F F L L V B (AlgebraTensorModule.map (f.baseChange L) g y) =
          (AlgebraTensorModule.map f g).lTensor L (AlgebraTensorModule.assoc F F L L V B y) := by
      intro f g y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul u b =>
        induction u using TensorProduct.induction_on with
        | zero => simp
        | tmul a v => simp
        | add u₁ u₂ h₁ h₂ => simp only [TensorProduct.add_tmul, map_add (f := _), h₁, h₂]
      | add y₁ y₂ h₁ h₂ => simp only [map_add (f := _), h₁, h₂]
    have hmem : AlgebraTensorModule.assoc F F L L V B x ∈ (Dinv σ ρ).baseChange L := by
      rw [← hD]
      exact Submodule.mem_map_of_mem hx
    apply (AlgebraTensorModule.assoc F F L L V B).injective
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_zero]
    simp only [map_zsmul, comm]
    obtain ⟨z, hz⟩ := Submodule.toBaseChange_surjective' L (Dinv σ ρ) hmem
    rw [← hz]
    clear hz hmem
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a w =>
      simp only [Submodule.coe_toBaseChange_tmul, LinearMap.lTensor_tmul]
      have := hA w w.2
      calc _ = TensorProduct.mk F L (V ⊗[F] B) a (∑ j ∈ Finset.range (n + 1), ((-1) ^ j * (q : ℤ) ^ j.choose 2) • (AlgebraTensorModule.map (T j) (ψ ^ (n - j))) w) := by
            set_option synthInstance.maxHeartbeats 100000 in
              simp only [map_sum, map_zsmul, TensorProduct.mk_apply]
        _ = 0 := by rw [this, map_zero]
    | add z₁ z₂ h₁ h₂ => simp only [map_add (f := _), Submodule.coe_add, Finset.sum_add_distrib, smul_add, h₁, h₂, add_zero]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PDinvExt
open TensorProduct Module
open UpperTheory.Gal.crystallineComparison

private theorem mem_baseChange_iInf_ker_sub_id_of_baseChange_eq {F L X ι : Type} [Field F] [Field L] [Algebra F L]
    [AddCommGroup X] [Module F X] (A : ι → X →ₗ[F] X) (z : L ⊗[F] X)
    (hz : ∀ k, (A k).baseChange L z = z) :
    z ∈ (⨅ k, LinearMap.ker (A k - LinearMap.id)).baseChange L := by
  let b := Module.Free.chooseBasis F L
  let e : L ⊗[F] X ≃ₗ[F] (Module.Free.ChooseBasisIndex F L →₀ X) :=
    (TensorProduct.congr b.repr (LinearEquiv.refl F X)).trans (finsuppScalarLeft F X _)
  have nat : ∀ (f : X →ₗ[F] X) (w : L ⊗[F] X) j, e (f.baseChange L w) j = f (e w j) := by
    intro f w j
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a x => simp [e, finsuppScalarLeft_apply_tmul_apply]
    | add u v hu hv => simp only [map_add (f := _), Finsupp.add_apply, hu, hv]
  have hmem : ∀ j, e z j ∈ ⨅ k, LinearMap.ker (A k - LinearMap.id) := by
    intro j
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero]
    intro k
    have h := congrArg (fun w => e w j) (hz k)
    simpa only [nat] using h
  have hsingle : ∀ j (x : X), e.symm (Finsupp.single j x) = b j ⊗ₜ[F] x := by
    intro j x
    simp [e]
  have hz' : z = (e z).sum (fun j x => b j ⊗ₜ[F] x) := by
    conv_lhs => rw [← e.symm_apply_apply z, ← Finsupp.sum_single (e z)]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Finsupp.sum, map_sum]
    exact Finset.sum_congr rfl fun j _ => hsingle j _
  rw [hz']
  exact Submodule.sum_mem _ fun j _ => Submodule.tmul_mem_baseChange_of_mem _ (hmem j)

theorem UpperTheory.Gal.crystallineComparison.dinvExt_of :
    DinvExt := by
  unfold DinvExt
  intro F G B _ _ _ _ σ L _ _ V _ _ ρ
  let T : G → (V ⊗[F] B) →ₗ[F] (V ⊗[F] B) := fun g => AlgebraTensorModule.map (ρ g) (σ g)
  have hD : Dinv σ ρ = ⨅ g, LinearMap.ker (T g - LinearMap.id) := rfl
  have comm : ∀ g (w : (L ⊗[F] V) ⊗[F] B),
      AlgebraTensorModule.assoc F F L L V B (AlgebraTensorModule.map (extRep L ρ g) (σ g) w) =
        (T g).baseChange L (AlgebraTensorModule.assoc F F L L V B w) := by
    intro g w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul u c =>
      induction u using TensorProduct.induction_on with
      | zero => simp
      | tmul a v => simp [T, extRep, AlgebraTensorModule.map_tmul]
      | add u₁ u₂ h₁ h₂ => simp only [TensorProduct.add_tmul, map_add (f := _), h₁, h₂]
    | add u v hu hv => simp only [map_add (f := _), hu, hv]
  ext z
  rw [Submodule.mem_map_equiv]
  constructor
  · intro hz
    rw [hD]
    apply mem_baseChange_iInf_ker_sub_id_of_baseChange_eq
    intro g
    have h : AlgebraTensorModule.map (extRep L ρ g) (σ g)
        ((AlgebraTensorModule.assoc F F L L V B).symm z) =
          (AlgebraTensorModule.assoc F F L L V B).symm z := by
      simp only [Dinv, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero] at hz
      exact hz g
    have h2 := congrArg (AlgebraTensorModule.assoc F F L L V B) h
    rwa [comm, LinearEquiv.apply_symm_apply] at h2
  · intro hz
    simp only [Dinv, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero]
    intro g
    apply (AlgebraTensorModule.assoc F F L L V B).injective
    rw [comm, LinearEquiv.apply_symm_apply]
    obtain ⟨w, rfl⟩ := hz
    have hfix : T g ∘ₗ (Dinv σ ρ).subtype = (Dinv σ ρ).subtype := by
      refine LinearMap.ext fun s => ?_
      have hs := s.2
      simp only [Dinv, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero] at hs
      exact hs g
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hfix]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PJoinAbs
open TensorProduct Module
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.joinAbs_of :
    NilEmb → NilSubq → NilOfAnn → AnnSub → AnnExt → AdmExact → JoinAbs := by
  intro hEmb hSubq hOfAnn hAnnSub hAnnExt hAdmExact
  intro F G B _ _ _ _ σ ψ hσψ L _ _ e hB V _ _ _ ρ q n T hAdm hAnn U _ _ ρU i TU θ hi hinj hT hTg hTT hnil
    W _ _ _ _ ρW I _ C _ _ ρC f hsub hf hsep
  letI : Module F U := Module.compHom _ (algebraMap F L)
  haveI : IsScalarTower F L U := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  letI : ∀ a, Module F (C a) := fun a => Module.compHom _ (algebraMap F L)
  haveI : ∀ a, IsScalarTower F L (C a) := fun a => IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : Module.Finite L U := Module.Finite.of_injective i hinj
  obtain ⟨hE1, hE2⟩ := hAnnExt F G B σ ψ L V ρ
  have hAdmL := hE1 e hAdm
  have hAnnL := hE2 q n T hAnn
  have hAdmU : admitted σ e ρU :=
    (hAdmExact F G B σ L e hB U (L ⊗[F] V) ρU (extRep L ρ) i hi).1 hinj hAdmL
  have hAnnU : AnnD σ ψ q n ρU TU :=
    hAnnSub F G B σ ψ L U (L ⊗[F] V) ρU (extRep L ρ) i hi hinj q n TU
      (fun j => (T j).baseChange L) hT hAnnL
  have hNilU : NilD σ ψ ρU (heckePol q n θ) :=
    hOfAnn F G B σ ψ hσψ L U ρU q n TU θ hTg hTT hnil hAnnU
  have hNilC : ∀ a, NilD σ ψ (ρC a) (heckePol q n θ) := fun a =>
    (hSubq F G B σ ψ L e hB U (C a) ρU (ρC a) (hsub a) hAdmU).2 _ hNilU
  exact hEmb F G B σ ψ L W ρW I C ρC f hf hsep _ hNilC
end

namespace UpperTheory.Gal.crystallineComparison

theorem admissible_sequence_exact : AdmExact := admissibleExact_of_dualInvariantExact dinvExact_of
theorem joinAbs_holds : JoinAbs :=
  joinAbs_of nilEmb_of (nilSubq_of admissible_sequence_exact nilEmb_of) nilAnn_of annSub_of (annExt_of dinvExt_of) admissible_sequence_exact
theorem boundSt_holds : BoundSt := boundSt_of
theorem stOfCr_holds : StOfCr := stOfCr_of annPer_of boundSt_of

end UpperTheory.Gal.crystallineComparison
