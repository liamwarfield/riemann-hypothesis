module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LeAdicClosure
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.CharPerm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.NicePrimeEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.WPresGrZeroIsCOOfMemMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.PropagationTheoremGL2
noncomputable section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

namespace UpperTheory.V.Pr

section Nice

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {n : ℕ} {R : Type} [CommRing R]

structure Nice (ρ : NRep F n R) (p : Ideal R) : Prop where
  prime : p.IsPrime
  dim : qdim p = 1
  char : (l : R) ∈ p
  off : ρ.OffTri p
  sep : ∀ v i j, i ≠ j → ¬ ρ.Coin p v i j

def ThickLink [IsLocalRing R] (ρ : NRep F 3 R) (p q : Ideal R) : Prop :=
  Nice ρ p ∧ ρ.TE p ∧ Nice ρ q ∧ ρ.TE q ∧ ∃ e : Ideal R, e.IsPrime ∧ Thick ρ e ∧ e ≤ p ∧ e ≤ q

end Nice

section Input

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] {F : Frame l (ResidueField O)} {n : ℕ}

def P1' (S : Space O F n) (M : Ideal S.B) : Prop :=
  ∀ (x : Ideal S.A) (L : S.Loc x) (p : Ideal L.R), Nice L.ρ p → L.ρ.TI p → M ≤ L.π p →
    ∀ P : Ideal L.R, P.IsPrime → P ≤ p → M ≤ L.π P

def P23' (S : Space O F 3) (M : Ideal S.B) : Prop :=
  ∀ (x : Ideal S.A) (L : S.Loc x) (p q : Ideal L.R), Nice L.ρ p → L.ρ.TE p → Relation.ReflTransGen (ThickLink L.ρ) p q →
    (∃ P : Ideal L.R, P.IsPrime ∧ P ≤ p ∧ L.ρ.TI P ∧ M ≤ L.π P) →
    ∀ P' : Ideal L.R, P'.IsPrime → P' ≤ q → L.ρ.TI P' → M ≤ L.π P'

def SeedIn (S : Space O F n) (M : Ideal S.B) : Prop :=
  ∃ (ξ : Ideal S.A) (Z : Ideal S.B), ξ.IsPrime ∧ S.u.TI ξ ∧ Z.IsPrime ∧ M ≤ Z ∧ Z ≤ S.π ξ ∧
    qdim Z = ((1 + n * F.d : ℕ) : WithBot ℕ∞)

def AllGood (S : Space O F n) (M : Ideal S.B) : Prop := ∀ p : Ideal S.A, p.IsPrime → S.u.TI p → M ≤ S.π p

def OffFin (S : Space O F n) : Prop := ∃ I : Ideal S.B, S.FinLam I ∧ ∀ p : Ideal S.A, p.IsPrime → S.u.OffTri p → I ≤ S.π p

end Input

def PropagationTheoremGL2 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O]
    (F : Frame l (ResidueField O)) (C₀ : ℕ), F.Ok C₀ → F.Big C₀ → ∀ (S : Space O F 2) (M : Ideal S.B),
    S.FinLam M → P1' S M → SeedIn S M → AllGood S M

def PropagationTheoremGL3 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O]
    (F : Frame l (ResidueField O)) (C₀ : ℕ), F.Ok C₀ → F.Big C₀ → ∀ (S₂ : Space O F 2) (M₂ : Ideal S₂.B),
    S₂.FinLam M₂ → AllGood S₂ M₂ → ∀ (S : Space O F 3) (M : Ideal S.B),
    S.FinLam M → P1' S M → P23' S M → SeedIn S M → AllGood S M ∧ OffFin S

section Points

variable {l : ℕ} [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O] {F : Frame l (ResidueField O)} {n : ℕ}

structure IsLiftA {A : Type} [CommRing A] [IsLocalRing A] [Algebra O A] [IsLocalHom (algebraMap O A)]
    (ρ : NRep F n A) : Prop where
  cont : ρ.Cont (maximalIdeal A)
  bar : (ρ.map (residue A)).IsBar (ResidueField.map (algebraMap O A))
  diag : (ρ.map (residue A)).IsDiag


variable (F n) in
def FinPt : Prop :=
  ∀ (A : Type) [CommRing A] [Algebra O A] [IsCD O A] [Algebra (ResidueField O) A] [IsScalarTower O (ResidueField O) A]
    (ρ : NRep F n A), IsLiftA O ρ → (∀ v i, ∀ g ∈ F.Iv v, F.Ψ (F.loc v g) = 1 → ρ.ψ v i g = 1) →
    ∀ g, (ρ.r g).charpoly =
      ∏ i, (Polynomial.X - Polynomial.C (algebraMap (ResidueField O) A ((F.Ψ g ^ w n i : (ResidueField O)ˣ) : ResidueField O)))

end Points

def FinPtOf : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O]
    (F : Frame l (ResidueField O)) (C₀ : ℕ), F.Ok C₀ → ∀ S : Space O F 3, OffFin S → FinPt O F 3

section Link

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
  (F : Frame l (ResidueField O)) {n : ℕ} {G : W.GFrame l} (r : W.Resid G O n)

structure TwLink where
  π : G.G₀ →* F.G0
  π_cont : Continuous π
  π_surj : Function.Surjective π
  π_conj : ∀ g, π (G.conj g) = F.conj (π g)
  π_eps : ∀ g : G.G₀, F.eps (π g) = G.ε g
  e : G.Vl ≃ F.V
  lam : ∀ v, G.Gv v ≃ₜ* F.Gv (e v)
  lam_loc : ∀ v g, F.loc0 (e v) (lam v g) = π (G.φ v g)
  lam_I : ∀ v g, lam v g ∈ F.Iv (e v) ↔ g ∈ G.Iv v
  κ : G.G₀ →* Oˣ
  κ_cont : AdicCont (maximalIdeal O) fun g => (κ g : O)
  κ_conj : ∀ g, κ g * κ (G.conj g) = G.eps O O g ^ (1 - (n : ℤ))
  chib : ∀ i g, r.chib i g = F.Ψ (π g) ^ w n i * W.pushCh (residue O) κ g
  psib : ∀ v i g, r.psib v i g = r.chib i (G.φ v g)
  mu : ∀ v, G.mu v ≤ (commutator (G.Gv v)).topologicalClosure
  tame : ∀ u, ∀ g ∈ G.Iu u, ∃ m : ℕ, ¬ l ∣ m ∧ π g ^ m = 1 ∧ κ g ^ m = 1
  ramκ : ∀ g ∈ G.I0, κ g = 1
  ker : ∀ N : Subgroup G.G₀, N.Normal → IsClosed (N : Set G.G₀) → (∀ g ∈ N, G.conj g ∈ N) →
    (∀ u, ∀ g ∈ G.Iu u, F.Ψ (π g) = 1 → g ∈ N) → G.I0 ≤ N → π.ker ≤ N

namespace TwLink

variable {F r} (K : TwLink F r) {A : Type} [CommRing A] [Algebra O A]

def κA (A : Type) [CommRing A] [Algebra O A] : G.G₀ →* Aˣ := W.pushCh (algebraMap O A) K.κ

def tw (ρ : NRep F n A) : G.G₀ →* Matrix (Fin n) (Fin n) A where
  toFun g := ((K.κA A g : Aˣ) : A) • ρ.r (K.π g)
  map_one' := by simp
  map_mul' g h := by simp [smul_smul, mul_comm]

def twψ (ρ : NRep F n A) (v : G.Vl) (i : Fin n) : G.Gv v →* Aˣ :=
  (ρ.ψ (K.e v) i).comp (K.lam v).toMulEquiv.toMonoidHom * (K.κA A).comp (G.φ v)

def IsPhi (B : W.UniversalOrdinaryDeterminantRing r) (S : Space O F n) (Φ : B.B →ₐ[O] S.B) : Prop :=
  B.u.Maps ((S.B.val.comp Φ : B.B →ₐ[O] S.R) : B.B →+* S.R) (W.GDet.ofRep (K.tw S.ρ)) (K.twψ S.ρ)

end TwLink

end Link

end UpperTheory.V.Pr

end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.IrrNormal
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExtIntegral
theorem UpperTheory.Reformulated.B.Qe16.ext_integral :
    ∀ {B S K : Type} [inst : CommRing B] [inst_1 : CommRing S]
    [inst_2 : Field K] [IsAlgClosed K] [inst_4 : Algebra B S] [Algebra.IsIntegral B S],
    Function.Injective (⇑(Algebra.algebraMap B S) : B → S) →
      ∀ (φ : B →+* K), ∃ (Φ : S →+* K), ∀ (b : B), (Φ : S → K) ((Algebra.algebraMap B S : B → S) b) = (φ : B → K) b := by
  intro B S K _ _ _ _ _ _ hinj φ
  haveI hP : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  obtain ⟨Q, -, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := S)
    (RingHom.ker φ) ⊥ (by
      rw [Ideal.under_def, ← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).1 hinj]
      exact bot_le)
  haveI : Q.LiesOver (RingHom.ker φ) := ⟨hQP.symm⟩
  letI : Algebra (B ⧸ RingHom.ker φ) K := (RingHom.kerLift φ).toAlgebra
  haveI : FaithfulSMul (B ⧸ RingHom.ker φ) K :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.kerLift_injective φ)
  haveI : Algebra.IsIntegral (B ⧸ RingHom.ker φ) (S ⧸ Q) :=
    Algebra.IsIntegral.tower_top (R := B)
  haveI : FaithfulSMul (B ⧸ RingHom.ker φ) (S ⧸ Q) := inferInstance
  haveI : Module.IsTorsionFree (B ⧸ RingHom.ker φ) (S ⧸ Q) :=
    Module.isTorsionFree_iff_faithfulSMul.2 inferInstance
  haveI : Module.IsTorsionFree (B ⧸ RingHom.ker φ) K :=
    Module.isTorsionFree_iff_faithfulSMul.2 inferInstance
  haveI : Nontrivial (B ⧸ RingHom.ker φ) := Ideal.Quotient.nontrivial_iff.2 hP.ne_top
  haveI : Algebra.IsAlgebraic (B ⧸ RingHom.ker φ) (S ⧸ Q) := Algebra.IsIntegral.isAlgebraic
  let f : (S ⧸ Q) →ₐ[B ⧸ RingHom.ker φ] K := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨f.toRingHom.comp (Ideal.Quotient.mk Q), fun b => ?_⟩
  exact (f.commutes (Ideal.Quotient.mk _ b)).trans (RingHom.kerLift_mk φ b)
end

open Matrix Polynomial UpperTheory.V.U3 UpperTheory.V.Alg

private theorem ext_integral {B S K : Type} [CommRing B] [CommRing S] [Field K] [IsAlgClosed K] [Algebra B S]
    [Algebra.IsIntegral B S] (hinj : Function.Injective (algebraMap B S)) (φ : B →+* K) :
    ∃ Φ : S →+* K, ∀ b, Φ (algebraMap B S b) = φ b :=
  _root_.UpperTheory.Reformulated.B.Qe16.ext_integral hinj φ

private theorem charpoly_of_basis {κ : Type} [Field κ] {n : ℕ} (M : Matrix (Fin n) (Fin n) κ)
    (b : Module.Basis (Fin n) κ (Fin n → κ)) (a : Fin n → κ) (h : ∀ i, M *ᵥ b i = a i • b i) :
    M.charpoly = ∏ i, (X - C (a i)) := by
  rw [← Matrix.charpoly_toLin', ← LinearMap.charpoly_toMatrix _ b, ← Matrix.charpoly_diagonal]
  congr 1
  ext i j
  rw [LinearMap.toMatrix_apply, Matrix.toLin'_apply, h, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij, Finsupp.single_apply, Ne.symm hij]

private theorem reduce_roots {κ k B : Type} [Field κ] [Field k] [CommRing B] (j : B →+* κ)
    (hj : Function.Injective j) (φ : B →+* k) :
    ∃ (S : Subring κ) (Φ : S →+* AlgebraicClosure k), ∀ (n : ℕ) (p : B[X]) (a : Fin n → κ),
      p.map j = ∏ i, (X - C (a i)) → ∃ h : ∀ i, a i ∈ S,
        (p.map φ).map (algebraMap k (AlgebraicClosure k)) = ∏ i, (X - C (Φ ⟨a i, h i⟩)) := by
  letI : Algebra B κ := j.toAlgebra
  have hinj : Function.Injective (algebraMap B (integralClosure B κ)) := by
    intro x y hxy
    exact hj (congrArg Subtype.val hxy)
  obtain ⟨Φ, hΦ⟩ := ext_integral hinj ((algebraMap k (AlgebraicClosure k)).comp φ)
  refine ⟨(integralClosure B κ).toSubring, Φ, fun n p a hp => ?_⟩
  have hm : p.Monic := by
    apply Polynomial.monic_of_injective hj
    rw [hp]
    exact monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _
  have h : ∀ i, a i ∈ integralClosure B κ := fun i => by
    refine ⟨p, hm, ?_⟩
    rw [Polynomial.eval₂_eq_eval_map]
    change (p.map j).eval _ = 0
    rw [hp, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  refine ⟨h, ?_⟩
  have h1 : p.map (algebraMap B (integralClosure B κ)) = ∏ i, (X - C (⟨a i, h i⟩ : integralClosure B κ)) := by
    apply Polynomial.map_injective (integralClosure B κ).val.toRingHom Subtype.val_injective
    rw [Polynomial.map_map, Polynomial.map_prod]
    simp only [Polynomial.map_sub, map_X, map_C]
    exact hp
  have h2 := congrArg (Polynomial.map Φ) h1
  rw [Polynomial.map_map, Polynomial.map_prod] at h2
  simp only [Polynomial.map_sub, map_X, map_C] at h2
  rw [Polynomial.map_map]
  refine Eq.trans ?_ h2
  congr 1
  exact RingHom.ext fun b => (hΦ b).symm

theorem UpperTheory.V.Pr.irrNormal :
    UpperTheory.V.Pr.IrrNormal := by
  intro G κ k B _ _ _ _ _ n hn r hr j φ χ hj hred D _ ι ψ hψ U _ hdist hχ
  rcases UpperTheory.V.Pr.cliffPrime G κ n hn r hr U with h | h | ⟨b, la, π, -, hla, hπ, htr⟩
  · exact h
  · exfalso
    have h2 := hn.two_le
    obtain ⟨g, hg, hne⟩ := hdist ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp)
    obtain ⟨c, hc⟩ := h _ hg
    have hall : ∀ a, ((ψ a g : κˣ) : κ) = c := fun a => by
      have h1 := hψ g
      rw [hc, Matrix.smul_one_eq_diagonal, Matrix.charpoly_diagonal] at h1
      have h3 := congrArg (Polynomial.eval ((ψ a g : κˣ) : κ)) h1
      rw [UpperTheory.V.Pr.chPoly, eval_prod, eval_prod,
        Finset.prod_eq_zero (f := fun i => eval ((ψ a g : κˣ) : κ) (X - C ((ψ i g : κˣ) : κ)))
          (Finset.mem_univ a) (by simp), Finset.prod_eq_zero_iff] at h3
      obtain ⟨_, _, h4⟩ := h3
      simpa [sub_eq_zero] using h4
    exact hne (Units.ext ((hall _).trans (hall _).symm))
  exfalso
  choose c hc using hπ
  have hb : ∀ i (x y : κ), x • b i = y • b i → x = y := fun i x y h =>
    smul_left_injective κ (b.ne_zero i) h
  have c1 : ∀ i, c 1 i = 1 := fun i => by
    have := hc 1 i
    simp only [UpperTheory.V.Pr.gm, map_one, Units.val_one, Matrix.one_mulVec, Equiv.Perm.coe_one, id] at this
    exact hb i _ _ (by rw [← this, one_smul])
  have cmul : ∀ g h i, c (g * h) i = c g (π h i) * c h i := fun g h i => by
    have := hc (g * h) i
    simp only [UpperTheory.V.Pr.gm, map_mul, Units.val_mul, ← Matrix.mulVec_mulVec] at this
    rw [hc h i, Matrix.mulVec_smul, hc g, smul_smul] at this
    rw [mul_comm]
    exact (hb _ _ _ this).symm
  have cne : ∀ g i, c g i ≠ 0 := fun g i h0 => by
    have := cmul g⁻¹ g i
    rw [inv_mul_cancel, c1, h0, mul_zero] at this
    exact one_ne_zero this
  have cconj : ∀ g h i, π h = 1 → c (g * h * g⁻¹) (π g i) = c h i := fun g h i hh => by
    have e1 := cmul (g * h * g⁻¹) g i
    rw [inv_mul_cancel_right, cmul, hh] at e1
    apply mul_right_cancel₀ (cne g i)
    rw [← e1, mul_comm]; rfl
  have hU : ∀ u ∈ U, π u = 1 := fun u hu => by
    ext i
    by_contra hne
    have e := (hla i ⟨u, hu⟩).symm.trans (hc u i)
    have e2 := congrArg (fun v => b.repr v (π u i)) e
    have hne' : i ≠ π u i := fun h => hne (by rw [← h]; rfl)
    simp [Finsupp.single_apply, hne'] at e2
    exact cne u i e2.symm
  let kap : Fin n → π.ker →* κ := fun i =>
    { toFun := fun h => c h i
      map_one' := c1 i
      map_mul' := fun g h => by
        have := cmul g h i
        rw [(MonoidHom.mem_ker.1 h.2)] at this
        exact this }
  have hchar : ∀ h, π h = 1 → (UpperTheory.V.Pr.gm r h).charpoly = ∏ i, (X - C (c h i)) := fun h hh =>
    charpoly_of_basis _ b _ fun i => by rw [hc, hh]; rfl

  have hD : ∀ d, π (ι d) = 1 := by
    let e : U.comap ι →* π.ker :=
      (ι.comp (U.comap ι).subtype).codRestrict π.ker fun u => hU _ u.2
    obtain ⟨σ, hσ⟩ := UpperTheory.V.Pr.charPerm (U.comap ι) κ n (fun i => (ψ i).comp (U.comap ι).subtype)
      (fun i => ((kap i).comp e).toHomUnits) (fun u => by
        have := hψ u
        rw [hchar _ (hU _ u.2)] at this
        exact this.symm)
    have hσ' : ∀ i u, ι u ∈ U → c (ι u) i = (ψ (σ i) u : κˣ) := fun i u hu => by
      have := congrArg Units.val (DFunLike.congr_fun (hσ i) (⟨u, hu⟩ : U.comap ι))
      exact this
    intro d
    refine Equiv.ext fun i => ?_
    by_contra hne
    obtain ⟨u, hu, hne'⟩ := hdist (σ (π (ι d) i)) (σ i) (fun h => hne (σ.injective h))
    apply hne'
    have e1 := cconj (ι d) (ι u) i (hU _ hu)
    have hu' : ι (d * u * d⁻¹) ∈ U := by
      rw [map_mul, map_mul, map_inv]; exact Subgroup.Normal.conj_mem _ hu _
    rw [← map_inv, ← map_mul, ← map_mul, hσ' _ _ hu', hσ' _ _ hu, map_mul, map_mul, map_inv,
      mul_inv_cancel_comm] at e1
    exact Units.ext e1
  obtain ⟨S, Φ, hS⟩ := reduce_roots j hj φ
  let t : kˣ →* (AlgebraicClosure k)ˣ := Units.map (algebraMap k (AlgebraicClosure k)).toMonoidHom
  have ht : Function.Injective t := Units.map_injective (algebraMap k (AlgebraicClosure k)).injective
  have key : ∀ h, π h = 1 → ∃ hh : ∀ i, c h i ∈ S,
      UpperTheory.V.Pr.chPoly (fun i => t.comp (χ i)) h = ∏ i, (X - C (Φ ⟨c h i, hh i⟩)) := fun h hh => by
    obtain ⟨p, hp1, hp2⟩ := hred h
    obtain ⟨hm, hq⟩ := hS n p _ (hp1.trans (hchar h hh))
    refine ⟨hm, ?_⟩
    rw [← hq, hp2, UpperTheory.V.Pr.chPoly, UpperTheory.V.Pr.chPoly, Polynomial.map_prod]
    simp only [Polynomial.map_sub, map_X, map_C]
    rfl
  choose hmem hkey using key
  let kb : Fin n → π.ker →* AlgebraicClosure k := fun i =>
    Φ.toMonoidHom.comp ((kap i).codRestrict S fun h => hmem h h.2 i)
  obtain ⟨τ, hτ⟩ := UpperTheory.V.Pr.charPerm π.ker (AlgebraicClosure k) n
    (fun i => (t.comp (χ i)).comp π.ker.subtype) (fun i => (kb i).toHomUnits) (fun h => hkey h h.2)
  have hτ' : ∀ i h (hh : π h = 1), Φ ⟨c h i, hmem h hh i⟩ = (t (χ (τ i) h) : (AlgebraicClosure k)ˣ) :=
    fun i h hh => by
      have := congrArg Units.val (DFunLike.congr_fun (hτ i) (⟨h, hh⟩ : π.ker))
      exact this
  obtain ⟨a, a', d, hne⟩ := hχ
  obtain ⟨g, hg⟩ := htr (τ.symm a') (τ.symm a)
  apply hne
  apply ht
  apply Units.ext
  have hc' : π (g * ι d * g⁻¹) = 1 := by rw [map_mul, map_mul, hD, mul_one, map_inv, mul_inv_cancel]
  have e1 := hτ' (τ.symm a) _ hc'
  have e2 := hτ' (τ.symm a') _ (hD d)
  rw [Equiv.apply_symm_apply] at e1 e2
  rw [map_mul (χ a), map_mul (χ a), map_inv (χ a), mul_inv_cancel_comm] at e1
  rw [← e1, ← e2]
  congr 1
  apply Subtype.ext
  show c _ _ = c _ _
  rw [← hg]
  exact cconj _ _ _ (hD d)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.FinCrit
open IsLocalRing UpperTheory.V.Alg

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete
  UpperTheory.V.Pr.IsCD.fin UpperTheory.V.Pr.IsCD.isLocalHom

private theorem fc_abs (D V : Type) [CommRing D] [IsDomain D] [IsNoetherianRing D] [IsLocalRing D]
    [IsAdicComplete (maximalIdeal D) D] [Finite (ResidueField D)] [Ring.DimensionLEOne D]
    [CommRing V] [IsDomain V] [ValuationRing V] [Algebra D V] [FaithfulSMul D V] [IsLocalHom (algebraMap D V)]
    (hm : maximalIdeal D ≠ ⊥)
    (hB : ∀ x : V, ∃ c : D, c ≠ 0 ∧ ∃ b : D, algebraMap D V c * x = algebraMap D V b) :
    IsDiscreteValuationRing V ∧ IsAdicComplete (maximalIdeal V) V ∧ Finite (ResidueField V) := by
  have hVn : IsNoetherianRing V := (GlobalTheory.krullAkizuki_of_birational (A := D) (B := V) hB).1
  obtain ⟨t, ht, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hm
  have hle : (maximalIdeal D).map (algebraMap D V) ≤ maximalIdeal V :=
    Ideal.map_le_iff_le_comap.2 fun a ha => map_nonunit (algebraMap D V) a ha
  have h1 := GlobalTheory.finite_quotient_span_of_birational hB ht0
  have hs : Ideal.span {algebraMap D V t} ≤ (maximalIdeal D).map (algebraMap D V) :=
    (Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mem_map_of_mem _ ht)
  have h2 : Module.Finite D (V ⧸ (maximalIdeal D).map (algebraMap D V)) :=
    Module.Finite.of_surjective (Ideal.Quotient.factorₐ D hs).toLinearMap
      (Ideal.Quotient.factor_surjective hs)
  have h3 : IsHausdorff ((maximalIdeal D).map (algebraMap D V)) V :=
    IsHausdorff.of_isLocalRing _ _ (ne_top_of_le_ne_top (maximalIdeal.isMaximal V).ne_top hle)
  have h4 : Module.Finite D V := GlobalTheory.FormalIsogeny.finite_of_finite_quotient_map (maximalIdeal D)
  have hnf : ¬ IsField V := by
    rw [isField_iff_maximalIdeal_eq]
    intro h
    have := hle (Ideal.mem_map_of_mem _ ht)
    rw [h, Ideal.mem_bot] at this
    exact ht0 (FaithfulSMul.algebraMap_injective D V (this.trans (map_zero _).symm))
  have hval : ValuationRing V := inferInstance
  refine ⟨((IsDiscreteValuationRing.TFAE V hnf).out 2 1).mp hval,
    GlobalTheory.FormalIsogeny.isAdicComplete_maximalIdeal_of_finite D V, ?_⟩
  have : Module.Finite (ResidueField D) (ResidueField V) := inferInstance
  exact Module.finite_of_finite (ResidueField D)

private theorem fc_point (D : Type) [CommRing D] [IsDomain D] [IsNoetherianRing D] [IsLocalRing D]
    [IsAdicComplete (maximalIdeal D) D] [Finite (ResidueField D)] (hd : ringKrullDim D = 1) :
    ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : IsDiscreteValuationRing A),
      IsAdicComplete (maximalIdeal A) A ∧ Finite (ResidueField A) ∧
        ∃ φ : D →+* A, Function.Injective φ ∧ IsLocalHom φ := by
  have hk : Ring.KrullDimLE 1 D := by
    rw [Ring.krullDimLE_iff, hd]; exact le_rfl
  have : Ring.DimensionLEOne D :=
    ⟨fun {q} hq hq' => Ring.krullDimLE_one_iff_of_noZeroDivisors.mp hk q hq hq'⟩
  have hm : maximalIdeal D ≠ ⊥ := fun h => by
    rw [ringKrullDim_eq_zero_of_isField (isField_iff_maximalIdeal_eq.2 h)] at hd
    exact absurd hd (by decide)
  obtain ⟨V, hV, hloc⟩ := IsLocalRing.exists_factor_valuationRing (algebraMap D (FractionRing D))
  let φ : D →+* V := (algebraMap D (FractionRing D)).codRestrict V.toSubring hV
  have hφ : Function.Injective φ := fun a b h =>
    IsFractionRing.injective D (FractionRing D) (congrArg Subtype.val h)
  letI : Algebra D V := φ.toAlgebra
  have : FaithfulSMul D V := (faithfulSMul_iff_algebraMap_injective _ _).mpr hφ
  have hl : IsLocalHom (algebraMap D V) := hloc
  obtain ⟨h1, h2, h3⟩ := fc_abs D V hm fun x => by
    obtain ⟨⟨b, c⟩, h⟩ := IsLocalization.surj (nonZeroDivisors D) (x : FractionRing D)
    exact ⟨c, nonZeroDivisors.coe_ne_zero c, b, Subtype.ext ((mul_comm _ _).trans h)⟩
  exact ⟨V, inferInstance, inferInstance, h1, h2, h3, φ, hφ, hl⟩

private theorem fc_finres (O R : Type) [CommRing O] [IsLocalRing O] [Finite (ResidueField O)] [CommRing R]
    [Algebra O R] [IsCO O R] : Finite (ResidueField R) :=
  Finite.of_surjective _ (resMap_bijective O R).2

private theorem fc_sign {σ : Type} (wt : σ → ℤ) (n : σ →₀ ℕ) (hn : n ≠ 0) (hw : Finsupp.weight wt n = 0)
    (P : σ → Prop) (h0 : ∀ i, wt i = 0 → P i) (h : (∀ i, wt i < 0 → P i) ∨ ∀ i, 0 < wt i → P i) :
    ∃ i ∈ n.support, P i := by
  by_contra hc
  push Not at hc
  have hne := Finsupp.support_nonempty_iff.2 hn
  rw [Finsupp.weight_apply, Finsupp.sum] at hw
  rcases h with h | h
  · refine absurd hw (ne_of_gt (Finset.sum_pos (fun i hi => ?_) hne))
    have h1 : 0 < wt i := by
      rcases lt_trichotomy (wt i) 0 with e | e | e
      · exact absurd (h i e) (hc i hi)
      · exact absurd (h0 i e) (hc i hi)
      · exact e
    have := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hi)
    rw [nsmul_eq_mul]
    positivity
  · refine absurd hw (ne_of_lt (Finset.sum_neg (fun i hi => ?_) hne))
    have h1 : wt i < 0 := by
      rcases lt_trichotomy (wt i) 0 with e | e | e
      · exact e
      · exact absurd (h0 i e) (hc i hi)
      · exact absurd (h i e) (hc i hi)
    have := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hi)
    rw [nsmul_eq_mul]
    exact mul_neg_of_pos_of_neg (by exact_mod_cast this) h1

private theorem fc_contract {O R : Type} [CommRing O] [CommRing R] [Algebra O R] (W : WPres O ℤ R) (ϖ : O)
    (b : W.gr 0) (hb : ((b : W.A) : R) ∈ Ideal.span {algebraMap O R ϖ}) :
    b ∈ Ideal.span {algebraMap O (W.gr 0) ϖ} := by
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hb
  obtain ⟨g, rfl⟩ := W.surj r
  obtain ⟨f, hf, hfb⟩ : ((b : W.A) : R) ∈ W.part 0 := b.2
  have hfb' : W.π f = ((b : W.A) : R) := hfb
  have h1 : ϖ • g - f ∈ RingHom.ker W.π := by
    rw [RingHom.mem_ker, map_sub, map_smul, hfb', ← hr, Algebra.smul_def, mul_comm, sub_self]
  have h2 := W.homog _ h1 0
  have h3 : wcomp O W.wt 0 f = f := by
    ext n
    rw [coeff_wcomp]
    split_ifs with h
    · rfl
    · exact (hf n h).symm
  rw [map_sub, map_smul, h3, RingHom.mem_ker, map_sub, map_smul, hfb', sub_eq_zero] at h2
  have hp : W.π (wcomp O W.wt 0 g) ∈ W.part 0 := ⟨_, wcomp_mem O W.wt 0 g, rfl⟩
  refine Ideal.mem_span_singleton'.2 ⟨⟨⟨_, W.part_le_A hp⟩, hp⟩, Subtype.ext (Subtype.ext ?_)⟩
  rw [← h2, Algebra.smul_def, mul_comm]
  rfl

theorem UpperTheory.V.Pr.finCrit :
    UpperTheory.V.Pr.FinCrit := by
  intro O R _ _ _ _ _ _ _ _ W hz H
  classical
  haveI hB : IsCO O (W.gr 0) := UpperTheory.V.Alg.wPres_gr_zero_isCO_of_mem_maximalIdeal O ℤ R W hz
  obtain ⟨h1, u, hu, hmax⟩ := UpperTheory.V.Alg.wPres_maximalIdeal_gr_zero_eq_sup_span_monomials O ℤ R W hz
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hmO := hϖ.maximalIdeal_eq
  have hJ : (maximalIdeal O).map (algebraMap O (W.gr 0)) = Ideal.span {algebraMap O (W.gr 0) ϖ} := by
    rw [hmO, Ideal.map_span, Set.image_singleton]
  have hrad : ∀ b ∈ u, ((b : W.A) : R) ∈ (Ideal.span {algebraMap O R ϖ}).radical := by
    intro b hb
    rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
    rintro Q ⟨hQ, hQp⟩
    by_contra hbQ
    have hbm : ((b : W.A) : R) ∈ maximalIdeal R :=
      (h1 b).1 (hmax ▸ Ideal.mem_sup_right (Ideal.subset_span hb))
    let x : R := ((b : W.A) : R)
    obtain ⟨(p : Ideal R), ⟨hp, hQle, hbp⟩, hmaxp⟩ := set_has_maximal_iff_noetherian.mpr
      (inferInstance : IsNoetherian R R) {p : Ideal R | p.IsPrime ∧ Q ≤ p ∧ x ∉ p}
      ⟨Q, hQp, le_rfl, hbQ⟩
    have hd : ringKrullDim (R ⧸ p) = 1 := by
      let q := Ideal.Quotient.mk p
      have : Nontrivial (R ⧸ p) := Ideal.Quotient.nontrivial_iff.mpr hp.ne_top
      have : IsLocalRing (R ⧸ p) := IsLocalRing.of_surjective' q Ideal.Quotient.mk_surjective
      let m := maximalIdeal (R ⧸ p)
      have : m.IsPrime := inferInstanceAs (maximalIdeal (R ⧸ p)).IsPrime
      have hx0 : q x ≠ 0 := fun h => hbp (Ideal.Quotient.eq_zero_iff_mem.mp h)
      have := IsLocalHom.of_surjective q Ideal.Quotient.mk_surjective
      have hxm : q x ∈ m := map_nonunit q x hbm
      have hlt : ⊥ < m := bot_lt_iff_ne_bot.mpr fun e => hx0 (by simpa [e] using hxm)
      have hxP (P : Ideal (R ⧸ p)) [P.IsPrime] (hP0 : P ≠ ⊥) : q x ∈ P := by
        by_contra hx
        have hle : p ≤ P.comap q := fun y hy => by
          change q y ∈ P
          rw [Ideal.Quotient.eq_zero_iff_mem.mpr hy]
          exact P.zero_mem
        refine hmaxp (P.comap q) ⟨Ideal.comap_isPrime _ _, hQle.trans hle, hx⟩
          (lt_of_le_of_ne hle fun e => hP0 ?_)
        rw [← Ideal.map_comap_of_surjective q Ideal.Quotient.mk_surjective P, ← e]
        exact Ideal.map_quotient_self p
      let J : Ideal (R ⧸ p) := Ideal.span {q x}
      have hJm : J ≤ m := (Ideal.span_singleton_le_iff_mem _).2 hxm
      -- Every nonzero element of m belongs to a minimal prime over J.
      have hcover : (m : Set (R ⧸ p)) ⊆ ⋃ P ∈ J.minimalPrimes, ((id P : Ideal _) : Set _) := by
        intro y hy
        simp only [Set.mem_iUnion, id, SetLike.mem_coe]
        by_cases hy0 : y = 0
        · obtain ⟨P, hP, -⟩ := Ideal.exists_minimalPrimes_le hJm
          exact ⟨P, hP, hy0 ▸ P.zero_mem⟩
        obtain ⟨P, hP, -⟩ := Ideal.exists_minimalPrimes_le
          ((Ideal.span_singleton_le_iff_mem m).2 hy)
        have hPp : P.IsPrime := hP.1.1
        have hyP : y ∈ P := (Ideal.span_singleton_le_iff_mem _).1 hP.1.2
        have hP1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hP
        have hJP : J ≤ P := (Ideal.span_singleton_le_iff_mem _).2
          (hxP P fun e => hy0 (by simpa [e] using hyP))
        obtain ⟨T, hT, hTP⟩ := Ideal.exists_minimalPrimes_le hJP
        have hTp : T.IsPrime := hT.1.1
        have hxT : q x ∈ T := (Ideal.span_singleton_le_iff_mem _).1 hT.1.2
        have hT0 : ⊥ < T := bot_lt_iff_ne_bot.mpr fun e => hx0 (by simpa [e] using hxT)
        refine ⟨T, hT, ?_⟩
        rcases hTP.eq_or_lt with e | hTP
        · exact e ▸ hyP
        · exfalso
          have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hT0
          have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hTP
          have h3 : (⊥ : Ideal (R ⧸ p)).height + 1 + 1 ≤ 1 :=
            (add_le_add h1 le_rfl).trans (h2.trans hP1)
          simp at h3
          exact absurd h3 (by decide)
      obtain ⟨P, hP, hmP⟩ := (Ideal.subset_union_prime_finite
        J.finite_minimalPrimes_of_isNoetherianRing (f := id) ⊥ ⊥
        (fun i hi _ _ => hi.1.1)).mp hcover
      have hh : m.height ≤ 1 := (Ideal.height_mono hmP).trans
        (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes J P hP)
      have hm1 : m.height = 1 := le_antisymm hh
        (le_trans le_add_self (Ideal.height_add_one_le_of_lt_of_isPrime hlt))
      rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, ← show m = maximalIdeal (R ⧸ p) from rfl, hm1]
      rfl
    haveI : IsCO O (R ⧸ p) := UpperTheory.V.Alg.co_quot O R (R ⧸ p) (Ideal.Quotient.mkₐ O p)
      Ideal.Quotient.mk_surjective
    haveI := fc_finres O (R ⧸ p)
    obtain ⟨A, _, _, _, hc, hf, φ, hφ, hl⟩ := fc_point (R ⧸ p) hd
    letI : Algebra O A := (φ.comp (algebraMap O (R ⧸ p))).toAlgebra
    haveI : UpperTheory.V.Pr.IsCD O A :=
      { complete := hc
        isLocalHom := inferInstanceAs (IsLocalHom (φ.comp (algebraMap O (R ⧸ p))))
        fin := hf }
    let f : R →ₐ[O] A := { φ.comp (Ideal.Quotient.mk p) with commutes' := fun _ => rfl }
    have hker : ∀ x, f x = 0 ↔ x ∈ p := fun x => by
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← map_eq_zero_iff φ hφ]
      rfl
    haveI := IsLocalHom.of_surjective (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
    have hfl : IsLocalHom f := ⟨fun a ha =>
      IsLocalHom.map_nonunit (f := φ.comp (Ideal.Quotient.mk p)) a ha⟩
    obtain ⟨h0, hs⟩ := H A f hfl fun a ha => by
      rw [← f.commutes, hker]
      rw [hmO] at ha
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      rw [map_mul]
      exact p.mul_mem_left _ (hQle (hQ (Ideal.mem_span_singleton_self _)))
    obtain ⟨n, hn, hw, hbn⟩ := hu b hb
    obtain ⟨i, hi, hi0⟩ := fc_sign W.wt n hn hw _ h0 hs
    apply hbp
    change ((b : W.A) : R) ∈ p
    rw [hbn]
    exact Ideal.prod_mem _ hi (Ideal.pow_mem_of_mem _ ((hker _).1 hi0) _
      (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.1 hi)))
  have hrad' : maximalIdeal (W.gr 0) ≤ ((maximalIdeal O).map (algebraMap O (W.gr 0))).radical := by
    rw [hmax]
    refine sup_le Ideal.le_radical (Ideal.span_le.2 fun b hb => ?_)
    obtain ⟨N, hN⟩ := hrad b hb
    exact ⟨N, hJ ▸ fc_contract W ϖ (b ^ N) hN⟩
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad' (IsNoetherian.noetherian _)
  haveI : Finite (W.gr 0 ⧸ maximalIdeal (W.gr 0)) := fc_finres O (W.gr 0)
  haveI := Ideal.finite_quotient_pow (IsNoetherian.noetherian (maximalIdeal (W.gr 0))) N
  haveI : Finite (W.gr 0 ⧸ (maximalIdeal O).map (algebraMap O (W.gr 0))) :=
    Finite.of_surjective _ (Ideal.Quotient.factor_surjective hN)
  haveI : IsHausdorff ((maximalIdeal O).map (algebraMap O (W.gr 0))) (W.gr 0) :=
    IsHausdorff.of_isLocalRing _ _ (ne_top_of_le_ne_top (maximalIdeal.isMaximal (W.gr 0)).ne_top
      (le_sup_left.trans hmax.ge))
  haveI : Module.Finite O (W.gr 0) := GlobalTheory.FormalIsogeny.finite_of_finite_quotient_map (maximalIdeal O)
  let e : W.gr 0 →ₗ[O] W.part 0 :=
    { toFun := fun b => ⟨((b : W.A) : R), b.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact Module.Finite.of_surjective e fun x => ⟨⟨⟨x.1, W.part_le_A x.2⟩, x.2⟩, rfl⟩
end
