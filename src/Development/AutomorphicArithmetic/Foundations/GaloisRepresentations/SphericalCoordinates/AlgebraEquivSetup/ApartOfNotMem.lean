module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.CodiffUnit
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.HeckeTraceEq
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CompLocOfApart
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.InvPol

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.ApartOfNotMem
noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC
open GlobalTheory.SplitPts (conjE)
open GroundTheory.Global.AdeleBaseChange (finiteAdeleMap)
open GlobalTheory.LFun (KGL)
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct

namespace UpperTheory.Gal.W2.Seed

def OHat (p : ℕ) (E : Type) [Field E] [NumberField E] : AddSubgroup (AfP p ⊗[ℚ] E) :=
  AddSubgroup.closure {z | ∃ (a : AfP p) (x : 𝓞 E), IsIntAf a ∧ z = a ⊗ₜ (x : E)}

structure AdQ (p : ℕ) where
  ρ : AfQ →+* AfP p
  surj : Function.Surjective ρ
  ker : ∀ a, ρ a = 0 ↔ ∀ v : Plc ℚ, (p : 𝓞 ℚ) ∉ v.asIdeal → a v = 0
  int : ∀ a, IsIntAf (ρ a) ↔ ∀ v : Plc ℚ, (p : 𝓞 ℚ) ∉ v.asIdeal → Valued.v (a v) ≤ 1

structure AdT (p : ℕ) (E : Type) [Field E] [NumberField E] [IsCMField E] extends AdQ p where
  Φ : Af E →+* AfP p ⊗[ℚ] E
  Φ_E : ∀ x : E, Φ (algebraMap E (Af E) x) = 1 ⊗ₜ x
  Φ_Q : ∀ a : AfQ, Φ (finiteAdeleMap ℚ E a) = ρ a ⊗ₜ 1
  Φ_surj : Function.Surjective Φ
  Φ_ker : ∀ x, Φ x = 0 ↔ ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → pLoc E w x = 0
  Φ_int : ∀ x, Φ x ∈ OHat p E ↔ ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → Valued.v (pLoc E w x) ≤ 1
  Φ_conj : ∀ x, Φ (conjFin (conjE E) x) = conjT E (AfP p) (Φ x)

def AdQEx : Prop := ∀ (p : ℕ) [Fact p.Prime], Nonempty (AdQ p)

def AdTensor : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∃ ι : AfQ ⊗[ℚ] E ≃+* Af E,
  (∀ (a : AfQ) (x : E), ι (a ⊗ₜ x) = finiteAdeleMap ℚ E a * algebraMap E (Af E) x) ∧
  (∀ y, y ∈ AddSubgroup.closure {y : AfQ ⊗[ℚ] E | ∃ (a : AfQ) (x : 𝓞 E), (∀ v : Plc ℚ, Valued.v (a v) ≤ 1) ∧ y = a ⊗ₜ (x : E)} ↔
    ∀ w : Plc E, Valued.v (pLoc E w (ι y)) ≤ 1) ∧
  ∀ a : AfQ, conjFin (conjE E) (finiteAdeleMap ℚ E a) = finiteAdeleMap ℚ E a

def IdemP : Prop := ∀ (p : ℕ) [Fact p.Prime] (E : Type) [Field E] [NumberField E], ∃ e : AfQ,
  (∀ v : Plc ℚ, ((p : 𝓞 ℚ) ∈ v.asIdeal → e v = 1) ∧ ((p : 𝓞 ℚ) ∉ v.asIdeal → e v = 0)) ∧
  ∀ w : Plc E, ((p : 𝓞 E) ∈ w.asIdeal → pLoc E w (finiteAdeleMap ℚ E e) = 1) ∧
    ((p : 𝓞 E) ∉ w.asIdeal → pLoc E w (finiteAdeleMap ℚ E e) = 0)

def AdTEx : Prop := ∀ (p : ℕ) [Fact p.Prime] (E : Type) [Field E] [NumberField E] [IsCMField E], Nonempty (AdT p E)

def IsMu {R E : Type} [CommRing R] [Algebra ℚ R] [Field E] [NumberField E] {n : ℕ}
    (μ : R ⊗[ℚ] Matrix (Fin n) (Fin n) E ≃+* Matrix (Fin n) (Fin n) (R ⊗[ℚ] E)) : Prop :=
  ∀ (r : R) (x : Matrix (Fin n) (Fin n) E) i k, μ (r ⊗ₜ x) i k = r ⊗ₜ x i k

def MuEx : Prop := ∀ (R E : Type) [CommRing R] [Algebra ℚ R] [Field E] [NumberField E] (n : ℕ),
  ∃ μ : R ⊗[ℚ] Matrix (Fin n) (Fin n) E ≃+* Matrix (Fin n) (Fin n) (R ⊗[ℚ] E), IsMu μ

def MuStar : Prop := ∀ (R E : Type) [CommRing R] [Algebra ℚ R] [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ)
  (μ : R ⊗[ℚ] Matrix (Fin n) (Fin n) E ≃+* Matrix (Fin n) (Fin n) (R ⊗[ℚ] E)), IsMu μ → ∀ x,
  Matrix.diagonal (fun i => (1 : R) ⊗ₜ[ℚ] (A.dg n i : E)) * μ (starT (hermStar (A.H n) (A.det_ne n)) R x).unop =
    ((μ x).map (conjT E R))ᵀ * Matrix.diagonal (fun i => (1 : R) ⊗ₜ[ℚ] (A.dg n i : E))

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def IsIso (A : Arith E) (n : ℕ) (a : GL (Fin n) (Af E)) : Prop :=
  (a.val.map (conjFin (conjE E)))ᵀ * Matrix.diagonal (fun i => algebraMap E (Af E) (A.dg n i : E)) * a.val = 1 ∧
    ∀ (w : Plc E) (q : ℕ), q.Prime → A.Good q → (q : 𝓞 E) ∈ w.asIdeal → GeneralLinearGroup.map (pLoc E w) a ∈ KGL w (n := n)

def Arith.β₀ (A : Arith E) (n : ℕ) : (Matrix (Fin n) (Fin n) E)ˣ :=
  GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal fun i => (A.dg n i : E)) (by
    rw [Matrix.det_diagonal, Finset.prod_ne_zero_iff]
    intro i _
    have := A.c_ne
    unfold Arith.dg; split_ifs <;> simp [this])

variable {A : Arith E} {n p : ℕ} [Fact p.Prime]

def Setup.mx (S : Setup A n p) (h : S.G.GAf) : AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E :=
  ((h : (AfP p ⊗[ℚ] S.G.C)ˣ × (AfP p)ˣ).1 : AfP p ⊗[ℚ] S.G.C)

structure Tr (S : Setup A n p) extends AdT p E where
  μ : AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E ≃+* Matrix (Fin n) (Fin n) (AfP p ⊗[ℚ] E)
  mu : IsMu μ
  a : GL (Fin n) (Af E)
  iso : IsIso A n a
  j : GUf E n →* S.G.GAf
  j_mx : ∀ g, μ (S.mx (j g)) = (a * mat g * a⁻¹).val.map Φ
  j_sim : ∀ g, ((uSimR (AfP p) (j g) : (AfP p)ˣ) : AfP p) = ρ (sim g : AfQˣ)
  sec : S.G.GAf →* GUf E n
  j_sec : ∀ h, j (sec h) = h
  sec_p : ∀ h (w : Plc E), (p : 𝓞 E) ∈ w.asIdeal → comp w (sec h) = 1
  j_eq : ∀ g g', j g = j g' ↔ ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → comp w g = comp w g'

def JEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (T : AdT p E) (μ : AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E ≃+* Matrix (Fin n) (Fin n) (AfP p ⊗[ℚ] E)), IsMu μ →
  ∀ a : GL (Fin n) (Af E), IsIso A n a → ∃ j : GUf E n →* S.G.GAf,
    (∀ g, μ (S.mx (j g)) = (a * mat g * a⁻¹).val.map T.Φ) ∧
    ∀ g, ((uSimR (AfP p) (j g) : (AfP p)ˣ) : AfP p) = T.ρ (sim g : AfQˣ)

def JEq : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (T : AdT p E) (μ : AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E ≃+* Matrix (Fin n) (Fin n) (AfP p ⊗[ℚ] E)), IsMu μ →
  ∀ (a : GL (Fin n) (Af E)) (j : GUf E n →* S.G.GAf), (∀ g, μ (S.mx (j g)) = (a * mat g * a⁻¹).val.map T.Φ) →
  (∀ g g' : GUf E n, (∀ w, comp w g = comp w g') → g = g') ∧
  ∀ g g', j g = j g' ↔ ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → comp w g = comp w g'

def JSurj : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (T : AdT p E) (μ : AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E ≃+* Matrix (Fin n) (Fin n) (AfP p ⊗[ℚ] E)), IsMu μ →
  ∀ a : GL (Fin n) (Af E), IsIso A n a → ∀ h : S.G.GAf, ∃ g : GUf E n,
    μ (S.mx h) = (a * mat g * a⁻¹).val.map T.Φ ∧ ∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → comp w g = 1

def IsoEx' : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ), Odd n → ∃ a, IsIso A n a

def TrEx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p),
  Odd n → Nonempty (Tr S)

def LocComm : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Plc E) (hw : IsSplitAt w)
  (x : GL (Fin n) (w.adicCompletion E)) (g : GUf E n), comp w g = 1 → CertificateRingHomMap.loc hw x * g = g * CertificateRingHomMap.loc hw x

theorem apart_of_not_mem {w u : Plc E} (hw : (p : 𝓞 E) ∉ w.asIdeal) (hu : (p : 𝓞 E) ∈ u.asIdeal) : GlobalTheory.Cong.Apart u w := by
  intro h
  apply hw
  have h1 : (p : 𝓞 (maximalRealSubfield E)) ∈ (u.under (𝓞 (maximalRealSubfield E))).asIdeal := by
    show algebraMap _ (𝓞 E) (p : 𝓞 (maximalRealSubfield E)) ∈ u.asIdeal
    simpa using hu
  rw [h] at h1
  have h2 : algebraMap _ (𝓞 E) (p : 𝓞 (maximalRealSubfield E)) ∈ w.asIdeal := h1
  simpa using h2

def Tr.at {S : Setup A n p} (T : Tr S) (hc : LocComm) (w : Plc E) (hw : IsSplitAt w) (hp : (p : 𝓞 E) ∉ w.asIdeal) :
    Loc S.G.GAf (GL (Fin n) (w.adicCompletion E)) where
  pr := (comp w).comp T.sec
  loc := T.j.comp (CertificateRingHomMap.loc hw)
  pr_loc x := by
    have := (T.j_eq (T.sec (T.j (CertificateRingHomMap.loc hw x))) (CertificateRingHomMap.loc hw x)).1 (T.j_sec _) w hp
    simpa using this
  comm x g h := by
    have := congrArg T.j (hc E n w hw x (T.sec g) h)
    simpa [T.j_sec] using this

def LatCoord : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (μ : AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E ≃+* Matrix (Fin n) (Fin n) (AfP p ⊗[ℚ] E)), IsMu μ →
  ∃ ν : AfP p ⊗[ℚ] VQ S.D ≃+ (Fin n → AfP p ⊗[ℚ] E),
    (∀ (r : AfP p) (v : Fin n → 𝓞 E) i, ν (r ⊗ₜ ((1 : ℚ) ⊗ₜ[ℤ] v)) i = r ⊗ₜ (v i : E)) ∧
    (∀ h v, ν (S.L.actG h v) = μ (S.mx h) *ᵥ ν v) ∧ ∀ v, v ∈ LaHat S.D ↔ ∀ i, ν v i ∈ OHat p E

def Cong1 (N : ℕ) (w : Plc E) (x : GL (Fin n) (w.adicCompletion E)) : Prop :=
  ∀ i k, Valued.v ((x.val - 1) i k) ≤ Valued.v (N : w.adicCompletion E)

def KNIff : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (T : Tr S) (g : GUf E n),
  ((∀ v ∈ LaHat S.D, S.L.actG (T.j g) v ∈ LaHat S.D) ↔ ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → ∀ i k,
    Valued.v ((GeneralLinearGroup.map (pLoc E w) (T.a * mat g * T.a⁻¹)).val i k) ≤ 1) ∧
  ∀ N : ℕ, 0 < N → (S.L.CongOne N (T.j g) ↔ ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal →
    Cong1 N w (GeneralLinearGroup.map (pLoc E w) (T.a * mat g * T.a⁻¹)))

def StdForm : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (T : Tr S), ∃ (B : DForm S.G) (x : (AfP p ⊗[ℚ] S.G.C)ˣ) (hx : Triv S.G (AfP p) B.β x 1) (e : GlobalTheory.LKCx.grp S.G B.β →* Gam0 E n),
    (∀ y, ((e y : Gam0 E n) : GL (Fin n) E × ℚˣ) = (y : S.G.Cˣ × ℚˣ)) ∧ ∀ y, GlobalTheory.LKCx.toAfF S.G B.β x 1 hx y = T.j (rat (e y))

def PInt : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (y : Gam0 E n), inclG S.G 1 (locC S.G (y : GL (Fin n) E × ℚˣ)) ∈ LocalSmoothExtension.Kp S.G →
  (∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → comp w (rat y) ∈ KGL w (n := n)) ∧
    ∀ v : Plc ℚ, (p : 𝓞 ℚ) ∈ v.asIdeal → Valued.v (((sim (rat y) : AfQˣ) : AfQ) v) = 1

end UpperTheory.Gal.W2.Seed
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PRepLaws
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

private lemma beta_baseChange {E : Type} [Field E] [NumberField E] {n : ℕ}
    (β : ℚ ⊗[ℤ] (Fin n → 𝓞 E) ≃ₗ[ℚ] (Fin n → E))
    (hβ : ∀ (v : Fin n → 𝓞 E) i, β (1 ⊗ₜ v) i = (v i : E)) (b : 𝓞 E)
    (z : ℚ ⊗[ℤ] (Fin n → 𝓞 E)) :
    β ((DistribSMul.toLinearMap ℤ (Fin n → 𝓞 E) b).baseChange ℚ z) = (b : E) • β z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy, smul_add]
  | tmul q v =>
    have h1 : ∀ w : Fin n → 𝓞 E, q ⊗ₜ[ℤ] w = q • ((1 : ℚ) ⊗ₜ[ℤ] w) := by
      intro w
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have h2 : (DistribSMul.toLinearMap ℤ (Fin n → 𝓞 E) b).baseChange ℚ (q ⊗ₜ[ℤ] v)
        = q ⊗ₜ[ℤ] (b • v) := by
      rw [LinearMap.baseChange_tmul]
      rfl
    rw [h2, h1 (b • v), h1 v, map_smul, map_smul]
    funext i
    simp only [Pi.smul_apply, hβ]
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, RingOfIntegers.coe_eq_algebraMap, Rat.smul_def, mul_left_comm, Algebra.smul_def]

theorem UpperTheory.Gal.W2.Seed.pRepLaws :
    RepLaws := by
  rintro E _ _ _ A n rep ⟨β, hβ, hr⟩
  have hβ1 : ∀ v : Fin n → 𝓞 E, β (1 ⊗ₜ v) = fun i => (v i : E) := fun v => funext (hβ v)
  have hsc : ∀ c : 𝓞 E, rep (algebraMap E (Matrix (Fin n) (Fin n) E) c)
      = (DistribSMul.toLinearMap ℤ (Fin n → 𝓞 E) c).baseChange ℚ := by
    intro c
    refine LinearMap.ext fun z => β.injective ?_
    rw [hr, beta_baseChange β hβ c z, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec,
      Matrix.one_mulVec]
  refine ⟨?_, ?_, hsc, ?_⟩
  · intro x y hxy
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun w => ?_
    obtain ⟨z, rfl⟩ := β.surjective w
    simp only [Matrix.toLin'_apply]
    rw [← hr, ← hr, hxy]
  · intro M
    constructor
    · rintro ⟨x, rfl⟩ b
      rw [← hsc, ← map_mul, ← map_mul, Algebra.commutes]
    · intro hM
      let F0 : (Fin n → E) →ₗ[ℚ] (Fin n → E) := β.toLinearMap ∘ₗ M ∘ₗ β.symm.toLinearMap
      have hF0 : ∀ (b : 𝓞 E) w, F0 ((b : E) • w) = (b : E) • F0 w := by
        intro b w
        obtain ⟨z, rfl⟩ := β.surjective w
        have h := congrArg (fun N => β (N z)) (hM b)
        simp only [Module.End.mul_apply] at h
        rw [beta_baseChange β hβ] at h
        simp only [F0, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
        rw [← beta_baseChange β hβ, LinearEquiv.symm_apply_apply, h]
      have hF : ∀ (e : E) w, F0 (e • w) = e • F0 w := by
        intro e w
        obtain ⟨b, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) e
        have hd0 : (algebraMap (𝓞 E) E d) ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
        apply smul_right_injective (Fin n → E) hd0
        change algebraMap (𝓞 E) E d • F0 _ = algebraMap (𝓞 E) E d • _
        rw [smul_smul, mul_div_cancel₀ _ hd0]
        have h2 := hF0 d ((algebraMap (𝓞 E) E b / algebraMap (𝓞 E) E d) • w)
        have h3 := hF0 b w
        change F0 (algebraMap (𝓞 E) E d • _) = algebraMap (𝓞 E) E d • _ at h2
        change F0 (algebraMap (𝓞 E) E b • _) = algebraMap (𝓞 E) E b • _ at h3
        rw [← h2, smul_smul, mul_div_cancel₀ _ hd0, h3]
      let F : (Fin n → E) →ₗ[E] (Fin n → E) :=
        { toFun := F0, map_add' := F0.map_add, map_smul' := hF }
      refine ⟨Matrix.toLin'.symm F, ?_⟩
      refine LinearMap.ext fun z => β.injective ?_
      rw [hr]
      have hx : (Matrix.toLin'.symm F) *ᵥ β z = F (β z) := by
        rw [← Matrix.toLin'_apply, LinearEquiv.apply_symm_apply]
      rw [hx]
      simp [F, F0]
  · intro x v
    apply β.injective
    rw [hr, hβ1, hβ1]
    funext i
    exact (RingHom.map_mulVec (algebraMap (𝓞 E) E) x v i).symm
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PSetupBasic
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pSetupBasic :
    SetupBasic := by
  intro E _ _ _ A n p _ S
  have key : ∀ v : InfinitePlace E, sigPosH (S.G.gram_herm v) = 1 ↔ v = InfinitePlace.mk A.τ₀ := by
    intro v
    show sigPos (A.herm n) v.embedding = 1 ↔ _
    have h := S.sig v.embedding
    rw [InfinitePlace.mk_embedding] at h
    constructor
    · intro h1
      by_contra hne
      have h0 := (h.2 hne).1
      omega
    · intro hv
      exact (h.1 hv).1
  refine ⟨?_, (key _).2 rfl, fun h => ?_⟩
  · exact Fintype.card_eq_one_iff.2 ⟨⟨InfinitePlace.mk A.τ₀, (key _).2 rfl⟩,
      fun w => Subtype.ext ((key w.1).1 w.2)⟩
  · have h2 : 2 * 1 < Module.finrank ℚ E := by simpa using h
    exact ⟨Or.inl h2, Or.inl h2⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PRepEx
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pRepEx :
    RepEx := by
  intro E _ _ n
  classical
  let b := NumberField.RingOfIntegers.basis E
  let bZ := Pi.basis (fun _ : Fin n => b)
  let bQ := Pi.basis (fun _ : Fin n => NumberField.integralBasis E)
  let b1 := Algebra.TensorProduct.basis ℚ bZ
  refine ⟨b1.equiv bQ (Equiv.refl _), ?_⟩
  let f1 : (Fin n → 𝓞 E) →ₗ[ℤ] (Fin n → E) :=
    ((b1.equiv bQ (Equiv.refl _)).toLinearMap.restrictScalars ℤ) ∘ₗ
      TensorProduct.mk ℤ ℚ (Fin n → 𝓞 E) 1
  let f2 : (Fin n → 𝓞 E) →ₗ[ℤ] (Fin n → E) :=
    LinearMap.pi (fun i => (algebraMap (𝓞 E) E).toIntAlgHom.toLinearMap ∘ₗ LinearMap.proj i)
  have hf : f1 = f2 := by
    refine bZ.ext fun k => ?_
    have hk : f1 (bZ k) = b1.equiv bQ (Equiv.refl _) (b1 k) := by
      rw [Algebra.TensorProduct.basis_apply]
      rfl
    rw [hk, Module.Basis.equiv_apply]
    obtain ⟨i, j⟩ := k
    funext l
    simp [bQ, bZ, f2, Pi.basis_apply, Pi.single_apply, NumberField.integralBasis_apply]
    split_ifs <;> simp
    rfl
  intro v i
  exact congr_fun (LinearMap.congr_fun hf v) i
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PFormPerfSt
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pFormPerfSt :
    FormPerfSt := by
  intro E _ _ _ A n q hP
  obtain ⟨e, he, hx, c', hc⟩ := hP
  refine ⟨e ^ 3, Nat.Coprime.pow_left 3 he, fun f => ?_⟩
  choose x hxf using fun i : Fin n =>
    hx (((f.toAddMonoidHom.comp (AddMonoidHom.single _ i)).comp A.bar.toAddMonoidHom).toIntLinearMap)
  refine ⟨fun i => -((if (i : ℕ) = 0 then c' * (e : 𝓞 E) else c' ^ 2) * x i), ?_⟩
  refine LinearMap.ext fun y => ?_
  rw [Arith.EF_apply]
  have key : ∀ i, A.hd n i * -((if (i : ℕ) = 0 then c' * (e : 𝓞 E) else c' ^ 2) * x i) * A.bar (y i)
      = ((e ^ 2 : ℕ) : 𝓞 E) * (x i * A.bar (y i)) := by
    intro i
    simp only [Arith.hd, Arith.dg]
    push_cast
    split_ifs
    · linear_combination ((e : 𝓞 E) * x i * A.bar (y i)) * hc
    · linear_combination (c' * A.c + (e : 𝓞 E)) * x i * A.bar (y i) * hc
  have hs : ∀ i, A.trd (x i * A.bar (y i)) = (e : ℤ) * f (Pi.single i (y i)) := by
    intro i
    rw [hxf i]
    simp [Arith.bar_bar]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.sum_congr rfl (fun i _ => key i), ← Finset.mul_sum, ← nsmul_eq_mul, map_nsmul, map_sum]
  simp_rw [hs]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← Finset.mul_sum, ← map_sum, Finset.univ_sum_single]
  simp only [LinearMap.smul_apply, nsmul_eq_mul]
  push_cast
  ring
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PPerfCof
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pPerfCof :
    PerfCof := by
  intro E _ _ _ A
  classical
  have hδ : A.δ ≠ 0 := by
    intro h
    have h2 := A.δ_sign A.τ₀ rfl
    rw [h, map_zero, Complex.zero_im] at h2
    exact lt_irrefl _ h2
  let Ψ : E →ₗ[ℚ] Module.Dual ℚ E :=
    ((LinearMap.mul ℚ E).compr₂ (Algebra.trace ℚ E)) ∘ₗ LinearMap.mulLeft ℚ A.δ
  have hΨ : ∀ x z, Ψ x z = Algebra.trace ℚ E (A.δ * x * z) := fun x z => rfl
  have hinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    by_contra hx0
    have h1 := LinearMap.congr_fun hx (A.δ * x)⁻¹
    rw [hΨ, mul_inv_cancel₀ (mul_ne_zero hδ hx0), LinearMap.zero_apply,
      show (1 : E) = algebraMap ℚ E 1 from (map_one _).symm, Algebra.trace_algebraMap] at h1
    have hpos : 0 < Module.finrank ℚ E := Module.finrank_pos
    simp at h1
    omega
  have hsurj : Function.Surjective Ψ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank Subspace.dual_finrank_eq.symm).mp hinj
  let bQ := NumberField.integralBasis E
  let b := NumberField.RingOfIntegers.basis E
  choose ξ hξ using fun i => hsurj (bQ.coord i)
  obtain ⟨y, hy0, hyint⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image ξ)
  have hint : ∀ i, ∃ w : 𝓞 E, algebraMap (𝓞 E) E w = y • ξ i := fun i =>
    (IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).mp
      (hyint _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  choose w hw using hint
  let η : _ → 𝓞 E := fun i => (y : 𝓞 E) * w i
  have hηc : ∀ i, algebraMap (𝓞 E) E (η i) = (y : E) * ((y : E) * ξ i) := by
    intro i
    change algebraMap (𝓞 E) E ((y : 𝓞 E) * w i) = _
    rw [map_mul, map_intCast, hw i, zsmul_eq_mul]
  have hDz : ((y.natAbs * y.natAbs : ℕ) : ℤ) = y * y := Int.natAbs_mul_self
  have hDpos : 0 < y.natAbs * y.natAbs :=
    Nat.mul_pos (Int.natAbs_pos.mpr hy0) (Int.natAbs_pos.mpr hy0)
  have key : ∀ i z, A.trd (η i * z) = ((y.natAbs * y.natAbs : ℕ) : ℤ) * b.coord i z := by
    intro i
    have hlin : A.trd ∘ₗ LinearMap.mulLeft ℤ (η i) = ((y.natAbs * y.natAbs : ℕ) : ℤ) • b.coord i := by
      refine b.ext fun j => ?_
      apply Int.cast_injective (α := ℚ)
      have hb : bQ j = algebraMap (𝓞 E) E (b j) := NumberField.integralBasis_apply E j
      have hc : (((η i * b j : 𝓞 E)) : E) = (y : E) * ((y : E) * ξ i) * bQ j := by
        change algebraMap (𝓞 E) E (η i * b j) = _
        rw [map_mul, hηc, hb]
      rw [LinearMap.comp_apply, LinearMap.mulLeft_apply, A.trd_spec, hc, LinearMap.smul_apply,
        smul_eq_mul, hDz,
        show A.δ * ((y : E) * ((y : E) * ξ i) * bQ j) = ((y * y : ℤ) : ℚ) • (A.δ * ξ i * bQ j) by
          rw [Algebra.smul_def, map_intCast]
          push_cast
          ring,
        map_smul, smul_eq_mul, ← hΨ, hξ]
      rw [Module.Basis.coord_apply, Module.Basis.coord_apply, Module.Basis.repr_self,
        Module.Basis.repr_self]
      rcases eq_or_ne j i with h | h
      · subst h
        simp
      · simp [Finsupp.single_apply, h]
    intro z
    exact LinearMap.congr_fun hlin z
  have hdual : ∀ f : 𝓞 E →ₗ[ℤ] ℤ, ∃ x : 𝓞 E, ∀ z,
      A.trd (x * z) = ((y.natAbs * y.natAbs : ℕ) : ℤ) * f z := by
    intro f
    refine ⟨∑ i, f (b i) • η i, fun z => ?_⟩
    conv_rhs => rw [← b.sum_dual_apply_smul_coord f]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_mul, map_sum, LinearMap.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_mul_assoc, map_smul, key, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
    ring
  have hc0 : A.c ≠ 0 := by
    intro h
    exact A.c_ne (by rw [h]; rfl)
  have hN0 : 0 < Ideal.absNorm (Ideal.span {A.c}) := by
    refine Nat.pos_of_ne_zero ?_
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hc0
  obtain ⟨c', hc'⟩ := Ideal.mem_span_singleton.mp (Ideal.absNorm_mem (Ideal.span {A.c}))
  refine ⟨y.natAbs * y.natAbs * Ideal.absNorm (Ideal.span {A.c}), Nat.mul_pos hDpos hN0,
    fun q hq => ⟨_, hq, fun f => ?_, ⟨c' * ((y.natAbs * y.natAbs : ℕ) : 𝓞 E), ?_⟩⟩⟩
  · obtain ⟨x, hx⟩ := hdual ((Ideal.absNorm (Ideal.span {A.c}) : ℤ) • f)
    refine ⟨x, fun z => ?_⟩
    rw [hx, LinearMap.smul_apply, smul_eq_mul]
    push_cast
    ring
  · rw [← mul_assoc, ← hc']
    push_cast
    ring
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PDiagTrace
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pDiagTrace :
    DiagTrace := by
  intro I _ a M hM
  classical
  have hdec : M = ∑ k, (LinearMap.single ℝ (fun _ : I => ℂ) k) ∘ₗ
      ((Algebra.lmul ℝ ℂ (a k)) ∘ₗ LinearMap.proj k) := by
    refine LinearMap.ext fun z => funext fun j => ?_
    simp [hM, LinearMap.sum_apply, Finset.sum_apply, Pi.single_apply]
  have hk : ∀ k : I, LinearMap.trace ℝ (I → ℂ) ((LinearMap.single ℝ (fun _ : I => ℂ) k) ∘ₗ
      ((Algebra.lmul ℝ ℂ (a k)) ∘ₗ LinearMap.proj k)) = 2 * (a k).re := by
    intro k
    rw [LinearMap.trace_comp_comm', LinearMap.comp_assoc, LinearMap.proj_comp_single_same,
      LinearMap.comp_id, ← Algebra.trace_complex_apply, Algebra.trace_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hdec, map_sum, Finset.sum_congr rfl (fun k _ => hk k), Complex.re_sum, Finset.mul_sum]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PAtPEx
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pAtPEx :
    KqEx → UEx → OrbEx → LiftEx → AtPEx := by
  intro hK hU hO hL E _ _ _ A p _ hs
  obtain ⟨Kq, hω, hKq, hgen⟩ := hK E A
  obtain ⟨s, iotaC, hsC⟩ := hL E A.τ₀
  haveI : CharZero (PadicAlgCl p) := charZero_of_injective_algebraMap (algebraMap ℚ_[p] (PadicAlgCl p)).injective
  haveI hAlg : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
    convert (AlgebraicClosure.isAlgebraic ℚ)
  let iotaA : AlgebraicClosure ℚ →ₐ[ℚ] PadicAlgCl p := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let iotaP : AlgebraicClosure ℚ →+* PadicAlgCl p := iotaA.toRingHom
  let τ₁ : E →+* PadicAlgCl p := iotaP.comp s
  obtain ⟨u, ρ, hover, hρ⟩ := hU E A p hs Kq hω hgen τ₁
  obtain ⟨m, emb, w, hw, hov, hinj, hall⟩ := hO E p Kq u τ₁ hover
  exact ⟨{ Kq := Kq, hKq := hKq, u := u, m := m, emb := emb, emb_over := hov, emb_inj := hinj, emb_all := hall,
           iotaP := iotaP, iotaC := iotaC, ρp := ρ, ρp_eq := ⟨hω, hρ⟩, s := s, s_C := hsC, w := w,
           s_P := fun x => by rw [hw]; rfl }⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PLiftEx
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pLiftEx :
    LiftEx := by
  unfold UpperTheory.Gal.W2.Seed.LiftEx
  intro E _ _ τ₀
  let sA : E →ₐ[ℚ] AlgebraicClosure ℚ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  letI : Algebra E (AlgebraicClosure ℚ) := sA.toRingHom.toAlgebra
  letI : Algebra E ℂ := τ₀.toAlgebra
  haveI : IsScalarTower ℚ E (AlgebraicClosure ℚ) :=
    IsScalarTower.of_algebraMap_eq (fun x => (sA.commutes x).symm)
  haveI hQ : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI : Algebra.IsAlgebraic E (AlgebraicClosure ℚ) := Algebra.IsAlgebraic.tower_top (K := ℚ) E
  let iA : AlgebraicClosure ℚ →ₐ[E] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨sA.toRingHom, iA.toRingHom, fun x => ?_⟩
  exact iA.commutes x
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PUnitMod
noncomputable section

open NumberField

namespace UpperTheory.Gal.W2.Seed

private theorem norm_cast_eq_one {E : Type} [Field E] [NumberField E] (M : ℕ) (b : 𝓞 E) :
    ((Algebra.norm ℤ (1 + (M : 𝓞 E) * b) : ℤ) : ZMod M) = 1 := by
  classical
  let bs := Module.Free.chooseBasis ℤ (𝓞 E)
  rw [Algebra.norm_eq_matrix_det bs, ← eq_intCast (Int.castRingHom (ZMod M)), RingHom.map_det]
  simp only [map_add (f := _), map_one, map_mul, map_natCast, ZMod.natCast_self, zero_mul, add_zero,
    Matrix.det_one, CharP.cast_eq_zero]

theorem pUnitMod : UnitMod := by
  intro E _ _ M c b _ h
  refine ⟨(Algebra.norm ℤ c).natAbs, ?_, ?_⟩
  · rw [← ZMod.isUnit_iff_coprime]
    have key := norm_cast_eq_one (E := E) M b
    rw [← h] at key
    rcases Int.natAbs_eq (Algebra.norm ℤ c) with hn | hn
    · rw [hn, Int.cast_natCast] at key
      rw [key]
      exact isUnit_one
    · rw [hn, Int.cast_neg, Int.cast_natCast, neg_eq_iff_eq_neg] at key
      rw [key]
      exact isUnit_one.neg
  · have hm := Ideal.absNorm_mem (Ideal.span ({c} : Set (𝓞 E)))
    rw [Ideal.absNorm_span_singleton, Ideal.mem_span_singleton] at hm
    obtain ⟨c', hc'⟩ := hm
    exact ⟨c', hc'.symm⟩

end UpperTheory.Gal.W2.Seed
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PPerfOf
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

private theorem exists_trace_rep (E : Type) [Field E] [NumberField E] (f : 𝓞 E →ₗ[ℤ] ℤ) :
    ∃ z : E, ∀ y : 𝓞 E, Algebra.trace ℚ E (z * (y : E)) = ((f y : ℤ) : ℚ) := by
  let g : E →ₗ[ℚ] ℚ := (integralBasis E).constr ℚ (fun i => ((f (RingOfIntegers.basis E i) : ℤ) : ℚ))
  have hg : ∀ y : 𝓞 E, g (y : E) = ((f y : ℤ) : ℚ) := by
    have hext : ((g.restrictScalars ℤ).comp ((Algebra.linearMap (𝓞 E) E).restrictScalars ℤ)) =
        (Algebra.linearMap ℤ ℚ).comp f := by
      refine (RingOfIntegers.basis E).ext fun i => ?_
      simp [g, ← integralBasis_apply]
    intro y
    simpa using LinearMap.congr_fun hext y
  have hnd : (Algebra.traceForm ℚ E).Nondegenerate := traceForm_nondegenerate ℚ E
  refine ⟨(LinearMap.BilinForm.toDual (Algebra.traceForm ℚ E) hnd).symm g, fun y => ?_⟩
  rw [← Algebra.traceForm_apply, ← LinearMap.BilinForm.toDual_def hnd, LinearEquiv.apply_symm_apply]
  exact hg y

theorem UpperTheory.Gal.W2.Seed.pPerfOf :
    PerfOf := by
  intro E _ _ _ A M hgen hc q hq
  obtain ⟨_, e1, he1, hz⟩ := hgen
  obtain ⟨e2, he2, c', hc'⟩ := hc
  refine ⟨e1 * e2, Nat.Coprime.mul_left (he1.coprime_dvd_right hq) (he2.coprime_dvd_right hq), ?_, ⟨c' * e1, ?_⟩⟩
  · intro f
    obtain ⟨z, hzf⟩ := exists_trace_rep E f
    have hzc : InCodiff z := fun y => ⟨f y, hzf y⟩
    obtain ⟨x, hx⟩ := hz z hzc
    refine ⟨(e2 : 𝓞 E) * x, fun y => ?_⟩
    have h := A.trd_spec ((e2 : 𝓞 E) * x * y)
    have hmul : A.δ * ((((e2 : 𝓞 E) * x * y : 𝓞 E)) : E) = ((e1 * e2 : ℕ) : ℚ) • (z * (y : E)) := by
      rw [Algebra.smul_def, map_natCast]
      push_cast
      linear_combination (-((e2 : E) * (y : E))) * hx
    have hq' : ((A.trd ((e2 : 𝓞 E) * x * y) : ℤ) : ℚ) = (((e1 * e2 : ℕ) : ℤ) : ℚ) * ((f y : ℤ) : ℚ) := by
      rw [h, hmul, map_smul, hzf, smul_eq_mul]
      push_cast; ring
    exact_mod_cast hq'
  · rw [← mul_assoc, hc']
    push_cast
    ring
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PSigSt
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

private theorem UpperTheory.Gal.W2.Seed.card_signs {n : ℕ} (hn : 1 ≤ n) (r : Fin n → ℝ)
    (h0 : ∀ i : Fin n, (i : ℕ) = 0 → 0 < r i) (h1 : ∀ i : Fin n, (i : ℕ) ≠ 0 → r i < 0) :
    Fintype.card {i // 0 < r i} = 1 ∧ Fintype.card {i // r i < 0} = n - 1 := by
  have hiff : ∀ i : Fin n, r i < 0 ↔ ¬ 0 < r i := by
    intro i
    by_cases hi : (i : ℕ) = 0
    · have hp := h0 i hi
      exact ⟨fun h => by linarith, fun h => absurd hp h⟩
    · have hq := h1 i hi
      exact ⟨fun _ h' => by linarith, fun _ => hq⟩
  have hc1 : Fintype.card {i // 0 < r i} = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨⟨0, hn⟩, h0 _ rfl⟩, fun ⟨j, hj⟩ => ?_⟩
    apply Subtype.ext
    apply Fin.ext
    by_contra hne
    exact absurd hj (not_lt.mpr (le_of_lt (h1 j hne)))
  refine ⟨hc1, ?_⟩
  rw [Fintype.card_congr (Equiv.subtypeEquivRight hiff), Fintype.card_subtype_compl, hc1,
    Fintype.card_fin]

theorem UpperTheory.Gal.W2.Seed.pSigSt :
    HdSign → SigSt := by
  intro hS E _ _ _ A n hn τ
  have hdiag : gramAt (A.H n) τ = diagonal (fun i => ((τ (A.hd n i : E)).re : ℂ)) := by
    ext i j
    simp only [gramAt, Arith.H, transpose_apply, map_apply, diagonal_apply]
    by_cases h : i = j
    · subst h
      rw [if_pos rfl, if_pos rfl, Complex.ext_iff]
      simp [(hS E A n τ i).1]
    · simp [h, Ne.symm h]
  have aux : ∀ (r : Fin n → ℝ) (M : Matrix (Fin n) (Fin n) ℂ) (hM : M.IsHermitian),
      M = diagonal (fun i => (r i : ℂ)) →
      sigPosH hM = Fintype.card {i // 0 < r i} ∧ sigNegH hM = Fintype.card {i // r i < 0} := by
    rintro r M hM rfl
    exact sigPosH_sigNegH_diagonal n r hM
  obtain ⟨hp, hneg⟩ := aux _ _ (isHermitian_gramAt (A.herm n) τ) hdiag
  refine ⟨fun hτ => ?_, fun hτ => ?_⟩
  · have hcs := card_signs hn _ (fun i hi => (hS E A n τ i).2.2.1 ⟨hτ, hi⟩)
      (fun i hi => (hS E A n τ i).2.2.2 (fun h => hi h.2))
    exact ⟨hp.trans hcs.1, hneg.trans hcs.2⟩
  · have hall : ∀ i : Fin n, (τ (A.hd n i : E)).re < 0 := fun i =>
      (hS E A n τ i).2.2.2 (fun h => hτ h.1)
    refine ⟨hp.trans ?_, hneg.trans ?_⟩
    · rw [Fintype.card_eq_zero_iff]
      exact ⟨fun ⟨i, hi⟩ => absurd hi (not_lt.mpr (le_of_lt (hall i)))⟩
    · rw [Fintype.card_congr (Equiv.subtypeUnivEquiv hall), Fintype.card_fin]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PFormCoord
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pFormCoord :
    TraceType → FormCoord := by
  intro hT E _ _ _ A n Θ hΘ x y
  classical
  have hconj : ∀ (τ : E →+* ℂ) (b : 𝓞 E),
      τ ((A.bar b : 𝓞 E) : E) = (starRingEnd ℂ) (τ (b : E)) := fun τ b => by
    rw [A.bar_eq, IsCMField.complexEmbedding_complexConj]
  have hkey : ∀ a b : Fin n → 𝓞 E, ((A.EF n a b : ℤ) : ℝ) =
      ∑ k : Phi A × Fin n, 2 * (k.1.1 A.δ * k.1.1 (A.hd n k.2 : E) * k.1.1 (a k.2 : E) *
        (starRingEnd ℂ) (k.1.1 (b k.2 : E))).re := by
    intro a b
    have h1 : ((A.EF n a b : ℤ) : ℝ) =
        ((Algebra.trace ℚ E (A.δ * ((∑ i, A.hd n i * a i * A.bar (b i) : 𝓞 E) : E)) : ℚ) : ℝ) := by
      rw [← A.trd_spec, A.EF_apply]; norm_cast
    rw [h1, (hT E A).1, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun τ _ => ?_
    have h2 : ((∑ i, A.hd n i * a i * A.bar (b i) : 𝓞 E) : E) =
        ∑ i, ((A.hd n i : 𝓞 E) : E) * (a i : E) * ((A.bar (b i) : 𝓞 E) : E) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simpa using map_sum (algebraMap (𝓞 E) E) (fun i => A.hd n i * a i * A.bar (b i)) Finset.univ
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h2, map_mul, map_sum, Finset.mul_sum, Complex.re_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [map_mul, hconj, mul_assoc]
  have hx : ∀ (r : ℝ) (a : Fin n → 𝓞 E) (k : Phi A × Fin n),
      Θ (r ⊗ₜ[ℤ] a) k = (r : ℂ) * k.1.1 (a k.2 : E) := by
    rintro r a ⟨τ, i⟩
    have h : r ⊗ₜ[ℤ] a = r • ((1 : ℝ) ⊗ₜ[ℤ] a) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h, map_smul, Pi.smul_apply, hΘ, Complex.real_smul]
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x₁ x₂ h₁ h₂ =>
    simp only [map_add (f := _), LinearMap.add_apply, h₁, h₂, Pi.add_apply, mul_add, add_mul, Complex.add_re,
      Finset.sum_add_distrib]
  | tmul r a =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y₁ y₂ h₁ h₂ =>
      simp only [map_add (f := _), h₁, h₂, Pi.add_apply, mul_add, Complex.add_re, Finset.sum_add_distrib]
    | tmul s b =>
      rw [LinearMap.BilinForm.baseChange_tmul, zsmul_eq_mul, hkey, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hx, hx, map_mul, Complex.conj_ofReal]
      have h : k.1.1 A.δ * k.1.1 (A.hd n k.2 : E) * ((r : ℂ) * k.1.1 (a k.2 : E)) *
          ((s : ℂ) * (starRingEnd ℂ) (k.1.1 (b k.2 : E))) =
          ((r * s : ℝ) : ℂ) * (k.1.1 A.δ * k.1.1 (A.hd n k.2 : E) * k.1.1 (a k.2 : E) *
            (starRingEnd ℂ) (k.1.1 (b k.2 : E))) := by
        push_cast; ring
      rw [h, Complex.re_ofReal_mul]; ring
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PSetupEx
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

namespace UpperTheory.Gal.W2.Seed

private noncomputable def repOf {E V : Type} [Field E] [Algebra ℚ E] [AddCommGroup V] [Module ℚ V] {n : ℕ}
    (β : V ≃ₗ[ℚ] (Fin n → E)) : Matrix (Fin n) (Fin n) E →ₐ[ℚ] Module.End ℚ V :=
  AlgHom.ofLinearMap
    { toFun := fun x => β.symm.toLinearMap ∘ₗ (x.mulVecLin.restrictScalars ℚ) ∘ₗ β.toLinearMap
      map_add' := fun x y => by
        ext v
        simp [Matrix.add_mulVec]
      map_smul' := fun c x => by
        ext v
        simp [Matrix.smul_mulVec] }
    (by ext v; simp)
    (fun x y => by ext v; simp [Matrix.mulVec_mulVec])

private theorem repOf_apply {E V : Type} [Field E] [Algebra ℚ E] [AddCommGroup V] [Module ℚ V] {n : ℕ}
    (β : V ≃ₗ[ℚ] (Fin n → E)) (x : Matrix (Fin n) (Fin n) E) (z : V) : β (repOf β x z) = x *ᵥ β z := by
  simp [repOf]

end UpperTheory.Gal.W2.Seed

theorem UpperTheory.Gal.W2.Seed.pSetupEx :
    FormOKSt → FormPerfSt → SigSt → DomSt → AtPEx → RepEx → RepLaws → RepAdj → Orient → SetupEx := by
  intro hF hFP hS hD hP hR hL hA hO E _ _ _ A n p _ hn hg
  have facts : A.Facts n := ⟨hn, hF E A n, hD E A n hn⟩
  have hs : A.SigOK n := hS E A n hn
  have perf : A.FormPerf n p := hFP E A n p hg.2
  obtain ⟨P⟩ := hP E A p hg.1
  obtain ⟨β, hβ⟩ := hR E n
  have hok : RepOK A n (repOf β) := ⟨β, hβ, repOf_apply β⟩
  obtain ⟨r1, r2, r3, r4⟩ := hL E A n (repOf β) hok
  have radj := hA E A n (repOf β) hok
  obtain ⟨J, j1, j2, j3, j4⟩ := hO E A n hn hs p P (repOf β) hok
  have hsig : ∀ v : InfinitePlace E, sigPos (A.herm n) v.embedding = 1 ↔
      ∃ _ : Fin 1, v = InfinitePlace.mk (P.iotaC.comp P.s) := fun v => by
    have hv := hs v.embedding
    rw [InfinitePlace.mk_embedding] at hv
    have hc : P.iotaC.comp P.s = A.τ₀ := RingHom.ext P.s_C
    rw [hc]
    constructor
    · intro h
      by_cases hv0 : v = InfinitePlace.mk A.τ₀
      · exact ⟨0, hv0⟩
      · have h0 := (hv.2 hv0).1
        omega
    · rintro ⟨_, h⟩
      exact (hv.1 h).1
  refine ⟨⟨facts, hs, hg, perf, P, ?_, ?_, ?_⟩⟩
  · exact
      { e := RingEquiv.refl E
        n_eq := rfl
        rep := repOf β
        rep_inj := r1
        rep_range := r2
        rep_F := fun c => r3 c
        adj := radj
        ρp := P.ρp
        ρp_eq := P.ρp_eq
        s := fun _ => P.s
        s_C := fun _ x => P.s_C x
        w := fun _ => P.w
        s_P := fun _ x => P.s_P x
        sig := hsig
        orient := ⟨J, j1, j2, j3, j4⟩ }
  · intro x; rfl
  · exact r4
end
