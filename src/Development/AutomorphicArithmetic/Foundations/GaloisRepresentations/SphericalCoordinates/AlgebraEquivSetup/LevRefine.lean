module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.ApartOfNotMem
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.TypeSlice

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.LevRefine
noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.UG
open GlobalTheory.LFun (KGL)
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct Classical

namespace UpperTheory.Gal.W2.Seed

def memFn {X : Type} [Group X] (K KM K₀ : Subgroup X) (h y : X) : ℂ :=
  (Nat.card {k : K ⧸ KM.subgroupOf K // h * (k.out : X) * y ∈ K₀} : ℕ)

def MemSum : Prop := ∀ (X : Type) [Group X] (K KM K₀ : Subgroup X) (h : X), K₀ ≤ K → KM.relIndex K ≠ 0 →
  (∀ k ∈ K, ∀ u ∈ KM, k * u * k⁻¹ ∈ KM) → (∀ k ∈ K, ∀ u ∈ KM, h * k * u * (h * k)⁻¹ ∈ K₀) →
  memFn K KM K₀ h ∈ Hecke ℂ K₀ ∧ (∀ y, memFn K KM K₀ h y ≠ 0 → ∃ k ∈ K, h * k * y ∈ K₀) ∧
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (Φ : X → V), (∀ k ∈ K₀, ∀ g, Φ (g * k) = Φ g) → ∀ g,
    hAct K₀ (memFn K KM K₀ h) Φ g = ∑ᶠ k : K ⧸ KM.subgroupOf K, Φ (g * (h * (k.out : X))⁻¹)

def SumDoset : Prop := ∀ (X : Type) [Group X] (K KM : Subgroup X) (h : X), KM ≤ K → KM.relIndex K ≠ 0 →
  (∀ u ∈ KM, h * u * h⁻¹ ∈ K) →
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (Φ : X → V), (∀ k ∈ K, ∀ g, Φ (g * k) = Φ g) →
    (∀ k ∈ K, ∀ u ∈ KM, k * u * k⁻¹ ∈ KM) → ∀ g,
    ∑ᶠ k : K ⧸ KM.subgroupOf K, Φ (g * (h * (k.out : X))⁻¹) =
      ((KM.relIndex (K ⊓ K.comap (MulAut.conj h).toMonoidHom) : ℕ) : ℂ) • hAct K (dosetInd ℂ K h⁻¹) Φ g

def TyLev.Acts {X M : Type} [Group X] [Group M] (T : TyLev X M) (ψ : X → ℂ) (c : ℂ) (h : X) : Prop :=
  ψ ∈ Hecke ℂ T.K₀ ∧ T.L.pr h = 1 ∧
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (Φ : X → V), T.IsTy Φ → hAct T.K₀ ψ Φ = c • hAct T.K₀ (T.tf h) Φ

def TyLev.Triv {X M : Type} [Group X] [Group M] (T : TyLev X M) (K : Subgroup X) : Prop :=
  K ≤ T.K ∧ ∀ k ∈ K, ∀ h, T.ψ ⟨T.L.pr k, h⟩ = 1

def MemAct : Prop := ∀ (X M M' : Type) [Group X] [Group M] [Group M'] (T : TyLev X M) (L' : Loc X M') (Kw : Subgroup M'),
  L'.Fact T.K Kw → T.L.Apart L' → ∀ K KM : Subgroup X, T.Triv K → L'.Fact K Kw → T.K₀ ≤ K → KM ≤ T.K₀ → KM.relIndex K ≠ 0 →
  (∀ k ∈ K, ∀ u ∈ KM, k * u * k⁻¹ ∈ KM) → ∀ (t : M') (z h : X), T.Cen z → h⁻¹ = L'.loc t * z →
  (∀ k ∈ K, ∀ u ∈ KM, h * k * u * (h * k)⁻¹ ∈ T.K₀) →
  T.Acts (memFn K KM T.K₀ h) (KM.relIndex (K ⊓ K.comap (MulAut.conj h).toMonoidHom) : ℕ) (L'.loc t * z)

def MemDeck : Prop := ∀ (X M : Type) [Group X] [Group M] (T : TyLev X M) (K : Subgroup X), T.Triv K → ∀ k ∈ K,
  (∀ u ∈ T.K₀, k * u * k⁻¹ ∈ T.K₀) → T.Acts (memFn T.K₀ T.K₀ T.K₀ k) 1 1

def RelOf : Prop := ∀ (X M J : Type) [Group X] [Group M] (T : TyLev X M) (ψ : J → X → ℂ) (c : J → ℂ) (h : J → X) (hu : X) (u' : X → ℂ),
  (∀ j, T.Acts (ψ j) (c j) (h j)) → T.L.pr hu = 1 → u' ∈ Hecke ℂ T.K₀ →
  (∀ i j, conv T.K₀ (T.tf (h i)) (T.tf (h j)) = conv T.K₀ (T.tf (h j)) (T.tf (h i))) →
  (∀ j, conv T.K₀ (T.tf hu) (T.tf (h j)) = conv T.K₀ (T.tf (h j)) (T.tf hu)) → conv T.K₀ u' (T.tf hu) = T.tf 1 →
  Spc.Rel (conv T.K₀) ψ (T.tf 1) (T.tf hu) u'

def SphComm : Prop := ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (w : Plc E) (t t' : GL (Fin n) (w.adicCompletion E)),
  conv (KGL w (n := n)) (dosetInd ℂ (KGL w (n := n)) t) (dosetInd ℂ (KGL w (n := n)) t') = conv (KGL w (n := n)) (dosetInd ℂ (KGL w (n := n)) t') (dosetInd ℂ (KGL w (n := n)) t)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {A : Arith E} {n p : ℕ} [Fact p.Prime] {S : Setup A n p}

def Tr.lv (T : Tr S) (K : Subgroup (GUf E n)) : Subgroup S.G.GAf := K.comap T.sec

def AtApart : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (T : Tr S) (hc : LocComm) (w : Plc E) (hw : IsSplitAt w) (hp : (p : 𝓞 E) ∉ w.asIdeal),
  (∀ x, T.sec ((T.at hc w hw hp).loc x) = CertificateRingHomMap.loc hw x) ∧
  ∀ (w' : Plc E) (hw' : IsSplitAt w') (hp' : (p : 𝓞 E) ∉ w'.asIdeal), GlobalTheory.Cong.Apart w w' → (T.at hc w hw hp).Apart (T.at hc w' hw' hp')

def LevFact : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (T : Tr S) (hc : LocComm) (S₀ : Finset (Plc E)) (Kw : ∀ w : Plc E, Subgroup (GL (Fin n) (w.adicCompletion E)))
  (w : Plc E) (hw : IsSplitAt w) (hp : (p : 𝓞 E) ∉ w.asIdeal), CertificateRingHomMap.cj w ∉ S₀ →
  (w ∈ S₀ → (T.at hc w hw hp).Fact (T.lv (lev S₀ Kw)) (Kw w)) ∧ (w ∉ S₀ → (T.at hc w hw hp).Fact (T.lv (lev S₀ Kw)) (KGL w (n := n)))

def IntConj : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (g : GUf E n) (w : Plc E), 0 < n →
  (sim g ∈ ZU → comp w g ∈ KGL w (n := n) → comp (CertificateRingHomMap.cj w) g ∈ KGL (CertificateRingHomMap.cj w) (n := n)) ∧
  ((∀ u, comp u g ∈ KGL u (n := n)) → sim g ∈ ZU) ∧ {u : Plc E | comp u g ∉ KGL u (n := n)}.Finite

def KNOpen : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (T : Tr S) (N : ℕ), 0 < N → IsOpen (((S.L.KN N).comap T.j : Subgroup (GUf E n)) : Set (GUf E n))

def KNIdx : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (T : Tr S) (N : ℕ), 0 < N → IsCommensurated (S.L.KN N) ∧ ∀ K : Subgroup (GUf E n), IsCompact (K : Set (GUf E n)) →
    IsOpen (K : Set (GUf E n)) → (S.L.KN N).relIndex (T.lv K) ≠ 0

def PPart : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (T : Tr S) (g : GUf E n), ∃ k : GUf E n, g = T.sec (T.j g) * k ∧ (∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → comp w k = 1) ∧
    (∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → comp w k = comp w g) ∧ ∀ h, T.sec h * k = k * T.sec h

def HasEigOf : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p)
  (T : Tr S) (V : Type) [AddCommGroup V] [Module ℂ V] (ξ : Representation ℂ (GL (Fin n) E × ℚˣ) V) (Φ : GUf E n → V),
  (∀ (γ : Gam0 E n) g, Φ (rat γ * g) = ξ γ (Φ g)) →
  (∀ k : GUf E n, (∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → comp w k = 1) → (∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → comp w k ∈ KGL w (n := n)) →
    ∀ g, Φ (g * k) = Φ g) →
  (∃ g₀, Φ g₀ ≠ 0 ∧ ∀ w : Plc E, (p : 𝓞 E) ∈ w.asIdeal → comp w g₀ ∈ KGL w (n := n)) →
  ∀ K₀ : Subgroup S.G.GAf, IsCommensurated K₀ → (∀ k ∈ K₀, ∀ h, Φ (T.sec (h * k)) = Φ (T.sec h)) →
  ∀ (J : Type) (ψ : J → S.G.GAf → ℂ) (θ : J → ℂ) (e : S.G.GAf → ℂ), (∀ j, ψ j ∈ Hecke ℂ K₀) → e ∈ Hecke ℂ K₀ →
    hAct K₀ e (fun h => Φ (T.sec h)) = (fun h => Φ (T.sec h)) →
    (∀ j, hAct K₀ (ψ j) (fun h => Φ (T.sec h)) = θ j • fun h => Φ (T.sec h)) →
  Spc.HasEig S.G (V := V) ξ K₀ ψ θ e

end UpperTheory.Gal.W2.Seed
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.MatEqOfComp
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open GroundTheory.Global.AdeleBaseChange (finiteAdeleMap below)
open scoped TensorProduct

namespace UpperTheory.Gal.W2.Seed

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private theorem exists_over (v : Plc ℚ) : ∃ w : Plc E, below ℚ w = v := by
  haveI := v.isMaximal
  obtain ⟨Q, hQm, hQo⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
  exact ⟨⟨Q, hQm.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, HeightOneSpectrum.ext hQo.over.symm⟩

private theorem fam_inj : Function.Injective (finiteAdeleMap ℚ E) := by
  intro x y h
  refine FiniteAdeleRing.ext (K := ℚ) fun v => ?_
  obtain ⟨w, rfl⟩ := exists_over (E := E) v
  have h1 := congrArg (fun z : FiniteAdeleRing (𝓞 E) E => z w) h
  exact (GroundTheory.Global.SemiLocal.completionMap (below ℚ w) w).injective h1

variable {n : ℕ}

private theorem mat_eq_of_comp {g g' : GUf E n} (h : ∀ w, comp w g = comp w g') : mat g = mat g' := by
  refine Units.ext (Matrix.ext fun i k => GlobalTheory.EulerTw.pLoc_ext E fun w => ?_)
  exact congrArg (fun x : GL (Fin n) (w.adicCompletion E) => x.val i k) (h w)

private theorem sim_eq_of_mat (hn : 1 ≤ n) {g g' : GUf E n} (h : mat g = mat g') : sim g = sim g' := by
  have h1 := UpperTheory.Gal.CertificateRingHomMap.mem_Sim.1 g.2
  have h2 := UpperTheory.Gal.CertificateRingHomMap.mem_Sim.1 g'.2
  have h3 : (g : GL (Fin n) (Af E) × AfQˣ).1 = (g' : GL (Fin n) (Af E) × AfQˣ).1 := h
  rw [h3, h2] at h1
  have h4 := congrFun (congrFun h1 ⟨0, hn⟩) ⟨0, hn⟩
  simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h4
  exact Units.ext (fam_inj h4.symm)

private theorem eq_of_comp (hn : 1 ≤ n) {g g' : GUf E n} (h : ∀ w, comp w g = comp w g') : g = g' :=
  Subtype.ext (Prod.ext (mat_eq_of_comp h) (sim_eq_of_mat hn (mat_eq_of_comp h)))

private theorem map_eq_iff {p : ℕ} [Fact p.Prime] (T : AdT p E) (x y : GL (Fin n) (Af E)) :
    x.val.map T.Φ = y.val.map T.Φ ↔ ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal →
      GeneralLinearGroup.map (pLoc E w) x = GeneralLinearGroup.map (pLoc E w) y := by
  constructor
  · intro h w hw
    refine Units.ext (Matrix.ext fun i k => ?_)
    have h1 : T.Φ (x.val i k - y.val i k) = 0 := by
      rw [map_sub]
      exact sub_eq_zero.2 (congrFun (congrFun h i) k)
    have h2 := (T.Φ_ker _).1 h1 w hw
    rw [map_sub] at h2
    exact sub_eq_zero.1 h2
  · intro h
    refine Matrix.ext fun i k => ?_
    have h1 : T.Φ (x.val i k - y.val i k) = 0 := by
      refine (T.Φ_ker _).2 fun w hw => ?_
      rw [map_sub]
      exact sub_eq_zero.2 (congrArg (fun z : GL (Fin n) (w.adicCompletion E) => z.val i k) (h w hw))
    rw [map_sub] at h1
    exact sub_eq_zero.1 h1

private theorem conj_comp_iff (a : GL (Fin n) (Af E)) (w : Plc E) (g g' : GUf E n) :
    GeneralLinearGroup.map (pLoc E w) (a * mat g * a⁻¹) = GeneralLinearGroup.map (pLoc E w) (a * mat g' * a⁻¹) ↔
      comp w g = comp w g' := by
  have e : ∀ h : GUf E n, GeneralLinearGroup.map (pLoc E w) (a * mat h * a⁻¹) =
      GeneralLinearGroup.map (pLoc E w) a * comp w h * (GeneralLinearGroup.map (pLoc E w) a)⁻¹ := fun h => by
    rw [map_mul, map_mul, map_inv]; rfl
  rw [e, e, mul_left_inj, mul_right_inj]

private theorem algMap_inj {p : ℕ} [Fact p.Prime] (hn : 1 ≤ n)
    (μ : AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E ≃+* Matrix (Fin n) (Fin n) (AfP p ⊗[ℚ] E)) (hμ : IsMu μ)
    {c c' : AfP p} (h : c ⊗ₜ[ℚ] (1 : Matrix (Fin n) (Fin n) E) = c' ⊗ₜ[ℚ] (1 : Matrix (Fin n) (Fin n) E)) : c = c' := by
  have h1 := congrFun (congrFun (congrArg μ h) ⟨0, hn⟩) ⟨0, hn⟩
  rw [hμ, hμ, Matrix.one_apply_eq] at h1
  exact Algebra.TensorProduct.includeLeft_injective (R := ℚ) (S := ℚ) (A := AfP p) (B := E)
    (algebraMap ℚ E).injective h1

end UpperTheory.Gal.W2.Seed

theorem UpperTheory.Gal.W2.Seed.pJEq :
    JEq := by
  intro E _ _ _ A n p _ S T μ hμ a j hj
  refine ⟨fun g g' h => eq_of_comp S.facts.pos h, fun g g' => ?_⟩
  have key : S.mx (j g) = S.mx (j g') ↔ ∀ w : Plc E, (p : 𝓞 E) ∉ w.asIdeal → comp w g = comp w g' := by
    rw [← μ.injective.eq_iff, hj, hj, map_eq_iff]
    exact forall₂_congr fun w _ => conj_comp_iff a w g g'
  rw [← key]
  refine ⟨fun h => congrArg S.mx h, fun h => ?_⟩
  have h1 : (((j g : S.G.GAf) : (AfP p ⊗[ℚ] S.G.C)ˣ × (AfP p)ˣ).1) = ((j g' : S.G.GAf) : (AfP p ⊗[ℚ] S.G.C)ˣ × (AfP p)ˣ).1 := Units.ext h
  refine Subtype.ext (Prod.ext h1 (Units.ext ?_))
  have e1 := mem_uGroup.1 (j g).2
  have e2 := mem_uGroup.1 (j g').2
  rw [h1, e2] at e1
  exact algMap_inj S.facts.pos μ hμ e1.symm
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PKNIff
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct

private theorem ohat_mul {E : Type} [Field E] [NumberField E] [IsCMField E] {p : ℕ} (T : AdT p E)
    {x y : AfP p ⊗[ℚ] E} (hx : x ∈ OHat p E) (hy : y ∈ OHat p E) : x * y ∈ OHat p E := by
  obtain ⟨a, rfl⟩ := T.Φ_surj x
  obtain ⟨b, rfl⟩ := T.Φ_surj y
  rw [← map_mul, T.Φ_int]
  intro w hw
  rw [map_mul, map_mul]
  exact mul_le_one' ((T.Φ_int a).1 hx w hw) ((T.Φ_int b).1 hy w hw)

private theorem one_mem_ohat {E : Type} [Field E] [NumberField E] [IsCMField E] {p : ℕ} (T : AdT p E) :
    (1 : AfP p ⊗[ℚ] E) ∈ OHat p E := by
  rw [← map_one T.Φ, T.Φ_int]
  intro w hw
  simp

theorem UpperTheory.Gal.W2.Seed.pKNIff :
    LatCoord → KNIff := by
  intro hL E _ _ _ A n p _ S T g
  obtain ⟨ν, -, hact, hlat⟩ := hL E A n p S T.μ T.mu
  have hM : T.μ (S.mx (T.j g)) = (T.a * mat g * T.a⁻¹).val.map T.Φ := T.j_mx g
  generalize hY : T.a * mat g * T.a⁻¹ = Y at hM ⊢
  have hactM : ∀ v, ν (S.L.actG (T.j g) v) = (Y.val.map T.Φ) *ᵥ ν v := fun v => by rw [hact, hM]
  have hcol : ∀ k i, ((Y.val.map T.Φ) *ᵥ (Pi.single k 1 : Fin n → AfP p ⊗[ℚ] E)) i = T.Φ (Y.val i k) := by
    intro k i
    simp [Matrix.mulVec_single_one]
  have hsingle : ∀ k, ν.symm (Pi.single k 1) ∈ LaHat S.D := by
    intro k
    rw [hlat]
    intro i
    rw [ν.apply_symm_apply, Pi.single_apply]
    split_ifs
    · exact one_mem_ohat T.toAdT
    · exact zero_mem _
  have hΦ1 : ∀ i k, T.Φ ((1 : Matrix (Fin n) (Fin n) (Af E)) i k) = (1 : Matrix (Fin n) (Fin n) (AfP p ⊗[ℚ] E)) i k := by
    intro i k
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  have hw1 : ∀ (w : Plc E) i k, pLoc E w ((1 : Matrix (Fin n) (Fin n) (Af E)) i k) = (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i k := by
    intro w i k
    rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  constructor
  · constructor
    · intro h w hw i k
      have := (hlat _).1 (h _ (hsingle k)) i
      rw [hactM, ν.apply_symm_apply, hcol, T.Φ_int] at this
      exact this w hw
    · intro h v hv
      rw [hlat]
      intro i
      rw [hactM]
      have hv' := (hlat v).1 hv
      simp only [Matrix.mulVec, dotProduct]
      refine sum_mem fun k _ => ohat_mul T.toAdT ?_ (hv' k)
      rw [Matrix.map_apply, T.Φ_int]
      exact fun w hw => h w hw i k
  · intro N hN
    constructor
    · intro h w hw i k
      obtain ⟨u, hu, e⟩ := h _ (hsingle k)
      have e2 := congrFun (congrArg ν e) i
      rw [hactM, ν.apply_symm_apply, hcol, map_add (f := _), map_nsmul, ν.apply_symm_apply] at e2
      have hui := (hlat u).1 hu i
      obtain ⟨x, hx⟩ := T.Φ_surj (ν u i)
      have hxi := (T.Φ_int x).1 (hx ▸ hui) w hw
      have e3 : T.Φ (Y.val i k - (1 : Matrix (Fin n) (Fin n) (Af E)) i k - (N : Af E) * x) = 0 := by
        rw [map_sub, map_sub, map_mul, hΦ1, hx, map_natCast, e2, Pi.add_apply, Pi.smul_apply, nsmul_eq_mul,
          Matrix.one_apply, Pi.single_apply]
        simp [eq_comm]
      have e4 := (T.Φ_ker _).1 e3 w hw
      rw [map_sub, map_sub, map_mul, hw1, map_natCast, sub_eq_zero, sub_eq_iff_eq_add'] at e4
      have e5 : ((GeneralLinearGroup.map (pLoc E w) Y).val - 1) i k = (N : w.adicCompletion E) * pLoc E w x := by
        rw [Matrix.sub_apply]
        show pLoc E w (Y.val i k) - _ = _
        rw [e4]
        ring
      rw [e5, map_mul]
      exact mul_le_of_le_one_right' hxi
    · intro h v hv
      have hv' := (hlat v).1 hv
      have hN0 : (N : E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
      obtain ⟨Ninv, hNinvdef⟩ : ∃ Ninv : Af E, Ninv = algebraMap E (Af E) ((N : E)⁻¹) := ⟨_, rfl⟩
      have hNinv : (N : Af E) * Ninv = 1 := by
        rw [hNinvdef, ← map_natCast (algebraMap E (Af E)) N, ← map_mul, mul_inv_cancel₀ hN0, map_one]
      obtain ⟨C, hCdef⟩ : ∃ C : Matrix (Fin n) (Fin n) (AfP p ⊗[ℚ] E),
          ∀ i k, C i k = T.Φ (Ninv * (Y.val - 1) i k) := ⟨Matrix.of fun i k => T.Φ (Ninv * (Y.val - 1) i k), fun _ _ => rfl⟩
      have hC : Y.val.map T.Φ = 1 + ((N : AfP p ⊗[ℚ] E)) • C := by
        ext i k
        rw [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, ← hΦ1, hCdef,
          ← map_natCast T.Φ N, ← map_mul, ← map_add]
        congr 1
        rw [← mul_assoc, hNinv, one_mul, Matrix.sub_apply]
        ring
      refine ⟨ν.symm (C *ᵥ ν v), ?_, ?_⟩
      · rw [hlat]
        intro i
        rw [ν.apply_symm_apply]
        simp only [Matrix.mulVec, dotProduct]
        refine sum_mem fun k _ => ohat_mul T.toAdT ?_ (hv' k)
        rw [hCdef, T.Φ_int]
        intro w hw
        have h1 := h w hw i k
        have hp' : (N : w.adicCompletion E) * pLoc E w Ninv = 1 := by
          rw [← map_natCast (pLoc E w) N, ← map_mul, hNinv, map_one]
        have h2 : (N : w.adicCompletion E) ≠ 0 := left_ne_zero_of_mul_eq_one hp'
        have h3 : pLoc E w Ninv = (N : w.adicCompletion E)⁻¹ := eq_inv_of_mul_eq_one_right hp'
        have e : pLoc E w ((Y.val - 1) i k) = ((GeneralLinearGroup.map (pLoc E w) Y).val - 1) i k := by
          rw [Matrix.sub_apply, map_sub, hw1, Matrix.sub_apply]
          rfl
        rw [map_mul, h3, e, map_mul, map_inv₀]
        exact (inv_mul_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 h2))).2 h1
      · apply ν.injective
        rw [hactM, hC, map_add (f := _), map_nsmul, ν.apply_symm_apply, Matrix.add_mulVec, Matrix.one_mulVec,
          Matrix.smul_mulVec, Nat.cast_smul_eq_nsmul]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PLatCoord
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct

namespace UpperTheory.Gal.W2.Seed.LatticeTensorCoordinates

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

private lemma exists_int_multiple (x : Matrix (Fin n) (Fin n) E) :
    ∃ (m : ℤ) (y : Matrix (Fin n) (Fin n) (𝓞 E)), m ≠ 0 ∧ y.map (algebraMap (𝓞 E) E) = (m : ℚ) • x := by
  classical
  obtain ⟨m, hm, hs⟩ := exists_integral_multiples ℤ ℚ
    (Finset.univ.image (fun ij : Fin n × Fin n => x ij.1 ij.2))
  have h : ∀ i j, ∃ a : 𝓞 E, algebraMap (𝓞 E) E a = (m : ℚ) • x i j := by
    intro i j
    have h1 := hs (x i j) (Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩)
    have h2 : m • x i j = (m : ℚ) • x i j := by
      simp [zsmul_eq_mul, Algebra.smul_def]
    rw [h2] at h1
    exact ⟨IsIntegralClosure.mk' (𝓞 E) _ h1, IsIntegralClosure.algebraMap_mk' _ _ _⟩
  choose y hy using h
  refine ⟨m, Matrix.of y, hm, ?_⟩
  ext i j
  simp [hy]

private lemma beta_rep (rep : Matrix (Fin n) (Fin n) E →ₐ[ℚ] Module.End ℚ (ℚ ⊗[ℤ] (Fin n → 𝓞 E)))
    (hrep : ∀ (x : Matrix (Fin n) (Fin n) (𝓞 E)) (v : Fin n → 𝓞 E),
      rep (x.map (algebraMap (𝓞 E) E)) ((1 : ℚ) ⊗ₜ[ℤ] v) = (1 : ℚ) ⊗ₜ[ℤ] (x *ᵥ v))
    (β : ℚ ⊗[ℤ] (Fin n → 𝓞 E) ≃ₗ[ℚ] (Fin n → E))
    (hβ : ∀ (v : Fin n → 𝓞 E) i, β (1 ⊗ₜ v) i = (v i : E))
    (x : Matrix (Fin n) (Fin n) E) (z : ℚ ⊗[ℤ] (Fin n → 𝓞 E)) : β (rep x z) = x *ᵥ β z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), mulVec_add, ha, hb]
  | tmul q v =>
    have hq : q ⊗ₜ[ℤ] v = q • ((1 : ℚ) ⊗ₜ[ℤ] v) := by
      rw [TensorProduct.smul_tmul']; simp
    obtain ⟨m, y, hm, hy⟩ := exists_int_multiple x
    have hmq : (m : ℚ) ≠ 0 := by exact_mod_cast hm
    have key : (m : ℚ) • β (rep x (1 ⊗ₜ v)) = (m : ℚ) • (x *ᵥ β (1 ⊗ₜ v)) := by
      have e1 : (m : ℚ) • β (rep x (1 ⊗ₜ v)) = β (rep ((m : ℚ) • x) (1 ⊗ₜ v)) := by
        rw [map_smul, LinearMap.smul_apply, map_smul]
      have e2 : (m : ℚ) • (x *ᵥ β (1 ⊗ₜ v)) = ((m : ℚ) • x) *ᵥ β (1 ⊗ₜ v) := by
        rw [smul_mulVec]
      rw [e1, e2, ← hy, hrep]
      ext i
      rw [hβ]
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
      rw [show ((∑ k, y i k * v k : 𝓞 E) : E) = ∑ k, ((y i k : 𝓞 E) : E) * (v k : E) by
        simp]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hβ]
    have h3 : β (rep x (1 ⊗ₜ v)) = x *ᵥ β (1 ⊗ₜ v) := smul_right_injective _ hmq key
    rw [hq, map_smul, map_smul, map_smul, mulVec_smul, h3]

private def nu (R : Type) [CommRing R] [Algebra ℚ R] (β : ℚ ⊗[ℤ] (Fin n → 𝓞 E) ≃ₗ[ℚ] (Fin n → E)) :
    R ⊗[ℚ] (ℚ ⊗[ℤ] (Fin n → 𝓞 E)) ≃+ (Fin n → R ⊗[ℚ] E) :=
  ((TensorProduct.congr (LinearEquiv.refl ℚ R) β).trans
    (TensorProduct.piRight ℚ ℚ R (fun _ : Fin n => E))).toAddEquiv

private lemma nu_tmul (R : Type) [CommRing R] [Algebra ℚ R]
    (β : ℚ ⊗[ℤ] (Fin n → 𝓞 E) ≃ₗ[ℚ] (Fin n → E)) (r : R) (z : ℚ ⊗[ℤ] (Fin n → 𝓞 E)) (i : Fin n) :
    nu R β (r ⊗ₜ z) i = r ⊗ₜ (β z i) := by
  simp [nu]

private lemma actOn_tmul {R : Type} [CommRing R] [Algebra ℚ R]
    (rep : Matrix (Fin n) (Fin n) E →ₐ[ℚ] Module.End ℚ (ℚ ⊗[ℤ] (Fin n → 𝓞 E)))
    (r r' : R) (x : Matrix (Fin n) (Fin n) E) (z : ℚ ⊗[ℤ] (Fin n → 𝓞 E)) :
    actOn rep R (r ⊗ₜ x) (r' ⊗ₜ z) = (r * r') ⊗ₜ rep x z := by
  unfold actOn
  erw [Algebra.TensorProduct.lift_tmul]
  show r • (LinearMap.baseChange R (rep x)) (r' ⊗ₜ z) = _
  rw [LinearMap.baseChange_tmul, TensorProduct.smul_tmul', smul_eq_mul]

private lemma nu_act {R : Type} [CommRing R] [Algebra ℚ R]
    (μ : R ⊗[ℚ] Matrix (Fin n) (Fin n) E ≃+* Matrix (Fin n) (Fin n) (R ⊗[ℚ] E)) (hμ : IsMu μ)
    (rep : Matrix (Fin n) (Fin n) E →ₐ[ℚ] Module.End ℚ (ℚ ⊗[ℤ] (Fin n → 𝓞 E)))
    (β : ℚ ⊗[ℤ] (Fin n → 𝓞 E) ≃ₗ[ℚ] (Fin n → E))
    (hr : ∀ x z, β (rep x z) = x *ᵥ β z)
    (y : R ⊗[ℚ] Matrix (Fin n) (Fin n) E) (v : R ⊗[ℚ] (ℚ ⊗[ℤ] (Fin n → 𝓞 E))) :
    nu R β (actOn rep R y v) = μ y *ᵥ nu R β v := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), LinearMap.add_apply, add_mulVec, ha, hb]
  | tmul r x =>
    induction v using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), mulVec_add, ha, hb]
    | tmul r' z =>
      ext1 i
      rw [actOn_tmul, nu_tmul, hr]
      simp only [Matrix.mulVec, dotProduct, TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hμ r x i k, nu_tmul, Algebra.TensorProduct.tmul_mul_tmul]

private lemma nu_mem {p : ℕ} (β : ℚ ⊗[ℤ] (Fin n → 𝓞 E) ≃ₗ[ℚ] (Fin n → E))
    (hβ : ∀ (v : Fin n → 𝓞 E) i, β (1 ⊗ₜ v) i = (v i : E))
    (v : AfP p ⊗[ℚ] (ℚ ⊗[ℤ] (Fin n → 𝓞 E))) :
    v ∈ AddSubgroup.closure {z : AfP p ⊗[ℚ] (ℚ ⊗[ℤ] (Fin n → 𝓞 E)) |
        ∃ (a : AfP p) (x : Fin n → 𝓞 E), IsIntAf a ∧ z = a ⊗ₜ ((1 : ℚ) ⊗ₜ x)} ↔
      ∀ i, nu (AfP p) β v i ∈ OHat p E := by
  classical
  constructor
  · intro h i
    induction h using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, x, ha, rfl⟩ := hz
      exact AddSubgroup.subset_closure ⟨a, x i, ha, by rw [nu_tmul, hβ]⟩
    | zero => simpa using zero_mem _
    | add a b _ _ h1 h2 =>
      simpa only [map_add, Pi.add_apply] using add_mem h1 h2
    | neg a _ h => rw [map_neg]; exact neg_mem h
  · intro h
    have hs : ∀ i, ∀ w ∈ OHat p E, (nu (AfP p) β).symm (Pi.single i w) ∈
        AddSubgroup.closure {z : AfP p ⊗[ℚ] (ℚ ⊗[ℤ] (Fin n → 𝓞 E)) |
          ∃ (a : AfP p) (x : Fin n → 𝓞 E), IsIntAf a ∧ z = a ⊗ₜ ((1 : ℚ) ⊗ₜ x)} := by
      intro i w hw
      induction hw using AddSubgroup.closure_induction with
      | mem z hz =>
        obtain ⟨a, x, ha, rfl⟩ := hz
        refine AddSubgroup.subset_closure ⟨a, Pi.single i x, ha, ?_⟩
        rw [AddEquiv.symm_apply_eq]
        funext j
        rw [nu_tmul, hβ]
        by_cases hj : j = i
        · subst hj; simp
        · simp [hj]
      | zero => simpa using zero_mem _
      | add a b _ _ h1 h2 => rw [Pi.single_add, map_add (f := _)]; exact add_mem h1 h2
      | neg a _ h => rw [Pi.single_neg, map_neg]; exact neg_mem h
    have hv : v = ∑ i, (nu (AfP p) β).symm (Pi.single i (nu (AfP p) β v i)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_sum, Finset.univ_sum_single]; simp
    rw [hv]
    exact sum_mem fun i _ => hs i _ (h i)

end UpperTheory.Gal.W2.Seed.LatticeTensorCoordinates

namespace UpperTheory.Gal.W2.Seed

open LatticeTensorCoordinates

theorem pLatCoord :
    RepLaws → LatCoord := by
  intro _ E _ _ _ A n p _ S μ hμ
  obtain ⟨β, hβ⟩ := pRepEx E n
  have hr : ∀ x z, β (S.L.rep x z) = x *ᵥ β z := beta_rep S.L.rep S.L_rep β hβ
  refine ⟨nu (AfP p) β, ?_, ?_, ?_⟩
  · intro r v i
    exact (nu_tmul (AfP p) β r _ i).trans (congrArg (fun t => r ⊗ₜ[ℚ] t) (hβ v i))
  · intro h v
    exact nu_act μ hμ S.L.rep β hr (S.mx h) v
  · intro v
    exact nu_mem β hβ v

end UpperTheory.Gal.W2.Seed
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PMuStar
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct

private theorem conj_H {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ) :
    (A.H n).map (IsCMField.complexConj E : E →+* E) = A.H n := by
  have hc : (IsCMField.complexConj E) ((A.c : 𝓞 E) : E) = (A.c : E) := by
    rw [← A.bar_eq, A.c_real]
  ext i j
  simp only [Arith.H, Matrix.map_apply, Matrix.diagonal_apply]
  split_ifs with hij
  · simp only [Arith.hd, Arith.dg]
    split_ifs <;> simp [hc]
  · simp

private theorem H_eq {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ) :
    A.H n = (-(A.c : E)) • Matrix.diagonal (fun i => (A.dg n i : E)) := by
  rw [Arith.H, ← Matrix.diagonal_smul]
  congr 1

private theorem key {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ)
    (y : Matrix (Fin n) (Fin n) E) :
    Matrix.diagonal (fun i => (A.dg n i : E)) *
        (((A.H n).map (IsCMField.complexConj E : E →+* E))⁻¹ * y * (A.H n).map (IsCMField.complexConj E : E →+* E)) =
      y * Matrix.diagonal (fun i => (A.dg n i : E)) := by
  rw [conj_H]
  have hc : (-(A.c : E)) ≠ 0 := neg_ne_zero.mpr A.c_ne
  have hD : Matrix.diagonal (fun i => (A.dg n i : E)) = (-(A.c : E))⁻¹ • A.H n := by
    rw [H_eq, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have hu : IsUnit (A.H n).det := isUnit_iff_ne_zero.mpr (A.det_ne n)
  rw [hD, Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]

theorem UpperTheory.Gal.W2.Seed.pMuStar :
    MuStar := by
  intro R E _ _ _ _ _ A n μ hμ x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r m =>
    have hk := key A n ((m.map (IsCMField.complexConj E : E →+* E))ᵀ)
    ext i k
    rw [starT_tmul, hermStar_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, hμ,
      Matrix.transpose_apply, Matrix.map_apply, hμ, conjT_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    congr 1
    have := congrFun (congrFun hk i) k
    simpa [Matrix.diagonal_mul, Matrix.mul_diagonal] using this
  | add x y hx hy =>
    rw [map_add (f := _), MulOpposite.unop_add, map_add (f := _), Matrix.mul_add, hx, hy, map_add (f := _),
      Matrix.map_add _ (map_add _), Matrix.transpose_add, Matrix.add_mul]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PLocComm
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open GlobalTheory.SplitPts (conjE)
open GroundTheory.Global.AdeleBaseChange (finiteAdeleMap)
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pLocComm :
    LocComm := by
  intro E _ _ _ n w hw x g hg
  have key : ∀ u : Plc E, comp u (UpperTheory.Gal.CertificateRingHomMap.loc hw x) * comp u g = comp u g * comp u (UpperTheory.Gal.CertificateRingHomMap.loc hw x) := by
    intro u
    by_cases hu : GlobalTheory.Cong.Apart u w
    · rw [UpperTheory.Gal.CertificateRingHomMap.comp_loc_of_apart hw hu, one_mul, mul_one]
    · have hu' : u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) := by
        by_contra h
        exact hu h
      obtain rfl | rfl := GlobalTheory.BCT.GlobLev.eq_or_eq_conjSrc hu'
      · rw [hg, one_mul, mul_one]
      · have hmem : ((mat g).val.map (conjFin (conjE E)))ᵀ * (mat g).val =
            finiteAdeleMap ℚ E (sim g : AfQˣ) • (1 : Matrix (Fin n) (Fin n) (Af E)) := g.2
        have h2 := congrArg (RingHom.mapMatrix (pLoc E w)) hmem
        have e1 : RingHom.mapMatrix (pLoc E w) (((mat g).val.map (conjFin (conjE E)))ᵀ) =
            ((comp (conjSrc (conjE E) w) g).val.map (conjLoc (conjE E) w))ᵀ := by
          refine Matrix.ext fun i k => ?_
          exact pLoc_conjFin (conjE E) _ w
        have e2 : RingHom.mapMatrix (pLoc E w) (mat g).val = 1 := by
          have : (comp w g).val = 1 := by rw [hg]; rfl
          exact this
        have e3 : RingHom.mapMatrix (pLoc E w) (finiteAdeleMap ℚ E (sim g : AfQˣ) • (1 : Matrix (Fin n) (Fin n) (Af E))) =
            pLoc E w (finiteAdeleMap ℚ E (sim g : AfQˣ)) • (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
          ext i k
          by_cases hik : i = k <;> simp [hik, Matrix.one_apply]
        rw [map_mul, e1, e2, mul_one, e3] at h2
        have hM : RingHom.mapMatrix (conjLoc (conjE E) w) (comp (conjSrc (conjE E) w) g).val =
            pLoc E w (finiteAdeleMap ℚ E (sim g : AfQˣ)) • (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
          have := congrArg Matrix.transpose h2
          rw [Matrix.transpose_transpose, Matrix.transpose_smul, Matrix.transpose_one] at this
          exact this
        have hinj : Function.Injective (RingHom.mapMatrix (conjLoc (conjE E) w) :
            Matrix (Fin n) (Fin n) _ →+* Matrix (Fin n) (Fin n) _) := by
          intro a b hab
          refine Matrix.ext fun i k => ?_
          exact (conjLoc (conjE E) w).injective (congrFun (congrFun hab i) k)
        apply Units.ext
        apply hinj
        rw [Units.val_mul, Units.val_mul, map_mul, map_mul, hM, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  refine Subtype.ext (Prod.ext (Units.ext (GlobalTheory.EulerTw.matrix_ext_pLoc E n fun v => ?_)) ?_)
  · have h3 : (comp v (UpperTheory.Gal.CertificateRingHomMap.loc hw x * g)).val = (comp v (g * UpperTheory.Gal.CertificateRingHomMap.loc hw x)).val := by
      rw [map_mul, map_mul, key v]
    exact h3
  · exact mul_comm (sim (UpperTheory.Gal.CertificateRingHomMap.loc hw x)) (sim g)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PIdemP
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct
open GroundTheory.Global.AdeleBaseChange (finiteAdeleMap below finiteAdeleMap_apply)

theorem UpperTheory.Gal.W2.Seed.pIdemP :
    IdemP := by
  classical
  intro p _ E _ _
  let e : AfQ := ⟨fun v => if (p : 𝓞 ℚ) ∈ v.asIdeal then 1 else 0,
    Filter.Eventually.of_forall fun v => by
      by_cases h : (p : 𝓞 ℚ) ∈ v.asIdeal
      · simpa [h] using one_mem (v.adicCompletionIntegers ℚ)
      · simpa [h] using zero_mem (v.adicCompletionIntegers ℚ)⟩
  have he : ∀ v : Plc ℚ, e v = if (p : 𝓞 ℚ) ∈ v.asIdeal then 1 else 0 := fun v => rfl
  refine ⟨e, fun v => ⟨fun h => by rw [he, if_pos h], fun h => by rw [he, if_neg h]⟩, fun w => ?_⟩
  have hiff : (p : 𝓞 ℚ) ∈ (below ℚ w).asIdeal ↔ (p : 𝓞 E) ∈ w.asIdeal := by
    show (p : 𝓞 ℚ) ∈ w.asIdeal.under (𝓞 ℚ) ↔ _
    rw [Ideal.under_def, Ideal.mem_comap, map_natCast]
  have hl : pLoc E w (finiteAdeleMap ℚ E e) =
      GroundTheory.Global.SemiLocal.completionMap (below ℚ w) w (e (below ℚ w)) := rfl
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [hl, he, if_pos (hiff.2 h), map_one]
  · rw [hl, he, if_neg (fun h' => h (hiff.1 h')), map_zero]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PStdForm
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 AfQ Plc sim mat comp rat lev ZU)
open scoped TensorProduct

noncomputable section

open GlobalTheory.SplitPts (conjE)

namespace UpperTheory.Gal.W2.Seed

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n p : ℕ} [Fact p.Prime]

private theorem conj_dg (A : Arith E) (n : ℕ) (i : Fin n) :
    IsCMField.complexConj E (A.dg n i : E) = (A.dg n i : E) := by
  rw [← A.bar_eq]
  unfold Arith.dg
  split_ifs <;> simp [A.c_real]

private abbrev Dg (A : Arith E) (n : ℕ) : Matrix (Fin n) (Fin n) E := Matrix.diagonal fun i => (A.dg n i : E)

private theorem H_eq (A : Arith E) (n : ℕ) : A.H n = (-(A.c : E)) • Dg A n := by
  ext i j
  by_cases h : i = j
  · subst h; simp [Arith.H, Arith.hd]
  · simp [Arith.H, h]

private theorem Dg_map (A : Arith E) (n : ℕ) : (Dg A n).map (IsCMField.complexConj E : E →+* E) = Dg A n := by
  rw [Matrix.diagonal_map (map_zero _)]
  congr 1; funext i
  exact conj_dg A n i

private theorem H_map (A : Arith E) (n : ℕ) : (A.H n).map (IsCMField.complexConj E : E →+* E) = A.H n := by
  have h := A.herm n
  have h2 : (A.H n)ᵀ = A.H n := by unfold Arith.H; simp
  have h3 := congrArg Matrix.transpose h
  rw [Matrix.transpose_transpose, h2] at h3
  exact h3

private theorem c_ne' (A : Arith E) : -(A.c : E) ≠ 0 := neg_ne_zero.2 A.c_ne

private theorem Dg_star (A : Arith E) (n : ℕ) (x : Matrix (Fin n) (Fin n) E) :
    Dg A n * (hermStar (A.H n) (A.det_ne n) x).unop = (x.map (IsCMField.complexConj E : E →+* E))ᵀ * Dg A n := by
  have hu : IsUnit (A.H n).det := (A.det_ne n).isUnit
  have h1 : A.H n * (hermStar (A.H n) (A.det_ne n) x).unop = (x.map (IsCMField.complexConj E : E →+* E))ᵀ * A.H n := by
    rw [hermStar_apply, H_map]
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ hu]
  generalize (hermStar (A.H n) (A.det_ne n) x).unop = Y at h1 ⊢
  rw [H_eq A n, Matrix.smul_mul, Matrix.mul_smul] at h1
  exact smul_right_injective _ (c_ne' A) h1

private theorem baseMatrix_eq_diagonal (A : Arith E) (n : ℕ) : ((A.β₀ n : (Matrix (Fin n) (Fin n) E)ˣ) : Matrix (Fin n) (Fin n) E) = Dg A n := rfl

private theorem hermStar_baseMatrix (A : Arith E) (n : ℕ) :
    (hermStar (A.H n) (A.det_ne n) ((A.β₀ n : (Matrix (Fin n) (Fin n) E)ˣ) : Matrix (Fin n) (Fin n) E)).unop = A.β₀ n := by
  apply (Units.mul_right_inj (A.β₀ n)).1
  rw [baseMatrix_eq_diagonal, Dg_star, Dg_map]
  simp

private theorem sim_of (A : Arith E) (n : ℕ) (y : (Matrix (Fin n) (Fin n) E)ˣ) (s : ℚˣ)
    (h : (y : Matrix (Fin n) (Fin n) E) * (A.β₀ n : (Matrix (Fin n) (Fin n) E)ˣ) *
      (hermStar (A.H n) (A.det_ne n) y).unop = algebraMap ℚ (Matrix (Fin n) (Fin n) E) s * (A.β₀ n : (Matrix (Fin n) (Fin n) E)ˣ)) :
    ((y : Matrix (Fin n) (Fin n) E).map (IsCMField.complexConj E : E →+* E))ᵀ * (y : Matrix (Fin n) (Fin n) E) =
      algebraMap ℚ E s • (1 : Matrix (Fin n) (Fin n) E) := by
  have hs : algebraMap ℚ E (s : ℚ) ≠ 0 := (map_ne_zero _).2 s.ne_zero
  refine (mul_eq_smul_one_comm hs).1 ?_
  rw [Matrix.mul_assoc, baseMatrix_eq_diagonal, Dg_star, ← Matrix.mul_assoc, ← baseMatrix_eq_diagonal] at h
  have h2 := (Units.mul_left_inj (A.β₀ n)).1 h
  rw [h2]
  ext i j
  by_cases hij : i = j
  · subst hij; simp [Matrix.algebraMap_matrix_apply]
  · simp [Matrix.algebraMap_matrix_apply, hij]

private theorem gram_psi (A : Arith E) (n : ℕ) (τ : E →+* ℂ) (b : Matrix (Fin n) (Fin n) E) (hb : Dg A n * b = 1) :
    gramAt (A.H n) τ * b.map τ = (-τ (A.c : E)) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  have e1 : gramAt (A.H n) τ = (-τ (A.c : E)) • (Dg A n).map τ := by
    ext i j
    by_cases h : i = j
    · subst h; simp [gramAt, Arith.H, Arith.hd]
    · simp [gramAt, Arith.H, h, Ne.symm h]
  have e2 : (Dg A n).map τ * b.map τ = 1 := by
    rw [← Matrix.map_mul, hb, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [e1, Matrix.smul_mul, e2]

private theorem c_im (A : Arith E) (τ : E →+* ℂ) : (τ (A.c : E)).im = 0 := by
  have h1 : τ (IsCMField.complexConj E (A.c : E)) = (starRingEnd ℂ) (τ (A.c : E)) :=
    IsCMField.complexEmbedding_complexConj E τ _
  rw [← A.bar_eq, A.c_real] at h1
  exact Complex.conj_eq_iff_im.1 h1.symm

private theorem form_val (r : ℂ) (hr : r.im = 0) (x : Fin n → ℂ) (hx : x ≠ 0) :
    ∃ t : ℝ, 0 < t ∧ (star x ⬝ᵥ ((r • (1 : Matrix (Fin n) (Fin n) ℂ)) *ᵥ x)).re = r.re * t := by
  open scoped ComplexOrder in
  have h := Matrix.dotProduct_star_self_pos_iff.2 hx
  refine ⟨(star x ⬝ᵥ x).re, (Complex.pos_iff.1 h).1, ?_⟩
  rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul, Complex.mul_re, hr, zero_mul, sub_zero]

private theorem c_neg_of (A : Arith E) (τ : E →+* ℂ) (h : InfinitePlace.mk τ = InfinitePlace.mk A.τ₀) :
    (τ (A.c : E)).re < 0 := by
  rcases InfinitePlace.mk_eq_iff.1 h with h | h
  · rw [h]; exact A.c_neg
  · have := A.c_neg
    rw [← h] at this
    simpa [ComplexEmbedding.conjugate_coe_eq] using this

private theorem book_constants_pos_of_pos (A : Arith E) (n : ℕ) (hs : A.SigOK n) (v : InfinitePlace E) (b : Matrix (Fin n) (Fin n) E)
    (hb : Dg A n * b = 1) (x : Fin n → ℂ) (hx : x ≠ 0) :
    (sigPos (A.herm n) v.embedding = 1 → 0 < (star x ⬝ᵥ ((gramAt (A.H n) v.embedding * b.map v.embedding) *ᵥ x)).re) ∧
    (sigPos (A.herm n) v.embedding ≠ 1 → (star x ⬝ᵥ ((gramAt (A.H n) v.embedding * b.map v.embedding) *ᵥ x)).re < 0) := by
  rw [gram_psi A n _ b hb]
  obtain ⟨t, ht, he⟩ := form_val (-v.embedding (A.c : E)) (by simp [c_im]) x hx
  rw [he]
  have hm : InfinitePlace.mk v.embedding = v := InfinitePlace.mk_embedding v
  constructor
  · intro h1
    have hv : InfinitePlace.mk v.embedding = InfinitePlace.mk A.τ₀ := by
      by_contra hne
      have := ((hs v.embedding).2 hne).1
      omega
    have := c_neg_of A _ hv
    simp only [Complex.neg_re]
    nlinarith
  · intro h1
    have hv : InfinitePlace.mk v.embedding ≠ InfinitePlace.mk A.τ₀ := fun h => h1 ((hs v.embedding).1 h).1
    have := A.c_pos _ hv
    simp only [Complex.neg_re]
    nlinarith

variable {A : Arith E}

private theorem iso_map {S : Setup A n p} (T : Tr S) :
    ((T.a.val.map T.Φ).map (conjT E (AfP p)))ᵀ * Matrix.diagonal (fun i => (1 : AfP p) ⊗ₜ[ℚ] (A.dg n i : E)) * T.a.val.map T.Φ = 1 := by
  have h := congrArg (fun M : Matrix (Fin n) (Fin n) (Af E) => M.map T.Φ) T.iso.1
  simp only [Matrix.map_mul] at h
  rw [Matrix.map_one _ (map_zero _) (map_one _)] at h
  have e1 : ((T.a.val.map (conjFin (conjE E)))ᵀ).map T.Φ = ((T.a.val.map T.Φ).map (conjT E (AfP p)))ᵀ := by
    ext i j
    exact T.Φ_conj _
  have e2 : (Matrix.diagonal (fun i => algebraMap E (Af E) (A.dg n i : E))).map T.Φ =
      Matrix.diagonal (fun i => (1 : AfP p) ⊗ₜ[ℚ] (A.dg n i : E)) := by
    rw [Matrix.diagonal_map (map_zero _)]
    congr 1; funext i
    exact T.Φ_E _
  rw [e1, e2] at h
  exact h

private def xU {S : Setup A n p} (T : Tr S) : (AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E)ˣ :=
  Units.map (T.μ.symm : Matrix (Fin n) (Fin n) (AfP p ⊗[ℚ] E) →* AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E)
    (GeneralLinearGroup.map T.Φ T.a)

private theorem traceMap_unipotent {S : Setup A n p} (T : Tr S) : T.μ (xU T) = T.a.val.map T.Φ := by
  show T.μ (T.μ.symm _) = _
  rw [RingEquiv.apply_symm_apply]
  rfl

private theorem mu_xi {S : Setup A n p} (T : Tr S) : T.μ ((xU T)⁻¹ : (AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E)ˣ) = (T.a⁻¹).val.map T.Φ := by
  show T.μ (T.μ.symm _) = _
  rw [RingEquiv.apply_symm_apply]
  rfl

private theorem mu_b {S : Setup A n p} (T : Tr S) (y : Matrix (Fin n) (Fin n) E) :
    T.μ ((1 : AfP p) ⊗ₜ[ℚ] y) = y.map (fun z => (1 : AfP p) ⊗ₜ[ℚ] z) := by
  ext i k
  exact T.mu 1 y i k

private theorem triv_mat (hM : MuStar) {S : Setup A n p} (T : Tr S) :
    (xU T : AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E) * ((1 : AfP p) ⊗ₜ[ℚ] Dg A n) *
      (starT (hermStar (A.H n) (A.det_ne n)) (AfP p) (xU T)).unop = 1 := by
  apply T.μ.injective
  have h := hM (AfP p) E A n T.μ T.mu (xU T : AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E)
  have h0 := iso_map T
  rw [map_mul, map_mul, map_one, mu_b, traceMap_unipotent, Matrix.mul_assoc]
  rw [traceMap_unipotent] at h
  have e : (Dg A n).map (fun z => (1 : AfP p) ⊗ₜ[ℚ] z) =
      Matrix.diagonal (fun i => (1 : AfP p) ⊗ₜ[ℚ] (A.dg n i : E)) := by
    rw [Matrix.diagonal_map (by simp)]
  rw [e, h]
  exact mul_eq_one_comm.1 h0

private def similitudeToGammaZeroHom (S : Setup A n p) : GlobalTheory.LKCx.grp S.G (A.β₀ n) →* Gam0 E n where
  toFun y := ⟨y.1, Subgroup.mem_inf.2 ⟨sim_of A n y.1.1 y.1.2 y.2.1, y.2.2⟩⟩
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem mat_rat {S : Setup A n p} (T : Tr S) (y : Gam0 E n) :
    (mat (rat y)).val.map T.Φ = (y.1.1.val).map (fun z => (1 : AfP p) ⊗ₜ[ℚ] z) := by
  ext i k
  exact T.Φ_E _

private theorem rho_rat {S : Setup A n p} (T : Tr S) (s : ℚ) : T.ρ (algebraMap ℚ AfQ s) = algebraMap ℚ (AfP p) s :=
  RingHom.congr_fun (RingHom.ext_rat (T.ρ.comp (algebraMap ℚ AfQ)) (algebraMap ℚ (AfP p))) s

end UpperTheory.Gal.W2.Seed

theorem UpperTheory.Gal.W2.Seed.pStdForm :
    MuStar → StdForm := by
  intro hM E _ _ _ A n p _ S T
  let β : S.G.Cˣ := A.β₀ n
  have hx : Triv S.G (AfP p) (β : S.G.C) (xU T) 1 :=
    (triv_mat hM T).trans (map_one (algebraMap (AfP p) (AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E))).symm
  have hsym : sh S.G (β : S.G.C) = (β : S.G.C) := hermStar_baseMatrix A n
  let B : DForm S.G := ⟨β, hsym, ⟨xU T, 1, hx⟩, fun v x h0 =>
    book_constants_pos_of_pos A n S.sig v (((A.β₀ n)⁻¹ : (Matrix (Fin n) (Fin n) E)ˣ) : Matrix (Fin n) (Fin n) E) (Units.mul_inv (A.β₀ n)) x h0⟩
  refine ⟨B, xU T, hx, similitudeToGammaZeroHom S, fun y => rfl, fun y => ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · apply Units.ext
    apply T.μ.injective
    have h1 := T.j_mx (rat (similitudeToGammaZeroHom S y))
    let Y : (Matrix (Fin n) (Fin n) E)ˣ := y.1.1
    have h2 : T.μ (S.mx (GlobalTheory.LKCx.toAfF S.G B.β (xU T) 1 hx y)) =
        T.a.val.map T.Φ * (Y : Matrix (Fin n) (Fin n) E).map (fun z => (1 : AfP p) ⊗ₜ[ℚ] z) * (T.a⁻¹).val.map T.Φ := by
      show T.μ ((xU T : AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E) * ((1 : AfP p) ⊗ₜ[ℚ] (Y : Matrix (Fin n) (Fin n) E)) *
        (((xU T)⁻¹ : (AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E)ˣ) : AfP p ⊗[ℚ] Matrix (Fin n) (Fin n) E)) = _
      rw [map_mul, map_mul, traceMap_unipotent, mu_xi, mu_b]
    refine h2.trans (Eq.trans ?_ h1.symm)
    rw [Units.val_mul, Units.val_mul, Matrix.map_mul, Matrix.map_mul, mat_rat]
    rfl
  · apply Units.ext
    have h1 := T.j_sim (rat (similitudeToGammaZeroHom S y))
    exact (rho_rat T _).symm.trans h1.symm
end
end
