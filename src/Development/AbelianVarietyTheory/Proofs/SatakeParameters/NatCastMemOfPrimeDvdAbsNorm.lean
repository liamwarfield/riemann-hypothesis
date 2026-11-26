module

public import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsIrrDistinctConstituentsAfterExtension
public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.BadPrimesPeriodBound
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.ExistsCoprimePowEqOne
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ModelsOK
public import Formalism.SharpRestriction.Divisibility.JetPolynomialLogs.LetterLogIntegrality
public import Development.AbelianVarietyTheory.Counterexamples.UpperHalfSurvey.NonemptyAlgebra
public import Formalism.LocalToGlobal.Columns.BaseHost
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSumTaylorCoordinateSpaceEntire

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NatCastMemOfPrimeDvdAbsNorm
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical

namespace GlobalTheory.KerTie

theorem natCast_mem_of_prime_dvd_absNorm {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) {q : ℕ}
    (hq : q.Prime) (h : q ∣ Ideal.absNorm P.asIdeal) : (q : 𝓞 E) ∈ P.asIdeal := by
  have : Fact q.Prime := ⟨hq⟩
  have := P.isPrime
  have : Finite (𝓞 E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot P.asIdeal P.ne_bot
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at h
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' (G := 𝓞 E ⧸ P.asIdeal) q h
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [addOrderOf_zero] at hx
    exact hq.one_lt.ne hx
  have h1 : q • x = 0 := by rw [← hx]; exact addOrderOf_nsmul_eq_zero x
  rw [nsmul_eq_mul] at h1
  have h2 : ((q : ℕ) : 𝓞 E ⧸ P.asIdeal) = 0 := (mul_eq_zero.1 h1).resolve_right hx0
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact h2

theorem sNum_qOf_rowSG :
    ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC)
      (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex),
      ∀ u μ (P : rowSG t.Pr t.sel (t.tup μ)), SNum (t.O u μ).S (qOf P.1) := by
  intro D L hT Gi Gl K Y cX ex t u μ P
  refine ⟨Nat.pos_of_ne_zero ?_, fun q hq hP => ?_⟩
  · simpa [Formalism.L2.Col.qOf, Ideal.absNorm_eq_zero_iff] using P.1.ne_bot
  rw [t.O_S]
  refine Finset.mem_insert_of_mem ?_
  rcases Finset.mem_union.1 P.2 with hG | hQ
  · refine Finset.mem_union_left _ ?_
    rcases Finset.mem_union.1 hG with h0 | h0
    · have e : Formalism.L2.Col.qOf P.1 = t.Pr.g 0 := t.pr_ok.vG_norm 0 P.1 h0
      rw [e] at hP
      rw [(Nat.prime_dvd_prime_iff_eq hq (t.pr_ok.g_prime 0)).1 hP, t.g_rec]
      simp
    · have e : Formalism.L2.Col.qOf P.1 = t.Pr.g 1 := t.pr_ok.vG_norm 1 P.1 h0
      rw [e] at hP
      rw [(Nat.prime_dvd_prime_iff_eq hq (t.pr_ok.g_prime 1)).1 hP, t.g_rec]
      simp
  · exact Finset.mem_union_right _
      ((t.Q_rec μ q).2 ⟨hq, P.1, hQ, natCast_mem_of_prime_dvd_absNorm P.1 hq hP⟩)

end GlobalTheory.KerTie
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsUnitOfStableLine
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

namespace GlobalTheory.Pst.StLine

theorem isUnit_of_stable_line : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) [IsDomain P.R.B] (K : FinExt l),
  (∀ b : P.R.B, ¬ ∀ g ∈ GK K, P.actQ g b - b = (kummer P g : ℚ_[l]) • P.tB) → GlobalTheory.RegularRing.LineUnit (P.PD K) →
  ∀ b : Bst P, b ≠ 0 → (∀ g : ↥(GK K), ∃ x : ℚ_[l], actSt P (g : GQ l) b = algebraMap ℚ_[l] (Bst P) x * b) → IsUnit b := by
  intro l _ P _ K hno hLU b hb hst
  unfold GlobalTheory.RegularRing.LineUnit at hLU
  haveI : CharZero P.R.B := charZero_of_injective_algebraMap (algebraMap ℚ_[l] P.R.B).injective

  have hact : ∀ (g : GQ l) (p : Bst P),
      actSt P g p = stHom P (P.actQ g) (X + C ((kummer P g : ℚ_[l]) • P.tB)) p := fun g p => rfl

  have hder : ∀ (g : GQ l) (p : Bst P), derivative (actSt P g p) = actSt P g (derivative p) := by
    intro g p
    rw [hact, hact, derivative_stHom]
    simp
  have hiter : ∀ (k : ℕ) (g : GQ l) (p : Bst P),
      actSt P g (derivative^[k] p) = derivative^[k] (actSt P g p) := by
    intro k g
    induction k with
    | zero => intro p; rfl
    | succ k ih =>
      intro p
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih, hder]

  have heig : ∀ (k : ℕ) (g : ↥(GK K)), ∃ x : ℚ_[l],
      actSt P (g : GQ l) (derivative^[k] b) = algebraMap ℚ_[l] (Bst P) x * derivative^[k] b := by
    intro k g
    obtain ⟨x, hx⟩ := hst g
    refine ⟨x, ?_⟩
    rw [hiter, hx, Polynomial.algebraMap_apply, iterate_derivative_C_mul]

  have hlin : ∀ p : Bst P, p.natDegree ≤ 1 → p.coeff 1 ≠ 0 →
      (∀ g : ↥(GK K), ∃ x : ℚ_[l], actSt P (g : GQ l) p = algebraMap ℚ_[l] (Bst P) x * p) → False := by
    intro p hp1 hp0 hpe
    obtain ⟨u, v, rfl⟩ : ∃ u v, p = C u * X + C v := ⟨p.coeff 1, p.coeff 0, eq_X_add_C_of_natDegree_le_one hp1⟩
    have hu0 : u ≠ 0 := by simpa using hp0
    have hco : ∀ (g : GQ l), g ∈ GK K → ∃ x : ℚ_[l],
        P.actQ g u = algebraMap ℚ_[l] P.R.B x * u ∧
        P.actQ g u * ((kummer P g : ℚ_[l]) • P.tB) + P.actQ g v = algebraMap ℚ_[l] P.R.B x * v := by
      intro g hg
      obtain ⟨x, hx⟩ := hpe ⟨g, hg⟩
      refine ⟨x, ?_, ?_⟩
      · have h1 := congrArg (fun q => _root_.AddMonoidAlgebra.coeff (M := ℕ) q 1) hx
        simpa [Polynomial.algebraMap_apply, mul_add] using h1
      · have h0 := congrArg (fun q => _root_.AddMonoidAlgebra.coeff (M := ℕ) q 0) hx
        simpa [Polynomial.algebraMap_apply, mul_add] using h0
    have hU : IsUnit u := hLU u hu0 (fun g => by
      obtain ⟨x, h1, -⟩ := hco (g : GQ l) g.2
      exact ⟨x, by rw [P.PD_actB]; exact h1⟩)
    obtain ⟨w, hw⟩ : ∃ w, w = v * ↑hU.unit⁻¹ := ⟨_, rfl⟩
    have hwu : w * u = v := by rw [hw, mul_assoc, IsUnit.val_inv_mul, mul_one]
    refine hno (-w) (fun g hg => ?_)
    obtain ⟨x, h1, h0⟩ := hco g hg
    have hne : P.actQ g u ≠ 0 := (hU.map (P.actQ g)).ne_zero
    have key : P.actQ g w * P.actQ g u = (w - (kummer P g : ℚ_[l]) • P.tB) * P.actQ g u := by
      rw [← map_mul, hwu]
      linear_combination h0 - w * h1 - (algebraMap ℚ_[l] P.R.B x) * hwu
    have hgw : P.actQ g w = w - (kummer P g : ℚ_[l]) • P.tB := mul_right_cancel₀ hne key
    rw [map_neg, hgw]
    ring
  by_cases hn : b.natDegree = 0
  · obtain ⟨c, rfl⟩ : ∃ c, b = C c := ⟨_, eq_C_of_natDegree_eq_zero hn⟩
    apply IsUnit.map C
    refine hLU c (fun h => hb (by rw [h, C_0])) (fun g => ?_)
    obtain ⟨x, hx⟩ := hst g
    refine ⟨x, ?_⟩
    rw [P.PD_actB]
    rw [actSt_C, Polynomial.algebraMap_apply, ← C_mul] at hx
    exact C_injective hx
  · exfalso
    apply hlin (derivative^[b.natDegree - 1] b)
    · have := natDegree_iterate_derivative b (b.natDegree - 1)
      omega
    · rw [coeff_iterate_derivative, show 1 + (b.natDegree - 1) = b.natDegree by omega]
      refine smul_ne_zero ?_ (leadingCoeff_ne_zero.mpr hb)
      intro h
      rw [Nat.descFactorial_eq_zero_iff_lt] at h
      omega
    · exact heig (b.natDegree - 1)

end GlobalTheory.Pst.StLine
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConclusionG6OfAllParts
noncomputable section

namespace GlobalTheory.EigenPoint

open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

section Alg

variable {Γ : Type} [Group Γ] {K : Type} [Field K]

theorem charpoly_smul [CharZero K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) {c : K} (hc : c ≠ 0) :
    (c • M).charpoly = M.charpoly.scaleRoots c := by
  have : Infinite K := Infinite.of_injective (Nat.cast : ℕ → K) Nat.cast_injective
  apply Polynomial.funext
  intro x
  obtain ⟨y, rfl⟩ : ∃ y, x = c * y := ⟨c⁻¹ * x, by rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]⟩
  rw [scaleRoots_eval_mul, Matrix.charpoly_natDegree_eq_dim, Matrix.eval_charpoly, Matrix.eval_charpoly,
    ← Matrix.det_smul, smul_sub]
  congr 2
  ext a b
  simp only [Matrix.smul_apply, Matrix.scalar_apply, Matrix.diagonal_apply, smul_eq_mul]
  split_ifs <;> simp

theorem twGL_val {a : ℕ} (ρ : Γ →* GL (Fin a) K) (χ : Γ →* Kˣ) (g : Γ) :
    ((Formalism.MainNotions.SumRepresentations.At.twGL ρ χ g : GL _ K) : Matrix (Fin a) (Fin a) K) =
      (χ g : K) • ((ρ g : GL _ K) : Matrix (Fin a) (Fin a) K) := by
  show algebraMap K (Matrix (Fin a) (Fin a) K) (χ g : K) * ((ρ g : GL _ K) : Matrix (Fin a) (Fin a) K) = _
  rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]

theorem isInv_twGL {a : ℕ} (ρ : Γ →* GL (Fin a) K) (χ : Γ →* Kˣ) (W : Submodule K (Fin a → K)) :
    IsInv (Formalism.MainNotions.SumRepresentations.At.twGL ρ χ) W ↔ IsInv ρ W := by
  constructor
  · intro h g v hv
    have := W.smul_mem ((χ g : K)⁻¹) (h g v hv)
    rwa [twGL_val, Matrix.smul_mulVec, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul] at this
  · intro h g v hv
    rw [twGL_val, Matrix.smul_mulVec]
    exact W.smul_mem _ (h g v hv)

theorem ss_twGL {a : ℕ} (ρ : Γ →* GL (Fin a) K) (χ : Γ →* Kˣ) (h : IsSSRep ρ) :
    IsSSRep (Formalism.MainNotions.SumRepresentations.At.twGL ρ χ) := fun W hW => by
  obtain ⟨W', hW', hc⟩ := h W ((isInv_twGL ρ χ W).1 hW)
  exact ⟨W', (isInv_twGL ρ χ W').2 hW', hc⟩

end Alg

theorem ms_one {s : Multiset ℕ} (h : s.sum = 1) (h1 : ∀ a ∈ s, 1 ≤ a) : s = {1} := by
  have hne : s ≠ 0 := by rintro rfl; simp at h
  have hc := Multiset.card_nsmul_le_sum h1
  have hp := Multiset.card_pos.2 hne
  rw [smul_eq_mul, mul_one, h] at hc
  have hc1 : Multiset.card s = 1 := by omega
  obtain ⟨a, rfl⟩ := Multiset.card_eq_one.1 hc1
  simp only [Multiset.sum_singleton] at h
  rw [h]

theorem sum_split {M : Type} [AddCommMonoid M] {n m : ℕ} (h : n = m + 1) (f : Fin n → M) :
    ∑ k, f k = ∑ k : Fin m, f (Fin.cast h.symm k.castSucc) + f (Fin.cast h.symm (Fin.last m)) := by
  subst h
  simp [Fin.sum_univ_castSucc]

theorem prod_flatMap' {α M : Type} [CommMonoid M] (l : List α) (f : α → List M) :
    (l.flatMap f).prod = (l.map fun a => (f a).prod).prod := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, List.prod_append, ih]

theorem prod_flat {M : Type} [CommMonoid M] (n : ℕ) (d : Fin n → ℕ) (f : Fin n → ℕ → M) :
    (((List.finRange n).map fun k => ((List.range (d k)).map (f k)).prod)).prod =
      ∏ k, ∏ a ∈ Finset.range (d k), f k a := by
  rw [Fin.prod_univ_def]
  congr 1

variable (D : D7) (i : D.nd.Loc)

def eU : G D.host.E D.nd.Om →* (Qbar (D.nd.l i))ˣ :=
  (Units.map (iotaOQ D.nd D.naut i).toMonoidHom).comp (Formalism.MainNotions.N.Glob.epsO D.nd i)

def cU : G D.host.E D.nd.Om →* (Qbar (D.nd.l i))ˣ :=
  (Units.map (iotaOQ D.nd D.naut i).toMonoidHom).comp (D.nd.chi i 1)

theorem eU_pow (g : G D.host.E D.nd.Om) (a : ℕ) :
    ((((eU D i)⁻¹ ^ a) g : (Qbar (D.nd.l i))ˣ) : Qbar (D.nd.l i)) = (epsQ D i g)⁻¹ ^ a := by
  rw [MonoidHom.pow_apply, MonoidHom.inv_apply, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
  rfl

def twList (Pa : List (Part D.naut.CG))
    (R : ∀ k : Fin Pa.length, G D.host.E D.nd.Om →* GL (Fin (Pa.get k).a) (Qbar (D.nd.l i))) :
    List (Σ m : ℕ, G D.host.E D.nd.Om →* GL (Fin m) (Qbar (D.nd.l i))) :=
  (List.finRange Pa.length).flatMap fun k =>
    (List.range (Pa.get k).d).map fun a => ⟨(Pa.get k).a, Formalism.MainNotions.SumRepresentations.At.twGL (R k) ((eU D i)⁻¹ ^ a)⟩

theorem mem_twList {Pa : List (Part D.naut.CG)}
    {R : ∀ k : Fin Pa.length, G D.host.E D.nd.Om →* GL (Fin (Pa.get k).a) (Qbar (D.nd.l i))}
    {p : Σ m : ℕ, G D.host.E D.nd.Om →* GL (Fin m) (Qbar (D.nd.l i))} (hp : p ∈ twList D i Pa R) :
    ∃ k : Fin Pa.length, ∃ a < (Pa.get k).d,
      p = ⟨(Pa.get k).a, Formalism.MainNotions.SumRepresentations.At.twGL (R k) ((eU D i)⁻¹ ^ a)⟩ := by
  obtain ⟨k, -, hk⟩ := List.mem_flatMap.1 hp
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hk
  exact ⟨k, a, List.mem_range.1 ha, rfl⟩

theorem twList_cp (Pa : List (Part D.naut.CG))
    (R : ∀ k : Fin Pa.length, G D.host.E D.nd.Om →* GL (Fin (Pa.get k).a) (Qbar (D.nd.l i)))
    (g : G D.host.E D.nd.Om) :
    ((twList D i Pa R).map fun p => ((p.2 g : GL _ _) : Matrix (Fin p.1) (Fin p.1) (Qbar (D.nd.l i))).charpoly).prod =
      ∏ k : Fin Pa.length, ∏ a ∈ Finset.range (Pa.get k).d,
        (((R k g : GL _ _) : Matrix (Fin (Pa.get k).a) (Fin (Pa.get k).a) (Qbar (D.nd.l i))).charpoly).scaleRoots
          ((epsQ D i g)⁻¹ ^ a) := by
  rw [twList, List.map_flatMap, prod_flatMap']
  simp only [List.map_map, Function.comp_def]
  rw [prod_flat]
  refine Finset.prod_congr rfl fun k _ => Finset.prod_congr rfl fun a _ => ?_
  rw [twGL_val, charpoly_smul _ (Units.ne_zero _), eU_pow]

theorem mapRep_val {Γ A B : Type} [Group Γ] [CommRing A] [CommRing B] {a : ℕ} (f : A →+* B)
    (ρ : Γ →* GL (Fin a) A) (g : Γ) :
    ((mapRep f ρ g : GL _ _) : Matrix (Fin a) (Fin a) B) = ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) A).map f := rfl

theorem eig_map (r : G D.host.E D.nd.Om →* GL (Fin D.R.nV) (D.nd.O i)) (v : Fin D.R.nV → Kf D.nd i)
    (hv0 : v ≠ 0) (hv : ∀ g, ((mapRep (algebraMap (D.nd.O i) (Kf D.nd i)) r g : GL _ _) :
        Matrix (Fin D.R.nV) (Fin D.R.nV) (Kf D.nd i)).mulVec v =
          algebraMap (D.nd.O i) (Kf D.nd i) (chi1 D.nd i g) • v) :
    ∃ w : Fin D.R.nV → Qbar (D.nd.l i), w ≠ 0 ∧ ∀ g,
      ((mapRep (iotaOQ D.nd D.naut i) r g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar (D.nd.l i))).mulVec w =
        ((cU D i g : (Qbar (D.nd.l i))ˣ) : Qbar (D.nd.l i)) • w := by
  refine ⟨fun j => D.naut.iotaQ i (v j), fun h => hv0 (funext fun j => ?_), fun g => funext fun j => ?_⟩
  · have := congrFun h j
    exact (D.naut.iotaQ i).injective (by simpa using this)
  · have e1 := congrArg (D.naut.iotaQ i) (congrFun (hv g) j)
    rw [RingHom.map_mulVec, mapRep_val] at e1
    rw [mapRep_val]
    refine e1.trans ?_
    rw [Pi.smul_apply, smul_eq_mul, map_mul, Pi.smul_apply, smul_eq_mul]
    rfl

end GlobalTheory.EigenPoint
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelJets
noncomputable section

namespace GlobalTheory.LiftTypePrime

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta GlobalTheory.IndefiniteRowSideFullHecke.IntegralityWeylConditions

def StdAt (D : D7) (g : ℕ) {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) : Prop :=
  ∃ L₀ : Submodule (𝓞 D.host.E) (Fin N → D.host.E), (∀ x, x ∈ L₀ ↔ ∀ k, IsIntegral ℤ (x k)) ∧ EqAt D g L L₀


end GlobalTheory.LiftTypePrime

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JetZ
noncomputable section

namespace GlobalTheory.OnePlace

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem GlobalTheory.TwU

def xiE {p : ℕ} [Fact p.Prime] {n' r0 r1 : ℕ} (x : Fin (n' / 2) ⊕ Fin (n' / 2) → MvPowerSeries (ZMod n') ℂ_[p]) :
    Eidx n' r0 r1 ⊕ Eidx n' r0 r1 → MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p]
  | Sum.inl (r, a, b) => MvPowerSeries.subst (fun s : ZMod n' =>
      (MvPowerSeries.X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p])) (x (Sum.inl r))
  | Sum.inr (r, a, b) => MvPowerSeries.subst (fun s : ZMod n' =>
      (MvPowerSeries.X (s, a, b) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p])) (x (Sum.inr r))

def jetZ (p : ℕ) [Fact p.Prime] (n' r0 r1 : ℕ) (z : Zidx n' r0 r1) : MvPowerSeries (ZMod n' × Fin r0 × Fin r1) ℂ_[p] :=
  jetLogG p n' (((z.1 : ℕ) : ZMod n'), z.2)

end GlobalTheory.OnePlace

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConstantCoeffJetLogG
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

noncomputable section

namespace GlobalTheory.BeProps

open MvPowerSeries GlobalTheory.ThStr Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric

variable {l : ℕ} [hl : Fact l.Prime] {d : ℕ}

theorem norm_eq_one_of_pow {n : ℕ} (hn : 0 < n) {a : ℂ_[l]} (ha : a ^ n = 1) : ‖a‖ = 1 := by
  have h : ‖a‖ ^ n = 1 := by rw [← norm_pow, ha, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg a) hn.ne').1 h

theorem norm_le_one_of_mem_Wp {w : ℂ_[l]} (hw : w ∈ Wp l) : ‖w‖ ≤ 1 := by
  have hc : IsClosed {x : ℂ_[l] | ‖x‖ ≤ 1} := isClosed_le continuous_norm continuous_const
  refine closure_minimal (t := {x : ℂ_[l] | ‖x‖ ≤ 1}) (fun x hx => ?_) hc hw
  change ‖x‖ ≤ 1
  induction hx using Subring.closure_induction with
  | mem x hx => obtain ⟨n, hn, -, h⟩ := hx; exact (norm_eq_one_of_pow hn h).le
  | zero => simp
  | one => simp
  | add x y _ _ hx hy => exact (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)
  | neg x _ hx => simpa using hx
  | mul x y _ _ hx hy => rw [norm_mul]; exact mul_le_one₀ hx (norm_nonneg _) hy

variable [NeZero d]

theorem constantCoeff_laS (s : ZMod d) : constantCoeff (laS l d s) = 0 :=
  (GlobalTheory.BiextInhab.laK_idMod2 (K := ℂ_[l]) (d := d) hl.out).1 s

theorem constantCoeff_laAt {κ : Type} [Finite κ] (ι : ZMod d → κ) (s : ZMod d) :
    constantCoeff (laAt (l := l) ι s) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)
    (fun _ => constantCoeff_X _) (constantCoeff_laS s)

theorem coeff_subst_range {K σ : Type*} [CommRing K] {G : MvPowerSeries σ K}
    (hG : MvPowerSeries.constantCoeff G = 0) (f : PowerSeries K) (α : σ →₀ ℕ) :
    MvPowerSeries.coeff α (f.subst G) =
      ∑ n ∈ Finset.range ((α.sum fun _ k => k) + 1),
        PowerSeries.coeff n f * MvPowerSeries.coeff α (G ^ n) := by
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hG),
    finsum_eq_sum_of_support_subset (s := Finset.range ((α.sum fun _ k => k) + 1))]
  · rfl
  · intro k hk
    by_contra h
    apply hk
    have hlt : (α.sum fun _ k => k) < k := by simpa using h
    have h0 : MvPowerSeries.coeff α (G ^ k) = 0 := by
      apply MvPowerSeries.coeff_of_lt_order
      refine lt_of_lt_of_le ?_ (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero k hG)
      exact_mod_cast hlt
    simp [h0]

theorem expMv_eq_subst {σ : Type*} {G : MvPowerSeries σ ℂ_[l]} (hG : MvPowerSeries.constantCoeff G = 0) :
    expMv G = (PowerSeries.exp ℂ_[l]).subst G := by
  ext α
  rw [coeff_subst_range hG]
  show expMv G α = _
  rw [expMv]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [div_eq_inv_mul]

theorem subst_psubst {σ τ : Type} [Finite σ] {b : σ → MvPowerSeries τ ℂ_[l]} (hb : HasSubst b)
    {f : MvPowerSeries σ ℂ_[l]} (hf : constantCoeff f = 0) (g : PowerSeries ℂ_[l]) :
    subst b (PowerSeries.subst f g) = PowerSeries.subst (subst b f) g := by
  have ha : HasSubst (fun _ : Unit => f) := hasSubst_of_constantCoeff_zero fun _ => hf
  unfold PowerSeries.subst
  rw [subst_comp_subst_apply ha hb]

end GlobalTheory.BeProps
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardSeriesBConditionsLargePrime
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardSeriesBConditionsLargePrime
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual addC thetaInZ sumE)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

namespace GlobalTheory.KerStd.StdHyp

open Formalism.DworkPowerSeriesWeights (BHyp NoLowBidegree degE degO letterLog mvExp de1 de2 Integral torus lw V2)
open Formalism.MainNotions.DIV.Bridge.LetterLogIntegrality (eV coeff_subst_scale lw_twist cobX_eq cobY_eq jetLog_rename coeff_subst_rename
  hasSubst_XeV letterLog_cc jetLogG_cc)

theorem kur_sub_wfrac (l : ℕ) [Fact l.Prime] : ∀ x ∈ MaximalUnramifiedExtension l, x ∈ product_zeroth_first_parts.Wfrac l := by
  have hS : {ζ : ℂ_[l] | ∃ n : ℕ, 0 < n ∧ ¬ l ∣ n ∧ ζ ^ n = 1} = product_zeroth_first_parts.rootsPrimeTo l := by
    ext ζ
    simp only [Set.mem_setOf_eq, product_zeroth_first_parts.rootsPrimeTo]
    refine exists_congr fun n => and_congr_right fun _ => and_congr_left fun _ => ?_
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd (Fact.out : l.Prime)]
  have halg : ∀ x ∈ product_zeroth_first_parts.rootsPrimeTo l, IsAlgebraic ℚ_[l] x := by
    rintro x ⟨n, hn, -, hx⟩
    exact (IsIntegral.of_pow hn (by rw [hx]; exact isIntegral_one)).isAlgebraic
  have hsub : (Subfield.closure (product_zeroth_first_parts.rootsPrimeTo l) : Set ℂ_[l]) ⊆ Algebra.adjoin ℚ_[l] (product_zeroth_first_parts.rootsPrimeTo l) := by
    intro x hx
    have h1 : Subfield.closure (product_zeroth_first_parts.rootsPrimeTo l) ≤
        (IntermediateField.adjoin ℚ_[l] (product_zeroth_first_parts.rootsPrimeTo l)).toSubfield :=
      Subfield.closure_le.mpr (IntermediateField.subset_adjoin _ _)
    have h2 := h1 hx
    rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic halg]
    exact h2
  intro x hx
  unfold MaximalUnramifiedExtension at hx
  rw [hS] at hx
  unfold product_zeroth_first_parts.Wfrac
  have hc : x ∈ closure (Subfield.closure (product_zeroth_first_parts.rootsPrimeTo l) : Set ℂ_[l]) := hx
  exact closure_mono hsub hc

theorem b3_of_noLowBidegree (l d : ℕ) [Fact l.Prime] [NeZero d] (be : MvPowerSeries (ZMod d) ℂ_[l])
    (h : NoLowBidegree be) : product_zeroth_first_parts.B3 l d be := by
  intro n hn
  obtain ⟨h1, h2, h3⟩ := h n hn
  have e1 : (product_zeroth_first_parts.bideg d n).1 = degE n := by
    unfold product_zeroth_first_parts.bideg degE
    simp only [Nat.even_iff]
    exact Finsupp.sum_fintype _ _ (by intro s; split_ifs <;> rfl)
  have e2 : (product_zeroth_first_parts.bideg d n).2 = degO n := by
    unfold product_zeroth_first_parts.bideg degO
    simp only [Nat.even_iff]
    exact Finsupp.sum_fintype _ _ (by intro s; split_ifs <;> rfl)
  refine ⟨by rw [e1]; exact h1.ne', by rw [e2]; exact h2.ne', ?_⟩
  intro hb
  apply h3
  have a := congrArg Prod.fst hb
  have b := congrArg Prod.snd hb
  exact ⟨e1 ▸ a, e2 ▸ b⟩

theorem b2_of_subst_torus_eq (l d : ℕ) [Fact l.Prime] [NeZero d] (ζ : ℂ_[l]) (hζ : IsPrimitiveRoot ζ (l ^ d - 1))
    (be : MvPowerSeries (ZMod d) ℂ_[l]) (h : MvPowerSeries.subst (torus l ζ) be = be) : product_zeroth_first_parts.B2 l d be := by
  intro u hu m
  haveI : NeZero (l ^ d - 1) := ⟨by
    have h1 := (Fact.out : l.Prime).one_lt
    have : 1 < l ^ d := Nat.one_lt_pow (NeZero.ne d) h1
    omega⟩
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hu
  have hm := congrArg (MvPowerSeries.coeff m) h
  have e : (torus l ζ : ZMod d → MvPowerSeries (ZMod d) ℂ_[l]) =
      fun s => MvPowerSeries.C (ζ ^ lw l s) * MvPowerSeries.X s := rfl
  rw [e, coeff_subst_scale] at hm
  by_cases hc : MvPowerSeries.coeff m be = 0
  · rw [hc, zero_mul]
  have hP : (m.prod fun s k => (ζ ^ lw l s) ^ k) = 1 :=
    mul_right_cancel₀ hc (by rw [one_mul]; exact hm)
  have hT : (m.prod fun s n => product_zeroth_first_parts.twist l d (ζ ^ i) s ^ n) = (m.prod fun s k => (ζ ^ lw l s) ^ k) ^ i := by
    unfold Finsupp.prod
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun s _ => ?_
    show product_zeroth_first_parts.twist l d (ζ ^ i) s ^ m s = ((ζ ^ lw l s) ^ m s) ^ i
    rw [← lw_twist]
    simp only [← zpow_natCast, ← zpow_mul]
    congr 1
    ring
  rw [hT, hP, one_pow, mul_one]

theorem b4_of_coeff_subst_letterLog (l d : ℕ) [Fact l.Prime] [NeZero d] (D : MvPowerSeries (V2 d) ℂ_[l])
    (hD0 : MvPowerSeries.constantCoeff D = 0)
    (hW : ∀ n, MvPowerSeries.coeff n (MvPowerSeries.subst (letterLog (K := ℂ_[l]) l) (mvExp D)) ∈ product_zeroth_first_parts.Wint l)
    (h1 : MvPowerSeries.constantCoeff (MvPowerSeries.subst (letterLog (K := ℂ_[l]) l) (mvExp D)) = 1) :
    product_zeroth_first_parts.OverWOne l (MvPowerSeries.subst (Formalism.BasicNotions.jetLogG l d (β := Fin 2))
      (product_zeroth_first_parts.expS ℂ_[l] (MvPowerSeries.subst (fun u : Bool × ZMod d => (MvPowerSeries.X (eV d u) :
        MvPowerSeries (ZMod d × Fin 2) ℂ_[l])) D))) := by
  have hb := hasSubst_XeV l d
  have hbs : MvPowerSeries.HasSubst (fun w : ZMod d × Fin 2 => (MvPowerSeries.X ((eV d).symm w) :
      MvPowerSeries (V2 d) ℂ_[l])) := MvPowerSeries.hasSubst_of_constantCoeff_zero (fun w => by simp)
  have hJ : MvPowerSeries.HasSubst (Formalism.BasicNotions.jetLogG l d (β := Fin 2)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (jetLogG_cc l d)
  have hD : MvPowerSeries.HasSubst (fun _ : Unit => D) := MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => hD0)
  have hLr : MvPowerSeries.HasSubst (fun v : ZMod d × Fin 2 => letterLog (K := ℂ_[l]) l ((eV d).symm v)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun v => letterLog_cc l d _)
  have hrn : (fun v : ZMod d × Fin 2 => MvPowerSeries.subst (fun w : ZMod d × Fin 2 => (MvPowerSeries.X ((eV d).symm w) :
      MvPowerSeries (V2 d) ℂ_[l])) (Formalism.BasicNotions.jetLogG l d (β := Fin 2) v)) =
      fun v => letterLog (K := ℂ_[l]) l ((eV d).symm v) := by
    funext v
    have := jetLog_rename l d ((eV d).symm v)
    rwa [Equiv.apply_symm_apply] at this
  have hexp : product_zeroth_first_parts.expS ℂ_[l] (MvPowerSeries.subst (fun u : Bool × ZMod d => (MvPowerSeries.X (eV d u) :
        MvPowerSeries (ZMod d × Fin 2) ℂ_[l])) D) =
      MvPowerSeries.subst (fun u : Bool × ZMod d => (MvPowerSeries.X (eV d u) :
        MvPowerSeries (ZMod d × Fin 2) ℂ_[l])) (mvExp D) := by
    unfold product_zeroth_first_parts.expS mvExp PowerSeries.subst
    rw [MvPowerSeries.subst_comp_subst_apply hD hb]
  have key : MvPowerSeries.subst (fun w : ZMod d × Fin 2 => (MvPowerSeries.X ((eV d).symm w) :
      MvPowerSeries (V2 d) ℂ_[l])) (MvPowerSeries.subst (Formalism.BasicNotions.jetLogG l d (β := Fin 2))
        (product_zeroth_first_parts.expS ℂ_[l] (MvPowerSeries.subst (fun u : Bool × ZMod d => (MvPowerSeries.X (eV d u) :
          MvPowerSeries (ZMod d × Fin 2) ℂ_[l])) D))) =
      MvPowerSeries.subst (letterLog (K := ℂ_[l]) l) (mvExp D) := by
    rw [hexp, MvPowerSeries.subst_comp_subst_apply hJ hbs, hrn, MvPowerSeries.subst_comp_subst_apply hb hLr]
    congr 1
    funext u
    rw [MvPowerSeries.subst_X hLr, Equiv.symm_apply_apply]
  refine ⟨fun n => ?_, ?_⟩
  · have := hW (Finsupp.equivMapDomain (eV d).symm n)
    rw [← key, coeff_subst_rename, Equiv.symm_symm, ← Finsupp.equivMapDomain_trans] at this
    simpa using this
  · have e := congrArg (MvPowerSeries.coeff 0) key
    rw [coeff_subst_rename, Finsupp.equivMapDomain_zero, MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply] at e
    rw [e, h1]

end GlobalTheory.KerStd.StdHyp

namespace GlobalTheory.KerStd

open Formalism.DworkPowerSeriesWeights (NoLowBidegree)
open Formalism.DworkPowerSeriesWeights.Transfer (map_defectOne map_defectTwo map_logExp constantCoeff_defectOne constantCoeff_defectTwo cc_of_noLow map_torus cc_torus)

theorem bHyps_of_beStd : ∀ (l d : ℕ) [Fact l.Prime] [NeZero d] (be : MvPowerSeries (ZMod d) ℂ_[l]), 5 ≤ l → 2 ≤ d →
    Even d → BeStd l d be → product_zeroth_first_parts.B1 l d be ∧ product_zeroth_first_parts.B2 l d be ∧ product_zeroth_first_parts.B3 l d be ∧ product_zeroth_first_parts.B4 l d be := by
  intro l d _ _ be _ hd2 hde hstd
  obtain ⟨σ, F, be0, om, oms, ζ, ⟨hσ, hF, hF1, -, hO, -, hζ⟩, rfl⟩ := hstd
  obtain ⟨-, h2, h3, ⟨h4, h4'⟩, ⟨h5, h5'⟩⟩ := Formalism.L2.Th1.D.biextension_hypotheses_of_level_one (MaximalUnramifiedExtension l) l d σ hσ hd2 hde F hF be0 hF1
    (Fin (d / 2)) om oms hO ζ hζ
  have hbe : beOf l d σ be0 om oms ζ =
      MvPowerSeries.map (MaximalUnramifiedExtension l).subtype (Formalism.L2.Th1.D.beMean (d := d) l σ be0 om oms ζ) := rfl
  rw [hbe]
  have hc := cc_of_noLow h3
  have hc' : MvPowerSeries.constantCoeff
      (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype (Formalism.L2.Th1.D.beMean (d := d) l σ be0 om oms ζ)) = 0 := by
    rw [MvPowerSeries.constantCoeff_map, hc, map_zero]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m
    rw [MvPowerSeries.coeff_map]
    exact StdHyp.kur_sub_wfrac l _ (SetLike.coe_mem _)
  · have ht := congrArg (MvPowerSeries.map (MaximalUnramifiedExtension l).subtype) h2
    rw [MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero (cc_torus l ζ))] at ht
    simp only [map_torus] at ht
    exact StdHyp.b2_of_subst_torus_eq l d _ (hζ.map_of_injective (MaximalUnramifiedExtension l).subtype.injective) _ ht
  · apply StdHyp.b3_of_noLowBidegree
    intro n hn
    refine h3 n ?_
    intro h0
    rw [MvPowerSeries.coeff_map, h0, map_zero] at hn
    exact hn rfl
  · unfold product_zeroth_first_parts.B4
    rw [Formalism.MainNotions.DIV.Bridge.LetterLogIntegrality.cobX_eq, Formalism.MainNotions.DIV.Bridge.LetterLogIntegrality.cobY_eq]
    constructor
    · refine StdHyp.b4_of_coeff_subst_letterLog l d _ (constantCoeff_defectOne hc') (fun n => ?_) ?_
      · rw [← map_defectOne, ← map_logExp _ l (constantCoeff_defectOne hc), MvPowerSeries.coeff_map]
        exact ⟨StdHyp.kur_sub_wfrac l _ (SetLike.coe_mem _), h4 n⟩
      · rw [← map_defectOne, ← map_logExp _ l (constantCoeff_defectOne hc), MvPowerSeries.constantCoeff_map, h4', map_one]
    · refine StdHyp.b4_of_coeff_subst_letterLog l d _ (constantCoeff_defectTwo hc') (fun n => ?_) ?_
      · rw [← map_defectTwo, ← map_logExp _ l (constantCoeff_defectTwo hc), MvPowerSeries.coeff_map]
        exact ⟨StdHyp.kur_sub_wfrac l _ (SetLike.coe_mem _), h5 n⟩
      · rw [← map_defectTwo, ← map_logExp _ l (constantCoeff_defectTwo hc), MvPowerSeries.constantCoeff_map, h5', map_one]

end GlobalTheory.KerStd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardSeriesBConditionsLargePrimeStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual addC thetaInZ sumE)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standard_series_b_conditions_large_prime : ∀ (l d : ℕ) [Fact l.Prime] [NeZero d] (be : MvPowerSeries (ZMod d) ℂ_[l]), 5 ≤ l → 2 ≤ d → Even d → BeStd l d be → product_zeroth_first_parts.B1 l d be ∧ product_zeroth_first_parts.B2 l d be ∧ product_zeroth_first_parts.B3 l d be ∧ product_zeroth_first_parts.B4 l d be := by
  first | exact @GlobalTheory.KerStd.bHyps_of_beStd | exact GlobalTheory.KerStd.bHyps_of_beStd | (intros; apply GlobalTheory.KerStd.bHyps_of_beStd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChainCompatibleTwistTransport
noncomputable section

namespace GlobalTheory.ColPeriodCompare

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke

section Mem

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (L : Type) [Field L]

def unramOff (S : Set ℕ) (v : HeightOneSpectrum (𝓞 F)) : Subgroup (Chr F E L) :=
  ⨅ _ : ¬ GoodPl E S v, kills Lˣ (inertAt E v)

def IsTwist (S : Set ℕ) (x : Chr F E L) : Prop :=
  x ∈ finChar F E L ⊓ kills Lˣ (idF F E).range ⊓ (⨅ v : HeightOneSpectrum (𝓞 F), kills Lˣ (wildAt E v)) ∧
    x ∈ ⨅ v : HeightOneSpectrum (𝓞 F), unramOff F E L S v

end Mem

section Transport

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S S' : Set ℕ}
  {χ : Chr X.F X.E X.K} (h : IsTwist X.F X.E X.K S χ) (h' : IsTwist X.F X.E X.K S' χ)
  (cst : LocCst X (uSG Pr.vGs (QE sel χ))) (L : ChIdx X Pr R (QE sel χ))

end Transport

section Chain

variable (D : D7) (EX : ErrX D) (Ch : Chars (ColumnAvoidanceConditions.fieldsOf D) (ColumnAvoidanceConditions.primesOf D EX) D.R.m)
  (m0 : Fin D.R.m → Formalism.L2.Host.HChar D.host.E)
  (sel : HeightOneSpectrum (𝓞 (ColumnAvoidanceConditions.fieldsOf D).F) → HeightOneSpectrum (𝓞 (ColumnAvoidanceConditions.fieldsOf D).E)) {S S' : Set ℕ}
  (A : Amb (ColumnAvoidanceConditions.fieldsOf D)) (u : D.what₂.Word) (μ : D.what₂.Tup)

end Chain

end GlobalTheory.ColPeriodCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KerPEqSpanBeta
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KerPEqSpanBeta
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per

namespace GlobalTheory.Pst.StLat

theorem ker_localizedTheta_eq_span_beta : ∀ (l : ℕ) [Fact l.Prime] (ϖ : Per.Fl l), ϖ.untilt = ((l : ℕ) : Per.OC l) →
    Per.kerP l = Ideal.span {beta ϖ} := by
  intro l _ ϖ hϖ
  obtain ⟨_, _, -, -, hK, -⟩ := GlobalTheory.AinfChecks.padicComplex l
  have hk : RingHom.ker (Per.θ l) = Ideal.span {((l : ℕ) : Per.Ainf l) - Per.tm ϖ} := (hK ϖ hϖ).1
  obtain ⟨-, hker, hA, -⟩ := thetaP_facts l
  have hu := GlobalTheory.RingBasics.isUnit_l l
  have hmem : ∀ a : Per.Ainf l, Per.θ l a = 0 →
      algebraMap (Per.Ainf l) (Per.AinfP l) a ∈ Per.kerP l := by
    intro a ha
    rw [← hker, RingHom.mem_ker, hA, ha]
    rfl
  have h0 : Per.θ l (((l : ℕ) : Per.Ainf l) - Per.tm ϖ) = 0 := by
    have : ((l : ℕ) : Per.Ainf l) - Per.tm ϖ ∈ RingHom.ker (Per.θ l) := by
      rw [hk]; exact Ideal.mem_span_singleton_self _
    exact this
  have hlb : ((l : ℕ) : Per.AinfP l) * beta ϖ =
      -algebraMap (Per.Ainf l) (Per.AinfP l) (((l : ℕ) : Per.Ainf l) - Per.tm ϖ) := by
    rw [l_mul_beta, map_sub, map_natCast]; ring
  refine le_antisymm (fun y hy => ?_) ?_
  · rw [← hker, RingHom.mem_ker] at hy
    obtain ⟨n, a, h⟩ := IsLocalization.Away.surj ((l : ℕ) : Per.Ainf l) y
    rw [map_natCast] at h
    have ha : Per.θ l a = 0 := by
      apply Subtype.ext
      rw [← hA, ← h, map_mul, hy, zero_mul]
      rfl
    have h2 : a ∈ Ideal.span {((l : ℕ) : Per.Ainf l) - Per.tm ϖ} := hk ▸ ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 h2
    rw [← Ideal.mul_unit_mem_iff_mem _ (hu.pow n), h, map_mul]
    have : algebraMap (Per.Ainf l) (Per.AinfP l) (((l : ℕ) : Per.Ainf l) - Per.tm ϖ) =
        -(((l : ℕ) : Per.AinfP l) * beta ϖ) := by rw [hlb, neg_neg]
    rw [this]
    exact Ideal.mul_mem_left _ _ (neg_mem (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)))
  · rw [Ideal.span_singleton_le_iff_mem]
    have h3 : ((l : ℕ) : Per.AinfP l) * beta ϖ ∈ Per.kerP l := by
      rw [hlb]; exact neg_mem (hmem _ h0)
    have h4 : linv l * (((l : ℕ) : Per.AinfP l) * beta ϖ) = beta ϖ := by
      rw [← mul_assoc, mul_comm (linv l), mul_linv, one_mul]
    rw [← h4]
    exact Ideal.mul_mem_left _ _ h3

end GlobalTheory.Pst.StLat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KerPEqSpanBetaStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial GlobalTheory.Pst GlobalTheory.MemLoc GlobalTheory.Pst.StLat GlobalTheory.Pst.NoLog
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kerP_eq_span_beta_of_untilt_eq : ∀ (l : ℕ) [Fact l.Prime] (ϖ : Per.Fl l), ϖ.untilt = ((l : ℕ) : Per.OC l) → Per.kerP l = Ideal.span {beta ϖ} := by
  first | exact @GlobalTheory.Pst.StLat.ker_localizedTheta_eq_span_beta | exact GlobalTheory.Pst.StLat.ker_localizedTheta_eq_span_beta | (intros; apply GlobalTheory.Pst.StLat.ker_localizedTheta_eq_span_beta <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColumnFieldRamificationIdxInEqOne
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColumnFieldRamificationIdxInEqOne
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col NumberField IsDedekindDomain

namespace GlobalTheory.ColumnField

theorem conj_notMem_inertia (D : D7) (X : Fields) (s : Seam D X) (hs : s.Ok) (P : HeightOneSpectrum (𝓞 X.E)) :
    ¬ ∀ x : 𝓞 X.E, X.conjO x - x ∈ P.asIdeal := by
  intro hall
  let φ : 𝓞 X.E ≃+* 𝓞 D.host.E := RingOfIntegers.mapRingEquiv s.iE
  let P' : Ideal (𝓞 D.host.E) := P.asIdeal.comap (φ.symm : 𝓞 D.host.E →+* 𝓞 X.E)
  have hmax : P'.IsMaximal :=
    have := P.isMaximal
    Ideal.comap_isMaximal_of_surjective _ φ.symm.surjective
  obtain ⟨θ, t, h1, h2⟩ := Formalism.BasicNotions.Examples₂.unram_at D.host P' hmax
  have hcoe : ∀ y : 𝓞 X.E, algebraMap (𝓞 D.host.E) D.host.E (φ y) = s.iE (algebraMap (𝓞 X.E) X.E y) := fun _ => rfl
  have e : φ.symm t = X.conjO (φ.symm θ) := by
    apply φ.injective
    apply RingOfIntegers.ext
    rw [RingEquiv.apply_symm_apply]
    change algebraMap (𝓞 D.host.E) D.host.E t = algebraMap (𝓞 D.host.E) D.host.E (φ (X.conjO (φ.symm θ)))
    rw [hcoe, h1]
    change _ = s.iE (star (algebraMap (𝓞 X.E) X.E (φ.symm θ)))
    rw [hs.2, ← hcoe, RingEquiv.apply_symm_apply]
  apply h2
  change φ.symm (θ - t) ∈ P.asIdeal
  rw [map_sub, e, ← neg_sub]
  exact P.asIdeal.neg_mem (hall _)

theorem ramificationIdxIn_eq_one : ∀ (D : D7) (X : Fields) (s : Seam D X), X.Ok → s.Ok →
    ∀ v : HeightOneSpectrum (𝓞 X.F), v.asIdeal.ramificationIdxIn (𝓞 X.E) = 1 := by
  intro D X s hX hs v
  have : Algebra.IsQuadraticExtension X.F X.E := ⟨hX.rankE⟩
  have : IsGalois X.F X.E := inferInstance
  have := v.isMaximal
  obtain ⟨Q, hQ, hlo⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 X.E) v.asIdeal
  have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q
  let P : HeightOneSpectrum (𝓞 X.E) := ⟨Q, hQ.isPrime, hQ0⟩
  have hun := hX.unram_of_inertia (conj_notMem_inertia D X s hs) P
  have hcomap : Q.comap (algebraMap (𝓞 X.F) (𝓞 X.E)) = v.asIdeal := (Ideal.over_def Q v.asIdeal).symm
  have hun' : ¬ v.asIdeal.map (algebraMap (𝓞 X.F) (𝓞 X.E)) ≤ Q ^ 2 := by
    rw [← hcomap]
    exact hun
  have h1 : v.asIdeal.map (algebraMap (𝓞 X.F) (𝓞 X.E)) ≤ Q ^ 1 := by
    rw [pow_one, Ideal.map_le_iff_le_comap, hcomap]
  have he : v.asIdeal.ramificationIdx' Q = 1 := Ideal.ramificationIdx_spec h1 hun'
  have := hQ.isPrime
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx _ Q (X.E ≃ₐ[X.F] X.E),
    ← Ideal.ramificationIdx'_eq_ramificationIdx _ _ v.ne_bot]
  exact he

end GlobalTheory.ColumnField
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColumnFieldRamificationIdxInEqOneStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.columnField_ramificationIdxIn_eq_one : ∀ (D : D7) (X : Fields) (s : Seam D X), X.Ok → s.Ok → ∀ v : HeightOneSpectrum (𝓞 X.F), v.asIdeal.ramificationIdxIn (𝓞 X.E) = 1 := by
  first | exact @GlobalTheory.ColumnField.ramificationIdxIn_eq_one | exact GlobalTheory.ColumnField.ramificationIdxIn_eq_one | (intros; apply GlobalTheory.ColumnField.ramificationIdxIn_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralSubst
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta

namespace GlobalTheory.CurveToStdLog

open MvPowerSeries

variable {l : ℕ} [Fact l.Prime] {κ κ' : Type}

theorem mvsubst_subst {a : κ → MvPowerSeries κ' ℂ_[l]} (ha : HasSubst a) {b : MvPowerSeries κ ℂ_[l]}
    (hb : constantCoeff b = 0) (f : PowerSeries ℂ_[l]) :
    MvPowerSeries.subst a (f.subst b : MvPowerSeries κ ℂ_[l]) = f.subst (MvPowerSeries.subst a b) := by
  rw [PowerSeries.subst_def, subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero hb).const ha]
  rfl

theorem subst_expMv [Finite κ] {a : κ → MvPowerSeries κ' ℂ_[l]} (ha : ∀ i, constantCoeff (a i) = 0)
    {f : MvPowerSeries κ ℂ_[l]} (hf : constantCoeff f = 0) : subst a (expMv f) = expMv (subst a f) := by
  have hs : HasSubst a := hasSubst_of_constantCoeff_zero ha
  rw [GlobalTheory.ExpLogMv.expMv_eq_subst hf, mvsubst_subst hs hf,
    GlobalTheory.ExpLogMv.expMv_eq_subst (constantCoeff_subst_eq_zero hs ha hf)]

theorem expMv_add {f g : MvPowerSeries κ ℂ_[l]} (hf : constantCoeff f = 0) (hg : constantCoeff g = 0) :
    expMv (f + g) = expMv f * expMv g := by
  rw [GlobalTheory.ExpLogMv.expMv_eq_subst hf, GlobalTheory.ExpLogMv.expMv_eq_subst hg,
    GlobalTheory.ExpLogMv.expMv_eq_subst (by simp [hf, hg])]
  exact ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_add hf hg

theorem expMv_zero : expMv (0 : MvPowerSeries κ ℂ_[l]) = 1 := by
  rw [GlobalTheory.ExpLogMv.expMv_eq_subst (by simp)]
  exact ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_zero

theorem expMv_sum {ι : Type*} (s : Finset ι) {f : ι → MvPowerSeries κ ℂ_[l]}
    (hf : ∀ i, constantCoeff (f i) = 0) : expMv (∑ i ∈ s, f i) = ∏ i ∈ s, expMv (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using expMv_zero
  | insert i s hi ih =>
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_insert hi, Finset.prod_insert hi, expMv_add (hf i) (by simp [map_sum, hf]), ih]

theorem cc_ph (g : G1 l) (hE : PowerSeries.constantCoeff (ePhi1 g.lam g.abelian₂ g.C g.wq) = 1) :
    PowerSeries.constantCoeff g.ph = 0 := by
  have h := (GlobalTheory.ExpLogMv.expMv_neg_logMv_mul l Unit _ hE).1
  show constantCoeff (-logMv (ePhi1 g.lam g.abelian₂ g.C g.wq)) = 0
  rw [map_neg, h, neg_zero]

theorem cc_phAt (g : G1 l) (hE : PowerSeries.constantCoeff (ePhi1 g.lam g.abelian₂ g.C g.wq) = 1)
    {y : MvPowerSeries κ ℂ_[l]} (hy : constantCoeff y = 0) : constantCoeff (g.phAt y) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero hy _ (cc_ph g hE)

theorem inv_ePhi1 (g : G1 l) (hE : PowerSeries.constantCoeff (ePhi1 g.lam g.abelian₂ g.C g.wq) = 1)
    {y : MvPowerSeries κ ℂ_[l]} (hy : constantCoeff y = 0) :
    (PowerSeries.subst y (ePhi1 g.lam g.abelian₂ g.C g.wq))⁻¹ = expMv (g.phAt y) := by
  have hs : HasSubst (fun _ : Unit => y) := hasSubst_of_constantCoeff_zero fun _ => hy
  have h := congrArg (subst (fun _ : Unit => y)) (GlobalTheory.ExpLogMv.expMv_neg_logMv_mul l Unit _ hE).2
  rw [subst_mul hs, subst_expMv (f := -logMv (ePhi1 g.lam g.abelian₂ g.C g.wq)) (fun _ => hy) (cc_ph g hE), ← coe_substAlgHom hs (R := ℂ_[l]), map_one,
    coe_substAlgHom] at h
  have h1 : constantCoeff (PowerSeries.subst y (ePhi1 g.lam g.abelian₂ g.C g.wq)) ≠ 0 := by
    rw [ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.constantCoeff_psubst hy, hE]; exact one_ne_zero
  rw [MvPowerSeries.inv_eq_iff_mul_eq_one h1]
  exact h

end GlobalTheory.CurveToStdLog
end
