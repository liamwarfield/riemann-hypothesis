module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjThetaKOMulIntegrableOn

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.LocalEmbeddings.JetsChain
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.DefStep
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsOpenCompactLevel IsDefiniteSpace)
open scoped ComplexOrder Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.JetsOne

variable {D : D7}

theorem finG_finOf (V : HSp D) (g : GA D V) : finG V (finOf V g) = Lev.finE V g := by
  have h : Lev.finE V (infOf V g : GA D V) = 1 := by
    show Formalism.UG.bc (Lev.swapAE D) (finHom V (infOf V g : GA D V)) = 1
    rw [show finHom V (infOf V g : GA D V) = 1 from (infOf V g).2, map_one]
  conv_rhs => rw [← infOf_mul_finOf V g, map_mul, h, one_mul]
  rfl

theorem avg_rat (V : HSp D) (κ : Measure (GinfC V)) [κ.IsMulLeftInvariant] (Φ : GA D V → ℂ)
    (hΦ : ∀ γ ∈ GQ V, ∀ g, Φ (γ * g) = Φ g) {γ : GfC V} (hγ : γ ∈ ratFin V) (x : GfC V) :
    ∫ k, Φ (((γ * x : GfC V) : GA D V) * k) ∂κ = ∫ k, Φ ((x : GA D V) * k) ∂κ := by
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  have hSC := hT.2.1
  have hB := hT.2.2.2.1
  have hG := hT.2.2.2.2.1
  obtain ⟨q, hq, e⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 hγ)
  have e1 : finOf V q = γ := ClassFin.finG_injective V ((finG_finOf V q).trans e)
  have e2 : ((infOf V q : GinfC V) : GA D V) * γ = q := e1 ▸ infOf_mul_finOf V q
  have c1 := GlobalTheory.AdelicSplit.commute_GinfC_GfC V (infOf V q).2 (γ * x).2
  rw [← integral_mul_left_eq_self (fun k : GinfC V => Φ (((γ * x : GfC V) : GA D V) * k)) (infOf V q)]
  refine integral_congr_ae (.of_forall fun k => ?_)
  have e3 : ((γ * x : GfC V) : GA D V) * ((infOf V q * k : GinfC V) : GA D V) = q * ((x : GA D V) * k) := by
    rw [Subgroup.coe_mul (GinfC V), ← mul_assoc, ← c1, Subgroup.coe_mul, ← mul_assoc, e2, mul_assoc]
  dsimp only
  rw [e3, hΦ q hq]

theorem exists_haar (V : HSp D) (hV : IsDefiniteSpace V) : ∃ κ : Measure (GinfC V), κ.IsHaarMeasure ∧ IsProbabilityMeasure κ := by
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  have hSC := hT.2.1
  have hB := hT.2.2.2.1
  have hG := hT.2.2.2.2.1
  haveI : CompactSpace (GinfC V) := isCompact_iff_compactSpace.1 (Eqv.isCompact_GinfC hV.1 hV.2)
  exact ⟨Measure.haarMeasure ⊤, Measure.isHaarMeasure_haarMeasure _, ⟨by
    simpa using Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts (GinfC V)))⟩⟩

theorem exists_fine (V : HSp D) {K : Subgroup (GL (Fin V.rank) (Lev.EAf D))} (hK : IsOpenCompactLevel V K) {p : GA D V → Prop}
    (h : ∀ᶠ k in 𝓝 (1 : GA D V), k ∈ GfC V → p k) :
    ∃ K'' ≤ K, IsOpenCompactLevel V K'' ∧ ∀ k ∈ Lev.levA V K'', p k := by
  have hT := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  have hG := hT.2.2.2.2.1
  obtain ⟨U, hU, hUN⟩ := GlobalTheory.Mem.SmallSub.exists_open_subgroup_finite_subset D V _ h
  have key : ∀ g, Lev.finE V g ∈ (U.comap (GfC V).subtype).map (finG V) ↔ (finOf V g : GA D V) ∈ U := fun g => by
    rw [← finG_finOf, Subgroup.mem_map_iff_mem (ClassFin.finG_injective V)]
    rfl
  have hc : Continuous fun g => (finOf V g : GA D V) :=
    continuous_subtype_val.comp (continuous_snd.comp (GlobalTheory.AdelicSplit.splitEquiv V).symm.continuous)
  have hl : ∀ k, k ∈ Lev.levA V (K ⊓ (U.comap (GfC V).subtype).map (finG V)) ↔ k ∈ Lev.levA V K ∧ k ∈ U := fun k => by
    rw [Lev.mem_levA, Lev.mem_levA, Subgroup.mem_inf, key, and_assoc]
    refine and_congr_right fun hk => ?_
    rw [finOf_fin V ⟨k, hk⟩]
  refine ⟨K ⊓ (U.comap (GfC V).subtype).map (finG V), inf_le_left, ⟨?_, ?_⟩, fun k hk => ?_⟩
  · convert hK.1.inter (hU.preimage hc) using 1
    ext g
    exact and_congr Iff.rfl (key g)
  · convert hK.2.inter_right (U.isClosed_of_isOpen hU) using 1
    ext g
    exact hl g
  · exact hUN k ((hl k).1 hk).2 (Lev.mem_levA.1 hk).1 (Lev.mem_levA.1 hk).1

theorem isFinReal_apply {V : HSp D} {M : Type} [AddCommGroup M] [Module ℂ M] {ρ : GA D V →* Module.End ℂ M}
    (hρ : ∀ g ∈ GfC V, ρ g = 1) {F : GA D V → ℂ} {Λ : Module.Dual ℂ M} {v : GfC V → M} (h : IsFinReal ρ F Λ v)
    (x : GfC V) (k : GinfC V) : F (x * k) = Λ (ρ (k : GA D V)⁻¹ (v x)) := by
  rw [h, finOf_mul_inf, finOf_fin, mul_inv_rev, map_mul, hρ _ (inv_mem x.2), mul_one]

def wgt (V : HSp D) (μ : Measure (GA D V)) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (c : FinCl V K) : ℂ :=
  ((μ (K.comap (Lev.finE V))).toReal : ℂ) * ((gamOrd V K (Quotient.out c) : ℂ))⁻¹

def ext {P : ℕ → Type} [∀ j, One (P j)] (n : ℕ) (x : ∀ j : Fin n, P j) (j : ℕ) : P j := if h : j < n then x ⟨j, h⟩ else 1

theorem finsum_snoc {A : ℕ → Type} {M : Type} [AddCommMonoid M] (n : ℕ) (hA : ∀ j < n + 1, Finite (A j))
    (f : (∀ j : Fin (n + 1), A j) → M) :
    ∑ᶠ c, f c = ∑ᶠ a : A n, ∑ᶠ c : (∀ j : Fin n, A j), f (Fin.snoc (α := fun j : Fin (n + 1) => A j) c a) := by
  letI : ∀ j : Fin (n + 1), Fintype (A j) := fun j => @Fintype.ofFinite _ (hA j j.2)
  letI : ∀ j : Fin n, Fintype (A j) := fun j => @Fintype.ofFinite _ (hA j (by omega))
  letI : Fintype (A n) := @Fintype.ofFinite _ (hA n (by omega))
  simp only [finsum_eq_sum_of_fintype]
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.snocEquiv fun j : Fin (n + 1) => A j) _ _ fun _ => rfl).symm

section Chain

variable {V : ℕ → HSp D} {Mo : ℕ → Type} [∀ n, AddCommGroup (Mo n)] [∀ n, Module ℂ (Mo n)]

noncomputable def ptV (comp : ∀ n, GfC (V n) → GfC (V (n + 1)) → Mo n →ₗ[ℂ] Mo (n + 1)) (v : GfC (V 0) → Mo 0)
    (x : ∀ n, GfC (V n)) : ∀ n, GfC (V n) → Mo n
  | 0 => v
  | n + 1 => fun y => comp n (x n) y (ptV comp v x n (x n))

noncomputable def sumV {A : ℕ → Type} (o : ∀ n, A n → GfC (V n)) (w : ∀ n, A n → ℂ)
    (comp : ∀ n, GfC (V n) → GfC (V (n + 1)) → Mo n →ₗ[ℂ] Mo (n + 1)) (v : GfC (V 0) → Mo 0) : ∀ n, GfC (V n) → Mo n
  | 0 => v
  | n + 1 => fun y => ∑ᶠ c : A n, w n c • comp n (o n c) y (sumV o w comp v n (o n c))

noncomputable def liftC (μ : ∀ n, Measure (GA D (V n))) (fd : ∀ n, Set (GA D (V n)))
    (ker : ∀ n, GA D (V n) → GA D (V (n + 1)) → ℂ) (F : GA D (V 0) → ℂ) : ∀ n, GA D (V n) → ℂ
  | 0 => F
  | n + 1 => fun h => ∫ g in fd n, ker n g h * liftC μ fd ker F n g ∂μ n

def FixAt (ker : ∀ n, GA D (V n) → GA D (V (n + 1)) → ℂ) (F : GA D (V 0) → ℂ) : ∀ n, GA D (V n) → Prop
  | 0 => fun k => ∀ g, F (g * k) = F g
  | n + 1 => fun k => ∀ g h, ker n g (h * k) = ker n g h

variable (comp : ∀ n, GfC (V n) → GfC (V (n + 1)) → Mo n →ₗ[ℂ] Mo (n + 1)) (v : GfC (V 0) → Mo 0)

theorem ptV_congr {x x' : ∀ n, GfC (V n)} : ∀ n, (∀ j < n, x j = x' j) → ptV comp v x n = ptV comp v x' n
  | 0, _ => rfl
  | n + 1, h => by
    funext y
    simp only [ptV]
    rw [ptV_congr n fun j hj => h j (by omega), h n (by omega)]

theorem ptV_eq_chainTo (x : ∀ n, GfC (V n)) :
    ∀ n, ptV comp v x n (x n) = chainTo (V := Mo) (fun j => comp j (x j) (x (j + 1))) n (v (x 0))
  | 0 => rfl
  | n + 1 => by
    simp only [ptV, chainTo, LinearMap.comp_apply]
    rw [ptV_eq_chainTo x n]

theorem sumV_eq {A : ℕ → Type} (o : ∀ n, A n → GfC (V n)) (w : ∀ n, A n → ℂ) :
    ∀ n, (∀ j < n, Finite (A j)) → ∀ y, sumV o w comp v n y =
      ∑ᶠ c : (∀ j : Fin n, A j), (∏ j : Fin n, w j (c j)) • ptV comp v (ext n fun j => o j (c j)) n y
  | 0, _, y => by
    rw [finsum_unique]
    simp [sumV, ptV]
  | n + 1, hA, y => by
    rw [finsum_snoc n hA]
    simp only [sumV]
    refine finsum_congr fun a => ?_
    letI : ∀ j : Fin n, Fintype (A j) := fun j => @Fintype.ofFinite _ (hA j (by omega))
    set_option synthInstance.maxHeartbeats 100000 in
      rw [sumV_eq o w n fun j hj => hA j (by omega), finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    have e1 : ext (P := fun j => GfC (V j)) (n + 1)
        (fun j => o j (Fin.snoc (α := fun j : Fin (n + 1) => A j) c a j)) n = o n a := by
      rw [ext, dite_eq_left (Nat.lt_succ_self n)]
      exact congrArg (o n) (Fin.snoc_last (α := fun j : Fin (n + 1) => A j) a c)
    have e2 : ptV comp v (ext (n + 1) fun j => o j (Fin.snoc (α := fun j : Fin (n + 1) => A j) c a j)) n =
        ptV comp v (ext n fun j => o j (c j)) n := ptV_congr comp v n fun j hj => by
      rw [ext, ext, dite_eq_left (Nat.lt_succ_of_lt hj), dite_eq_left hj]
      exact congrArg (o j) (Fin.snoc_castSucc (α := fun j : Fin (n + 1) => A j) a c ⟨j, hj⟩)
    have e3 : ∏ j : Fin (n + 1), w j (Fin.snoc (α := fun j : Fin (n + 1) => A j) c a j) = w n a * ∏ j : Fin n, w j (c j) := by
      rw [Fin.prod_univ_castSucc, mul_comm]
      refine congrArg₂ _ (congrArg (w n) (Fin.snoc_last (α := fun j : Fin (n + 1) => A j) a c)) ?_
      exact Finset.prod_congr rfl fun j _ => congrArg (w j) (Fin.snoc_castSucc (α := fun j : Fin (n + 1) => A j) a c j)
    simp only [ptV]
    rw [e1, e2, e3, map_smul, smul_smul]

variable (ρ : ∀ n, GA D (V n) →* Module.End ℂ (Mo n)) (ker : ∀ n, GA D (V n) → GA D (V (n + 1)) → ℂ)
  (Λ : ∀ n, Module.Dual ℂ (Mo n))

def ArrowOK (n : ℕ) : Prop :=
  IsDefiniteSpace (V n) ∧ (∀ φ : D.host.E →+* ℂ, ((V n).gram.map φ).PosDef) ∧ (∀ g ∈ GfC (V n), ρ n g = 1) ∧
  (∀ u, Continuous fun k : GinfC (V n) => Λ n (ρ n (k : GA D (V n))⁻¹ u)) ∧
  (∀ γ ∈ GQ (V n), ∀ g h, ker n (γ * g) h = ker n g h) ∧ (∀ γ ∈ GQ (V (n + 1)), ∀ g h, ker n g (γ * h) = ker n g h) ∧
  (∀ z h, Continuous fun k : GinfC (V n) => ker n (z * k) h) ∧
  ∀ κ : Measure (GinfC (V n)), κ.IsHaarMeasure → IsProbabilityMeasure κ → ∀ (x : GfC (V n)) (h : GA D (V (n + 1))) (u : Mo n),
    ∫ k, ker n ((x : GA D (V n)) * (k : GA D (V n))) h * Λ n (ρ n (k : GA D (V n))⁻¹ u) ∂κ =
      Λ (n + 1) (ρ (n + 1) h⁻¹ (comp n x (finOf _ h) u))

def ptF (x : ∀ n, GfC (V n)) (n : ℕ) (h : GA D (V n)) : ℂ := Λ n (ρ n h⁻¹ (ptV comp v x n (finOf _ h)))

theorem ptF_real (x : ∀ n, GfC (V n)) (n : ℕ) : IsFinReal (ρ n) (ptF comp v ρ Λ x n) (Λ n) (ptV comp v x n) := fun _ => rfl

variable {comp v ρ ker Λ}

theorem ptF_succ {n : ℕ} (h : ArrowOK comp ρ ker Λ n) (κ : Measure (GinfC (V n))) (h1 : κ.IsHaarMeasure)
    (h2 : IsProbabilityMeasure κ) (x : ∀ n, GfC (V n)) (g : GA D (V (n + 1))) :
    ptF comp v ρ Λ x (n + 1) g = ∫ k, ker n (x n * k) g * ptF comp v ρ Λ x n (x n * k) ∂κ := by
  simp only [isFinReal_apply h.2.2.1 (ptF_real comp v ρ Λ x n)]
  exact (h.2.2.2.2.2.2.2 κ h1 h2 _ _ _).symm

variable {N : ℕ} (hc : ∀ n < N, ArrowOK comp ρ ker Λ n) {F : GA D (V 0) → ℂ} (hF : IsFinReal (ρ 0) F (Λ 0) v)
  (hFa : ∀ γ ∈ GQ (V 0), ∀ g, F (γ * g) = F g)
include hc hF hFa

theorem ptF_left (x : ∀ n, GfC (V n)) : ∀ n ≤ N, ∀ γ ∈ GQ (V n), ∀ g, ptF comp v ρ Λ x n (γ * g) = ptF comp v ρ Λ x n g
  | 0, _, γ, hγ, g => (hF _).symm.trans ((hFa γ hγ g).trans (hF _))
  | n + 1, hn, γ, hγ, g => by
    have hArrow : ArrowOK comp ρ ker Λ n := hc n (Nat.lt_of_succ_le hn)
    have hDef : IsDefiniteSpace (V n) := hArrow.1
    have hHaar := exists_haar (V n) hDef
    rcases hHaar with ⟨κ, h1, h2⟩
    simp only [ptF_succ hArrow κ h1 h2, hArrow.2.2.2.2.2.1 γ hγ]

theorem ptF_rat {x x' : ∀ n, GfC (V n)} (hx : ∀ j < N, ∃ γ ∈ ratFin (V j), x' j = γ * x j) :
    ∀ n ≤ N, ptF comp v ρ Λ x' n = ptF comp v ρ Λ x n
  | 0, _ => rfl
  | n + 1, hn => by
    have hn' : n < N := Nat.lt_of_succ_le hn
    have hArrow : ArrowOK comp ρ ker Λ n := hc n hn'
    have hDef : IsDefiniteSpace (V n) := hArrow.1
    have hHaar := exists_haar (V n) hDef
    rcases hHaar with ⟨κ, h1, h2⟩
    have hRat : ∃ γ ∈ ratFin (V n), x' n = γ * x n := hx n hn'
    rcases hRat with ⟨γ, hγ, e⟩
    funext g
    rw [ptF_succ hArrow κ h1 h2, ptF_succ hArrow κ h1 h2, ptF_rat hx n (by omega), e]
    exact avg_rat _ κ (fun z => ker n z g * ptF comp v ρ Λ x n z) (fun q hq z => by
      rw [hArrow.2.2.2.2.1 q hq, ptF_left hc hF hFa x n (by omega) q hq]) hγ _


omit hF in
theorem liftC_left (μ : ∀ n, Measure (GA D (V n))) (fd : ∀ n, Set (GA D (V n))) :
    ∀ n ≤ N, ∀ γ ∈ GQ (V n), ∀ g, liftC μ fd ker F n (γ * g) = liftC μ fd ker F n g
  | 0, _, γ, hγ, g => hFa γ hγ g
  | n + 1, hn, γ, hγ, g => by
    simp only [liftC, (hc n (Nat.lt_of_succ_le hn)).2.2.2.2.2.1 γ hγ]

omit hc hF hFa in
theorem liftC_right (μ : ∀ n, Measure (GA D (V n))) (fd : ∀ n, Set (GA D (V n))) :
    ∀ n k, FixAt ker F n k → ∀ g, liftC μ fd ker F n (g * k) = liftC μ fd ker F n g
  | 0, _, hk, g => hk g
  | n + 1, k, hk, g => by
    have hk' : ∀ g h, ker n g (h * k) = ker n g h := hk
    simp only [liftC, hk']

theorem liftC_real (μ : ∀ n, Measure (GA D (V n))) (fd : ∀ n, Set (GA D (V n)))
    (K : ∀ n, Subgroup (GL (Fin (V n).rank) (Lev.EAf D)))
    (hK : ∀ n < N, IsOpenCompactLevel _ (K n) ∧ (∃ K₀, IsOpenCompactLevel _ K₀ ∧ K n ≤ K₀ ∧ IsMeasDef _ K₀ (μ n) (fd n)) ∧
      ∀ k ∈ Lev.levA _ (K n), FixAt ker F n k ∧ ∀ g h, ker n (g * k) h = ker n g h) :
    ∀ n ≤ N, IsFinReal (ρ n) (liftC μ fd ker F n) (Λ n)
      (sumV (A := fun n => FinCl (V n) (K n)) (fun _ c => Quotient.out c) (fun n => wgt (V n) (μ n) (K n)) comp v n)
  | 0, _ => hF
  | n + 1, hn => by
    intro h
    have ih := liftC_real μ fd K hK n (by omega)
    have hn' : n < N := Nat.lt_of_succ_le hn
    have hLevel := hK n hn'
    rcases hLevel with ⟨h1, ⟨K₀, h2, h3, h4⟩, h5⟩
    have hArrow : ArrowOK comp ρ ker Λ n := hc n hn'
    rcases hArrow with ⟨-, a2, a3, a4, a5, -, a7, a8⟩
    have hAvg := GlobalTheory.DefiniteClassReal.integral_eq_finClSum_avg (V n) a2 K₀ (K n) h2 h1 h3 (μ n) (fd n) h4
      (fun g => ker n g h * liftC μ fd ker F n g)
      (fun γ hγ g => by
        rw [a5 γ hγ, liftC_left hc hFa μ fd n (by omega) γ hγ])
      (fun k hk g => by
        rw [(h5 k hk).2, liftC_right μ fd n k (h5 k hk).1])
      (fun z => (a7 z h).mul (by
        have e : ∀ k : GinfC (V n), liftC μ fd ker F n (z * k) = Λ n (ρ n (k : GA D (V n))⁻¹ (ρ n z⁻¹ (sumV
            (A := fun n => FinCl (V n) (K n)) (fun _ c => Quotient.out c) (fun n => wgt (V n) (μ n) (K n)) comp v n
            (finOf _ z)))) := fun k => by
          rw [ih, finOf_mul_inf, mul_inv_rev, map_mul, Module.End.mul_apply]
        simp only [e]
        exact a4 _))
    rcases hAvg with ⟨hfin, κ, hκH, hκP, hU⟩
    haveI := Fintype.ofFinite (FinCl (V n) (K n))
    simp only [liftC, sumV]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hU, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, map_sum, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [isFinReal_apply a3 ih]
    rw [a8 κ hκH hκP, map_smul, map_smul, smul_eq_mul, wgt, div_eq_mul_inv]

end Chain

end GlobalTheory.JetsOne

end
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.DefStep
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsOpenCompactLevel IsDefiniteSpace)
open scoped ComplexOrder Topology

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.JetsOne

variable {D : D7}

section Last

variable {A A' : HSp D} {M M' : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup M'] [Module ℂ M']
  (ρ : GA D A →* Module.End ℂ M) (Λ : Module.Dual ℂ M) (ρ' : GA D A' →* Module.End ℂ M') (Λ' : Module.Dual ℂ M')
  (s : GA D A' →* GA D A) (e : GfC A' → GfC A) (B : M →ₗ[ℂ] M' →ₗ[ℂ] ℂ)

structure LastOK : Prop where

  defn : IsDefiniteSpace A'

  pos : ∀ φ : D.host.E →+* ℂ, (A'.gram.map φ).PosDef

  fin : ∀ g ∈ GfC A, ρ g = 1

  fin' : ∀ g ∈ GfC A', ρ' g = 1

  cont : Continuous s

  rat : ∀ γ ∈ GQ A', s γ ∈ GQ A

  sfin : ∀ z : GfC A', s z = e z

  sinf : ∀ k ∈ GinfC A', s k ∈ GinfC A

  coef : ∀ u u', Continuous fun k : GinfC A' => Λ (ρ (s k)⁻¹ u) * Λ' (ρ' (k : GA D A')⁻¹ u')

  avg : ∀ κ : Measure (GinfC A'), κ.IsHaarMeasure → IsProbabilityMeasure κ → ∀ u u',
    ∫ k, Λ (ρ (s k)⁻¹ u) * Λ' (ρ' (k : GA D A')⁻¹ u') ∂κ = B u u'

variable {ρ Λ ρ' Λ' s e B} (h : LastOK ρ Λ ρ' Λ' s e B) {F : GA D A → ℂ} {F' : GA D A' → ℂ} {v : GfC A → M} {v' : GfC A' → M'}
  (hF : IsFinReal ρ F Λ v) (hF' : IsFinReal ρ' F' Λ' v')
include h hF hF'

theorem last_avg (κ : Measure (GinfC A')) (h1 : κ.IsHaarMeasure) (h2 : IsProbabilityMeasure κ) (z : GfC A') :
    ∫ k, F (s (z * k)) * F' (z * k) ∂κ = B (v (e z)) (v' z) := by
  rw [← h.avg κ h1 h2]
  refine integral_congr_ae (.of_forall fun k => ?_)
  have e1 := isFinReal_apply h.fin hF (e z) ⟨s k, h.sinf _ k.2⟩
  beta_reduce
  rw [map_mul, h.sfin, isFinReal_apply h.fin' hF']
  exact congrArg (· * _) e1

theorem last_int (hFa : ∀ γ ∈ GQ A, ∀ g, F (γ * g) = F g) (hFa' : ∀ γ ∈ GQ A', ∀ g, F' (γ * g) = F' g)
    {K K₀ : Subgroup (GL (Fin A'.rank) (Lev.EAf D))} (hK : IsOpenCompactLevel _ K) (hK₀ : IsOpenCompactLevel _ K₀) (hle : K ≤ K₀)
    {μ : Measure (GA D A')} {fd : Set (GA D A')} (hμ : IsMeasDef _ K₀ μ fd)
    (hr : ∀ k ∈ Lev.levA _ K, (∀ g, F (g * s k) = F g) ∧ ∀ g, F' (g * k) = F' g) :
    ∫ g in fd, F (s g) * F' g ∂μ = ∑ᶠ c : FinCl A' K, wgt A' μ K c * B (v (e (Quotient.out c))) (v' (Quotient.out c)) := by
  obtain ⟨hfin, κ, hκH, hκP, hU⟩ := GlobalTheory.DefiniteClassReal.integral_eq_finClSum_avg A' h.pos K₀ K hK₀ hK hle μ fd hμ
    (fun g => F (s g) * F' g)
    (fun γ hγ g => by rw [map_mul, hFa _ (h.rat γ hγ), hFa' γ hγ])
    (fun k hk g => by rw [map_mul, (hr k hk).1, (hr k hk).2])
    (fun z => by
      have e1 : ∀ k : GinfC A', F (s (z * k)) = Λ (ρ (s k)⁻¹ (ρ (s z)⁻¹ (v (finOf _ (s z))))) := fun k => by
        rw [hF, map_mul, finOf_mul_inf _ _ ⟨s k, h.sinf _ k.2⟩, mul_inv_rev, map_mul, Module.End.mul_apply]
      have e2 : ∀ k : GinfC A', F' (z * k) = Λ' (ρ' (k : GA D A')⁻¹ (ρ' z⁻¹ (v' (finOf _ z)))) := fun k => by
        rw [hF', finOf_mul_inf, mul_inv_rev, map_mul, Module.End.mul_apply]
      simp only [e1, e2]
      exact h.coef _ _)
  rw [hU]
  refine finsum_congr fun c => ?_
  rw [last_avg h hF hF' κ hκH hκP, wgt, div_eq_mul_inv]

end Last

section Sums

variable {V : ℕ → HSp D} {Mo : ℕ → Type} [∀ n, AddCommGroup (Mo n)] [∀ n, Module ℂ (Mo n)]
  (comp : ∀ n, GfC (V n) → GfC (V (n + 1)) → Mo n →ₗ[ℂ] Mo (n + 1)) (v : GfC (V 0) → Mo 0)

theorem ext_lt {P : ℕ → Type} [∀ j, One (P j)] {n : ℕ} (x : ∀ j : Fin n, P j) {j : ℕ} (h : j < n) : ext n x j = x ⟨j, h⟩ :=
  dif_pos h

theorem ext_update {P : ℕ → Type} [∀ j, One (P j)] {n : ℕ} (x : ∀ j : Fin n, P j) (j : Fin n) (z : P j) :
    ext n (Function.update (β := fun j : Fin n => P j) x j z) = Function.update (β := P) (ext n x) (j : ℕ) z := by
  funext i
  by_cases hi : i = j
  · subst hi
    rw [ext_lt _ j.2, Function.update_self]
    exact (Function.update_self (β := P) (j : ℕ) z _).symm
  · rw [Function.update_of_ne hi]
    unfold ext
    split_ifs with h
    · exact Function.update_of_ne (fun e => hi (congrArg Fin.val e)) _ _
    · rfl

theorem sum_last {A : ℕ → Type} (o : ∀ n, A n → GfC (V n)) (w : ∀ n, A n → ℂ) (n : ℕ) (hA : ∀ j < n + 1, Finite (A j))
    (ℓ : GfC (V n) → Mo n →ₗ[ℂ] ℂ) :
    ∑ᶠ a : A n, w n a * ℓ (o n a) (sumV o w comp v n (o n a)) =
      ∑ᶠ c : (∀ j : Fin (n + 1), A j), (∏ j : Fin (n + 1), w j (c j)) *
        ℓ (ext (P := fun j => GfC (V j)) (n + 1) (fun j => o j (c j)) n)
          (ptV comp v (ext (n + 1) fun j => o j (c j)) n (ext (P := fun j => GfC (V j)) (n + 1) (fun j => o j (c j)) n)) := by
  rw [finsum_snoc n hA]
  refine finsum_congr fun a => ?_
  letI : ∀ j : Fin n, Fintype (A j) := fun j => @Fintype.ofFinite _ (hA j (by omega))
  set_option synthInstance.maxHeartbeats 100000 in
    rw [sumV_eq comp v o w n fun j hj => hA j (by omega), finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  have e1 : ext (P := fun j => GfC (V j)) (n + 1)
      (fun j => o j (Fin.snoc (α := fun j : Fin (n + 1) => A j) c a j)) n = o n a := by
    rw [ext, dif_pos (Nat.lt_succ_self n)]
    exact congrArg (o n) (Fin.snoc_last (α := fun j : Fin (n + 1) => A j) a c)
  have e2 : ptV comp v (ext (n + 1) fun j => o j (Fin.snoc (α := fun j : Fin (n + 1) => A j) c a j)) n =
      ptV comp v (ext n fun j => o j (c j)) n := ptV_congr comp v n fun j hj => by
    rw [ext, ext, dif_pos (Nat.lt_succ_of_lt hj), dif_pos hj]
    exact congrArg (o j) (Fin.snoc_castSucc (α := fun j : Fin (n + 1) => A j) a c ⟨j, hj⟩)
  have e3 : ∏ j : Fin (n + 1), w j (Fin.snoc (α := fun j : Fin (n + 1) => A j) c a j) = w n a * ∏ j : Fin n, w j (c j) := by
    rw [Fin.prod_univ_castSucc, mul_comm]
    refine congrArg₂ _ (congrArg (w n) (Fin.snoc_last (α := fun j : Fin (n + 1) => A j) a c)) ?_
    exact Finset.prod_congr rfl fun j _ => congrArg (w j) (Fin.snoc_castSucc (α := fun j : Fin (n + 1) => A j) a c j)
  rw [e1, e2, e3, map_smul, smul_eq_mul, mul_assoc]

end Sums

section Glue

variable {V V' : ℕ → HSp D} {Mo Mo' : ℕ → Type} [∀ n, AddCommGroup (Mo n)] [∀ n, Module ℂ (Mo n)]
  [∀ n, AddCommGroup (Mo' n)] [∀ n, Module ℂ (Mo' n)]

def pairP (comp : ∀ n, GfC (V n) → GfC (V (n + 1)) → Mo n →ₗ[ℂ] Mo (n + 1)) (v : GfC (V 0) → Mo 0)
    (comp' : ∀ n, GfC (V' n) → GfC (V' (n + 1)) → Mo' n →ₗ[ℂ] Mo' (n + 1)) (v' : GfC (V' 0) → Mo' 0) (N : ℕ)
    (B : Mo N →ₗ[ℂ] Mo' N →ₗ[ℂ] ℂ) (X : ∀ n, GfC (V n)) (Y : ∀ n, GfC (V' n)) : ℂ :=
  B (ptV comp v X N (X N)) (ptV comp' v' Y N (Y N))

def ptX (N : ℕ) (e : GfC (V' N) → GfC (V N)) (x : ∀ j : Fin N, GfC (V j)) (y : ∀ i : Fin (N + 1), GfC (V' i)) : ∀ j, GfC (V j) :=
  Function.update (ext (P := fun j => GfC (V j)) N x) N (e (ext (P := fun j => GfC (V' j)) (N + 1) y N))

variable {comp : ∀ n, GfC (V n) → GfC (V (n + 1)) → Mo n →ₗ[ℂ] Mo (n + 1)} {v : GfC (V 0) → Mo 0}
  {comp' : ∀ n, GfC (V' n) → GfC (V' (n + 1)) → Mo' n →ₗ[ℂ] Mo' (n + 1)} {v' : GfC (V' 0) → Mo' 0}
  {ρ : ∀ n, GA D (V n) →* Module.End ℂ (Mo n)} {ker : ∀ n, GA D (V n) → GA D (V (n + 1)) → ℂ} {Λ : ∀ n, Module.Dual ℂ (Mo n)}
  {ρ' : ∀ n, GA D (V' n) →* Module.End ℂ (Mo' n)} {ker' : ∀ n, GA D (V' n) → GA D (V' (n + 1)) → ℂ}
  {Λ' : ∀ n, Module.Dual ℂ (Mo' n)} {N : ℕ} {s : GA D (V' N) →* GA D (V N)} {e : GfC (V' N) → GfC (V N)}
  {B : Mo N →ₗ[ℂ] Mo' N →ₗ[ℂ] ℂ}
  (hc : ∀ n < N, ArrowOK comp ρ ker Λ n) {F : GA D (V 0) → ℂ} (hF : IsFinReal (ρ 0) F (Λ 0) v)
  (hFa : ∀ γ ∈ GQ (V 0), ∀ g, F (γ * g) = F g)
  (hc' : ∀ n < N, ArrowOK comp' ρ' ker' Λ' n) {F' : GA D (V' 0) → ℂ} (hF' : IsFinReal (ρ' 0) F' (Λ' 0) v')
  (hFa' : ∀ γ ∈ GQ (V' 0), ∀ g, F' (γ * g) = F' g)
  (h : LastOK (ρ N) (Λ N) (ρ' N) (Λ' N) s e B)
include hc hF hFa hc' hF' hFa' h

theorem pairP_rat {X X' : ∀ n, GfC (V n)} {Y Y' : ∀ n, GfC (V' n)} (hX : ∀ j < N, ∃ γ ∈ ratFin (V j), X' j = γ * X j)
    (hY : ∀ j ≤ N, ∃ γ ∈ ratFin (V' j), Y' j = γ * Y j) (h1 : X N = e (Y N)) (h2 : X' N = e (Y' N)) :
    pairP comp v comp' v' N B X' Y' = pairP comp v comp' v' N B X Y := by
  have left : ∀ n ≤ N, ∀ γ ∈ GQ (V n), ∀ g, ptF comp v ρ Λ X n (γ * g) = ptF comp v ρ Λ X n g := by
    intro n hn
    cases n with
    | zero => exact fun γ hγ g => (hF _).symm.trans ((hFa γ hγ g).trans (hF _))
    | succ n =>
      intro γ hγ g
      have hArrow : ArrowOK comp ρ ker Λ n := hc n (by omega)
      obtain ⟨κ, h1, h2⟩ := exists_haar (V n) hArrow.1
      simp only [ptF_succ hArrow κ h1 h2, hArrow.2.2.2.2.2.1 γ hγ]
  have leftp : ∀ n ≤ N, ∀ γ ∈ GQ (V' n), ∀ g, ptF comp' v' ρ' Λ' Y n (γ * g) = ptF comp' v' ρ' Λ' Y n g := by
    intro n hn
    cases n with
    | zero => exact fun γ hγ g => (hF' _).symm.trans ((hFa' γ hγ g).trans (hF' _))
    | succ n =>
      intro γ hγ g
      have hArrow : ArrowOK comp' ρ' ker' Λ' n := hc' n (by omega)
      obtain ⟨κ, h1, h2⟩ := exists_haar (V' n) hArrow.1
      simp only [ptF_succ hArrow κ h1 h2, hArrow.2.2.2.2.2.1 γ hγ]
  have rat : ∀ n ≤ N, ptF comp v ρ Λ X' n = ptF comp v ρ Λ X n := by
    intro n hn
    induction n with
    | zero => rfl
    | succ n ih =>
      have hArrow : ArrowOK comp ρ ker Λ n := hc n (by omega)
      obtain ⟨κ, h1, h2⟩ := exists_haar (V n) hArrow.1
      obtain ⟨γ, hγ, e⟩ := hX n (by omega)
      funext g
      rw [ptF_succ hArrow κ h1 h2, ptF_succ hArrow κ h1 h2, ih (by omega), e]
      exact avg_rat _ κ (fun z => ker n z g * ptF comp v ρ Λ X n z) (fun q hq z => by
        rw [hArrow.2.2.2.2.1 q hq, left n (by omega) q hq]) hγ _
  have ratp : ∀ n ≤ N, ptF comp' v' ρ' Λ' Y' n = ptF comp' v' ρ' Λ' Y n := by
    intro n hn
    induction n with
    | zero => rfl
    | succ n ih =>
      have hArrow : ArrowOK comp' ρ' ker' Λ' n := hc' n (by omega)
      obtain ⟨κ, h1, h2⟩ := exists_haar (V' n) hArrow.1
      obtain ⟨γ, hγ, e⟩ := hY n (by omega)
      funext g
      rw [ptF_succ hArrow κ h1 h2, ptF_succ hArrow κ h1 h2, ih (by omega), e]
      exact avg_rat _ κ (fun z => ker' n z g * ptF comp' v' ρ' Λ' Y n z) (fun q hq z => by
        rw [hArrow.2.2.2.2.1 q hq, leftp n (by omega) q hq]) hγ _
  obtain ⟨κ, k1, k2⟩ := exists_haar _ h.defn
  obtain ⟨γ, hγ, e3⟩ := hY N le_rfl
  rw [pairP, pairP, h1, h2, ← last_avg h (ptF_real comp v ρ Λ X' N) (ptF_real comp' v' ρ' Λ' Y' N) κ k1 k2,
    ← last_avg h (ptF_real comp v ρ Λ X N) (ptF_real comp' v' ρ' Λ' Y N) κ k1 k2, rat N le_rfl,
    ratp N le_rfl, e3]
  exact avg_rat _ κ (fun z => ptF comp v ρ Λ X N (s z) * ptF comp' v' ρ' Λ' Y N z) (fun q hq z => by
    rw [map_mul, left N le_rfl _ (h.rat q hq), leftp N le_rfl q hq]) hγ _

theorem one_term (μ : ∀ n, Measure (GA D (V n))) (fd : ∀ n, Set (GA D (V n)))
    (K : ∀ n, Subgroup (GL (Fin (V n).rank) (Lev.EAf D)))
    (hK : ∀ n < N, IsOpenCompactLevel _ (K n) ∧ (∃ K₀, IsOpenCompactLevel _ K₀ ∧ K n ≤ K₀ ∧ IsMeasDef _ K₀ (μ n) (fd n)) ∧
      ∀ k ∈ Lev.levA _ (K n), FixAt ker F n k ∧ ∀ g h, ker n (g * k) h = ker n g h)
    (μ' : ∀ n, Measure (GA D (V' n))) (fd' : ∀ n, Set (GA D (V' n)))
    (K' : ∀ n, Subgroup (GL (Fin (V' n).rank) (Lev.EAf D)))
    (hK' : ∀ n < N, IsOpenCompactLevel _ (K' n) ∧ (∃ K₀, IsOpenCompactLevel _ K₀ ∧ K' n ≤ K₀ ∧ IsMeasDef _ K₀ (μ' n) (fd' n)) ∧
      ∀ k ∈ Lev.levA _ (K' n), FixAt ker' F' n k ∧ ∀ g h, ker' n (g * k) h = ker' n g h)
    (hN : IsOpenCompactLevel _ (K' N) ∧ (∃ K₀, IsOpenCompactLevel _ K₀ ∧ K' N ≤ K₀ ∧ IsMeasDef _ K₀ (μ' N) (fd' N)) ∧
      ∀ k ∈ Lev.levA _ (K' N), FixAt ker F N (s k) ∧ FixAt ker' F' N k) :
    ∫ g in fd' N, liftC μ fd ker F N (s g) * liftC μ' fd' ker' F' N g ∂μ' N =
      ∑ᶠ c : (∀ j : Fin N, FinCl (V j) (K j)) × (∀ i : Fin (N + 1), FinCl (V' i) (K' i)),
        ((∏ j : Fin N, wgt (V j) (μ j) (K j) (c.1 j)) * ∏ i : Fin (N + 1), wgt (V' i) (μ' i) (K' i) (c.2 i)) *
          pairP comp v comp' v' N B (ptX N e (fun j => Quotient.out (c.1 j)) (fun i => Quotient.out (c.2 i)))
            (ext (P := fun j => GfC (V' j)) (N + 1) fun i => Quotient.out (c.2 i)) := by
  have real : ∀ n ≤ N, IsFinReal (ρ n) (liftC μ fd ker F n) (Λ n)
      (sumV (A := fun n => FinCl (V n) (K n)) (fun _ c => Quotient.out c)
        (fun n => wgt (V n) (μ n) (K n)) comp v n) := by
    intro n hn
    induction n with
    | zero => exact hF
    | succ n ih =>
      intro h
      have ih := ih (by omega)
      have hn' : n < N := Nat.lt_of_succ_le hn
      obtain ⟨h1, ⟨K₀, h2, h3, h4⟩, h5⟩ := hK n hn'
      obtain ⟨-, a2, a3, a4, a5, -, a7, a8⟩ := hc n hn'
      obtain ⟨hfin, κ, hκH, hκP, hU⟩ := GlobalTheory.DefiniteClassReal.integral_eq_finClSum_avg (V n) a2 K₀ (K n) h2 h1 h3 (μ n) (fd n) h4
        (fun g => ker n g h * liftC μ fd ker F n g)
        (fun γ hγ g => by
          rw [a5 γ hγ, liftC_left hc hFa μ fd n (by omega) γ hγ])
        (fun k hk g => by
          rw [(h5 k hk).2, liftC_right μ fd n k (h5 k hk).1])
        (fun z => (a7 z h).mul (by
          have e : ∀ k : GinfC (V n), liftC μ fd ker F n (z * k) = Λ n (ρ n (k : GA D (V n))⁻¹ (ρ n z⁻¹ (sumV
              (A := fun n => FinCl (V n) (K n)) (fun _ c => Quotient.out c) (fun n => wgt (V n) (μ n) (K n)) comp v n
              (finOf _ z)))) := fun k => by
            rw [ih, finOf_mul_inf, mul_inv_rev, map_mul, Module.End.mul_apply]
          simp only [e]
          exact a4 _))
      haveI := Fintype.ofFinite (FinCl (V n) (K n))
      simp only [liftC, sumV]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hU, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, map_sum, map_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp only [isFinReal_apply a3 ih]
      rw [a8 κ hκH hκP, map_smul, map_smul, smul_eq_mul, wgt, div_eq_mul_inv]
  have real' : ∀ n ≤ N, IsFinReal (ρ' n) (liftC μ' fd' ker' F' n) (Λ' n)
      (sumV (A := fun n => FinCl (V' n) (K' n)) (fun _ c => Quotient.out c)
        (fun n => wgt (V' n) (μ' n) (K' n)) comp' v' n) := by
    intro n hn
    induction n with
    | zero => exact hF'
    | succ n ih =>
      intro h
      have ih := ih (by omega)
      have hn' : n < N := Nat.lt_of_succ_le hn
      obtain ⟨h1, ⟨K₀, h2, h3, h4⟩, h5⟩ := hK' n hn'
      obtain ⟨-, a2, a3, a4, a5, -, a7, a8⟩ := hc' n hn'
      obtain ⟨hfin, κ, hκH, hκP, hU⟩ := GlobalTheory.DefiniteClassReal.integral_eq_finClSum_avg (V' n) a2 K₀ (K' n) h2 h1 h3 (μ' n) (fd' n) h4
        (fun g => ker' n g h * liftC μ' fd' ker' F' n g)
        (fun γ hγ g => by
          rw [a5 γ hγ, liftC_left hc' hFa' μ' fd' n (by omega) γ hγ])
        (fun k hk g => by
          rw [(h5 k hk).2, liftC_right μ' fd' n k (h5 k hk).1])
        (fun z => (a7 z h).mul (by
          have e : ∀ k : GinfC (V' n), liftC μ' fd' ker' F' n (z * k) = Λ' n (ρ' n (k : GA D (V' n))⁻¹ (ρ' n z⁻¹ (sumV
              (A := fun n => FinCl (V' n) (K' n)) (fun _ c => Quotient.out c) (fun n => wgt (V' n) (μ' n) (K' n)) comp' v' n
              (finOf _ z)))) := fun k => by
            rw [ih, finOf_mul_inf, mul_inv_rev, map_mul, Module.End.mul_apply]
          simp only [e]
          exact a4 _))
      haveI := Fintype.ofFinite (FinCl (V' n) (K' n))
      simp only [liftC, sumV]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hU, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, map_sum, map_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp only [isFinReal_apply a3 ih]
      rw [a8 κ hκH hκP, map_smul, map_smul, smul_eq_mul, wgt, div_eq_mul_inv]
  obtain ⟨n1, ⟨K₀, n2, n3, n4⟩, n5⟩ := hN
  have fA : ∀ j < N, Finite (FinCl (V j) (K j)) := fun j hj =>
    (ClassFin.finite_finCl_and_gamOrd _ _ (hc j hj).2.1 (hK j hj).1).1
  have fA' : ∀ j < N + 1, Finite (FinCl (V' j) (K' j)) := fun j hj => by
    rcases (Nat.lt_succ_iff.1 hj).eq_or_lt with rfl | hj
    · exact (ClassFin.finite_finCl_and_gamOrd _ _ h.pos n1).1
    · exact (ClassFin.finite_finCl_and_gamOrd _ _ (hc' j hj).2.1 (hK' j hj).1).1
  rw [last_int h (real N le_rfl) (real' N le_rfl)
    (liftC_left hc hFa μ fd N le_rfl) (liftC_left hc' hFa' μ' fd' N le_rfl) n1 n2 n3 n4
    (fun k hk => ⟨liftC_right μ fd N _ (n5 k hk).1, liftC_right μ' fd' N _ (n5 k hk).2⟩)]
  refine (sum_last comp' v' (A := fun n => FinCl (V' n) (K' n)) (fun _ c => Quotient.out c) (fun n => wgt (V' n) (μ' n) (K' n)) N fA'
    (fun z => B (sumV (A := fun n => FinCl (V n) (K n)) (fun _ c => Quotient.out c) (fun n => wgt (V n) (μ n) (K n))
      comp v N (e z)))).trans ?_
  letI : ∀ j : Fin N, Fintype (FinCl (V j) (K j)) := fun j => @Fintype.ofFinite _ (fA j j.2)
  letI : ∀ j : Fin (N + 1), Fintype (FinCl (V' j) (K' j)) := fun j => @Fintype.ofFinite _ (fA' j j.2)
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun b _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [sumV_eq comp v _ _ N fA, finsum_eq_sum_of_fintype, map_sum, LinearMap.sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have e1 : ptV comp v (ptX N e (fun j => Quotient.out (a j)) (fun i => Quotient.out (b i))) N =
      ptV comp v (ext N fun j => Quotient.out (a j)) N := ptV_congr comp v N fun j hj => Function.update_of_ne hj.ne _ _
  have e2 : ptX N e (fun j => Quotient.out (a j)) (fun i => Quotient.out (b i)) N =
      e (ext (P := fun j => GfC (V' j)) (N + 1) (fun i => Quotient.out (b i)) N) := Function.update_self ..
  rw [pairP, e1, e2, map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

end Glue

section Total

variable {V V' : ℕ → HSp D} {Mo Mo' : ℕ → Type} [∀ n, AddCommGroup (Mo n)] [∀ n, Module ℂ (Mo n)]
  [∀ n, AddCommGroup (Mo' n)] [∀ n, Module ℂ (Mo' n)]

def NearOK (ker : ∀ n, GA D (V n) → GA D (V (n + 1)) → ℂ) (F : GA D (V 0) → ℂ) (N : ℕ) : Prop :=
  (∀ᶠ k in 𝓝 (1 : GA D (V 0)), k ∈ GfC (V 0) → ∀ g, F (g * k) = F g) ∧
  ∀ n < N, (∀ᶠ k in 𝓝 (1 : GA D (V n)), k ∈ GfC (V n) → ∀ g h, ker n (g * k) h = ker n g h) ∧
    ∀ᶠ k in 𝓝 (1 : GA D (V (n + 1))), k ∈ GfC (V (n + 1)) → ∀ g h, ker n g (h * k) = ker n g h

theorem NearOK.fixAt {ker : ∀ n, GA D (V n) → GA D (V (n + 1)) → ℂ} {F : GA D (V 0) → ℂ} {N : ℕ} (h : NearOK ker F N) :
    ∀ n ≤ N, ∀ᶠ k in 𝓝 (1 : GA D (V n)), k ∈ GfC (V n) → FixAt ker F n k
  | 0, _ => h.1
  | n + 1, hn => (h.2 n hn).2

theorem exists_fine_chain {ι : Type} (S : Finset ι) {ker : ι → ∀ n, GA D (V n) → GA D (V (n + 1)) → ℂ} {F : GA D (V 0) → ℂ} {N : ℕ}
    (h : ∀ d ∈ S, NearOK (ker d) F N) {n : ℕ} (hn : n < N) {K : Subgroup (GL (Fin (V n).rank) (Lev.EAf D))}
    (hK : IsOpenCompactLevel _ K) : ∃ K'' ≤ K, IsOpenCompactLevel _ K'' ∧ ∀ k ∈ Lev.levA _ K'', ∀ d ∈ S,
      FixAt (ker d) F n k ∧ ∀ g h, ker d n (g * k) h = ker d n g h := by
  refine exists_fine _ hK ?_
  have := (Filter.eventually_all_finset S).2 fun d hd => ((h d hd).fixAt n hn.le).and ((h d hd).2 n hn).1
  exact this.mono fun k hk hf d hd => ⟨(hk d hd).1 hf, (hk d hd).2 hf⟩

variable {ι : Type} (τ : ι →₀ ℂ)
  {comp : ι → ∀ n, GfC (V n) → GfC (V (n + 1)) → Mo n →ₗ[ℂ] Mo (n + 1)} {v : GfC (V 0) → Mo 0}
  {comp' : ι → ∀ n, GfC (V' n) → GfC (V' (n + 1)) → Mo' n →ₗ[ℂ] Mo' (n + 1)} {v' : GfC (V' 0) → Mo' 0}
  {ρ : ∀ n, GA D (V n) →* Module.End ℂ (Mo n)} {ker : ι → ∀ n, GA D (V n) → GA D (V (n + 1)) → ℂ} {Λ : ∀ n, Module.Dual ℂ (Mo n)}
  {ρ' : ∀ n, GA D (V' n) →* Module.End ℂ (Mo' n)} {ker' : ι → ∀ n, GA D (V' n) → GA D (V' (n + 1)) → ℂ}
  {Λ' : ∀ n, Module.Dual ℂ (Mo' n)} {N : ℕ} {s : GA D (V' N) →* GA D (V N)} {e : GfC (V' N) → GfC (V N)}
  {B : Mo N →ₗ[ℂ] Mo' N →ₗ[ℂ] ℂ} {F : GA D (V 0) → ℂ} {F' : GA D (V' 0) → ℂ}

theorem glue (hc : ∀ d ∈ τ.support, ∀ n < N, ArrowOK (comp d) ρ (ker d) Λ n) (hF : IsFinReal (ρ 0) F (Λ 0) v)
    (hFa : ∀ γ ∈ GQ (V 0), ∀ g, F (γ * g) = F g) (hn : ∀ d ∈ τ.support, NearOK (ker d) F N)
    (hc' : ∀ d ∈ τ.support, ∀ n < N, ArrowOK (comp' d) ρ' (ker' d) Λ' n) (hF' : IsFinReal (ρ' 0) F' (Λ' 0) v')
    (hFa' : ∀ γ ∈ GQ (V' 0), ∀ g, F' (γ * g) = F' g) (hn' : ∀ d ∈ τ.support, NearOK (ker' d) F' N)
    (h : LastOK (ρ N) (Λ N) (ρ' N) (Λ' N) s e B)
    (hV : ∀ n < N, ∀ φ : D.host.E →+* ℂ, ((V n).gram.map φ).PosDef)
    (hV' : ∀ n ≤ N, ∀ φ : D.host.E →+* ℂ, ((V' n).gram.map φ).PosDef)
    (μ : ∀ n, Measure (GA D (V n))) (fd : ∀ n, Set (GA D (V n))) (K : ∀ n, n < N → Subgroup (GL (Fin (V n).rank) (Lev.EAf D)))
    (hK : ∀ n hn, IsOpenCompactLevel _ (K n hn) ∧ IsMeasDef _ (K n hn) (μ n) (fd n))
    (μ' : ∀ n, Measure (GA D (V' n))) (fd' : ∀ n, Set (GA D (V' n))) (K' : ∀ n, n ≤ N → Subgroup (GL (Fin (V' n).rank) (Lev.EAf D)))
    (hK' : ∀ n hn, IsOpenCompactLevel _ (K' n hn) ∧ IsMeasDef _ (K' n hn) (μ' n) (fd' n))
    (P : (∀ n, GfC (V n)) → (∀ n, GfC (V' n)) → ℂ)
    (hP : ∀ X Y, P X Y = τ.sum fun d a => a * pairP (comp d) v (comp' d) v' N B X Y)
    (r1 : ∀ X Y j (hj : j < N) k, finG (V j) k ∈ K j hj → P (Function.update X j (X j * k)) Y = P X Y)
    (r2 : ∀ X Y i (hi : i < N) k, finG (V' i) k ∈ K' i hi.le → P X (Function.update Y i (Y i * k)) = P X Y)
    (r3 : ∀ X Y k, X N = e (Y N) → finG (V' N) k ∈ K' N le_rfl →
      P (Function.update X N (e (Y N * k))) (Function.update Y N (Y N * k)) = P X Y) :
    (τ.sum fun d a => a * ∫ g in fd' N, liftC μ fd (ker d) F N (s g) * liftC μ' fd' (ker' d) F' N g ∂μ' N) =
      ∑ᶠ c : (∀ j : Fin N, FinCl (V j) (K j j.2)) × (∀ i : Fin (N + 1), FinCl (V' i) (K' i (Nat.le_of_lt_succ i.2))),
        ((∏ j : Fin N, ((gamOrd (V j) (K j j.2) (Quotient.out (c.1 j)) : ℂ))⁻¹) *
          ∏ i : Fin (N + 1), ((gamOrd (V' i) (K' i (Nat.le_of_lt_succ i.2)) (Quotient.out (c.2 i)) : ℂ))⁻¹) *
          P (ptX N e (fun j => Quotient.out (c.1 j)) (fun i => Quotient.out (c.2 i)))
            (ext (P := fun j => GfC (V' j)) (N + 1) fun i => Quotient.out (c.2 i)) := by
  have hG := (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (V N)).2.2.2.2.1
  have hG' := (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (V' N)).2.2.2.2.1
  have x1 : ∀ n, ∃ K'' : Subgroup (GL (Fin (V n).rank) (Lev.EAf D)), ∀ hn : n < N, K'' ≤ K n hn ∧ IsOpenCompactLevel _ K'' ∧
      ∀ k ∈ Lev.levA _ K'', ∀ d ∈ τ.support, FixAt (ker d) F n k ∧ ∀ g h, ker d n (g * k) h = ker d n g h := fun n => by
    by_cases h0 : n < N
    · obtain ⟨K'', a⟩ := exists_fine_chain τ.support hn h0 (hK n h0).1
      exact ⟨K'', fun _ => a⟩
    · exact ⟨⊤, fun h1 => absurd h1 h0⟩
  have x2 : ∀ n, ∃ K'' : Subgroup (GL (Fin (V' n).rank) (Lev.EAf D)), ∀ hn : n ≤ N, K'' ≤ K' n hn ∧ IsOpenCompactLevel _ K'' ∧
      (n < N → ∀ k ∈ Lev.levA _ K'', ∀ d ∈ τ.support, FixAt (ker' d) F' n k ∧ ∀ g h, ker' d n (g * k) h = ker' d n g h) ∧
      ∀ hN : n = N, ∀ k ∈ Lev.levA _ K'', ∀ d ∈ τ.support, FixAt (ker d) F N (s (hN ▸ k)) ∧ FixAt (ker' d) F' n k := fun n => by
    rcases lt_trichotomy n N with h0 | rfl | h0
    · obtain ⟨K'', a, b, c⟩ := exists_fine_chain τ.support hn' h0 (hK' n h0.le).1
      exact ⟨K'', fun _ => ⟨a, b, fun _ => c, fun e => absurd e h0.ne⟩⟩
    · have t : Filter.Tendsto s (𝓝 1) (𝓝 1) := by simpa using h.cont.tendsto 1
      have := (Filter.eventually_all_finset τ.support).2 fun d hd =>
        (t.eventually ((hn d hd).fixAt n le_rfl)).and ((hn' d hd).fixAt n le_rfl)
      obtain ⟨K'', a, b, c⟩ := exists_fine _ (hK' n le_rfl).1
        (p := fun k => ∀ d ∈ τ.support, FixAt (ker d) F n (s k) ∧ FixAt (ker' d) F' n k)
        (this.mono fun k hk hf d hd => ⟨(hk d hd).1 (by rw [h.sfin ⟨k, hf⟩]; exact (e _).2), (hk d hd).2 hf⟩)
      exact ⟨K'', fun _ => ⟨a, b, fun e => absurd e (lt_irrefl _), fun _ => c⟩⟩
    · exact ⟨⊤, fun h1 => absurd h0 (not_lt.2 h1)⟩
  choose J hJ using x1
  choose J' hJ' using x2
  have hrat : ∀ {X X' : ∀ n, GfC (V n)} {Y Y' : ∀ n, GfC (V' n)}, (∀ j < N, ∃ γ ∈ ratFin (V j), X' j = γ * X j) →
      (∀ j ≤ N, ∃ γ ∈ ratFin (V' j), Y' j = γ * Y j) → X N = e (Y N) → X' N = e (Y' N) → P X' Y' = P X Y :=
    fun a1 a2 a3 a4 => by
      rw [hP, hP]
      exact Finsupp.sum_congr fun d hd => by rw [pairP_rat (hc d hd) hF hFa (hc' d hd) hF' hFa' h a1 a2 a3 a4]
  have up : ∀ {W : ℕ → HSp D} (X : ∀ n, GfC (W n)) (j : ℕ) (γ : GfC (W j)), γ ∈ ratFin (W j) → ∀ (z : GfC (W j)) (i : ℕ),
      ∃ γ' ∈ ratFin (W i), Function.update X j (γ * z) i = γ' * Function.update X j z i := fun X j γ hγ z i => by
    by_cases hi : i = j
    · subst hi
      exact ⟨γ, hγ, by simp⟩
    · exact ⟨1, one_mem _, by simp [Function.update_of_ne hi]⟩
  have pN : ∀ x y, ptX (V := V) (V' := V') N e x y N = e (ext (P := fun j => GfC (V' j)) (N + 1) y N) := fun x y =>
    Function.update_self ..
  have pU : ∀ x y (j : Fin N) z, ptX (V := V) (V' := V') N e (Function.update (β := fun j : Fin N => GfC (V j)) x j z) y =
      Function.update (β := fun j => GfC (V j)) (ptX N e x y) (j : ℕ) z := fun x y j z => by
    rw [ptX, ptX, ext_update (P := fun j => GfC (V j)), Function.update_comm j.2.ne]
  rw [← GlobalTheory.ClassRegroup.finCl_regroup_prod (fun j : Fin N => V j) (fun i : Fin (N + 1) => V' i) (fun j => hV j j.2)
    (fun i => hV' i (Nat.le_of_lt_succ i.2)) (K := fun j => K j j.2) (K'' := fun j => J j)
    (L := fun i => K' i (Nat.le_of_lt_succ i.2)) (L'' := fun i => J' i) (fun j => (hK j j.2).1) (fun j => (hJ j j.2).2.1)
    (fun j => (hJ j j.2).1) (fun i => (hK' i _).1) (fun i => (hJ' i (Nat.le_of_lt_succ i.2)).2.1) (fun i => (hJ' i _).1)
    (fun j => (hK j j.2).2) (fun i => (hK' i _).2)
    (fun x y => P (ptX N e x y) (ext (P := fun j => GfC (V' j)) (N + 1) y)) ?_ ?_]
  · letI : ∀ j : Fin N, Fintype (FinCl (V j) (J j)) := fun j =>
      @Fintype.ofFinite _ (ClassFin.finite_finCl_and_gamOrd _ _ (hV j j.2) (hJ j j.2).2.1).1
    letI : ∀ j : Fin (N + 1), Fintype (FinCl (V' j) (J' j)) := fun j =>
      @Fintype.ofFinite _ (ClassFin.finite_finCl_and_gamOrd _ _ (hV' j (Nat.le_of_lt_succ j.2))
        (hJ' j (Nat.le_of_lt_succ j.2)).2.1).1
    have key := fun d (hd : d ∈ τ.support) => (one_term (hc d hd) hF hFa (hc' d hd) hF' hFa' h μ fd J
      (fun n hn => ⟨(hJ n hn).2.1, ⟨_, (hK n hn).1, (hJ n hn).1, (hK n hn).2⟩, fun k hk => (hJ n hn).2.2 k hk d hd⟩) μ' fd' J'
      (fun n hn => ⟨(hJ' n hn.le).2.1, ⟨_, (hK' n hn.le).1, (hJ' n hn.le).1, (hK' n hn.le).2⟩,
        fun k hk => (hJ' n hn.le).2.2.1 hn k hk d hd⟩)
      ⟨(hJ' N le_rfl).2.1, ⟨_, (hK' N le_rfl).1, (hJ' N le_rfl).1, (hK' N le_rfl).2⟩,
        fun k hk => (hJ' N le_rfl).2.2.2 rfl k hk d hd⟩)
    rw [Finsupp.sum, Finset.sum_congr rfl fun d hd => congrArg (τ d * ·) (key d hd)]
    simp only [finsum_eq_sum_of_fintype, hP, Finsupp.sum, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => mul_left_comm _ _ _
  · intro y j x
    refine ⟨fun γ hγ z => ?_, fun k hk z => ?_⟩
    · refine hrat (fun i _ => ?_) (fun i _ => ⟨1, one_mem _, (one_mul _).symm⟩) (pN _ _) (pN _ _)
      rw [pU, pU]
      exact up _ _ γ hγ z i
    · have := r1 (Function.update (β := fun j => GfC (V j)) (ptX N e x y) (j : ℕ) z) (ext (P := fun j => GfC (V' j)) (N + 1) y)
        j j.2 k hk
      rw [Function.update_self, Function.update_idem] at this
      simpa only [pU] using this
  · intro x i y
    refine ⟨fun γ hγ z => ?_, fun k hk z => ?_⟩
    · refine hrat (fun j hj => ⟨1, one_mem _, ?_⟩) (fun j _ => ?_) (pN _ _) (pN _ _)
      · rw [one_mul, ptX, ptX, Function.update_of_ne hj.ne, Function.update_of_ne hj.ne]
      · rw [ext_update (P := fun j => GfC (V' j)), ext_update (P := fun j => GfC (V' j))]
        exact up _ _ γ hγ z j
    · simp only [ptX, ext_update (P := fun j => GfC (V' j))]
      obtain ⟨i, hi⟩ := i
      rcases (Nat.le_of_lt_succ hi).eq_or_lt with rfl | hi'
      · have := r3 (Function.update (ext (P := fun j => GfC (V j)) i x) i (e z))
          (Function.update (ext (P := fun j => GfC (V' j)) (i + 1) y) i z) k (by simp) hk
        simpa only [Function.update_self, Function.update_idem] using this
      · have := r2 (Function.update (ext (P := fun j => GfC (V j)) N x) N (e (ext (P := fun j => GfC (V' j)) (N + 1) y N)))
          (Function.update (ext (P := fun j => GfC (V' j)) (N + 1) y) i z) i hi' k hk
        simpa only [Function.update_self, Function.update_idem, Function.update_of_ne hi'.ne'] using this

end Total

end GlobalTheory.JetsOne

end
