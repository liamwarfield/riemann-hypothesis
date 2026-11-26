module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.EndoscopyRank2Ordinary
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.OrdConjTor
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TSolDescent
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.NewformAut0

@[expose] public section

attribute [-instance] Formalism.LFunctionChainParameters.LChain6.FamC.indexKFirst Formalism.LFunctionChainParameters.LChain6.FamC.indexKSecond Formalism.LFunctionChainParameters.LChain6.FamC.indexKThird Formalism.LFunctionChainParameters.LChain6.FamC.indexKFourth Formalism.BasicNotions.NTypes.instMray Formalism.BasicNotions.NTypes.nfMray Formalism.BasicNotions.NTypes.algKM UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.fin UpperTheory.V.Pr.IsCD.isLocalHom UpperTheory.V.Alg.IsCO.toIsLocalRing UpperTheory.V.Alg.IsCO.complete UpperTheory.V.Alg.IsCO.isLocalHom UpperTheory.V.Alg.IsCO.self UpperTheory.V.UnitaryThreeInertia.Coef.isLocalRing

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.OrdBornJ
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.OrdFlagJ
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z UpperTheory.V.Z.Ord
private theorem flag_of_rel {K H : Type} [Field K] [Group H] {n : ℕ} (r : H →* GL (Fin n) K) (ψ : Fin n → H →* Kˣ)
    (h0 : ∀ g : Fin n → H, (List.ofFn fun i => ((r (g i) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) -
      algebraMap K _ ((ψ i (g i) : Kˣ) : K)).prod = 0)
    (hch : ∀ t, (W.mat r t).charpoly = ∏ i, (X - C ((ψ i t : Kˣ) : K)))
    (s : H) (hs : Function.Injective fun i => ψ i s) : W.HasFlag r ψ := by
  classical
  let z : MonoidAlgebra K H := MonoidAlgebra.of K H s
  have hlz : ∀ i, MonoidAlgebra.lift K K H ((Units.coeHom K).comp (ψ i)) z = ((ψ i s : Kˣ) : K) := fun i => by
    simp only [z, MonoidAlgebra.lift_of]
    rfl
  have hPz : MonoidAlgebra.lift K (Matrix (Fin n) (Fin n) K) H ((Units.coeHom _).comp r) z = W.mat r s := by
    simp only [z, MonoidAlgebra.lift_of]
    rfl
  have hext := AlgebraTools.ord_ext (R := K) ((Units.coeHom (Matrix (Fin n) (Fin n) K)).comp r)
    (fun i => (Units.coeHom K).comp (ψ i)) h0
  have hz : ∀ i j, i ≠ j → IsUnit (MonoidAlgebra.lift K K H ((Units.coeHom K).comp (ψ i)) z -
      MonoidAlgebra.lift K K H ((Units.coeHom K).comp (ψ j)) z) := fun i j hij => by
    rw [hlz, hlz]
    exact (sub_ne_zero.2 fun e => hij (hs (Units.ext e))).isUnit
  obtain ⟨hc, hlow, hdiag⟩ := AlgebraTools.lag_triangular
    (MonoidAlgebra.lift K (Matrix (Fin n) (Fin n) K) H ((Units.coeHom _).comp r))
    (fun i => MonoidAlgebra.lift K K H ((Units.coeHom K).comp (ψ i))) z hext hz
  have hne := AlgebraTools.lag_ne_zero (fun i => MonoidAlgebra.lift K K H ((Units.coeHom K).comp (ψ i)) z)
    (MonoidAlgebra.lift K (Matrix (Fin n) (Fin n) K) H ((Units.coeHom _).comp r) z) hz (by
      rw [hPz, hch, Polynomial.map_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hlz]
      simp)
  obtain ⟨g, hg⟩ := AlgebraTools.coi_conj_single _ hc hne
  refine ⟨g, fun t => ?_⟩
  set f := AlgebraTools.lag (fun i => MonoidAlgebra.lift K K H ((Units.coeHom K).comp (ψ i)) z)
    (MonoidAlgebra.lift K (Matrix (Fin n) (Fin n) K) H ((Units.coeHom _).comp r) z) with hf
  have ent : ∀ (M : Matrix (Fin n) (Fin n) K) a b,
      (Matrix.single a a (1 : K) * M * Matrix.single b b (1 : K) : Matrix (Fin n) (Fin n) K) a b = M a b := fun M a b => by
    simp
  have key : ∀ a b, (g * r t * g⁻¹ : GL (Fin n) K) a b =
      ((g : Matrix (Fin n) (Fin n) K) * (f a * (r t : Matrix (Fin n) (Fin n) K) * f b) *
        ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) a b := by
    intro a b
    rw [← ent ((g * r t * g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a b, ← hg a, ← hg b]
    simp only [Units.val_mul, mul_assoc, Units.inv_mul_cancel_left]
  refine ⟨fun i j hji => ?_, fun i => ?_⟩
  · have h := hlow (MonoidAlgebra.of K H t) i j hji
    rw [MonoidAlgebra.lift_of] at h
    have h' : f i * (r t : Matrix (Fin n) (Fin n) K) * f j = 0 := h
    rw [key, h']
    simp
  · have h := hdiag (MonoidAlgebra.of K H t) i
    simp only [MonoidAlgebra.lift_of] at h
    have h' : f i * (r t : Matrix (Fin n) (Fin n) K) * f i = (ψ i t : K) • f i := h
    rw [key, h', Matrix.mul_smul, Matrix.smul_mul, hg i]
    simp
private theorem chi_single {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (D : W.GDet n A G) (φ : H →* G)
    (h : H) : (D.comap φ).chi (MonoidAlgebra.single h 1) = D.chi (MonoidAlgebra.single (φ h) 1) := by
  change D.D A[X] (MonoidAlgebra.mapDomainRingHom A[X] φ _) = D.D A[X] _
  congr 1
  rw [map_sub]
  simp
private theorem descend {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (D : W.GDet n A G) (φ : H →* G)
    (hφ : Function.Surjective φ) (ρ : H →* GL (Fin n) A) (hn : 1 ≤ n) (hF : Ws.Eb.Full ρ)
    (hD : D.comap φ = W.GDet.ofRep (W.mat ρ)) :
    ∃ ρ₀ : G →* GL (Fin n) A, ρ₀.comp φ = ρ ∧ Ws.Eb.Full ρ₀ ∧ D = W.GDet.ofRep (W.mat ρ₀) := by
  have hchi : ∀ h, D.chi (MonoidAlgebra.single (φ h) 1) = (W.GDet.ofRep (W.mat ρ)).chi (MonoidAlgebra.single h 1) :=
    fun h => by rw [← hD, chi_single]
  have hker : φ.ker ≤ ρ.ker := fun g hg => by
    have h0 := (Ws.Eb.trPlus ρ hF).1 (MonoidAlgebra.single g 1 - MonoidAlgebra.single 1 1) fun h => by
      have e : (W.GDet.ofRep (W.mat ρ)).tr (MonoidAlgebra.single (h * g) 1) =
          (W.GDet.ofRep (W.mat ρ)).tr (MonoidAlgebra.single h 1) := by
        unfold W.GDet.tr W.GDet.lam
        rw [← hchi, ← hchi, map_mul, MonoidHom.mem_ker.1 hg, mul_one]
      rw [(AlgebraTools.Det.repApi (W.mat ρ)).2.2.1 hn, (AlgebraTools.Det.repApi (W.mat ρ)).2.2.1 hn] at e
      rw [(AlgebraTools.Det.repApi (W.mat ρ)).2.2.1 hn, mul_sub, map_sub, Matrix.trace_sub,
        MonoidAlgebra.single_mul_single, MonoidAlgebra.single_mul_single, mul_one, mul_one, e, sub_self]
    rw [map_sub, sub_eq_zero] at h0
    refine Units.ext ?_
    simpa [W.GDet.repAlg, W.mat] using h0
  let ρ₀ : G →* GL (Fin n) A := φ.liftOfSurjective hφ ⟨ρ, hker⟩
  have h0 : ∀ h, ρ₀ (φ h) = ρ h := fun h => MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ h
  have hm : ∀ h, W.mat ρ₀ (φ h) = W.mat ρ h := fun h => congrArg Units.val (h0 h)
  refine ⟨ρ₀, MonoidHom.ext h0, ?_, CA.d_gext _ _ fun g i _ _ => ?_⟩
  · refine top_le_iff.1 (le_trans (le_of_eq (Eq.symm hF)) (Submodule.span_mono ?_))
    rintro _ ⟨h, rfl⟩
    exact ⟨φ h, hm h⟩
  · obtain ⟨h, rfl⟩ := hφ g
    unfold W.GDet.lam
    rw [hchi, (AlgebraTools.Det.repApi _).2.1, (AlgebraTools.Det.repApi _).2.1, hm]
theorem UpperTheory.V.Z.Ord.flagJ_alt :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → FlagJ := by
  intro H l _ L Ω _ _ _ _ _ _ s n V c r B Λ J hJ x h ρ hJx hA hx hirr v
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | h0
    · exact absurd (Subsingleton.elim _ _) hirr.1
    · exact h0
  have hs : Function.Surjective V.pr := fun g => by
    obtain ⟨τ, hτ⟩ : ∃ τ, toGS Ω V.S' τ = g.1 := QuotientGroup.mk_surjective g.1
    obtain ⟨σ, rfl⟩ := (V.hη τ).1 (by rw [hτ]; exact g.2)
    exact ⟨σ, Subtype.ext hτ⟩
  have hF : Ws.Eb.Full ρ := (AlgebraTools.Det.irrIffSpan (W.mat ρ)).1 fun N hN => by
    rcases hirr.2.2 N le_top fun g v hv => hN g v hv with h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
  obtain ⟨ρ₀, rfl, hfull, hD⟩ := descend x.D V.pr hs ρ hn hF hx
  obtain ⟨hO, -⟩ := Ws.Eb.relKill B x ρ₀ hfull hD
  obtain ⟨g₀, hg₀⟩ := _root_.UpperTheory.V.Th.Nm.regular_arithmetic_hida_of_literal_automorphy H s h v (x.psi v) hA.1 (hA.2 v)
  refine flag_of_rel _ (x.psi v) (hO v) (fun t => ?_) g₀ hg₀
  let xb : B.B ⧸ J →+* Qbar l := Ideal.Quotient.lift J (x : B.B →+* Qbar l) fun a ha => hJx ha
  have e0 : xb.comp (Ideal.Quotient.mk J) = (x : B.B →+* Qbar l) := RingHom.ext fun a => rfl
  have e1 : (B.DD J).map xb = W.GDet.ofRep (W.mat ρ₀) := by
    have h1 : (B.DD J).map xb = B.u.D.map (xb.comp (Ideal.Quotient.mk J)) := (CA.d_gmap B.u.D).2.1 _ _
    rw [h1, e0]
    exact hD
  have e2 := (AlgebraTools.Det.mapApi (B.DD J) xb).1 (MonoidAlgebra.single (V.frame.φ v t) 1)
  rw [MonoidAlgebra.mapRingHom_single, map_one, e1, (AlgebraTools.Det.repApi _).2.1] at e2
  refine e2.trans ((congrArg (Polynomial.map xb) (hJ.O1 v t)).trans ?_)
  rw [Polynomial.map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  rfl
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.OrdConjUnl
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z UpperTheory.V.Z.Ord
open scoped Matrix
open scoped Pointwise
namespace UpperTheory.V.Z.Ord.CU
section Abs
variable {H H' k : Type} [Group H] [Group H'] [Field k] {n : ℕ}
private theorem trace_of_flag {r : H →* GL (Fin n) k} {ψ : Fin n → H →* kˣ} (h : W.HasFlag r ψ) (s : H) :
    (r s : Matrix (Fin n) (Fin n) k).trace = ∑ i, (ψ i s : k) := by
  obtain ⟨g, hg⟩ := h
  have e : ((g * r s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).trace = (r s : Matrix (Fin n) (Fin n) k).trace := by
    rw [Units.val_mul, Units.val_mul, Matrix.trace_mul_cycle, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
  rw [← e]
  exact Finset.sum_congr rfl fun i _ => (hg s).2 i
private theorem mem_range_of_sum [CharZero k] (a b : Fin n → H →* kˣ) (h : ∀ s, ∑ i, (a i s : k) = ∑ i, (b i s : k)) (i : Fin n) :
    ∃ j, a i = b j := by
  classical
  by_contra hne
  push_neg at hne
  let c : (H →* kˣ) → (H →* k) := fun x => (Units.coeHom k).comp x
  have hc : Function.Injective c := fun x y e => MonoidHom.ext fun s => Units.ext (DFunLike.congr_fun e s)
  let L : (H →* k) →₀ k := ∑ j, Finsupp.single (c (a j)) 1 - ∑ j, Finsupp.single (c (b j)) 1
  have h0 : Finsupp.linearCombination k (fun f : H →* k => (f : H → k)) L = 0 := by
    funext s
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [L, map_sub, map_sum, Finsupp.linearCombination_single, one_smul, Pi.sub_apply, Finset.sum_apply, Pi.zero_apply]
    exact sub_eq_zero.2 (h s)
  have hL := (linearIndependent_iff.1 (linearIndependent_monoidHom H k)) L h0
  have hv : L (c (a i)) = 0 := by rw [hL]; rfl
  have h2 : ∑ j, (Finsupp.single (c (b j)) (1 : k)) (c (a i)) = 0 :=
    Finset.sum_eq_zero fun j _ => by
      rw [Finsupp.single_apply, if_neg fun e => hne j (hc e).symm]
  have h1 : ∑ j, (Finsupp.single (c (a j)) (1 : k)) (c (a i)) = ((Finset.univ.filter fun j => a j = a i).card : k) := by
    simp only [Finsupp.single_apply, hc.eq_iff, Finset.sum_boole]
  have h3 : (Finset.univ.filter fun j => a j = a i).card ≠ 0 :=
    Finset.card_ne_zero.2 ⟨i, by simp⟩
  change (∑ j, Finsupp.single (c (a j)) (1 : k)) (c (a i)) -
    (∑ j, Finsupp.single (c (b j)) (1 : k)) (c (a i)) = 0 at hv
  have hv' : (∑ j, (Finsupp.single (c (a j)) (1 : k)) (c (a i))) -
      (∑ j, (Finsupp.single (c (b j)) (1 : k)) (c (a i))) = 0 := by
    simpa only [Finset.sum_apply'] using hv
  rw [h1, h2, sub_zero] at hv'
  exact h3 (by exact_mod_cast hv')
private theorem flag_range [CharZero k] {r : H →* GL (Fin n) k} {a b : Fin n → H →* kˣ} (ha : W.HasFlag r a) (hb : W.HasFlag r b)
    (i : Fin n) : ∃ j, a i = b j :=
  mem_range_of_sum a b (fun s => by rw [← trace_of_flag ha, ← trace_of_flag hb]) i
private theorem flag_comp {r₁ : H →* GL (Fin n) k} {r₂ : H' →* GL (Fin n) k} {f : H' →* H} {N : GL (Fin n) k}
    (hN : ∀ t, r₂ t = N * r₁ (f t) * N⁻¹) {ψ : Fin n → H →* kˣ} (h : W.HasFlag r₁ ψ) :
    W.HasFlag r₂ fun i => (ψ i).comp f := by
  obtain ⟨g, hg⟩ := h
  refine ⟨g * N⁻¹, fun t => ?_⟩
  have e : g * N⁻¹ * r₂ t * (g * N⁻¹)⁻¹ = g * r₁ (f t) * g⁻¹ := by rw [hN]; group
  rw [e]
  exact hg (f t)
private theorem flag_smul {r r' : H →* GL (Fin n) k} {β : H →* kˣ}
    (hr : ∀ s, (r' s : Matrix (Fin n) (Fin n) k) = (β s : k) • (r s : Matrix (Fin n) (Fin n) k)) {ψ : Fin n → H →* kˣ}
    (h : W.HasFlag r ψ) : W.HasFlag r' fun i => ψ i * β := by
  obtain ⟨g, hg⟩ := h
  refine ⟨g, fun s => ?_⟩
  have e : ((g * r' s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      (β s : k) • ((g * r s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
    simp only [Units.val_mul, hr, Matrix.mul_smul, Matrix.smul_mul]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · have h1 := (hg s).1 i j hij
    change ((g * r' s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j = 0
    rw [e, Matrix.smul_apply]
    change _ • ((g * r s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j = 0
    rw [show ((g * r s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j = 0 from h1, smul_zero]
  · have h1 := (hg s).2 i
    change ((g * r' s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i i = _
    rw [e, Matrix.smul_apply, show ((g * r s * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i i = _ from h1]
    simp [mul_comm]
private def revM (n : ℕ) (k : Type) [Field k] : Matrix (Fin n) (Fin n) k := (1 : Matrix (Fin n) (Fin n) k).submatrix Fin.rev id
private theorem revM_mul (X : Matrix (Fin n) (Fin n) k) (i j : Fin n) : (revM n k * X) i j = X (Fin.rev i) j := by
  simp [revM, Matrix.mul_apply, Matrix.one_apply]
private theorem mul_revM (X : Matrix (Fin n) (Fin n) k) (i j : Fin n) : (X * revM n k) i j = X i (Fin.rev j) := by
  simp [revM, Matrix.mul_apply, Matrix.one_apply, Fin.rev_eq_iff]
private theorem revM_sq : revM n k * revM n k = 1 := by
  ext i j
  rw [revM_mul]
  simp [revM, Matrix.one_apply]
private def revG (n : ℕ) (k : Type) [Field k] : GL (Fin n) k := ⟨revM n k, revM n k, revM_sq, revM_sq⟩
private def trG (g : GL (Fin n) k) : GL (Fin n) k :=
  ⟨(g : Matrix (Fin n) (Fin n) k)ᵀ, ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)ᵀ,
    by rw [← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one]⟩
private theorem flag_dual {r : H →* GL (Fin n) k} {ψ : Fin n → H →* kˣ} (h : W.HasFlag r ψ) :
    W.HasFlag (GlobalTheory.MonoConj.dualRep r) fun i => (ψ (Fin.rev i))⁻¹ := by
  obtain ⟨g, hg⟩ := h
  refine ⟨revG n k * (trG g)⁻¹, fun s => ?_⟩
  have e : ((revG n k * (trG g)⁻¹ * GlobalTheory.MonoConj.dualRep r s * (revG n k * (trG g)⁻¹)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      revM n k * ((g * r s⁻¹ * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)ᵀ * revM n k := by
    have e1 : revG n k * (trG g)⁻¹ * GlobalTheory.MonoConj.dualRep r s * (revG n k * (trG g)⁻¹)⁻¹ =
        revG n k * ((trG g)⁻¹ * GlobalTheory.MonoConj.dualRep r s * trG g) * (revG n k)⁻¹ := by group
    rw [e1]
    simp only [Units.val_mul, Matrix.transpose_mul, GlobalTheory.MonoConj.coe_dualRep, Matrix.mul_assoc]
    rfl
  have e2 : ∀ i j, ((revG n k * (trG g)⁻¹ * GlobalTheory.MonoConj.dualRep r s * (revG n k * (trG g)⁻¹)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j =
      ((g * r s⁻¹ * g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) (Fin.rev j) (Fin.rev i) := fun i j => by
    rw [e, mul_revM, revM_mul, Matrix.transpose_apply]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · exact (e2 i j).trans ((hg s⁻¹).1 _ _ (Fin.rev_lt_rev.2 hij))
  · refine (e2 i i).trans (((hg s⁻¹).2 _).trans ?_)
    simp
private theorem aux₁ {C : Type} [CommGroup C] {a b e μ : C} {m : ℕ} (h : a ^ m = (b * e) ^ m) :
    (b⁻¹ * μ) ^ m = (a⁻¹ * μ * e) ^ m := by
  simp only [mul_pow, inv_pow] at h ⊢
  rw [h, mul_inv]
  simp only [mul_comm, mul_left_comm, mul_assoc]
  rw [mul_left_comm (e ^ m), mul_left_comm (e ^ m), mul_inv_cancel, mul_one]
private theorem aux₂ {C : Type} [CommGroup C] {x y e μ : C} {m : ℕ} (h : (x⁻¹ * μ) ^ m = (y⁻¹ * μ * e) ^ m) :
    y ^ m = (x * e) ^ m := by
  simp only [mul_pow, inv_pow] at h ⊢
  have h' : (x ^ m)⁻¹ = (y ^ m)⁻¹ * e ^ m := by
    have := mul_right_cancel (b := μ ^ m) (a := (x ^ m)⁻¹) (c := (y ^ m)⁻¹ * e ^ m) (by rw [h]; simp [mul_comm, mul_left_comm, mul_assoc])
    exact this
  have h2 : x ^ m = y ^ m * (e ^ m)⁻¹ := by
    have := congrArg (·⁻¹) h'
    simpa [mul_comm] using this
  rw [h2]
  simp
private def Rel (r₁ : H →* GL (Fin n) k) (r₂ : H' →* GL (Fin n) k) (f : H' →* H) : Prop :=
  (∃ N : GL (Fin n) k, ∀ t, r₂ t = N * r₁ (f t) * N⁻¹) ∨
    ∃ (N : GL (Fin n) k) (μ : H' →* kˣ), ∀ t, (r₂ t : Matrix (Fin n) (Fin n) k) =
      (μ t : k) • ((N * GlobalTheory.MonoConj.dualRep r₁ (f t) * N⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)
private theorem abs_main {r₁ : H →* GL (Fin n) k} {r₂ : H' →* GL (Fin n) k} {f : H' →* H} (hf : Function.Surjective f)
    (hr : Rel r₁ r₂ f) {ε : H →* kˣ} {ε' : H' →* kˣ} (hε : ∀ t, ε (f t) = ε' t) {ψ : Fin n → H →* kˣ} (h : W.HasFlag r₁ ψ) :
    ∃ κ : Fin n → H' →* kˣ, W.HasFlag r₂ κ ∧ ∀ m : ℕ, (∃ i j, ψ i ^ m = (ψ j * ε) ^ m) ↔ ∃ a b, κ a ^ m = (κ b * ε') ^ m := by
  rcases hr with ⟨N, hN⟩ | ⟨N, μ, hN⟩
  · refine ⟨fun i => (ψ i).comp f, flag_comp hN h, fun m => ⟨?_, ?_⟩⟩
    · rintro ⟨i, j, e⟩
      refine ⟨i, j, MonoidHom.ext fun t => ?_⟩
      have := DFunLike.congr_fun e (f t)
      simpa [← hε] using this
    · rintro ⟨i, j, e⟩
      refine ⟨i, j, MonoidHom.ext fun s => ?_⟩
      obtain ⟨t, rfl⟩ := hf s
      have := DFunLike.congr_fun e t
      simpa [← hε] using this
  · let r₃ : H' →* GL (Fin n) k :=
      { toFun := fun t => N * GlobalTheory.MonoConj.dualRep r₁ (f t) * N⁻¹
        map_one' := by simp
        map_mul' := fun x y => by simp only [map_mul]; group }
    have h3 : W.HasFlag r₃ fun i => ((ψ (Fin.rev i))⁻¹).comp f := flag_comp (fun _ => rfl) (flag_dual h)
    refine ⟨fun i => ((ψ (Fin.rev i))⁻¹).comp f * μ, flag_smul (r := r₃) hN h3, fun m => ⟨?_, ?_⟩⟩
    · rintro ⟨i, j, e⟩
      refine ⟨Fin.rev j, Fin.rev i, MonoidHom.ext fun t => ?_⟩
      have e1 : ψ i (f t) ^ m = (ψ j (f t) * ε (f t)) ^ m := by
        simpa using DFunLike.congr_fun e (f t)
      have := aux₁ (μ := μ t) e1
      simpa [hε] using this
    · rintro ⟨a, b, e⟩
      refine ⟨Fin.rev b, Fin.rev a, MonoidHom.ext fun s => ?_⟩
      obtain ⟨t, rfl⟩ := hf s
      have e1 : ((ψ (Fin.rev a) (f t))⁻¹ * μ t) ^ m = ((ψ (Fin.rev b) (f t))⁻¹ * μ t * ε (f t)) ^ m := by
        simpa [hε] using DFunLike.congr_fun e t
      simpa using aux₂ e1
end Abs
end UpperTheory.V.Z.Ord.CU
namespace UpperTheory.V.Z.Ord.CU
open UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Af.Gu GlobalTheory.MonoConj
section Conc
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
private theorem cycBar_conjGal {τ : E ≃+* E} {σ : Ω ≃+* Ω} (h : IsLift τ σ) (g : G E Ω) :
    cycBar E Ω l (conjGal h g) = cycBar E Ω l g := by
  have e : cycZ E Ω l (conjGal h g) = cycZ E Ω l g := by
    show cyclotomicCharacter Ω l (conjGal h g).toRingEquiv = cyclotomicCharacter Ω l g.toRingEquiv
    have e : (conjGal h g).toRingEquiv = σ⁻¹ * g.toRingEquiv * σ := rfl
    rw [e, map_mul, map_mul, map_inv, mul_comm, ← mul_assoc, mul_inv_cancel, one_mul]
  simp only [cycBar, MonoidHom.comp_apply, e]
private def decMap {τ : E ≃+* E} {σ : Ω ≃+* Ω} (h : IsLift τ σ) {A A' : ValuationSubring Ω} (hA : ∀ x, σ x ∈ A' ↔ x ∈ A) :
    Dec (F := E) A' →* Dec (F := E) A :=
  ((conjGal h).comp (Dec (F := E) A').subtype).codRestrict _ fun t => conjGal_mem_Dec h hA t.2
private theorem decMap_surj {τ : E ≃+* E} {σ : Ω ≃+* Ω} (h : IsLift τ σ) {A A' : ValuationSubring Ω}
    (hA : ∀ x, σ x ∈ A' ↔ x ∈ A) : Function.Surjective (decMap h hA) := fun s => by
  have hA' : ∀ x, σ.symm x ∈ A ↔ x ∈ A' := fun x => by rw [← hA, RingEquiv.apply_symm_apply]
  refine ⟨⟨conjGal h.symm s.1, conjGal_mem_Dec h.symm hA' s.2⟩, Subtype.ext (AlgEquiv.ext fun x => ?_)⟩
  show conjGal h (conjGal h.symm s.1) x = s.1 x
  simp [conjGal_apply]
private theorem rel_one {τ : E ≃+* E} {σ : Ω ≃+* Ω} (h : IsLift τ σ) {A A' : ValuationSubring Ω} (hA : ∀ x, σ x ∈ A' ↔ x ∈ A)
    (ρ : G E Ω →* GL (Fin n) (Qbar l)) (hτ : ∀ x, τ x = x) :
    Rel (ρ.comp (Dec (F := E) A).subtype) (ρ.comp (Dec (F := E) A').subtype) (decMap h hA) := by
  let g₀ : G E Ω := AlgEquiv.ofRingEquiv (f := σ) fun x => by rw [h, hτ]
  refine Or.inl ⟨ρ g₀, fun t => ?_⟩
  have e : conjGal h t.1 = g₀⁻¹ * t.1 * g₀ := AlgEquiv.ext fun x => rfl
  show ρ t.1 = ρ g₀ * ρ (conjGal h t.1) * (ρ g₀)⁻¹
  rw [e, map_mul, map_mul, map_inv]
  group
private theorem isLift_of_conjEl [IsCMField E] {c : G (maximalRealSubfield E) Ω} (hc : IsConjEl c) :
    IsLift (IsCMField.complexConj E).toRingEquiv c.toRingEquiv := fun x => by
  obtain ⟨j, hj⟩ := hc
  refine j.injective ((hj _).trans ?_)
  exact (IsCMField.complexEmbedding_complexConj E (j.comp (algebraMap E Ω)) x).symm
private theorem rel_conj [IsCMField E] {τ : E ≃+* E} {σ : Ω ≃+* Ω} (h : IsLift τ σ) {A A' : ValuationSubring Ω}
    (hA : ∀ x, σ x ∈ A' ↔ x ∈ A) (ρ : G E Ω →* GL (Fin n) (Qbar l)) (hτ : ∀ x, τ x = IsCMField.complexConj E x)
    (g : G (maximalRealSubfield E) Ω) (hg : g.toRingEquiv = σ)
    {c : G (maximalRealSubfield E) Ω} (hc : IsConjEl c) {P : GL (Fin n) (Qbar l)}
    (hP : IsPairing c ρ (cycBar E Ω l ^ (1 - (n : ℤ))) P) :
    Rel (ρ.comp (Dec (F := E) A).subtype) (ρ.comp (Dec (F := E) A').subtype) (decMap h hA) := by
  subst hg
  have hL := isLift_of_conjEl hc
  let u : G E Ω := AlgEquiv.ofRingEquiv (f := c.symm.toRingEquiv.trans g.toRingEquiv) fun x => by
    have e : c.symm (algebraMap E Ω x) = algebraMap E Ω (IsCMField.complexConj E x) := by
      rw [AlgEquiv.symm_apply_eq]
      refine ((hL _).trans ?_).symm
      rw [show (IsCMField.complexConj E).toRingEquiv (IsCMField.complexConj E x) = x from IsCMField.complexConj_apply_apply E x]
    show g (c.symm (algebraMap E Ω x)) = _
    rw [e]
    refine (h _).trans ?_
    rw [hτ, IsCMField.complexConj_apply_apply]
  refine Or.inr ⟨ρ u * P⁻¹, ((cycBar E Ω l ^ (1 - (n : ℤ))).comp (conjGal h)).comp (Dec (F := E) A').subtype, fun t => ?_⟩
  set s : G E Ω := conjGal h t.1 with hs
  let s' : G E Ω := u⁻¹ * t.1 * u
  have hs' : s'.restrictScalars (maximalRealSubfield E) = c * s.restrictScalars (maximalRealSubfield E) * c⁻¹ :=
    AlgEquiv.ext fun x => rfl
  have hpair := hP s s' hs'
  have hD : (dualRep ρ s : Matrix (Fin n) (Fin n) (Qbar l)) * (ρ s : Matrix (Fin n) (Fin n) (Qbar l))ᵀ = 1 := by
    rw [coe_dualRep, ← Matrix.transpose_mul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.transpose_one]
  have hQ : (ρ s' : Matrix (Fin n) (Fin n) (Qbar l)) =
      ((cycBar E Ω l ^ (1 - (n : ℤ))) s : Qbar l) • ((P⁻¹ * dualRep ρ s * P : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) := by
    have h1 : (P : Matrix (Fin n) (Fin n) (Qbar l)) * (ρ s' : Matrix (Fin n) (Fin n) (Qbar l)) =
        ((cycBar E Ω l ^ (1 - (n : ℤ))) s : Qbar l) • ((dualRep ρ s : Matrix (Fin n) (Fin n) (Qbar l)) * (P : Matrix (Fin n) (Fin n) (Qbar l))) := by
      have := congrArg (fun X => (dualRep ρ s : Matrix (Fin n) (Fin n) (Qbar l)) * X) hpair
      simp only [Matrix.mul_smul, ← Matrix.mul_assoc, hD, Matrix.one_mul] at this
      exact this
    have h2 := congrArg (fun X => ((P⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) * X) h1
    simp only [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul, Matrix.mul_smul] at h2
    rw [inv_mul_cancel_left, ← mul_assoc] at h2
    exact h2
  have ht : ρ t.1 = ρ u * ρ s' * (ρ u)⁻¹ := by
    simp only [s', map_mul, map_inv]
    group
  have e1 : ρ u * P⁻¹ * dualRep (ρ.comp (Dec (F := E) A).subtype) (decMap h hA t) * (ρ u * P⁻¹)⁻¹ =
      ρ u * (P⁻¹ * dualRep ρ s * P) * (ρ u)⁻¹ := by
    have e2 : dualRep (ρ.comp (Dec (F := E) A).subtype) (decMap h hA t) = dualRep ρ s := rfl
    rw [e2]
    group
  show (ρ t.1 : Matrix (Fin n) (Fin n) (Qbar l)) = ((cycBar E Ω l ^ (1 - (n : ℤ))) s : Qbar l) • _
  rw [e1, ht]
  simp only [Units.val_mul (ρ u * ρ s'), Units.val_mul (ρ u), hQ]
  simp only [Units.val_mul, Matrix.mul_smul, Matrix.smul_mul]
end Conc
end UpperTheory.V.Z.Ord.CU
namespace UpperTheory.V.Z.Ord.CU
open UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Af.Gu GlobalTheory.MonoConj
variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
private theorem isPlaceOver_real {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w) :
    IsPlaceOver (F := maximalRealSubfield E) A (w.under (𝓞 (maximalRealSubfield E))) := fun x =>
  h (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) x)
private theorem gal_cases (t : E ≃ₐ[maximalRealSubfield E] E) : t = 1 ∨ t = IsCMField.complexConj E := by
  have hc : Nat.card (E ≃ₐ[maximalRealSubfield E] E) = 2 := by
    rw [IsGalois.card_aut_eq_finrank, Algebra.IsQuadraticExtension.finrank_eq_two]
  obtain ⟨y, _, hy⟩ := (Nat.card_eq_two_iff' (1 : E ≃ₐ[maximalRealSubfield E] E)).1 hc
  by_cases h1 : t = 1
  · exact Or.inl h1
  · exact Or.inr ((hy t h1).trans (hy _ (IsCMField.complexConj_ne_one E)).symm)
private theorem exists_rel (ρ : G E Ω →* GL (Fin n) (Qbar l))
    (hp : ∀ c : G (maximalRealSubfield E) Ω, IsConjEl c → ∃ P, IsPairing c ρ (cycBar E Ω l ^ (1 - (n : ℤ))) P)
    {A A' : ValuationSubring Ω} (g : G (maximalRealSubfield E) Ω) (hg : g • A = A') :
    ∃ f : Dec (F := E) A' →* Dec (F := E) A, Function.Surjective f ∧
      Rel (ρ.comp (Dec (F := E) A).subtype) (ρ.comp (Dec (F := E) A').subtype) f ∧
      ∀ t, cycBar E Ω l (f t).1 = cycBar E Ω l t.1 := by
  have hA : ∀ x, g.toRingEquiv x ∈ A' ↔ x ∈ A := fun x => by
    subst hg
    exact ValuationSubring.smul_mem_pointwise_smul_iff (g := g)
  have h : IsLift (g.restrictNormal E).toRingEquiv g.toRingEquiv := fun x =>
    (AlgEquiv.restrictNormal_commutes g E x).symm
  refine ⟨decMap h hA, decMap_surj h hA, ?_, fun t => cycBar_conjGal h t.1⟩
  rcases gal_cases (g.restrictNormal E) with e | e
  · exact rel_one h hA ρ fun x => by
      show g.restrictNormal E x = x
      rw [e]; rfl
  · obtain ⟨c, hc⟩ := (GlobalTheory.ConjElOverReal.main E Ω).1
    obtain ⟨P, hP⟩ := hp c hc
    exact rel_conj h hA ρ (fun x => by
      show g.restrictNormal E x = _
      rw [e]) g rfl hc hP
end UpperTheory.V.Z.Ord.CU
open UpperTheory.V.Af.Bc in
theorem UpperTheory.V.Z.Ord.conj_unlinked_of_printed_results :
    _root_.UpperTheory.V.Af.Hypotheses' → ConjUnl := by
  intro HP E Ω _ _ _ _ _ _ l _ ι n ρ π hc hd ha w w' hw A hA ψ hψ
  have hcsd : π.IsCsd := GlobalTheory.CsdBack.isCsd_of_paired HP.litN.aut.fin E n π (HP.litN.aut.gk E n π) hd
  have hp : ∀ c : G (maximalRealSubfield E) Ω, Af.IsConjEl c →
      ∃ P, Af.IsPairing c ρ (cycBar E Ω l ^ (1 - (n : ℤ))) P := by
    refine UpperTheory.twistedDual_frobenius_compatibility (_root_.UpperTheory.V.Af.iso_of_frobenius_of_printed_results HP) E Ω l ι n ρ hc ha.1 ?_
    filter_upwards [ha.2, (conjSrc_injective (IsCMField.complexConj E).toRingEquiv).tendsto_cofinite.eventually ha.2]
      with v ⟨B, hB, hF⟩ ⟨B', hB', hF'⟩
    refine ⟨B', ?_, hF'⟩
    have e := CG.HasSat.unique hB ((UpperTheory.satake_parameters_complex_conjugate E v).1 n π hcsd B' hB')
    rw [← e]
    exact hF
  haveI : IsAlgClosure (maximalRealSubfield E) Ω :=
    ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.trans (maximalRealSubfield E) E Ω⟩
  have key : ∀ A' : ValuationSubring Ω, IsPlaceOver A' w' → ∃ κ : Fin n → Dec (F := E) A' →* (Qbar l)ˣ,
      W.HasFlag (ρ.comp (Dec (F := E) A').subtype) κ ∧ ∀ m : ℕ,
        (∃ i j, ψ i ^ m = (ψ j * (cycBar E Ω l).comp (Dec (F := E) A).subtype) ^ m) ↔
          ∃ a b, κ a ^ m = (κ b * (cycBar E Ω l).comp (Dec (F := E) A').subtype) ^ m := by
    intro A' hA'
    have h1 := CU.isPlaceOver_real hA
    have h2 := CU.isPlaceOver_real hA'
    rw [hw] at h2
    obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver h1 h2
    obtain ⟨f, hf, hr, hε⟩ := CU.exists_rel ρ hp g hg
    exact CU.abs_main hf hr hε hψ
  refine ⟨fun hU i j e => ?_, fun hno A' hA' => ?_⟩
  · obtain ⟨A', hA'⟩ := exists_isPlaceOver (F := E) Ω w'
    obtain ⟨κ, hκ, hne⟩ := hU A' hA'
    obtain ⟨κ₀, h₀, hiff⟩ := key A' hA'
    obtain ⟨a, b, hab⟩ := (hiff 1).1 ⟨i, j, by simpa only [pow_one] using e⟩
    obtain ⟨a', ha'⟩ := CU.flag_range h₀ hκ a
    obtain ⟨b', hb'⟩ := CU.flag_range h₀ hκ b
    refine hne a' b' ?_
    rw [← ha', ← hb']
    simpa only [pow_one] using hab
  · obtain ⟨κ₀, h₀, hiff⟩ := key A' hA'
    refine ⟨κ₀, h₀, fun a b m hm e => ?_⟩
    obtain ⟨i, j, hij⟩ := (hiff m).2 ⟨a, b, e⟩
    exact hno i j m hm hij
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.OrdExpTor
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z UpperTheory.V.Z.Ord
private theorem unit_norm {Γ K : Type} [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ] [NormedField K]
    (χ : Γ →* Kˣ) (hχ : Continuous fun s => (χ s : K)) (s : Γ) : ‖(χ s : K)‖ = 1 := by
  have key : ∀ t, ‖(χ t : K)‖ ≤ 1 := fun t => by
    obtain ⟨C, hC⟩ := (isCompact_range hχ.norm).bddAbove
    refine not_lt.1 fun hlt => ?_
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt C hlt
    have h1 := hC ⟨t ^ m, rfl⟩
    simp only [map_pow, Units.val_pow_eq_pow_val, norm_pow] at h1
    exact absurd hm (not_lt.2 h1)
  refine le_antisymm (key s) ?_
  have h2 := key s⁻¹
  rw [map_inv, Units.val_inv_eq_inv_val, norm_inv] at h2
  exact (inv_le_one₀ (norm_pos_iff.2 (χ s).ne_zero)).1 h2
section Local
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
private theorem ord_unif : ord k (ImaginaryQuadraticEtaCharacter.unif k) = 1 := by
  have hs := (ImaginaryQuadraticEtaCharacter.polFacts k).1
  obtain ⟨p, hp⟩ := valuation_surjective (uniformizer k : ValueGroupWithZero k)
  exact ord_eq_one (le_antisymm (le_uniformizer_iff.2 hs.1) (hp ▸ hs.2 p (hp ▸ uniformizer_lt_one)))
end Local
section Gal
variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime]
  {w : Plc L} {A : ValuationSubring Ω} {h : IsPlaceOver A w} {a : Weil h →* (w.adicCompletion L)ˣ}
private theorem algPow_add' (d e : (L →+* Qbar l) → ℤ) (x : (w.adicCompletion L)ˣ) :
    algPow w (d + e) (x : w.adicCompletion L) = algPow w d (x : w.adicCompletion L) * algPow w e (x : w.adicCompletion L) := by
  haveI := GlobalTheory.HeckeGal.finite_contEmb (l := l) w
  unfold algPow
  rw [← finprod_mul_distrib (Set.toFinite _) (Set.toFinite _)]
  exact finprod_congr fun j => by rw [Pi.add_apply, zpow_add₀ ((map_ne_zero j.1).2 x.ne_zero)]
private theorem algPow_ne (d : (L →+* Qbar l) → ℤ) (x : (w.adicCompletion L)ˣ) :
    algPow w d (x : w.adicCompletion L) ≠ 0 := by
  haveI := GlobalTheory.HeckeGal.finite_contEmb (l := l) w
  haveI := Fintype.ofFinite (W.Emb l w)
  unfold algPow
  rw [show (∏ᶠ j : {j : w.adicCompletion L →+* Qbar l // Continuous j}, j.1 (x : w.adicCompletion L) ^ d (j.1.comp (algebraMap L (w.adicCompletion L)))) = _ from finprod_eq_prod_of_fintype _]
  exact Finset.prod_ne_zero_iff.2 fun j _ => zpow_ne_zero _ ((map_ne_zero j.1).2 x.ne_zero)
private theorem algPow_nat [Fintype (W.Emb l w)] (d : (L →+* Qbar l) → ℤ) (N : ℕ) (hN : N ≠ 0) :
    algPow w d ((N : ℕ) : w.adicCompletion L) = (N : Qbar l) ^ ∑ j : W.Emb l w, d (j.1.comp (algebraMap L _)) := by
  have h0 : (N : Qbar l) ≠ 0 := Nat.cast_ne_zero.2 hN
  have hp : ∀ (T : Finset (W.Emb l w)) (c : W.Emb l w → ℤ), ∏ j ∈ T, (N : Qbar l) ^ c j = (N : Qbar l) ^ ∑ j ∈ T, c j :=
    fun T c => T.cons_induction (by simp) fun j T hj ih => by rw [Finset.prod_cons, Finset.sum_cons, ih, zpow_add₀ h0]
  unfold algPow
  rw [finprod_eq_prod_of_fintype]
  simp only [map_natCast]
  exact hp _ _
private theorem sum_eq_zero [Fintype (W.Emb l w)] (ha : IsLocalArtin h a) (d : (L →+* Qbar l) → ℤ)
    (χ : Dec (F := L) A →* (Qbar l)ˣ) (hχ : Continuous χ)
    (hv : ∀ s : Weil h, (χ (Subgroup.inclusion (Weil_le_Dec h) s) : Qbar l) = algPow w d (a s : w.adicCompletion L)) :
    ∑ j : W.Emb l w, d (j.1.comp (algebraMap L _)) = 0 := by
  haveI : CompactSpace (Dec (F := L) A) := isCompact_iff_compactSpace.1 (isClosed_Dec A).isCompact
  haveI : CharZero (w.adicCompletion L) := algebraRat.charZero _
  have hl0 : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  obtain ⟨s, hs⟩ := ha.surj (Units.mk0 (l : w.adicCompletion L) (Nat.cast_ne_zero.2 hl0))
  have h1 := unit_norm χ (Units.continuous_val.comp hχ) (Subgroup.inclusion (Weil_le_Dec h) s)
  rw [hv, hs, Units.val_mk0, algPow_nat d l hl0, norm_zpow] at h1
  exact (zpow_eq_one_iff_right₀ (norm_nonneg _) (GlobalTheory.PlaceBridge.norm_l_lt_one (l := l)).ne).1 h1
private theorem gap_zero [Fintype (W.Emb l w)] {n : ℕ} {hh : Fin n → (L →+* Qbar l) → ℤ}
    (hm : ∀ τ, StrictMono fun j => hh j τ) {i j : Fin n}
    (hs : ∑ t : W.Emb l w, (hh j - hh i - 1) (t.1.comp (algebraMap L _)) = 0) (x : w.adicCompletion L) :
    algPow w (hh j - hh i - 1) x = 1 := by
  have key : ∀ t : W.Emb l w, (hh j - hh i - 1) (t.1.comp (algebraMap L _)) = 0 := fun t => by
    rcases lt_or_ge i j with hlt | hge
    · refine (Finset.sum_eq_zero_iff_of_nonneg fun t _ => ?_).1 hs t (Finset.mem_univ _)
      have := hm (t.1.comp (algebraMap L _)) hlt
      simp only [Pi.sub_apply, Pi.one_apply] at this ⊢
      omega
    · have hneg : ∀ t : W.Emb l w, (hh j - hh i - 1) (t.1.comp (algebraMap L _)) < 0 := fun t => by
        have := (hm (t.1.comp (algebraMap L _))).monotone hge
        simp only [Pi.sub_apply, Pi.one_apply] at this ⊢
        omega
      exact absurd hs (Finset.sum_neg (fun t _ => hneg t) ⟨t, Finset.mem_univ _⟩).ne
  exact finprod_eq_one_of_forall_eq_one fun t => by rw [key t, zpow_zero]
end Gal
section Near
open Filter Topology
variable {L : Type} [Field L] [NumberField L] {l : ℕ} [Fact l.Prime] {w : Plc L}
private theorem pow_tendsto (x : w.adicCompletion L) (hx : Valued.v x < 1) :
    Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) := by
  rw [(Valued.hasBasis_nhds_zero _ _).tendsto_right_iff]
  intro γ _
  have hne : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := by simp
  obtain ⟨n, hn⟩ := exists_pow_lt₀ hx (Units.mk0 _ hne)
  filter_upwards [eventually_ge_atTop n] with m hm
  rw [Valuation.restrict_lt_iff_lt_embedding, map_pow]
  exact lt_of_le_of_lt (pow_le_pow_right_of_le_one' hx.le hm) hn
private theorem near_one (hw : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal) {U : Set (w.adicCompletion L)ˣ} (hU : IsOpen U) (h1 : (1 : (w.adicCompletion L)ˣ) ∈ U) :
    ∃ (N : ℕ) (u : (w.adicCompletion L)ˣ), 2 ≤ N ∧ (u : w.adicCompletion L) = (N : w.adicCompletion L) ∧ u ∈ U ∧
      ord (w.adicCompletion L) u = 0 := by
  haveI : CharZero (w.adicCompletion L) := algebraRat.charZero _
  have hv : Valued.v (l : w.adicCompletion L) < 1 := by
    have h4 : Valued.v (algebraMap L (w.adicCompletion L) (((l : ℕ) : 𝓞 L) : L)) < 1 := by
      rw [show Valued.v (algebraMap L (w.adicCompletion L) (((l : ℕ) : 𝓞 L) : L)) =
        w.valuation L (algebraMap (𝓞 L) L ((l : ℕ) : 𝓞 L)) from HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _]
      exact (HeightOneSpectrum.valuation_lt_one_iff_mem w _).2 hw
    simpa using h4
  have hne : ∀ M : ℕ, (((1 + l ^ M : ℕ)) : w.adicCompletion L) ≠ 0 := fun M => Nat.cast_ne_zero.2 (by omega)
  have ht : Tendsto (fun M : ℕ => Units.mk0 _ (hne M)) atTop (𝓝 1) := by
    rw [Units.isEmbedding_val₀.tendsto_nhds_iff]
    have := (pow_tendsto _ hv).const_add (1 : w.adicCompletion L)
    simpa [Function.comp_def] using this
  obtain ⟨M, hM, hMU⟩ := ((eventually_ge_atTop 1).and (ht.eventually (hU.mem_nhds h1))).exists
  have hl : 0 < l ^ M := pow_pos (Fact.out : l.Prime).pos _
  refine ⟨1 + l ^ M, _, by omega, rfl, hMU, ?_⟩
  have hvM : Valued.v ((l : w.adicCompletion L) ^ M) < 1 := by
    rw [map_pow]
    exact pow_lt_one₀ zero_le' hv (by omega)
  rw [SphCompletion.ord_completion, Units.val_mk0]
  push_cast
  rw [Valuation.map_one_add_of_lt _ hvM]
  simp
end Near
section Tw
variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime]
  {w : Plc L} {A : ValuationSubring Ω} {h : IsPlaceOver A w} {a : Weil h →* (w.adicCompletion L)ˣ}
private theorem twist_val (H : GlobalTheory.Published.GlobalArtinReciprocity) (ι : Qbar l ≃+* ℂ) {n : ℕ}
    (hw : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal) (ha : IsLocalArtin h a) {hh : Fin n → (L →+* Qbar l) → ℤ}
    {ω : Fin n → (w.adicCompletion L)ˣ →* ℂˣ} {ψ : Fin n → Dec (F := L) A →* (Qbar l)ˣ}
    (hO : ∀ j, OrdChar ι a (ω j) (hh j) (ψ j)) (i j : Fin n) (s : Weil h) :
    (((ψ i * (ψ j * (cycBar L Ω l).comp (Dec (F := L) A).subtype)⁻¹) (Subgroup.inclusion (Weil_le_Dec h) s) : (Qbar l)ˣ) : Qbar l) *
        (ι.symm (ω j (a s)) * ((normV w : ℕ) : Qbar l) ^ deg s) =
      ι.symm (ω i (a s)) * algPow w (hh j - hh i - 1) (a s : w.adicCompletion L) := by
  set inc := Subgroup.inclusion (Weil_le_Dec h)
  set ε := (cycBar L Ω l).comp (Dec (F := L) A).subtype
  set X := (ψ i * (ψ j * ε)⁻¹) (inc s) with hX
  have hε : (ε (inc s) : Qbar l) = ((normV w : ℕ) : Qbar l) ^ deg s * algPow w 1 (a s : w.adicCompletion L) :=
    UpperTheory.V.Loc.epsArt H h hw a ha s
  have hv : ∀ k, (ψ k (inc s) : Qbar l) = ι.symm (ω k (a s)) * algPow w (-hh k) (a s : w.adicCompletion L) :=
    fun k => (hO k).val s _ rfl (Set.mem_univ _)
  have e00 : ψ i (inc s) = X * (ψ j (inc s) * ε (inc s)) := (inv_mul_cancel_right _ _).symm
  have e0 : (ψ i (inc s) : Qbar l) = (X : Qbar l) * ((ψ j (inc s) : Qbar l) * (ε (inc s) : Qbar l)) := by
    rw [← Units.val_mul, ← Units.val_mul, ← e00]
  have e2 : algPow w (-hh i) (a s : w.adicCompletion L) = algPow w (hh j - hh i - 1) (a s : w.adicCompletion L) *
      (algPow w (-hh j) (a s : w.adicCompletion L) * algPow w 1 (a s : w.adicCompletion L)) := by
    rw [← algPow_add', ← algPow_add']
    congr 1
    ring
  rw [hv, hv, hε, e2] at e0
  refine mul_right_cancel₀ (mul_ne_zero (algPow_ne (-hh j) (a s)) (algPow_ne 1 (a s))) ?_
  linear_combination -e0
private theorem abs_val (ι : Qbar l ≃+* ℂ) (ha : IsLocalArtin h a) (s : Weil h) :
    ι.symm (absPow (w.adicCompletion L) 1 (a s)) = ((normV w : ℕ) : Qbar l) ^ deg s := by
  have := DFunLike.congr_fun (ha.absPow_comp 1) s
  rw [Complex.ofReal_one] at this
  rw [← MonoidHom.comp_apply, this, GlobalTheory.WeilDeligne.unrChar_apply, Units.val_zpow_eq_zpow_val, map_zpow₀]
  simp
private theorem cyc_cont' : Continuous ((cycBar L Ω l).comp (Dec (F := L) A).subtype) :=
  ((Continuous.units_map ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom).toMonoidHom
    ((continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val)).comp (continuous_cycZ L Ω l)).comp continuous_subtype_val
private theorem q_ne : ((normV w : ℕ) : Qbar l) ≠ 0 := Nat.cast_ne_zero.mpr (GlobalTheory.WeilDeligne.one_lt_normV w).ne_bot
private theorem link (H : GlobalTheory.Published.GlobalArtinReciprocity) (ι : Qbar l ≃+* ℂ) {n : ℕ}
    (hw : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal) (ha : IsLocalArtin h a) {hh : Fin n → (L →+* Qbar l) → ℤ}
    (hm : ∀ τ, StrictMono fun j => hh j τ) {ω : Fin n → (w.adicCompletion L)ˣ →* ℂˣ}
    {ψ : Fin n → Dec (F := L) A →* (Qbar l)ˣ} (hO : ∀ j, OrdChar ι a (ω j) (hh j) (ψ j)) (i j : Fin n)
    (e : ω i = ω j * absPow (w.adicCompletion L) 1) : ψ i = ψ j * (cycBar L Ω l).comp (Dec (F := L) A).subtype := by
  haveI := GlobalTheory.HeckeGal.finite_contEmb (l := l) w
  haveI := Fintype.ofFinite (W.Emb l w)
  have hc : Continuous (ψ i * (ψ j * (cycBar L Ω l).comp (Dec (F := L) A).subtype)⁻¹) :=
    (hO i).cont.mul ((hO j).cont.mul cyc_cont').inv
  have hx : ∀ s : Weil h, (((ψ i * (ψ j * (cycBar L Ω l).comp (Dec (F := L) A).subtype)⁻¹) (Subgroup.inclusion (Weil_le_Dec h) s) : (Qbar l)ˣ) : Qbar l) =
      algPow w (hh j - hh i - 1) (a s : w.adicCompletion L) := fun s => by
    have h1 := twist_val H ι hw ha hO i j s
    have e' : ω i (a s) = ω j (a s) * absPow (w.adicCompletion L) 1 (a s) := by rw [e]; rfl
    rw [e', Units.val_mul, map_mul, abs_val ι ha] at h1
    exact mul_right_cancel₀ (mul_ne_zero ((map_ne_zero ι.symm).2 (Units.ne_zero _)) (zpow_ne_zero _ q_ne)) (h1.trans (mul_comm _ _))
  have h1 := gap_zero hm (sum_eq_zero ha _ _ hc hx)
  refine mul_inv_eq_one.1 (MonoidHom.ext fun g => Units.ext ?_)
  refine congrFun ((UpperTheory.weil_group_dense_in_galois_group L Ω w A h).equalizer (Units.continuous_val.comp hc) continuous_const
    (funext fun s => ?_)) g
  exact (hx s).trans (h1 _)
private theorem tors (H : GlobalTheory.Published.GlobalArtinReciprocity) (ι : Qbar l ≃+* ℂ) {n : ℕ}
    (hw : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal) (ha : IsLocalArtin h a) {hh : Fin n → (L →+* Qbar l) → ℤ}
    (hm : ∀ τ, StrictMono fun j => hh j τ) {ω : Fin n → (w.adicCompletion L)ˣ →* ℂˣ}
    {ψ : Fin n → Dec (F := L) A →* (Qbar l)ˣ} (hO : ∀ j, OrdChar ι a (ω j) (hh j) (ψ j)) (i j : Fin n) (m : ℕ) (hm1 : 1 ≤ m)
    (e : ψ i ^ m = (ψ j * (cycBar L Ω l).comp (Dec (F := L) A).subtype) ^ m) :
    ‖((ω j (ImaginaryQuadraticEtaCharacter.unif (w.adicCompletion L)) : ℂˣ) : ℂ)‖ = (normV w : ℝ) * ‖((ω i (ImaginaryQuadraticEtaCharacter.unif (w.adicCompletion L)) : ℂˣ) : ℂ)‖ := by
  haveI := GlobalTheory.HeckeGal.finite_contEmb (l := l) w
  haveI := Fintype.ofFinite (W.Emb l w)
  obtain ⟨ρ, hρ⟩ : ∃ ρ, ρ = ψ i * (ψ j * (cycBar L Ω l).comp (Dec (F := L) A).subtype)⁻¹ := ⟨_, rfl⟩
  have hρm : ∀ g, ((ρ g : (Qbar l)ˣ) : Qbar l) ^ m = 1 := fun g => by
    have h1 : ρ ^ m = 1 := by rw [hρ, mul_pow, inv_pow, e, mul_inv_cancel]
    have h2 := DFunLike.congr_fun h1 g
    rw [MonoidHom.pow_apply, MonoidHom.one_apply] at h2
    rw [← Units.val_pow_eq_pow_val, h2, Units.val_one]
  obtain ⟨N, u, hN, hu, huU, hu0⟩ := near_one hw (IsOpen.inter (hO i).smooth (hO j).smooth) ⟨one_mem _, one_mem _⟩
  obtain ⟨s, hs⟩ := ha.surj u
  have hd : deg s = 0 := by
    have := ha.ord_eq s
    rw [hs, hu0] at this
    omega
  have h1 := twist_val H ι hw ha hO i j s
  have hiu : ω i u = 1 := huU.1
  have hju : ω j u = 1 := huU.2
  rw [← hρ, hs, hiu, hju, hd, hu, algPow_nat _ N (by omega)] at h1
  simp only [Units.val_one, map_one, zpow_zero, mul_one, one_mul] at h1
  have h3 : ∑ t : W.Emb l w, (hh j - hh i - 1) (t.1.comp (algebraMap L _)) = 0 := by
    have h2 := hρm (Subgroup.inclusion (Weil_le_Dec h) s)
    rw [h1] at h2
    have h5 := congrArg (fun z => ‖ι z‖) h2
    simp only [map_pow, map_zpow₀, map_natCast, map_one, norm_pow, norm_zpow, norm_one, Complex.norm_natCast] at h5
    have h6 := (pow_eq_one_iff_of_nonneg (zpow_nonneg (Nat.cast_nonneg _) _) (by omega)).1 h5
    exact (zpow_eq_one_iff_right₀ (Nat.cast_nonneg _) (by exact_mod_cast (by omega : N ≠ 1))).1 h6
  have hone := gap_zero hm h3
  obtain ⟨s0, hs0⟩ := ha.surj (ImaginaryQuadraticEtaCharacter.unif (w.adicCompletion L))
  have hd0 : deg s0 = -1 := by
    have := ha.ord_eq s0
    rw [hs0, ord_unif] at this
    omega
  have h4 := twist_val H ι hw ha hO i j s0
  rw [← hρ, hs0, hd0, hone, mul_one, zpow_neg_one] at h4
  have h5 := congrArg (fun z => ‖ι z‖) h4
  simp only [map_mul, map_inv₀, map_natCast, RingEquiv.apply_symm_apply, norm_mul, norm_inv, Complex.norm_natCast] at h5
  have h6 : ‖ι ((ρ (Subgroup.inclusion (Weil_le_Dec h) s0) : (Qbar l)ˣ) : Qbar l)‖ = 1 :=
    Complex.norm_eq_one_of_pow_eq_one (n := m) (by rw [← map_pow, hρm, map_one]) (by omega)
  rw [h6, one_mul] at h5
  have hq : (normV w : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (GlobalTheory.WeilDeligne.one_lt_normV w).ne_bot
  rw [← h5]
  field_simp
end Tw
section Top
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
  {w : HeightOneSpectrum (𝓞 F)} {A : ValuationSubring Ω} {h : IsPlaceOver A w} {a : Weil h →* (w.adicCompletion F)ˣ}
private theorem normV_absNorm : normV w = Ideal.absNorm w.asIdeal := by
  rw [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
private theorem abs_unif (ι : Qbar l ≃+* ℂ) (ha : IsLocalArtin h a) :
    ((absPow (w.adicCompletion F) 1 (ImaginaryQuadraticEtaCharacter.unif (w.adicCompletion F)) : ℂˣ) : ℂ) = ((normV w : ℕ) : ℂ)⁻¹ := by
  obtain ⟨s0, hs0⟩ := ha.surj (ImaginaryQuadraticEtaCharacter.unif (w.adicCompletion F))
  have hd0 : deg s0 = -1 := by
    have := ha.ord_eq s0
    rw [hs0, ord_unif] at this
    omega
  have h1 := congrArg ι (abs_val ι ha s0)
  rw [hs0, hd0, ι.apply_symm_apply, zpow_neg_one, map_inv₀, map_natCast] at h1
  exact h1
private theorem supp_ps [_root_.NumberField.IsTotallyComplex F] {n : ℕ} (hn : 1 ≤ n) (π : CuspSub F n) {ω : Fin n → (w.adicCompletion F)ˣ →* ℂˣ}
    (hs : ∀ i, IsSmoothChar (ω i)) (hσ : ∀ σ, π.IsLocComp w σ → IsSubquotient σ.ρ (PS ω)) :
    Gam.TorAt π w ∧ ∀ s, Gam.SuppAt π w s → (∀ i, ω i * absPow (w.adicCompletion F) (((n : ℂ) - 1) / 2) ∈ ImaginaryQuadraticEtaCharacter.chars s) ∧
      ∀ ξ ∈ ImaginaryQuadraticEtaCharacter.chars s, ∃ i, ξ = ω i * absPow (w.adicCompletion F) (((n : ℂ) - 1) / 2) := by
  haveI : CharZero (w.adicCompletion F) := algebraRat.charZero _
  have hμ : ∀ i, IsSmoothChar (ω i * absPow (w.adicCompletion F) (((n : ℂ) - 1) / 2)) :=
    fun i => (hs i).mul (isSmoothChar_absPow _)
  have key : ∀ σ, π.IsLocComp w σ → HasSupport σ.ρ (Finset.univ.val.map fun i => IrrGL.ofChar _ (hμ i)) := fun σ h1 =>
    hasSupport_of_isSubquotient_prinSeries (w.adicCompletion F) n _ hμ ⟨_, σ.ρ, σ.smooth, σ.irred⟩ (hσ σ h1)
  refine ⟨fun σ h1 => ⟨_, (key σ h1).of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred), fun y hy => ?_⟩, fun s ⟨σ, h1, h2⟩ => ?_⟩
  · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hy
    rfl
  · obtain rfl := (Gam.suppFacts F n hn π w).2.1 s _ ⟨σ, h1, h2⟩ ⟨σ, h1, key σ h1⟩
    refine ⟨fun i => ⟨hμ i, Multiset.mem_map.2 ⟨i, Finset.mem_univ_val _, rfl⟩⟩, fun ξ ⟨hξ, hm⟩ => ?_⟩
    obtain ⟨i, -, e⟩ := Multiset.mem_map.1 hm
    exact ⟨i, ((ImaginaryQuadraticEtaCharacter.polFacts _).2.2.1 _ _ _ _ e).symm⟩
end Top
theorem UpperTheory.V.Z.Ord.exp_torsion_of_literal_automorphy_n :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ExpTor := by
  intro N F Ω _ _ _ _ _ _ l _ n hn ι A w h hl π ψ ⟨a, ha, hh, ω, hm, hO, hσ⟩
  have H := N.aut.art
  obtain ⟨tor, hch⟩ := supp_ps hn π (fun i => (hO i).smooth) hσ
  have hQ0 : (0 : ℝ) < (Ideal.absNorm w.asIdeal : ℝ) := by
    rw [← normV_absNorm]
    exact_mod_cast (GlobalTheory.WeilDeligne.one_lt_normV w).bot_lt
  refine ⟨tor, fun hU => ⟨tor, fun s hs ξ hξ ξ' hξ' hun hq => ?_⟩, fun t hW i j m hm1 e => ?_⟩
  · obtain ⟨i, rfl⟩ := (hch s hs).2 ξ hξ
    obtain ⟨j, rfl⟩ := (hch s hs).2 ξ' hξ'
    have hr : ∀ x, ((ω i * absPow (w.adicCompletion F) (((n : ℂ) - 1) / 2)) *
        (ω j * absPow (w.adicCompletion F) (((n : ℂ) - 1) / 2))⁻¹) x = ω i x * (ω j x)⁻¹ := fun x => by
      simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv_rev]
      rw [mul_assoc, mul_inv_cancel_left]
    have hu : IsUnram (ω j * (ω i * absPow (w.adicCompletion F) 1)⁻¹) := fun x hx => by
      have h1 := hun x hx
      rw [hr] at h1
      have h2 := isUnram_absPow (w.adicCompletion F) 1 x hx
      simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv_rev, h2, inv_one, one_mul]
      rw [mul_inv_eq_one]
      exact (mul_inv_eq_one.1 h1).symm
    have hv : ω j (ImaginaryQuadraticEtaCharacter.unif (w.adicCompletion F)) = (ω i * absPow (w.adicCompletion F) 1) (ImaginaryQuadraticEtaCharacter.unif (w.adicCompletion F)) := by
      rw [hr, Units.val_mul, Units.val_inv_eq_inv_val] at hq
      have a0 := (ω i (ImaginaryQuadraticEtaCharacter.unif (w.adicCompletion F))).ne_zero
      have b0 := (ω j (ImaginaryQuadraticEtaCharacter.unif (w.adicCompletion F))).ne_zero
      rw [MonoidHom.mul_apply]
      refine Units.ext ?_
      rw [Units.val_mul, abs_unif ι ha, normV_absNorm, ← hq]
      field_simp
    exact hU j i (link H ι hl ha hm hO j i ((ImaginaryQuadraticEtaCharacter.polFacts _).2.1 _ _ hu hv))
  · obtain ⟨s, hs⟩ := (Gam.suppFacts F n hn π w).1
    have hc := (hch s hs).1
    have wi := (hW.2 s hs _ (hc i)).1
    have wj := (hW.2 s hs _ (hc j)).2
    have ht := tors H ι hl ha hm hO i j m hm1 e
    rw [MonoidHom.mul_apply, Units.val_mul, norm_mul] at wi wj
    rw [ht, normV_absNorm] at wj
    have e2 : (Ideal.absNorm w.asIdeal : ℝ) ^ (t + 1 / 2) = (Ideal.absNorm w.asIdeal : ℝ) * (Ideal.absNorm w.asIdeal : ℝ) ^ (t - 1 / 2) := by
      rw [show t + 1 / 2 = 1 + (t - 1 / 2) by ring, Real.rpow_add hQ0, Real.rpow_one]
    rw [e2, mul_assoc] at wj
    exact absurd wi (not_lt.2 (lt_of_mul_lt_mul_left wj hQ0.le).le)
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z UpperTheory.V.Z.Ord
private theorem sat_of_frob {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l n : ℕ}
    [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {ρ : G F Ω →* GL (Fin n) (Qbar l)} {w : HeightOneSpectrum (𝓞 F)} {B B' : Multiset ℂˣ}
    (h : Af.FrobEig ι ρ w (Af.algSat n (normV w) B)) (h' : Af.FrobEig ι ρ w (Af.algSat n (normV w) B')) : B = B' := by
  obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
  obtain ⟨σ, hσ⟩ := ReciprocityTheory.Gal.exists_isFrob hA
  have e := congrArg Polynomial.roots (((h A hA).2 σ hσ).symm.trans ((h' A hA).2 σ hσ))
  rw [roots_multiset_prod_X_sub_C, roots_multiset_prod_X_sub_C] at e
  have hq : (0 : ℝ) < (normV w : ℕ) := Nat.cast_pos.2 (lt_trans one_pos (GlobalTheory.WeilDeligne.one_lt_normV w))
  have hc : (((normV w : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.rpow_pos_of_pos hq _).ne'
  have e' := Multiset.map_injective (mul_right_injective₀ hc) (a₁ := B.map Units.val) (a₂ := B'.map Units.val)
    (by simpa [Af.algSat, Multiset.map_map] using e)
  exact Multiset.map_injective Units.val_injective e'
theorem UpperTheory.V.Z.Ord.born_j_of_printed_polarization_window :
    _root_.UpperTheory.V.Af.Hypotheses' → ImaginaryQuadraticEtaCharacter.WinOf → BornJ := by
  intro P hO l _ L Ω _ _ _ _ _ _ s n hn V c r ι B Λ J hR hE x h ρ hJ hA hρ hI hc w hl hU
  obtain ⟨π₀, -, hd, ha, he⟩ := hE x h ρ hJ hA hρ hI
  have hl' := (UpperTheory.V.Hi.Pu.l_iff (l := l) w).2 hl
  let v : Vl l L := ⟨w.under (𝓞 (Lp L)), hl'⟩
  have hu : (s.w v.1).under (𝓞 (Lp L)) = v.1 := UpperTheory.V.Hi.Pu.w_under s v.1
  have hsl : ((l : ℕ) : 𝓞 L) ∈ (s.w v.1).asIdeal := (UpperTheory.V.Hi.Pu.l_iff (l := l) _).1 (by rw [hu]; exact hl')
  have hF := _root_.UpperTheory.V.Z.Ord.flagJ_alt P.litN l L Ω s n V c r B Λ J hR x h ρ hJ hA hρ hI v
  obtain ⟨hu1, hu2⟩ := _root_.UpperTheory.V.Z.Ord.conj_unlinked_of_printed_results P L Ω l ι n ρ π₀ hc hd ha (s.w v.1) w hu.symm (s.A v.1) (s.hw v.1) (x.psi v) hF
  obtain ⟨-, hTU, hW⟩ := _root_.UpperTheory.V.Z.Ord.exp_torsion_of_literal_automorphy_n P.litN L Ω l n hn ι (s.A v.1) (s.w v.1) (s.hw v.1) hsl π₀ (x.psi v) (he v)
  have hT : TU π₀ (s.w v.1) := hTU (hu1 hU)
  obtain ⟨t, ht⟩ := hO L n hn π₀
  refine ⟨hu2 (hW t (ht (s.w v.1) hT.1 hT.2)), fun π hπ => ?_⟩
  have e : π₀ = π := GlobalTheory.CuspRep.CuspSub.ext (UpperTheory.V.Af.strongMultOneC L n π₀ π (by
    filter_upwards [ha.2, hπ.2] with u ⟨b, hb, hf⟩ ⟨b', hb', hf'⟩
    obtain rfl := sat_of_frob hf hf'
    exact ⟨b, (CG.hasSat_mk π₀ u b).1 hb, (CG.hasSat_mk π u b).1 hb'⟩))
  exact e ▸ _root_.UpperTheory.V.Z.Ord.conj_torsion_of_printed_results P L n hn π₀ hd (s.w v.1) w hu.symm hT
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC GlobalTheory.PRep UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
open UpperTheory.V.Z UpperTheory.V.Z.Ord UpperTheory.Gal.projectedFormsSystemPart UpperTheory.GalN.V
theorem UpperTheory.Gal.projectedFormsSystemPart.arithPointDecomposition_and_irrAutomorphic_of_isJ (hL : _root_.UpperTheory.V.Af.HypothesesH' → _root_.UpperTheory.Gal.projectedFormsSystemPart.PartLinkAlt) :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ), ∀ (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) (R : _root_.UpperTheory.V.Hi.CaseU.UnitaryHeckeData Q ι Λ) (K : (hset Q R.τ₀).Lev), V.S' = s.S → ∀ J : Ideal B.B, R.IsJ B K J → ArithmeticPointDecomposition B ι J ∧ IrrArithPointsAutomorphicAway B ι J :=
  fun H l _ L Ω _ _ _ _ _ _ s n hn V Q c r ι B Λ R K hS J hJ =>
    ⟨_root_.UpperTheory.V.Hi.arithmeticPointDecomposition_of_isJ H l L Ω s n hn V Q c r ι B Λ R K hS J hJ,
      _root_.UpperTheory.Gal.projectedFormsSystemPart.irrArithPointsAutomorphicAway_of_isJ H (hL H) (_root_.UpperTheory.V.Z.Ord.conj_torsion_of_printed_results H.toClassicalTheorems) (_root_.UpperTheory.V.Z.Ord.endOrd_of_printsH H) (_root_.UpperTheory.V.Z.Ord.born_j_of_printed_polarization_window H.toClassicalTheorems ImaginaryQuadraticEtaCharacter.winOf) l L Ω s n hn V Q c r ι B Λ R K hS J hJ⟩
end
