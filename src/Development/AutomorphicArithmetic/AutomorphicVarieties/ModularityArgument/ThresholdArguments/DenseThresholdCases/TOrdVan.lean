module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.OrdVan
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.NewformAut0
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.THidaX
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TLocDataT
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SVREGOrd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LocalLanglandsGLOfPrints

@[expose] public section

attribute [-instance] Formalism.LFunctionChainParameters.LChain6.FamC.indexKFirst Formalism.LFunctionChainParameters.LChain6.FamC.indexKSecond Formalism.LFunctionChainParameters.LChain6.FamC.indexKThird Formalism.LFunctionChainParameters.LChain6.FamC.indexKFourth Formalism.BasicNotions.NTypes.instMray Formalism.BasicNotions.NTypes.nfMray Formalism.BasicNotions.NTypes.algKM UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.isLocalHom UpperTheory.V.Pr.IsCD.fin

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TCoreO
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.THasOp
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.OpOpOf
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ReductionOfPolynomialElementPow
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ModularityLinkedEnds
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.V.Th
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
abbrev _root_.UpperTheory.V.Th.LevelRelationTwoX : Prop :=
    _root_.UpperTheory.V.Pa.LocPAlt → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (V0 : s.Lev) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V0.frame O n) (B : UniversalOrdinaryDeterminantRing r) (J : Ideal B.B) (D : ℕ) (b : TWBase (pairOf B.u) J Empty D) (V : s.Lev) (h : (globOf r V).Hom (globOf r V0)) (q : ℕ) (w : Fin q → Plc L) (A : LevMod b h w) (x δ : ∀ j, ((w j).adicCompletion L)ˣ), (∀ j, ((l : ℕ) : 𝓞 L) ∉ (w j).asIdeal) → (∀ j, IsUnif (x j)) → (∀ j, IsGenMod _ (ellC l _) (δ j)) → ∀ (T : ThData l A.ρ x δ) (ph ta : Fin q → (globOf r V).G₀), _root_.UpperTheory.V.Pa.Lev.LocalLevelConditions A x δ ph ta → ∀ j i, T.act1 (fEl (qj w) (uV A.R) ^ (2 * n.factorial) * (A.p.D.map (MvPolynomial.C : A.R →+* PUY A.R q n)).tr (twoPowerModulus (2 * n.factorial) (ph j) (ta j) (uV A.R j) i (yV A.R j i))) = 0
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.OpRelOf
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.V.Th
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
private theorem relOf_act {T W κ : Type} [CommGroup T] [AddCommGroup W] [Module ℂ W]
    (θ : T →* (Module.End ℂ W)ˣ) (t : κ → T) :
    ∃ act : MvPolynomial κ ℂ →ₐ[ℂ] Module.End ℂ W, ∀ a, act (MvPolynomial.X a) = θ (t a) :=
  ⟨(MonoidAlgebra.lift ℂ (Module.End ℂ W) T ((Units.coeHom _).comp θ)).comp
    (MvPolynomial.aeval fun a => MonoidAlgebra.single (t a) 1), fun a => by simp⟩
private theorem relOf_int {R W W' κ S : Type} [CommRing R] [AddCommGroup W] [Module R W] [AddCommGroup W'] [Module ℂ W']
    [CommRing S] [Algebra ℂ S] (c : R →+* ℂ) (v : κ → S)
    (act : MvPolynomial κ R →ₐ[R] Module.End R W) (act' : S →ₐ[ℂ] Module.End ℂ W') (g : W →+ W')
    (hg : ∀ r m, g (r • m) = c r • g m)
    (h : ∀ a m, act' (v a) (g m) = g (act (MvPolynomial.X a) m)) (F : MvPolynomial κ R) (m : W) :
    act' (MvPolynomial.eval₂Hom ((algebraMap ℂ S).comp c) v F) (g m) = g (act F m) := by
  induction F using MvPolynomial.induction_on generalizing m with
  | C r =>
    rw [MvPolynomial.eval₂Hom_C, ← MvPolynomial.algebraMap_eq, AlgHom.commutes, RingHom.comp_apply, AlgHom.commutes]
    simp [hg]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), map_add (f := _), LinearMap.add_apply, LinearMap.add_apply, map_add (f := _), hp, hq]
  | mul_X p a hp =>
    rw [map_mul, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, MvPolynomial.eval₂Hom_X', h, hp]
private theorem relOf_uy {R W W' ι S : Type} [CommRing R] [AddCommGroup W] [Module R W] [AddCommGroup W'] [Module ℂ W']
    [CommRing S] [Algebra R S] (c : R →+* ℂ) (act : S →ₐ[R] Module.End R W)
    (act' : MvPolynomial (ι ⊕ ι) ℂ →ₐ[ℂ] Module.End ℂ W') (g : W →+ W') (hg : ∀ r m, g (r • m) = c r • g m)
    (ψ : MvPolynomial (ι ⊕ ι) R →ₐ[R] S) (N : ℕ) (e : ι → ℕ) (E : ι ⊕ ι → Module.End R W)
    (hu : ∀ i, act (ψ (MvPolynomial.X (.inl i))) = (N : R) ^ e i • E (.inl i))
    (hy : ∀ i, act (1 + ψ (MvPolynomial.X (.inr i))) = E (.inr i))
    (h : ∀ a m, act' (MvPolynomial.X a) (g m) = g (E a m)) (F : MvPolynomial (ι ⊕ ι) R) (k : ℕ)
    (h0 : act' (MvPolynomial.eval₂Hom ((algebraMap ℂ (MvPolynomial (ι ⊕ ι) ℂ)).comp c)
      (Sum.elim (fun i => ((N : ℂ) ^ e i) • MvPolynomial.X (.inl i)) fun i => MvPolynomial.X (.inr i) - 1) F ^ k) = 0) (m : W) :
    g (act (ψ F ^ k) m) = 0 := by
  have h1 := relOf_int c (Sum.elim (fun i => ((N : ℂ) ^ e i) • MvPolynomial.X (.inl i)) fun i => MvPolynomial.X (.inr i) - 1)
    (act.comp ψ) act' g hg (fun a m => by
      rw [AlgHom.comp_apply]
      rcases a with i | i
      · rw [Sum.elim_inl, hu, map_smul, LinearMap.smul_apply, LinearMap.smul_apply, hg, map_pow, map_natCast, h]
      · have e := hy i
        rw [map_add (f := _), map_one] at e
        rw [Sum.elim_inr, eq_sub_of_add_eq' e, map_sub, map_one, LinearMap.sub_apply, LinearMap.sub_apply, map_sub, h]
        rfl) (F ^ k) m
  rw [map_pow, h0, AlgHom.comp_apply, map_pow] at h1
  exact h1.symm
theorem UpperTheory.V.Th.relOfX_alt :
    _root_.UpperTheory.V.Pa.LocPAlt → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (V0 : s.Lev) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V0.frame O n) (B : UniversalOrdinaryDeterminantRing r) (J : Ideal B.B) (D : ℕ) (b : TWBase (pairOf B.u) J Empty D) (V : s.Lev) (h : (globOf r V).Hom (globOf r V0)) (q : ℕ) (w : Fin q → Plc L) (A : LevMod b h w) (x δ : ∀ j, ((w j).adicCompletion L)ˣ), (∀ j, ((l : ℕ) : 𝓞 L) ∉ (w j).asIdeal) → (∀ j, IsUnif (x j)) → (∀ j, IsGenMod _ (ellC l _) (δ j)) → ∀ (T : ThData l A.ρ x δ) (ι : Qbar l ≃+* ℂ), (∀ m : A.P, (∀ y : _root_.UpperTheory.V.Pa.LevPtAlt A ι, y.sp m = 0) → m = 0) → ∀ (j : Fin q) (F : MvPolynomial (Fin n ⊕ Fin n) A.R), (∀ (y : _root_.UpperTheory.V.Pa.LevPtAlt A ι) θ, IsTheta (y.σ j).ρ (ellC l _) θ → ∀ χ : (Fin n → ((w j).adicCompletion L)ˣ) →* ℂˣ, (⨅ t, Module.End.maxGenEigenspace (θ t).val (χ t : ℂ)) ≠ ⊥ → ∀ (S : Type) [CommRing S] [Algebra ℂ S] (U : Fin n → S), (∀ i : Fin n, (U i - algebraMap ℂ S ((qj w j : ℂ) ^ (i : ℕ) * (χ (Pi.mulSingle i (x j)) : ℂ))) ^ n.factorial = 0) → MvPolynomial.eval₂ ((algebraMap ℂ S).comp (ι.toRingHom.comp y.θ)) (Sum.elim U fun i => algebraMap ℂ S (χ (Pi.mulSingle i (δ j)) : ℂ) - 1) F = 0) → T.act1 (MvPolynomial.rename (Sum.map (fun i => (j, i)) fun i => (j, i)) F) = 0 := by
  intro hP l _ L Ω _ _ _ _ _ _ s V0 O _ _ _ _ _ n r B J D b V h q w A x δ _ _ hδ T ι hsep j F hF
  rw [← pow_one (MvPolynomial.rename _ F)]
  refine LinearMap.ext fun m => Subtype.ext (hsep _ fun y => ?_)
  obtain ⟨Θ, hΘ⟩ := thetaQ L n q w ℂ y.Y y.π (fun _ => ellC l _) fun j =>
    (Nat.cast_ne_zero.2 (Nat.card_pos (α := 𝓀[(w j).adicCompletion L])).ne').isUnit
  let t : Fin n ⊕ Fin n → Fin n → ((w j).adicCompletion L)ˣ :=
    Sum.elim (fun i => Pi.mulSingle i (x j)) fun i => Pi.mulSingle i (δ j)
  obtain ⟨act, hact⟩ := relOf_act (Θ j) t
  let c : A.R →+* ℂ := ι.toRingHom.comp y.θ
  let v : Fin n ⊕ Fin n → MvPolynomial (Fin n ⊕ Fin n) ℂ :=
    Sum.elim (fun i => ((qj w j : ℂ) ^ (i : ℕ)) • MvPolynomial.X (.inl i)) fun i => MvPolynomial.X (.inr i) - 1
  let g : fixd A.ρ (UC n w fun _ => ellC l _) →+ fixd y.π (UC n w fun _ => ellC l _) :=
    { toFun := fun m => ⟨y.sp m, fun u hu => by rw [← y.sp_act, m.2 u hu]⟩
      map_zero' := Subtype.ext (map_zero y.sp)
      map_add' := fun a a' => Subtype.ext (map_add y.sp _ _) }
  have hg : ∀ (r : A.R) m, g (r • m) = c r • g m := fun r m => Subtype.ext (y.sp_smul r m)
  have hΘg : ∀ t m, (Θ j t).val (g m) = g ((T.Θ1 j t).val m) := fun t m =>
    Subtype.ext (thetaMap L n q w A.R A.P ℂ y.Y A.ρ y.π _ T.Θ1 Θ T.h1 hΘ y.sp y.sp_act j t m (g m) rfl)
  have h0 := nilKillX hP.gl hP.bz L n q w y.Y y.π _ Θ hΘ j (y.σ j) (y.iso j) _ t (fun i => ⟨_, _, i, hδ j, rfl⟩) act hact
    (MvPolynomial.eval₂Hom ((algebraMap ℂ _).comp c) v F) (fun θ hθ χ hχ S _ _ φ h1 h2 => by
      refine Eq.trans ?_ (hF y θ hθ χ hχ S (fun i => ((qj w j : ℂ) ^ (i : ℕ)) • φ (MvPolynomial.X (.inl i))) fun i => ?_)
      · rw [MvPolynomial.coe_eval₂Hom]
        refine (MvPolynomial.eval₂_comp_left φ.toRingHom _ _ _).trans ?_
        congr 1
        · ext r
          exact φ.commutes _
        · funext a
          rcases a with i | i
          · exact map_smul φ _ _
          · exact (map_sub φ _ _).trans (by rw [h2, map_one]; rfl)
      · rw [map_mul, Algebra.smul_def, ← mul_sub, mul_pow]
        exact mul_eq_zero_of_right _ (h1 i))
  rw [← pow_one (MvPolynomial.eval₂Hom _ v F)] at h0
  exact congrArg Subtype.val (relOf_uy c T.act1 act g hg
    (MvPolynomial.rename (Sum.map (fun i => (j, i)) fun i => (j, i))) (qj w j) (fun i => (i : ℕ))
    (fun a => (T.Θ1 j (t a)).val)
    (fun i => by rw [MvPolynomial.rename_X]; exact T.act_uVariable_eq_pow j i)
    (fun i => by rw [MvPolynomial.rename_X]; exact T.act_yVariable j i)
    (fun a m => by rw [hact]; exact hΘg _ m) F _ h0 m)
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.V.Th
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
private theorem exists_place_above_prime_pow (K : Type) [Field K] [NumberField K] (l : ℕ) [hl : Fact l.Prime] :
    ∃ v : HeightOneSpectrum (𝓞 K), ((l : ℕ) : 𝓞 K) ∈ v.asIdeal := by
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.1 hl.out
  haveI : (Ideal.span {(l : ℤ)}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).2 hp
  obtain ⟨Q, hQ, hc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := 𝓞 K) (Ideal.span {(l : ℤ)})
    (by rw [(RingHom.injective_iff_ker_eq_bot (algebraMap ℤ (𝓞 K))).1 (RingHom.injective_int _)]; exact bot_le)
  have hm : ((l : ℕ) : 𝓞 K) ∈ Q := by
    have : (l : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 K)) := by
      change (l : ℤ) ∈ Ideal.under ℤ Q
      rw [hc]
      exact Ideal.mem_span_singleton_self _
    simpa using this
  refine ⟨⟨Q, hQ, fun h => ?_⟩, hm⟩
  rw [h, Ideal.mem_bot] at hm
  exact hl.out.ne_zero (by exact_mod_cast hm)
private theorem trace_map_ring_hom_pow {n : ℕ} {A B G : Type} [CommRing A] [CommRing B] [Group G] (D : GDet n A G) (f : A →+* B)
    (y : MonoidAlgebra A G) : (D.map f).tr (MonoidAlgebra.mapRingHom G f y) = f (D.tr y) :=
  ((UpperTheory.V.CA.d_gmap D).2.2.1 f y).2 1
private theorem trace_map_comp_pow {n : ℕ} {A B C G : Type} [CommRing A] [CommRing B] [CommRing C] [Group G] (D : GDet n A G)
    (f : A →+* B) (g : B →+* C) (k : A →+* C) (hk : g.comp f = k) (y : MonoidAlgebra B G) :
    g ((D.map f).tr y) = (D.map k).tr (MonoidAlgebra.mapRingHom G g y) := by
  rw [← trace_map_ring_hom_pow, (UpperTheory.V.CA.d_gmap D).2.1, hk]
private theorem charpoly_of_representation_pow {n : ℕ} {K G : Type} [CommRing K] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) K)
    (y : MonoidAlgebra K G) : (GDet.ofRep ρ).chi y = (GDet.repAlg ρ K y).charpoly := by
  change (GDet.repAlg ρ (Polynomial K) _).det = Matrix.det _
  congr 1
  have h : GDet.repAlg ρ (Polynomial K) (MonoidAlgebra.mapRingHom G Polynomial.C y) =
      (Polynomial.C : K →+* Polynomial K).mapMatrix (GDet.repAlg ρ K y) := by
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | single g r => ext i j; simp [GDet.repAlg]
  rw [map_sub, h, Matrix.charmatrix]
  congr 1
  exact (GDet.repAlg ρ (Polynomial K)).commutes Polynomial.X
private theorem trace_eq_zero_of_rep_eq_zero_pow {n : ℕ} {K G : Type} [CommRing K] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) K)
    (y₀ y : MonoidAlgebra K G) (h₀ : (GDet.ofRep ρ).tr y₀ = 0) (h : GDet.repAlg ρ K y = 0) : (GDet.ofRep ρ).tr y = 0 := by
  rcases n with _ | n
  · rw [← h₀, GDet.tr, GDet.tr, GDet.lam, GDet.lam, charpoly_of_representation_pow, charpoly_of_representation_pow, Subsingleton.elim (GDet.repAlg ρ K y) (GDet.repAlg ρ K y₀)]
  · nontriviality K
    rw [GDet.tr, GDet.lam, charpoly_of_representation_pow, h, Matrix.charpoly_zero, Polynomial.coeff_X_pow]
    simp
private theorem map_ring_hom_second_relation_pow {n : ℕ} {A B G : Type} [CommRing A] [CommRing B] [Group G] (f : A →+* B) (E : ℕ) (ph ta : G)
    (u : Fin n → A) (i : Fin n) (y : A) : MonoidAlgebra.mapRingHom G f (twoPowerModulus E ph ta u i y) =
      twoPowerModulus E ph ta (fun i => f (u i)) i (f y) := by
  simp only [twoPowerModulus, map_mul, map_pow, map_list_prod, List.map_ofFn, Function.comp_def, map_sub,
    apply_ite (MonoidAlgebra.mapRingHom G f), MonoidAlgebra.mapRingHom_single, map_one]
private theorem rep_single_eq_smul_pow {n : ℕ} {K G : Type} [CommRing K] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) K) (g : G) (a : K) :
    GDet.repAlg ρ K (MonoidAlgebra.single g a) = a • ρ g := by
  ext i j; simp [GDet.repAlg]
private theorem rep_second_relation_pow_eq_zero {n : ℕ} {K G : Type} [CommRing K] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) K) (E : ℕ) (ph ta : G)
    (α : Fin n → K) (i : Fin n) (c : K)
    (h : (List.ofFn fun i' => if i' = i then 1 else ρ ph - α i' • (1 : Matrix (Fin n) (Fin n) K)).prod ^ (E + 1) *
      (ρ ta - c • (1 : Matrix (Fin n) (Fin n) K)) = 0) :
    GDet.repAlg ρ K (twoPowerModulus E ph ta α i (c - 1)) = 0 := by
  rw [twoPowerModulus, map_mul, map_pow, map_list_prod, List.map_ofFn]
  refine Eq.trans ?_ h
  congr 1
  · congr 3
    funext k
    by_cases hk : k = i <;> simp [hk, rep_single_eq_smul_pow]
  · simp [rep_single_eq_smul_pow, sub_smul]
private theorem reduction_of_polynomial_element_pow {n q : ℕ} {R G E : Type} [CommRing R] [Group G] [Ring E] [Algebra R E] (D : GDet n R G)
    (act : PUY R q n →ₐ[R] E) (Nq : Fin q → ℕ) (j : Fin q) (k : ℕ) (z : MonoidAlgebra (MvPolynomial (Fin n ⊕ Fin n) R) G)
    (z' : MonoidAlgebra (PUY R q n) G)
    (hz : MonoidAlgebra.mapRingHom G (MvPolynomial.rename (Sum.map (fun i => (j, i)) fun i => (j, i)) :
      MvPolynomial (Fin n ⊕ Fin n) R →ₐ[R] PUY R q n).toRingHom z = z')
    (h : act (MvPolynomial.rename (Sum.map (fun i => (j, i)) fun i => (j, i))
      ((∏ i : Fin n, ∏ i' ∈ Finset.univ.erase i, ((MvPolynomial.X (.inl i) - MvPolynomial.X (.inl i')) *
        (MvPolynomial.X (.inl i) - (Nq j : MvPolynomial (Fin n ⊕ Fin n) R) * MvPolynomial.X (.inl i')))) ^ k *
        (D.map (MvPolynomial.C : R →+* MvPolynomial (Fin n ⊕ Fin n) R)).tr z)) = 0) :
    act (fEl Nq (uV R) ^ k * (D.map (MvPolynomial.C : R →+* PUY R q n)).tr z') = 0 := by
  have e := trace_map_comp_pow D (MvPolynomial.C : R →+* MvPolynomial (Fin n ⊕ Fin n) R)
    (MvPolynomial.rename (Sum.map (fun i => (j, i)) fun i => (j, i)) :
      MvPolynomial (Fin n ⊕ Fin n) R →ₐ[R] PUY R q n).toRingHom MvPolynomial.C (by ext : 1; simp) z
  rw [hz] at e
  rw [fEl, ← Finset.prod_erase_mul _ _ (Finset.mem_univ j), mul_pow, mul_assoc, map_mul, ← e]
  refine mul_eq_zero_of_right _ (Eq.trans ?_ h)
  simp [map_prod]
private theorem trace_vanishing_of_evaluation_pow {n : ℕ} {R K S G : Type} [CommRing R] [CommRing K] [CommRing S] [Group G] (D : GDet n R G) (θ : R →+* K) (ι : K →+* S)
    (ρ : G →* Matrix (Fin n) (Fin n) K) (hD : D.map θ = GDet.ofRep ρ) (z₀ : MonoidAlgebra R G) (h₀ : D.tr z₀ = 0)
    (v : Fin n ⊕ Fin n → S) (z : MonoidAlgebra (MvPolynomial (Fin n ⊕ Fin n) R) G)
    (h : GDet.repAlg (ι.mapMatrix.toMonoidHom.comp ρ) S
      (MonoidAlgebra.mapRingHom G (MvPolynomial.eval₂Hom (ι.comp θ) v) z) = 0) :
    MvPolynomial.eval₂ (ι.comp θ) v ((D.map (MvPolynomial.C : R →+* MvPolynomial (Fin n ⊕ Fin n) R)).tr z) = 0 := by
  have hD' : D.map (ι.comp θ) = GDet.ofRep (ι.mapMatrix.toMonoidHom.comp ρ) := by
    rw [← (UpperTheory.V.CA.d_gmap D).2.1, hD, (UpperTheory.V.CA.d_gmap (GDet.ofRep ρ)).2.2.2]
  rw [← MvPolynomial.coe_eval₂Hom, trace_map_comp_pow D _ _ (ι.comp θ) (by ext : 1; simp), hD']
  refine trace_eq_zero_of_rep_eq_zero_pow _ (MonoidAlgebra.mapRingHom G (ι.comp θ) z₀) _ ?_ h
  rw [← hD', trace_map_ring_hom_pow, h₀, map_zero]
theorem UpperTheory.V.Z.Win.T2.level_relation_two_x :
    _root_.UpperTheory.V.Th.LevelRelationTwoX := by
  intro hP l _ L Ω _ _ _ _ _ _ s V0 O _ _ _ _ _ n r B J D b V h q w A x δ h1 h2 h3 T ph ta ⟨ι, hsep, hloc⟩ j i
  obtain ⟨v⟩ : Nonempty (globOf r V).frame.Vl := (exists_place_above_prime_pow (Lp L) l).elim fun v hv => ⟨⟨v, hv⟩⟩
  have h₀ := A.p.Ord v (fun _ => 1) 1
  refine reduction_of_polynomial_element_pow A.p.D T.act1 (qj w) j _
    (twoPowerModulus (2 * n.factorial) (ph j) (ta j) (fun i => MvPolynomial.X (.inl i)) i (MvPolynomial.X (.inr i))) _
    ((map_ring_hom_second_relation_pow _ _ _ _ _ _ _).trans (by simp)) ?_
  refine _root_.UpperTheory.V.Th.relOfX_alt hP l L Ω s V0 O n r B J D b V h q w A x δ h1 h2 h3 T ι hsep j _ fun y θ hθ χ hχ S _ _ U hU => ?_
  rw [MvPolynomial.eval₂_mul]
  by_cases hreg : ∀ a a' : Fin n, a ≠ a' → (qj w j : ℂ) ^ (a : ℕ) * (χ (Pi.mulSingle a (x j)) : ℂ) ≠
      (qj w j : ℂ) ^ (a' : ℕ) * (χ (Pi.mulSingle a' (x j)) : ℂ) ∧ (qj w j : ℂ) ^ (a : ℕ) * (χ (Pi.mulSingle a (x j)) : ℂ) ≠
      (qj w j : ℂ) * ((qj w j : ℂ) ^ (a' : ℕ) * (χ (Pi.mulSingle a' (x j)) : ℂ))
  · refine mul_eq_zero_of_right _ ?_
    refine trace_vanishing_of_evaluation_pow A.p.D y.θ ((algebraMap ℂ S).comp ι.toRingHom) (mat y.rep) y.det _ h₀ _ _ ?_
    rw [map_ring_hom_second_relation_pow]
    simp only [MvPolynomial.eval₂Hom_X', Sum.elim_inl, Sum.elim_inr]
    refine rep_second_relation_pow_eq_zero _ _ _ _ _ _ _ ?_
    have h5 := powRel ℂ S (algebraMap ℂ S) n n.factorial (2 * n.factorial) _ _ _ _ U i (by omega) hU
      ((_root_.UpperTheory.V.Z.Win.relT' (hloc y j) _ le_rfl θ hθ χ hχ _ fun _ => rfl).2 hreg i)
    rw [Matrix.map_map, Matrix.map_map] at h5
    exact h5
  · refine mul_eq_zero_of_left ?_ _
    rw [← MvPolynomial.coe_eval₂Hom]
    simp only [map_pow, map_prod, map_mul, map_sub, map_natCast, MvPolynomial.eval₂Hom_X', Sum.elim_inl]
    exact fNil ℂ S (algebraMap ℂ S) n n.factorial (qj w j) _ U hU hreg
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.V.Th
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
private theorem opOf_proj {Λ Γ Q M : Type} [CommRing Λ] [Group Γ] [Group Q] [AddCommGroup M] [Module Λ M]
    (ρ : Representation Λ Q M) (e : Γ ≃* Q) (hP : Module.Projective (MonoidAlgebra Λ Q) ρ.asModule) :
    Module.Projective (MonoidAlgebra Λ Γ) (Representation.asModule (ρ.comp e.toMonoidHom : Representation Λ Γ M)) := by
  let σ : MonoidAlgebra Λ Q ≃+* MonoidAlgebra Λ Γ := (MonoidAlgebra.domCongr Λ Λ e.symm).toRingEquiv
  let ρ' : Representation Λ Γ M := ρ.comp e.toMonoidHom
  have key : ∀ a : MonoidAlgebra Λ Q, ρ'.asAlgebraHom (σ a) = ρ.asAlgebraHom a := fun a => by
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), map_add (f := _), ha, hb]
    | single g c => simp [σ, ρ']
  haveI := RingHomInvPair.of_ringEquiv σ
  haveI := RingHomInvPair.of_ringEquiv_symm σ
  let f : ρ.asModule ≃ₛₗ[(σ : MonoidAlgebra Λ Q →+* MonoidAlgebra Λ Γ)] ρ'.asModule :=
    { ρ.asModuleEquiv.toAddEquiv.trans ρ'.asModuleEquiv.symm.toAddEquiv with
      map_smul' := fun a m => by
        apply ρ'.asModuleEquiv.injective
        rw [Representation.asModuleEquiv_map_smul]
        simp [Representation.asModuleEquiv_map_smul, key] }
  exact Module.Projective.of_equiv f
private theorem opOf_dc {R G P : Type} [CommRing R] [Group G] [AddCommGroup P] [Module R P] (ρ : Representation R G P)
    (K K1 : Subgroup G) [Fintype (K ⧸ K1.subgroupOf K)] (m : P) (hm : m ∈ fixd ρ K1) :
    dc ρ K K1 1 m = ∑ g : K ⧸ K1.subgroupOf K, ρ (g.out : K) m := by
  let f : K ⧸ K1.subgroupOf K → MulAction.orbit K ((1 : G) : G ⧸ K1) := fun g =>
    ⟨((g.out : K) : G), g.out, congrArg QuotientGroup.mk (mul_one _)⟩
  have hf : Function.Bijective f := by
    refine ⟨fun a b hab => ?_, ?_⟩
    · have h1 := QuotientGroup.eq.1 (congrArg Subtype.val hab)
      rw [← a.out_eq', ← b.out_eq']
      exact QuotientGroup.eq.2 h1
    · rintro ⟨_, k, rfl⟩
      refine ⟨(k : K ⧸ K1.subgroupOf K), Subtype.ext ?_⟩
      have h1 := QuotientGroup.eq.1 (QuotientGroup.out_eq' (k : K ⧸ K1.subgroupOf K))
      have h2 : (((k : K ⧸ K1.subgroupOf K).out : K) : G ⧸ K1) = ((k : G) : G ⧸ K1) := QuotientGroup.eq.2 h1
      exact h2.trans (congrArg (QuotientGroup.mk (s := K1)) (mul_one (k : G)).symm)
  unfold dc
  rw [← finsum_comp f hf, finsum_eq_sum_of_fintype, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun g _ => ?_
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul K1 ((g.out : K) : G)
  show ρ (((g.out : K) : G) : G ⧸ K1).out m = _
  rw [hu, map_mul, Module.End.mul_apply, hm u u.2]
private theorem opOf_tr {Λ R G P Γ σ : Type} [CommRing Λ] [CommRing R] [Algebra Λ R] [Group G] [AddCommGroup P]
    [Module R P] [Module Λ P] [IsScalarTower Λ R P] [Group Γ] [Finite Γ] (ρ : Representation R G P)
    (K K1 : Subgroup G) (hle : K1 ≤ K) [(K1.subgroupOf K).Normal]
    (ρ' : Representation Λ (K ⧸ K1.subgroupOf K) (fixd ρ K1))
    (hρ' : ∀ (u : K) f, (ρ' (u : K ⧸ K1.subgroupOf K) f : P) = ρ u f)
    (hP : Module.Projective (MonoidAlgebra Λ (K ⧸ K1.subgroupOf K)) ρ'.asModule)
    (e : Γ ≃* K ⧸ K1.subgroupOf K) (γ : σ → Γ) (hγ : Subgroup.closure (Set.range γ) = ⊤)
    (Y : σ → Module.End R (fixd ρ K1)) (hY : ∀ p m, ρ' (e (γ p)) m = m + Y p m)
    (tr : fixd ρ K1 →ₗ[R] fixd ρ K) (htr : ∀ m, (tr m : P) = dc ρ K K1 1 m) :
    Function.Surjective tr ∧ LinearMap.ker tr = ⨆ p, LinearMap.range (Y p) := by
  haveI : Finite (K ⧸ K1.subgroupOf K) := Finite.of_equiv Γ e.toEquiv
  letI := Fintype.ofFinite (K ⧸ K1.subgroupOf K)
  obtain ⟨h1, h2⟩ := projNorm Λ _ _ ρ' hP
  have hs : ∀ m, (tr m : P) = (∑ g, ρ' g m : fixd ρ K1) := fun m => by
    rw [htr, opOf_dc ρ K K1 m m.2, AddSubmonoidClass.coe_finsetSum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [← hρ', QuotientGroup.out_eq']
  refine ⟨fun v => ?_, le_antisymm (fun m hm => ?_) (iSup_le fun p => ?_)⟩
  · obtain ⟨m, hm⟩ := h1 ⟨v, fixd_anti ρ hle v.2⟩ fun g => by
      obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective g
      exact Subtype.ext ((hρ' u _).trans (v.2 u u.2))
    exact ⟨m, Subtype.ext (by rw [hs, hm])⟩
  · have h0 : ∑ g, ρ' g m = 0 := Subtype.ext (by rw [← hs, LinearMap.mem_ker.1 hm]; rfl)
    have hc : Subgroup.closure (Set.range fun p => e (γ p)) = ⊤ := by
      have := congrArg (Subgroup.map e.toMonoidHom) hγ
      rw [MonoidHom.map_closure, ← Set.range_comp, Subgroup.map_top_of_surjective _ e.surjective] at this
      exact this
    have h3 : (⨆ g ∈ Set.range fun p => e (γ p), LinearMap.range (ρ' g - 1)) ≤
        (⨆ p, LinearMap.range (Y p)).restrictScalars Λ := by
      refine iSup₂_le ?_
      rintro _ ⟨p, rfl⟩ _ ⟨v, rfl⟩
      refine Submodule.mem_iSup_of_mem (p := fun p => LinearMap.range (Y p)) p ⟨v, ?_⟩
      rw [LinearMap.sub_apply, hY, Module.End.one_apply, add_sub_cancel_left]
    exact h3 (h2 _ hc m h0)
  · rintro _ ⟨m, rfl⟩
    have h4 : tr (ρ' (e (γ p)) m) = tr m := Subtype.ext (by
      rw [hs, hs]
      congr 1
      refine Fintype.sum_equiv (Equiv.mulRight (e (γ p))) _ _ fun g => ?_
      rw [Equiv.coe_mulRight, map_mul, Module.End.mul_apply])
    rw [hY, map_add (f := _)] at h4
    exact add_eq_left.1 h4
private theorem opOf_gen {l q n : ℕ} (hl : l.Prime) (a : Fin q → ℕ) :
    Subgroup.closure (Set.range fun p : Fin q × Fin n => (Pi.mulSingle p (Multiplicative.ofAdd 1) : Del l n a)) = ⊤ := by
  haveI : ∀ p : Fin q × Fin n, NeZero (l ^ a p.1) := fun s => ⟨pow_ne_zero _ hl.ne_zero⟩
  refine eq_top_iff.2 fun g _ => ?_
  rw [← Finset.univ_prod_mulSingle g]
  refine Subgroup.prod_mem _ fun s _ => ?_
  have h1 : g s = Multiplicative.ofAdd (1 : ZMod (l ^ a s.1)) ^ (Multiplicative.toAdd (g s)).val := by
    rw [← ofAdd_nsmul, nsmul_one, ZMod.natCast_zmod_val, ofAdd_toAdd]
  rw [h1, Pi.mulSingle_pow]
  exact Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_range_self s)) _
private theorem opOf_cop {L : Type} [Field L] [NumberField L] (w : Plc L) {l : ℕ} (hl : l.Prime)
    (hw : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal) : l.Coprime (resCard (w.adicCompletion L)) := by
  have h1 : Valued.v (l : w.adicCompletion L) = 1 := by
    have e : (l : w.adicCompletion L) = algebraMap L _ (algebraMap (𝓞 L) L l) := by simp
    rw [e]
    refine (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _).trans ?_
    exact (HeightOneSpectrum.valuation_of_algebraMap w _).trans (HeightOneSpectrum.intValuation_eq_one_iff.2 hw)
  have h2 : valuation (w.adicCompletion L) (l : w.adicCompletion L) = 1 := by
    haveI : (Valued.v : Valuation (w.adicCompletion L) _).Compatible := Valuation.Compatible.ofValuation _
    exact (ValuativeRel.isEquiv (valuation (w.adicCompletion L)) Valued.v).eq_one_iff_eq_one.2 h1
  have h3 : IsUnit (l : 𝒪[w.adicCompletion L]) :=
    (Valuation.integer.integers _).isUnit_iff_valuation_eq_one.2 (by simpa using h2)
  have h4 : (l : 𝓀[w.adicCompletion L]) ≠ 0 := by
    simpa using (h3.map (residue 𝒪[w.adicCompletion L])).ne_zero
  rw [hl.coprime_iff_not_dvd]
  intro hd
  letI := Fintype.ofFinite 𝓀[w.adicCompletion L]
  haveI := Fact.mk hl
  rw [resCard, Nat.card_eq_fintype_card] at hd
  exact h4 ((ringChar.spec _ _).2 (by
    have h5 := (prime_dvd_char_iff_dvd_card l).2 hd
    have h6 := CharP.char_is_prime 𝓀[w.adicCompletion L] (ringChar 𝓀[w.adicCompletion L])
    rw [(Nat.prime_dvd_prime_iff_eq hl h6).1 h5]))
private theorem opOf_le {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
    (C : Subgroup 𝓀[k]ˣ) : iwC k n C ≤ iwC k n ⊤ := by
  have h1 : unitsC k C ≤ unitsC k ⊤ := Subgroup.map_mono (Subgroup.comap_mono le_top)
  have h2 : torC k n C ≤ torC k n ⊤ := fun t ht i hi => h1 (ht i hi)
  exact sup_le_sup_left (Subgroup.map_mono h2) _
private theorem opOf_tow {Λ R P : Type} [CommRing Λ] [CommRing R] [Algebra Λ R] [AddCommGroup P]
    [Module R P] [Module Λ P] [IsScalarTower Λ R P] (S : Submodule R P) : IsScalarTower Λ R S := inferInstance
theorem UpperTheory.V.Th.opOfX_alt :
    _root_.UpperTheory.V.Pa.LocPAlt → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (V0 : s.Lev) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V0.frame O n) (B : UniversalOrdinaryDeterminantRing r) (J : Ideal B.B) (D : ℕ) (b : TWBase (pairOf B.u) J Empty D) (V : s.Lev) (h : (globOf r V).Hom (globOf r V0)) (q : ℕ) (w : Fin q → Plc L) (A : LevMod b h w) (x δ : ∀ j, ((w j).adicCompletion L)ˣ), (∀ j, ((l : ℕ) : 𝓞 L) ∉ (w j).asIdeal) → (∀ j, IsUnif (x j)) → (∀ j, IsGenMod _ (ellC l _) (δ j)) → ∀ (ph ta : Fin q → (globOf r V).G₀) (N : ℕ), _root_.UpperTheory.V.Pa.Lev.LocalLevelConditions A x δ ph ta → (∀ j, qj w j ≡ 1 [MOD l ^ N]) → ∃ A' : OpMod b h q N, OpRelX A' (qj w) ph ta (2 * n.factorial) := by
  intro hP l hl L Ω _ _ _ _ _ _ s V0 O _ _ _ hO _ n r B J D b V h q w A x δ hw hx hδ ph ta N hok hN
  have hq : ∀ j, IsUnit (qj w j : A.R) := fun j => by
    haveI := hO.char
    have h1 : IsUnit (qj w j : ResidueField O) :=
      (CharP.isUnit_natCast_iff hl.out).2 (hl.out.coprime_iff_not_dvd.1 (opOf_cop (w j) hl.out (hw j)))
    have h2 : IsUnit (qj w j : O) := by
      rw [← map_natCast (residue O)] at h1
      exact (isUnit_map_iff _ _).1 h1
    simpa using h2.map (algebraMap O A.R)
  obtain ⟨T⟩ := thEx L n q w l A.R A.P A.ρ x δ hq
  obtain ⟨hn, ρ', hρ', hpr⟩ := A.proj
  obtain ⟨e, he⟩ := delIso L n q w l δ hδ
  obtain ⟨hy, tr, htr, hu⟩ := trOf L n q w l A.R A.P A.ρ x δ T hδ
  have h2 := _root_.UpperTheory.V.Z.Win.T2.level_relation_two_x hP l L Ω s V0 O n r B J D b V h q w A x δ hw hx hδ T ph ta hok
  have h3 := _root_.UpperTheory.V.Pa.Lev.twoOf_alt hP l L Ω s V0 O n r B J D b V h q w A x δ hw hx hδ T ph ta hok
  have hg : ∀ j i m, ρ' (e (Pi.mulSingle (j, i) (Multiplicative.ofAdd 1))) m = T.act1 (1 + yV A.R j i) m := fun j i m => by
    obtain ⟨g, hg1, hg2⟩ := he j i
    exact Subtype.ext (by rw [hg2, hρ', hg1]; exact (hy j i m).symm)
  have hle : UIw1 l n w ≤ UIw n w := fun g hg j hj => opOf_le _ (hg j hj)
  haveI : ∀ p : Fin q × Fin n, NeZero (l ^ padicValNat l (qj w p.1 - 1)) := fun s => ⟨pow_ne_zero _ hl.out.ne_zero⟩
  obtain ⟨hs, hk⟩ := opOf_tr A.ρ (UIw n w) (UIw1 l n w) hle ρ' hρ' hpr e
    (fun p : Fin q × Fin n => Pi.mulSingle p (Multiplicative.ofAdd 1)) (opOf_gen hl.out fun j => padicValNat l (qj w j - 1))
    (fun p : Fin q × Fin n => T.act1 (yV A.R p.1 p.2)) (fun p m => (hg p.1 p.2 m).trans (by rw [map_add (f := _), map_one]; rfl)) tr htr
  have ha : ∀ j, N ≤ padicValNat l (qj w j - 1) := fun j => by
    have h4 : 1 < qj w j := Finite.one_lt_card
    exact ((by simpa only [_root_.Nat.padicValNat_def] using @_root_.multiplicity_dvd_iff_le : ∀ {p : _root_.Nat} [hp : _root_.Fact (_root_.Nat.Prime p)] {a n : _root_.Nat} (ha : a ≠ 0), p ^ n ∣ a ↔ n ≤ _root_.padicValNat p a) (by omega)).1 ((Nat.modEq_iff_dvd' h4.le).1 (hN j).symm)
  exact ⟨{ rN := A.rN, compat := A.compat, R := A.R, p := A.p, segmentWeightExponent := A.segmentWeightExponent, β := A.β, β_pair := A.β_pair
           M1 := fixd A.ρ (UC n w fun _ => ellC l _), tow1 := opOf_tow _, fin1 := A.fin, Mw := fixd A.ρ (UC n w fun _ => ⊤)
           act1 := T.act1, actw := T.actw, a := fun j => padicValNat l (qj w j - 1), le_a := ha
           ρ := ρ'.comp e.toMonoidHom, ρ_gen := hg, proj := opOf_proj ρ' e hpr
           tr := tr, tr_surj := hs, tr_ker := hk, tr_u := hu }, h3, h2⟩
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.V.Th
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
theorem UpperTheory.V.Th.has_operator_statement :
    _root_.UpperTheory.V.Th.HasHeckeOperatorDense := by
  intro hP l _ L Ω _ _ _ _ _ _ s V0 O _ _ _ _ _ n r B J D b hb T Q
  refine ⟨2 * n.factorial, ?_⟩
  · skip
    intro N
    have hl : ∀ j, ((l : ℕ) : 𝓞 L) ∉ (Q.w N j).asIdeal := by
      intro j hj
      apply Q.v_not N j
      left
      have h1 := (Q.B_w N j (l : 𝓞 L)).2 hj
      refine (Q.B_v N j (l : 𝓞 (Lp L))).1 ?_
      simpa using h1
    obtain ⟨A, ι, hι⟩ := hb (Q.V N) (homComp (Q.e N) (T.h N)) T.q (Q.v N) (Q.w N) (Q.B N) (Q.e_h N) (Q.v_inj N) (Q.v_not N)
      (Q.S_eq N) (Q.B_w N) (Q.B_v N) (Q.split N)
    have hd := fun j => _root_.UpperTheory.V.Z.Win.locDataT_alt hP l L Ω (Q.B N j) (Q.w N j) (Q.B_w N j) (hl j) (Q.fr N j) (Q.τ N j) (Q.fr_dec N j)
      (Q.fr_frob N j) (Q.τ_gen N j)
    choose hq x δ hx hδ hrel using hd
    have hNq : T.Nq N = qj (Q.w N) := funext fun j => (Q.Nq N j).trans (hq j).symm
    have hok : _root_.UpperTheory.V.Pa.Lev.LocalLevelConditions A x δ (fun j => (Q.V N).pr (Q.fr N j)) (fun j => (Q.V N).pr (Q.τ N j)) :=
      ⟨ι, hι, fun y j => hrel j n ι (y.rep.comp (Q.V N).pr) (y.σ j) (y.lg j (Q.B N j) (Q.B_w N j))⟩
    obtain ⟨A1, h1⟩ := _root_.UpperTheory.V.Th.opOfX_alt hP l L Ω s V0 O n r B J _ b (Q.V N) _ T.q (Q.w N) A x δ hl hx hδ _ _ N hok
      (fun j => by rw [← hNq]; exact T.Nq_mod N j)
    obtain ⟨A2, h2⟩ := opTransportX l _ _ O n _ B.B _ J _ b _ _ (Q.e N) _ (T.h N) T.q N A1 _ _ _ _ (Q.e_inj N) (fun _ => rfl) h1
    have e1 : T.ph N = fun j => (Q.e N).p₀ ((Q.V N).pr (Q.fr N j)) := funext (Q.ph N)
    have e2 : T.ta N = fun j => (Q.e N).p₀ ((Q.V N).pr (Q.τ N j)) := funext (Q.ta N)
    rw [hNq, e1, e2]
    exact ⟨A2, h2⟩
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.V UpperTheory.V.Th
namespace UpperTheory.V.Th.NormTraceLemmas
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
private theorem coef_isCoef (l : ℕ) [hl : Fact l.Prime] (c : HV.Coef l) : Pa.IsCoef l c.O := by
  obtain ⟨hc, hf, hlm, -, -, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
  refine ⟨hc, hf, (CharP.charP_iff_prime_eq_zero hl.out).2 ?_⟩
  rw [← map_natCast (IsLocalRing.residue c.O), IsLocalRing.residue_eq_zero_iff]
  exact hlm
private theorem locP_of (P : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) : _root_.UpperTheory.V.Pa.LocPAlt :=
  ⟨P.loc.bz, P.loc.geo, GlobalTheory.Published.TameLocal_of_duality P.coh.lt⟩
private theorem chi_ofRep {n : ℕ} {A G : Type} [CommRing A] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) A) (g : G) :
    (GDet.ofRep ρ).chi (MonoidAlgebra.single g 1) = (ρ g).charpoly := by
  change (GDet.repAlg ρ (Polynomial A) _).det = _
  rw [map_sub, MonoidAlgebra.mapRingHom_single, Matrix.charpoly]
  congr 1
  ext i j : 2
  by_cases h : i = j <;> simp [GDet.repAlg, Matrix.charmatrix, h, Matrix.one_apply, Matrix.diagonal_apply]
private theorem map_ofRep {n : ℕ} {A B G : Type} [CommRing A] [CommRing B] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) A)
    (f : A →+* B) : (GDet.ofRep ρ).map f = GDet.ofRep (f.mapMatrix.toMonoidHom.comp ρ) := by
  refine GDet.ext fun C _ _ x => ?_
  letI : Algebra A C := ((algebraMap B C).comp f).toAlgebra
  change (GDet.repAlg ρ C x).det = (GDet.repAlg _ C x).det
  congr 2
private theorem unip_pow (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O] [CharP (ResidueField O) l] (n m : ℕ)
    (M : Matrix (Fin n) (Fin n) O) (hM : (M.map (residue O)).charpoly = (Polynomial.X - 1) ^ n) (i j : Fin n) :
    (M ^ l ^ (n + m) - 1) i j ∈ maximalIdeal O ^ m := by
  have hl : l.Prime := Fact.out
  haveI : Nonempty (Fin n) := ⟨i⟩
  have h0 := Matrix.aeval_self_charpoly (M.map (residue O))
  rw [hM] at h0
  simp only [map_pow, map_sub, Polynomial.aeval_X, map_one] at h0
  have h1 : (residue O).mapMatrix (M ^ l ^ n) = 1 := by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Nat.lt_pow_self hl.one_lt (n := n)).le
    have h4 := sub_pow_char_pow_of_commute l n (Commute.one_right (M.map (residue O)))
    rw [one_pow] at h4
    rw [map_pow, ← sub_eq_zero]
    refine h4.symm.trans ?_
    rw [hd, pow_add, h0, zero_mul]
  have h2 : ∀ k, (residue O).mapMatrix (M ^ l ^ (n + k)) = 1 := fun k => by
    rw [pow_add, pow_mul, map_pow, h1, one_pow]
  induction m generalizing i j with
  | zero => simp
  | succ k ih =>
    rw [← add_assoc, pow_succ l, pow_mul, ← mul_geom_sum, Matrix.mul_apply, pow_succ]
    refine Ideal.sum_mem _ fun a _ => Ideal.mul_mem_mul (ih i a) ?_
    have h3 : (residue O).mapMatrix (∑ t ∈ Finset.range l, (M ^ l ^ (n + k)) ^ t) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_pow (residue O).mapMatrix (M ^ l ^ (n + k)), h2, one_pow]
      simp
    exact (residue_eq_zero_iff _).1 (congrFun (congrFun h3 a) j)
private theorem rhoPLO (l : ℕ) [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [CharP (ResidueField O) l] (n : ℕ) (ρ : F.G₀ →* GL (Fin n) O)
    (hc : ∀ i j, AdicCont (maximalIdeal O) fun g => mat ρ g i j) (H : OpenNormalSubgroup F.Γ)
    (hH : ∀ g ∈ H, ∃ h : F.η g = 1, ((mat ρ ⟨g, h⟩).map (residue O)).charpoly = (Polynomial.X - 1) ^ n)
    (g : F.G₀) (hg : (g : F.Γ) ∈ PL l H.toSubgroup) : ρ g = 1 := by
  have key : ∀ (m : ℕ) (i j : Fin n), (mat ρ g - 1) i j ∈ maximalIdeal O ^ m := by
    intro m
    let π := Ideal.Quotient.mk (maximalIdeal O ^ m)
    let Km : Subgroup F.G₀ := (π.mapMatrix.toMonoidHom.comp (mat ρ)).toHomUnits.ker
    have hKm : ∀ a : F.G₀, a ∈ Km ↔ ∀ i j, π (mat ρ a i j) = π ((1 : Matrix (Fin n) (Fin n) O) i j) := by
      intro a
      rw [MonoidHom.mem_ker, Units.ext_iff, MonoidHom.coe_toHomUnits, Units.val_one, ← map_one π.mapMatrix,
        ← Matrix.ext_iff]
      rfl
    have hKm' : ∀ a : F.G₀, a ∈ Km ↔ ∀ i j, (mat ρ a - 1) i j ∈ maximalIdeal O ^ m := by
      intro a
      simp only [hKm, Matrix.sub_apply, π, Ideal.Quotient.eq]
    have ho : IsOpen (Km : Set F.G₀) := by
      have : (Km : Set F.G₀) = ⋂ i, ⋂ j, {a | π (mat ρ a i j) = π ((1 : Matrix (Fin n) (Fin n) O) i j)} := by
        ext a
        simp only [SetLike.mem_coe, hKm, Set.mem_iInter, Set.mem_setOf_eq]
      rw [this]
      exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => (hc i j m).isOpen_fiber _
    let K' : Subgroup F.Γ := Km.map F.η.ker.subtype
    have ho' : IsOpen (K' : Set F.Γ) := F.η_open.isOpenMap_subtype_val _ ho
    haveI : Finite (F.Γ ⧸ K') := Subgroup.quotient_finite_of_isOpen K' ho'
    haveI : K'.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    have hc : IsOpen (K'.normalCore : Set F.Γ) :=
      Subgroup.isOpen_of_isClosed_of_finiteIndex _ (K'.normalCore_isClosed (K'.isClosed_of_isOpen ho'))
    let U : OpenNormalSubgroup F.Γ := ⟨⟨K'.normalCore, hc⟩, K'.normalCore_normal⟩
    have hU : ∀ h ∈ H.toSubgroup, ∃ e : ℕ, h ^ l ^ e ∈ U := by
      intro h hh
      refine ⟨n + m, fun b => ?_⟩
      obtain ⟨h1, h2⟩ := hH (b * h * b⁻¹) (H.isNormal'.conj_mem h hh b)
      refine ⟨(⟨b * h * b⁻¹, h1⟩ : F.G₀) ^ l ^ (n + m), ?_, ?_⟩
      · rw [SetLike.mem_coe, hKm', map_pow]
        exact unip_pow l O n m _ h2
      · simp only [Subgroup.coe_subtype, SubgroupClass.coe_pow, conj_pow]
    have h3 : (g : F.Γ) ∈ K'.normalCore := Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hg U) hU
    obtain ⟨a, ha, hag⟩ := K'.normalCore_le h3
    obtain rfl : a = g := Subtype.ext hag
    exact (hKm' a).1 ha
  apply Units.ext
  ext1 i j
  have h0 : (mat ρ g - 1) i j ∈ (⨅ m : ℕ, maximalIdeal O ^ m) := Ideal.mem_iInf.2 fun m => key m i j
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal O).ne_top, Ideal.mem_bot, Matrix.sub_apply,
    sub_eq_zero] at h0
  exact h0
private theorem red_unip {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] [Algebra ℤ_[l] O] {n : ℕ} {r : Resid F O n} {B : Type} [CommRing B] [Algebra O B]
    [IsCO O B] (u : Pair r B) (x : B →ₐ[O] O) (ρ : F.G₀ →* GL (Fin n) O) (h : u.D.map x.toRingHom = GDet.ofRep (mat ρ))
    (g : F.G₀) (hg : ∀ i, r.chib i g = 1) : ((mat ρ g).map (residue O)).charpoly = (Polynomial.X - 1) ^ n := by
  have e0 : (residue O).comp x.toRingHom = (res O B : B →+* ResidueField O) := RingHom.ext fun a =>
    ((res O O).commutes (x a)).symm.trans (res_map x a)
  have e3 : (GDet.ofRep (mat ρ)).map (residue O) = r.Dbar := by
    rw [← h, ← u.red, ← e0]
    rfl
  rw [map_ofRep, Resid.Dbar] at e3
  have e4 := congrArg (·.chi (MonoidAlgebra.single g 1)) e3
  simp only [chi_ofRep] at e4
  refine e4.trans ?_
  have e5 : W.diagRep r.chib g = 1 := by
    change Matrix.diagonal _ = _
    simp only [hg, Units.val_one, Matrix.diagonal_one]
  rw [e5, Matrix.charpoly_one, Fintype.card_fin]
end UpperTheory.V.Th.NormTraceLemmas
open UpperTheory.V.Th.NormTraceLemmas UpperTheory.V.Pa UpperTheory.V.W UpperTheory.V.Alg in
theorem UpperTheory.V.Th.core_o_of_literal_automorphy_n :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → _root_.UpperTheory.V.Th.OrdinaryMainCase := by
  intro hN l _ L Ω _ _ _ _ _ _ s V0 c n r B J y x h q sg al hS hn hLev hJ hAr hmap hN4 hsg hdet δ hδ h0
  have hC : Pa.CohP := ⟨hN.coh.lf, hN.coh.lt, hN.coh.le, hN.coh.gf, hN.coh.ge, hN.coh.gw, hN.coh.pt,
    GlobalTheory.Published.TameLocal_of_duality hN.coh.lt⟩
  haveI := coef_isCoef l c
  haveI := IsCoef.char (l := l) (O := c.O)
  haveI := IsCoef.finite (l := l) (O := c.O)
  haveI := IsCoef.complete (l := l) (O := c.O)
  obtain ⟨b, hb, hγ, hctrl⟩ := hLev
  obtain ⟨T, ⟨Pl⟩, rfl, hTs⟩ := (arPl hC l L Ω s V0 c.O n r hS).2 q sg fun j => (hsg j).1
  obtain rfl : T.sg = sg := funext hTs
  have hI := (ipEq l L Ω s V0 c.O n r).1
  have hgen : GenBy c.O (pairVals (pairOf B.u)) := fun N b => by
    obtain ⟨c, hc, hb⟩ := CA.exists_adjoin_coeff_character_sub_mem_maximalIdeal_pow r B N b
    refine ⟨c, Algebra.adjoin_mono ?_ hc, hb⟩
    rintro _ (⟨a, g, -, -, rfl⟩ | e)
    · exact Or.inl ⟨a, g, rfl⟩
    · exact Or.inr e
  have hmap' : (pairOf B.u).Maps x.toRingHom (GDet.ofRep (mat y.ρ)) y.ψ := hmap
  have hker : ∀ g : V0.frame.G₀, (g : V0.frame.Γ) ∈ PL l T.H.toSubgroup → y.ρ g = 1 := by
    refine rhoPLO l (globOf r V0).frame c.O n y.ρ y.cont T.H fun g hg => ?_
    obtain ⟨e1, e2, -⟩ := (Pl.H_eq g).1 hg
    exact ⟨e1, red_unip (pairOf B.u) x y.ρ hmap'.1 ⟨g, e1⟩ e2⟩
  have heig : Eig y T al := fun j => (hsg j).2
  exact count l _ (globOf r V0) T n c.O (residOf r) B.B (pairOf B.u) J _ b y x al s.odd hn
    ⟨fun g hg a => ((Pl.H_eq g).1 hg).2.1 a, fun u => (hI u).2⟩
    (_root_.UpperTheory.V.Th.has_operator_statement (locP_of hN) l L Ω s V0 c.O n r B J _ b hb T Pl) hgen hmap' hJ
    (etOf l _ (globOf r V0) n c.O (residOf r) B.B (pairOf B.u) J _ b y x hn hmap' hgen (hctrl x h hAr)) hker heig
    (b1O hC l L Ω s V0 c n r T Pl y al hS (W.locCFT hN.aut.art hC l L Ω s) hn hker hN4 heig hdet)
    δ hδ fun k => h0 _ _ _ (hγ k)
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open IsLocalRing Matrix NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th UpperTheory.V.Th.Nm GlobalTheory.GalOfCusp
private theorem ofRep_comap {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (ρ : G →* GL (Fin n) A) (φ : H →* G) :
    (GDet.ofRep (mat ρ)).comap φ = GDet.ofRep (mat (ρ.comp φ)) := by
  refine GDet.ext fun B _ _ x => ?_
  change (GDet.repAlg (mat ρ) B (MonoidAlgebra.mapDomainRingHom B φ x)).det = (GDet.repAlg (mat (ρ.comp φ)) B x).det
  congr 1
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | single g r => simp [GDet.repAlg, mat]
private theorem tr_cj {n : ℕ} {K : Type} [Field K] (Q A : GL (Fin n) K) (Z : Matrix (Fin n) (Fin n) K) (a : K) (ha : a ≠ 0)
    (h : ((a • (((Q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Z * Q)) * ((Q⁻¹ * A * Q : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).trace = 0) :
    (Z * (A : Matrix (Fin n) (Fin n) K)).trace = 0 := by
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, mul_eq_zero, or_iff_right ha] at h
  have e : ((Q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Z * Q * ((Q⁻¹ * A * Q : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((Q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (Z * A) * Q := by
    simp only [Units.val_mul, Matrix.mul_assoc, Units.mul_inv_cancel_left]
  rwa [e, Matrix.trace_mul_cycle, Units.mul_inv, Matrix.one_mul] at h
private theorem mat_push {n : ℕ} {A B G : Type} [CommRing A] [CommRing B] [Group G] (f : A →+* B) (ρ : G →* GL (Fin n) A) :
    f.mapMatrix.toMonoidHom.comp (mat ρ) = mat (pushRep f ρ) := rfl
private theorem mat_push' {n : ℕ} {A B G : Type} [CommRing A] [CommRing B] [Group G] (f : A →+* B) (ρ : G →* GL (Fin n) A) (g : G) :
    (mat ρ g).map f = (pushRep f ρ g : Matrix (Fin n) (Fin n) B) := rfl
private theorem map_pt {n : ℕ} {O R K G : Type} [CommRing O] [CommRing R] [CommRing K] [Algebra O R] [Algebra O K] [Group G]
    (D : GDet n R G) (x : R →ₐ[O] O) (ρ : G →* GL (Fin n) O) (h : D.map x.toRingHom = GDet.ofRep (mat ρ)) :
    D.map (((Algebra.ofId O K).comp x : R →ₐ[O] K) : R →+* K) = GDet.ofRep (mat (pushRep (algebraMap O K) ρ)) := by
  have e1 := (CA.d_gmap D).2.1 x.toRingHom (algebraMap O K)
  rw [h, (CA.d_gmap (GDet.ofRep (mat ρ))).2.2.2 (algebraMap O K) (mat ρ), mat_push] at e1
  exact e1.symm
private theorem map_ch {O R K G : Type} [CommRing O] [CommRing R] [CommRing K] [Algebra O R] [Algebra O K] [Group G]
    (χ : G →* Rˣ) (x : R →ₐ[O] O) (χ' : G →* Oˣ) (h : pushCh x.toRingHom χ = χ') :
    pushCh (((Algebra.ofId O K).comp x : R →ₐ[O] K) : R →+* K) χ = pushCh (algebraMap O K) χ' := by
  subst h
  rfl
private theorem tr_fin {n : ℕ} {O K : Type} [CommRing O] [Field K] (f : O →+* K) (Q A : GL (Fin n) K) (Z : Matrix (Fin n) (Fin n) K) (a : K)
    (ha : a ≠ 0) (Z₀ A₀ : Matrix (Fin n) (Fin n) O)
    (h1 : Z₀.map f = a • (((Q⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * Z * Q))
    (h2 : A₀.map f = ((Q⁻¹ * A * Q : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) (h : (Z₀ * A₀).trace = 0) :
    (Z * (A : Matrix (Fin n) (Fin n) K)).trace = 0 := by
  have e2 := congrArg f h
  rw [map_zero, AddMonoidHom.map_trace f, Matrix.map_mul, h1, h2] at e2
  exact tr_cj Q A Z a ha e2
private theorem re_form {l : ℕ} [Fact l.Prime] {n : ℕ} (F : GFrame l) (I : F.St → Subgroup F.G₀) (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [CommRing K] [Algebra O K]
    (ρ : F.G₀ →* GL (Fin n) K) (P : GL (Fin n) K) (h : F.IsForm O n ρ P) : (reIu F I).IsForm O n ρ P := h
private theorem re_coc {l : ℕ} [Fact l.Prime] {n : ℕ} (F : GFrame l) (I : F.St → Subgroup F.G₀) (ρ : F.G₀ →* GL (Fin n) (Qbar l)) (P : GL (Fin n) (Qbar l)) (ψ : ∀ v, Fin n → F.Gv v →* (Qbar l)ˣ) (z : F.G₀ → Matrix (Fin n) (Fin n) (Qbar l))
    (h : IsOrdCoc F ρ P I ψ z) : IsOrdCoc (reIu F I) ρ P (reIu F I).Iu ψ z := ⟨h.cont, h.coc, h.pol, h.ine, h.ord⟩
private theorem modelF {l : ℕ} [Fact l.Prime] {n : ℕ} (F : GFrame l) (I : F.St → Subgroup F.G₀) (c : Coef l) (ρ : F.G₀ →* GL (Fin n) (Qbar l)) (P : GL (Fin n) (Qbar l)) (ψ : ∀ v, Fin n → F.Gv v →* (Qbar l)ˣ) (z : F.G₀ → Matrix (Fin n) (Fin n) (Qbar l)) (q : ℕ) (sg : Fin q → F.G₀) (h1 : Continuous ρ)
    (h2 : Submodule.span (Qbar l) (Set.range (mat ρ)) = ⊤) (h3 : F.IsForm c.O n ρ P)
    (h4 : (P : Matrix (Fin n) (Fin n) (Qbar l))ᵀ = P ∨ (P : Matrix (Fin n) (Fin n) (Qbar l))ᵀ = -P) (h5 : ∀ u, ∀ g ∈ I u, ρ g = 1)
    (h6 : ∀ v, ∃ g, Function.Injective fun i => ψ v i g) (h7 : ∀ v i j, i < j → ψ v i ≠ ψ v j * (F.eps c.O (Qbar l)).comp (F.φ v))
    (h8 : IsOrdCoc F ρ P I ψ z) (h9 : ∀ g, IntM (mat ρ g)) (h10 : IntM (P : Matrix (Fin n) (Fin n) (Qbar l)))
    (h11 : IntM ((P⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l))) (h12 : ∀ j, (mat ρ (sg j)).charpoly.Separable) (c₁ : Coef l) :
    ∃ (c' : Coef l) (y : Pt (reIu F I) c'.O n) (z₀ : F.G₀ → Matrix (Fin n) (Fin n) c'.O) (a : Qbar l) (al : Fin q → Fin n → c'.O),
      c₁.O ≤ c'.O ∧ IsModel y ρ P ψ ∧ a ≠ 0 ∧ (∀ g, (z₀ g).map (algebraMap c'.O (Qbar l)) = a • z g) ∧ OCoc y z₀ ∧
      ∀ j, Function.Injective (al j) ∧ (mat y.ρ (sg j)).charpoly = ∏ i, (Polynomial.X - Polynomial.C (al j i)) :=
  model (reIu F I) c ρ P ψ z q sg h1 h2 (re_form F I _ _ ρ P h3) h4 h5 h6 h7 (re_coc F I ρ P ψ z h8) h9 h10 h11 h12 c₁
private theorem shr2 {l : ℕ} [Fact l.Prime] {n : ℕ} {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
    [Algebra O (Qbar l)] {r : Resid F O n} (B : UniversalOrdinaryDeterminantRing r) (x : B.B →ₐ[O] O) {I : F.St → Subgroup F.G₀} (y : Pt (reIu F I) O n)
    (ρ₀ : F.G₀ →* GL (Fin n) O) (ψ₀ : ∀ v, Fin n → F.Gv v →* Oˣ) (e1 : @Eq (F.G₀ →* GL (Fin n) O) y.ρ ρ₀)
    (e2 : @Eq (∀ v, Fin n → F.Gv v →* Oˣ) y.ψ ψ₀) {q : ℕ} (sg : Fin q → F.G₀) (al : Fin q → Fin n → O)
    (h1 : B.u.Maps x.toRingHom (GDet.ofRep (mat ρ₀)) ψ₀)
    (h2 : ∀ Z : Matrix (Fin n) (Fin n) O, (∀ g ∈ F.D0, ((F.eps O O g : Oˣ) : O) • (mat ρ₀ g * Z) = Z * mat ρ₀ g) → Z = 0)
    (h3 : ∀ j, Function.Injective (al j) ∧ (mat ρ₀ (sg j)).charpoly = ∏ i, (Polynomial.X - Polynomial.C (al j i)))
    (h4 : DetQ F O (pushRep (algebraMap O (Qbar l)) ρ₀) (GeneralLinearGroup.map (algebraMap O (Qbar l)) y.P) (Set.range sg))
    (I' : F.St → Subgroup F.G₀) (h : ∀ u, I' u ≤ I u) : ∃ y : Pt (reIu F I') O n,
        B.u.Maps x.toRingHom (GDet.ofRep (mat y.ρ)) y.ψ ∧ y.N4 F.D0 ∧
        (∀ j, Function.Injective (al j) ∧ (mat y.ρ (sg j)).charpoly = ∏ i, (Polynomial.X - Polynomial.C (al j i))) ∧
        DetQ (reIu F I') O (pushRep (algebraMap O (Qbar l)) y.ρ) (GeneralLinearGroup.map (algebraMap O (Qbar l)) y.P) (Set.range sg) := by
  subst e1 e2
  exact ⟨shrink y I' h, h1, h2, h3, h4⟩
private theorem detq_tr' {l : ℕ} [Fact l.Prime] {n : ℕ} (F : GFrame l) (O O' : Type) [CommRing O] [Algebra ℤ_[l] O]
    [Algebra O (Qbar l)] [CommRing O'] [Algebra ℤ_[l] O'] [Algebra O' (Qbar l)]
    (e : (algebraMap O (Qbar l)).comp (algebraMap ℤ_[l] O) = (algebraMap O' (Qbar l)).comp (algebraMap ℤ_[l] O'))
    (ρ : F.G₀ →* GL (Fin n) (Qbar l)) (P : GL (Fin n) (Qbar l)) (S : Set F.G₀) (h : DetQ F O ρ P S) : DetQ F O' ρ P S := by
  have e' : F.eps O (Qbar l) = F.eps O' (Qbar l) := by rw [GFrame.eps, GFrame.eps, e]
  unfold DetQ at h
  rw [e'] at h
  exact h
private theorem pairF {l : ℕ} [Fact l.Prime] {n : ℕ} (F : GFrame l) (c : Coef l) (r : Resid F c.O n) (I : F.St → Subgroup F.G₀)
    (hI : I = r.Ip) (y : Pt (reIu F I) c.O n) (z : F.G₀ → Matrix (Fin n) (Fin n) c.O) [IsCO c.O c.O] [IsCO c.O (DualNumber c.O)]
    (ρ₀ : F.G₀ →* GL (Fin n) c.O) (ψ₀ : ∀ v, Fin n → F.Gv v →* c.Oˣ) (e1 : @Eq (F.G₀ →* GL (Fin n) c.O) y.ρ ρ₀)
    (e2 : @Eq (∀ v, Fin n → F.Gv v →* c.Oˣ) y.ψ ψ₀) (hn : 1 ≤ n) (hO : OCoc y z)
    (h1 : (GDet.ofRep (mat ρ₀)).map (res c.O c.O : c.O →+* ResidueField c.O) = r.Dbar) (h2 : ∀ v i, r.IsPsi v i (ψ₀ v i)) :
    ∃ p : Pair r (DualNumber c.O), p.Maps (TrivSqZeroExt.fstHom c.O c.O c.O : DualNumber c.O →+* c.O) (GDet.ofRep (mat ρ₀)) ψ₀ ∧
      (∀ g, (p.D.tr (MonoidAlgebra.single g 1)).snd = (z g * mat ρ₀ g).trace) ∧
      ∀ v i, ∀ g ∈ F.Iv v, ((p.ψ v i g : (DualNumber c.O)ˣ) : DualNumber c.O).snd = 0 := by
  subst e1 e2 hI
  exact pairDual F c r y z hn hO h1 h2
private theorem modelG {l : ℕ} [Fact l.Prime] {n : ℕ} (F : GFrame l) (I : F.St → Subgroup F.G₀) (c : Coef l) (y : Pt (reIu F I) c.O n)
    (ρ : F.G₀ →* GL (Fin n) (Qbar l)) (P : GL (Fin n) (Qbar l)) (ψ : ∀ v, Fin n → F.Gv v →* (Qbar l)ˣ) (h : IsModel y ρ P ψ)
    {q : ℕ} (sg : Fin q → F.G₀) (al : Fin q → Fin n → c.O)
    (hal : ∀ j, Function.Injective (al j) ∧ (mat y.ρ (sg j)).charpoly = ∏ i, (Polynomial.X - Polynomial.C (al j i))) :
    ∃ (ρ₀ : F.G₀ →* GL (Fin n) c.O) (ψ₀ : ∀ v, Fin n → F.Gv v →* c.Oˣ), @Eq (F.G₀ →* GL (Fin n) c.O) y.ρ ρ₀ ∧
      @Eq (∀ v, Fin n → F.Gv v →* c.Oˣ) y.ψ ψ₀ ∧ pushRep (algebraMap c.O (Qbar l)) ρ₀ = ρ ∧
      GeneralLinearGroup.map (algebraMap c.O (Qbar l)) y.P = P ∧ (∀ v i, pushCh (algebraMap c.O (Qbar l)) (ψ₀ v i) = ψ v i) ∧
      ∀ j, Function.Injective (al j) ∧ (mat ρ₀ (sg j)).charpoly = ∏ i, (Polynomial.X - Polynomial.C (al j i)) :=
  ⟨y.ρ, y.ψ, rfl, rfl, h.1, h.2.1, h.2.2, hal⟩
private theorem nmAbs {l : ℕ} [Fact l.Prime] {n : ℕ} (F : GFrame l) (c : Coef l) (r : Resid F c.O n) (B : UniversalOrdinaryDeterminantRing r)
    (x : B.B →ₐ[c.O] Qbar l) (ρ : F.G₀ →* GL (Fin n) (Qbar l)) (P : GL (Fin n) (Qbar l)) (hn : 1 ≤ n) (h0 : r.V0ok)
    (hD : B.u.D.map (x : B.B →+* Qbar l) = GDet.ofRep (mat ρ)) (hc : Continuous ρ)
    (hsp : Submodule.span (Qbar l) (Set.range (mat ρ)) = ⊤) (hform : F.IsForm c.O n ρ P)
    (ψ : ∀ v, Fin n → F.Gv v →* (Qbar l)ˣ) (hψ : ∀ v i, ψ v i = pushCh (x : B.B →+* Qbar l) (B.u.ψ v i))
    (hreg : ∀ v, ∃ g, Function.Injective fun i => ψ v i g)
    (hN1 : ∀ v i j, i < j → ψ v i ≠ ψ v j * (F.eps c.O (Qbar l)).comp (F.φ v))
    (q : ℕ) (sg : Fin q → F.G₀) (hsg : ∀ j, (mat ρ (sg j)).charpoly.Separable) (hdet : DetQ F c.O ρ P (Set.range sg))
    (z : F.G₀ → Matrix (Fin n) (Fin n) (Qbar l)) (hz : IsOrdCoc F ρ P r.Ip ψ z)
    (hB : ∀ (c' : Coef l) (r' : Resid F c'.O n) (R : Type) [CommRing R] [Algebra c'.O R] [IsCO c'.O R], Nonempty (Pair r' R) → Nonempty (UniversalOrdinaryDeterminantRing r')) :
    ∃ (c' : Coef l) (r' : Resid F c'.O n) (B' : UniversalOrdinaryDeterminantRing r') (x' : B'.B →ₐ[c'.O] c'.O) (δ : B'.B →ₗ[c'.O] c'.O) (al : Fin q → Fin n → c'.O),
      B'.u.D.map (((Algebra.ofId c'.O (Qbar l)).comp x' : B'.B →ₐ[c'.O] Qbar l) : B'.B →+* Qbar l) = GDet.ofRep (mat ρ) ∧
      (∀ v i, pushCh (((Algebra.ofId c'.O (Qbar l)).comp x' : B'.B →ₐ[c'.O] Qbar l) : B'.B →+* Qbar l) (B'.u.ψ v i) = ψ v i) ∧
      IsDer x' δ ∧ (∀ v i, ∀ g ∈ F.Iv v, δ (B'.u.ψ v i g : B'.Bˣ) = 0) ∧
      ((∀ g, δ (B'.u.D.tr (MonoidAlgebra.single g 1)) = 0) → ∃ Y, ∀ g, z g = dY F (mat ρ) Y g) ∧
      ∀ I : F.St → Subgroup F.G₀, (∀ u, I u ≤ r'.Ip u) → ∃ y : Pt (reIu F I) c'.O n,
        B'.u.Maps x'.toRingHom (GDet.ofRep (mat y.ρ)) y.ψ ∧ y.N4 F.D0 ∧
        (∀ j, Function.Injective (al j) ∧ (mat y.ρ (sg j)).charpoly = ∏ i, (Polynomial.X - Polynomial.C (al j i))) ∧
        DetQ (reIu F I) c'.O (pushRep (algebraMap c'.O (Qbar l)) y.ρ) (GeneralLinearGroup.map (algebraMap c'.O (Qbar l)) y.P) (Set.range sg) := by
  obtain ⟨Q, P', hP', hsgn, hP1, hP2, hint⟩ := selfDual F c ρ P hc hsp hform
  obtain ⟨k1, k2, k3, k4, k5, k6, k7⟩ := conjAll F c ρ P Q P' hP'
  have hD' : B.u.D.map (x : B.B →+* Qbar l) = GDet.ofRep (mat (cj Q ρ)) := hD.trans k4.symm
  have hine := (Ws.Eb.relKill B x (cj Q ρ) (k2 hsp) hD').2
  obtain ⟨c₂, hc₂, hx₂⟩ := ((GradeZeroInterpolatingElement.coPt c B.B).1 x).1
  have hz' := k7 _ _ _ hz
  have hs : ∀ j, (mat (cj Q ρ) (sg j)).charpoly.Separable := fun j => by rw [k5]; exact hsg j
  have hm := modelF F r.Ip c (cj Q ρ) P' ψ _ q sg (k1 hc) (k2 hsp) (k3 hform) hsgn hine hreg hN1 hz' hint hP1 hP2 hs c₂
  obtain ⟨c', y, z₀, a, al, hle, hM, ha, hz₀, hO, hal'⟩ := hm
  obtain ⟨ρ₀, ψ₀, e1, e2, m1, m2, m3, hal⟩ := modelG F r.Ip c' y _ _ _ hM sg al hal'
  obtain ⟨r', hr', hIp, hV0⟩ := residPush F c c' (hc₂.trans hle) r
  haveI := (abelian₂.dvr_finite l c'.O).1
  haveI : IsCO c'.O (DualNumber c'.O) := co_sqz c'.O c'.O c'.O fun _ => rfl
  obtain ⟨hred, hpsi⟩ := redOf F c c' _ r r' B.B B.u x ρ₀ ψ₀ hr' (fun b => hle (hx₂ b))
    (hD'.trans (congrArg (fun t => GDet.ofRep (mat t)) m1.symm)) fun v i => (m3 v i).trans (hψ v i)
  obtain ⟨p, hp1, hp2, hp3⟩ := pairF F c' r' r.Ip (funext hIp).symm y z₀ ρ₀ ψ₀ e1 e2 hn hO hred hpsi
  obtain ⟨B'⟩ := hB c' r' _ ⟨p⟩
  obtain ⟨x', δ, hδ, hx', hδ1, hδ2⟩ := derOf F c'.O r' B' p _ _ hp1
  have h4 := detq_tr' F c.O c'.O ((IsScalarTower.algebraMap_eq _ _ _).symm.trans (IsScalarTower.algebraMap_eq _ _ _)) _ _ _ (k6 _ hdet)
  rw [← m1, ← m2] at h4
  refine ⟨c', r', B', x', δ, al, ?_, fun v i => ?_, hδ, fun v i g hg => (hδ2 v i g).trans (hp3 v i g hg), fun key => ?_,
    fun I hI => shr2 B' x' y ρ₀ ψ₀ e1 e2 sg al hx' (n4 F c'.O r' ρ₀ (hV0 h0) hred) hal h4 I fun u => (hI u).trans (hIp u).le⟩
  · exact (map_pt B'.u.D x' ρ₀ hx'.1).trans ((congrArg (fun t => GDet.ofRep (mat t)) m1).trans k4)
  · exact (map_ch _ x' _ (hx'.2 v i)).trans (m3 v i)
  · refine trZero ρ z hsp hz.coc fun g => tr_fin (algebraMap c'.O (Qbar l)) Q (ρ g) (z g) a ha (z₀ g) (mat ρ₀ g) (hz₀ g) ?_
      ((hp2 g).symm.trans ((hδ1 g).symm.trans (key g)))
    exact (mat_push' _ _ g).trans (congrArg Units.val ((DFunLike.congr_fun m1 g).trans (cj_apply Q ρ g)))
theorem UpperTheory.V.Th.ordinary_vanishing_two_of_printed_hida :
    _root_.UpperTheory.V.Af.HypothesesH' → _root_.UpperTheory.V.Th.OrdVan2Alt := by
  intro hP l _ L Ω _ _ _ _ _ _ s V c n r B ι x h ρ P hS hn2 hn4 h0 hA hD hc haut hsp hform hI0 hN1 ⟨q, sg, hsg, hdet⟩ z hz
  have hn : 1 ≤ n := by omega
  have hN := hP.litN
  have hC : Pa.CohP := ⟨hN.coh.lf, hN.coh.lt, hN.coh.le, hN.coh.gf, hN.coh.ge, hN.coh.gw, hN.coh.pt,
    GlobalTheory.Published.TameLocal_of_duality hN.coh.lt⟩
  have heps : ∀ v : V.frame.Vl, (V.frame.eps c.O (Qbar l)).comp (V.frame.φ v) =
      (cycBar L Ω l).comp (Dec (F := L) (s.A (Subtype.val v))).subtype := fun v => MonoidHom.ext fun g => by
    have e : V.ε (toGS Ω V.S' (W.resP L Ω g.1)) = cycZ (W.Lp L) Ω l (W.resP L Ω g.1) := DFunLike.congr_fun V.hε _
    apply Units.ext
    change algebraMap c.O (PadicAlgCl l) (algebraMap ℤ_[l] c.O (V.ε (toGS Ω V.S' (W.resP L Ω g.1)) : ℤ_[l]ˣ)) = _
    rw [e]
    rfl
  obtain ⟨c', r', B', x', δ, al, hDx, hψ', hδ, hδ2, hfin, hy⟩ := nmAbs V.frame c r B x ρ P hn h0 hD hc hsp hform x.psi (fun _ _ => rfl)
    (fun v => _root_.UpperTheory.V.Th.Nm.regular_arithmetic_hida_of_literal_automorphy hN s h v (x.psi v) hA.1 (hA.2 v)) (fun v i j _ e => hN1 v i j (e.trans (congrArg _ (heps v))))
    q sg (fun j => (hsg j).2) hdet z hz fun c' r' R _ _ _ => b0Ex (phiAll hC) l L Ω s V c' n r' R
  obtain ⟨Λ', -⟩ := lamEx (W.locCFT hN.aut.art hC) l L Ω s V c' n r'
  obtain ⟨J, hJ, hLev⟩ := _root_.UpperTheory.V.Th.hida_x_of_printed_hida hP l L Ω s V hS c' n hn r' B' Λ' ι
  have hψ : (barPt B' x').psi = x.psi := funext fun v => funext fun i => hψ' v i
  have hAr : (barPt B' x').Arith h := ⟨hA.1, fun v j => by rw [hψ]; exact hA.2 v j⟩
  have hR : (barPt B' x').IsRep (ρ.comp V.pr) :=
    (congrArg (fun D => GDet.comap D V.pr) hDx).trans (ofRep_comap ρ V.pr)
  have hF : ∀ v : Vl l L, HasFlag ((ρ.comp V.pr).comp (Dec (F := L) (s.A v)).subtype) (x.psi v) := fun v => by
    obtain ⟨w, Y, hw⟩ := hz.ord v
    exact ⟨w⁻¹, fun g => by rw [inv_inv]; exact ⟨(hw g).1, (hw g).2.1⟩⟩
  have hJx : J ≤ RingHom.ker (barPt B' x') :=
    hJ _ h (ρ.comp V.pr) hn2 hn4 hAr hR (hc.comp (V.pr_cont continuous_resP)) haut (fun g hg => hI0 _ ⟨g, hg, rfl⟩)
      fun v => by rw [hψ]; exact ⟨hF v, hN1 v⟩
  obtain ⟨y, y1, y2, y3, y4⟩ := hy (globOf r' V).frame.Iu fun u => by
    rintro g ⟨γ, ⟨h1, h2⟩, rfl⟩
    exact ⟨⟨Subtype.val γ, h1, rfl⟩, Subgroup.mem_iInf.2 fun i => Subgroup.mem_iInf.1 h2 i⟩
  exact hfin (_root_.UpperTheory.V.Th.core_o_of_literal_automorphy_n hN l L Ω s V c' n r' B' J y x' h q sg al hS hn hLev (fun b hb => Subtype.ext (hJx hb)) hAr y1 y2
    (fun j => ⟨(hsg j).1, y3 j⟩) y4 δ hδ hδ2)
end
