module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugateEmbApply
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsOpenKerFinIdele

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniversalAnticyclotomicCharacterLaws
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.FrobeniusOrbits GlobalTheory.HeckeGal

namespace GlobalTheory.GalChar

theorem isTorsionFree_field (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] : Module.IsTorsionFree E Ω := inferInstance

attribute [local instance 10000] isTorsionFree_field

section Avatar

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime]
  {O : Type} [CommRing O] [IsDomain O]

def toQ (κ : FractionRing O →+* Qbar l) : O →+* Qbar l := κ.comp (algebraMap O (FractionRing O))

def inQ (κ : FractionRing O →+* Qbar l) (r : G E Ω →* Oˣ) : G E Ω →* (Qbar l)ˣ :=
  (Units.map (toQ κ).toMonoidHom).comp r

def IsGal [TopologicalSpace O] (art : Ideles E →* Gab E Ω) (κ : FractionRing O →+* Qbar l) (ι : Qbar l ≃+* ℂ)
    (χ : HChar E) (n : (E →+* ℂ) → ℤ) (r : G E Ω →* Oˣ) : Prop :=
  IsAlgPos χ n ∧ Continuous (fun g => ((r g : Oˣ) : O)) ∧ IsLAdicOf art ι χ n (inQ κ r)

def sideIso (ι : Qbar l ≃+* ℂ) (b : Bool) : Qbar l ≃+* ℂ :=
  if b then ι else ι.trans (starRingAut : ℂ ≃+* ℂ)

def block (μ η : HChar E) (r : ℕ) : HChar E := μ * (η⁻¹ * Model.absPow E (-(r : ℝ) / 2))

end Avatar

section Universal

variable {R : Ranks} (H : Formalism.BasicNotions.Host R) {Ω : Type} [Field Ω] [Algebra H.E Ω]

def delAt {e : Fin R.m → R.Psi → ℚ} (C : GlobalTheory.Mem.Chr.HFrame H e) (l : ℕ) : HChar H.E :=
  if l = H.pde then C.del' else C.del

theorem conj_conj (x : H.E) : H.conj (H.conj x) = x := by
  let φ : H.E →+* ℂ := Classical.choice inferInstance
  apply φ.injective
  have h := fun y => H.conjE_apply φ y
  exact (h _).trans ((congrArg (starRingEnd ℂ) (h x)).trans (Complex.conj_conj _))

def pair (P : PlE H) : Set (PlE H) := {v | v = P ∨ IsConjPl H P v}

variable {H}

theorem isConjPl_symm {P P' : PlE H} (h : IsConjPl H P P') : IsConjPl H P' P := fun x y e =>
  (h y x (by rw [e, conj_conj])).symm

theorem isConjPl_unique {P P' P'' : PlE H} (h : IsConjPl H P P') (h' : IsConjPl H P P'') : P' = P'' :=
  (GlobalTheory.Mem.Chr.existsUnique_conjPl H.conj.toRingEquiv P).unique
    ((GlobalTheory.Mem.Chr.conjPl_main.2.1 R H P P').1 h) ((GlobalTheory.Mem.Chr.conjPl_main.2.1 R H P P'').1 h')

theorem pair_eq {P P' : PlE H} (h : IsConjPl H P P') : pair H P' = pair H P := by
  ext v
  constructor
  · rintro (rfl | hv)
    · exact Or.inr h
    · exact Or.inl (isConjPl_unique hv (isConjPl_symm h))
  · rintro (rfl | hv)
    · exact Or.inr (isConjPl_symm h)
    · exact Or.inl (isConjPl_unique hv h)

variable (H) (cc : Ω ≃+* Ω) (l : ℕ)

def IsDel (M : ℕ) (T : Set (PlE H)) (d : G H.E Ω →* Multiplicative (ZMod (l ^ M))) : Prop :=
  IsOpen (d.ker : Set (G H.E Ω)) ∧ AntiHom cc d ∧
    (∀ v ∈ placesOver H.E l, ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ σ ∈ Dec (F := H.E) A, d σ = 1) ∧
    (∀ v, v ∉ T → ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ σ ∈ Ine (F := H.E) A, d σ = 1) ∧
    (∀ v, v ∈ T → ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ c, ∃ σ ∈ Ine (F := H.E) A, d σ = c)


open Classical in
def delOf (M : ℕ) (T : Set (PlE H)) : G H.E Ω →* Multiplicative (ZMod (l ^ M)) :=
  if h : ∃ d, IsDel H cc l M T d then h.choose else 1

theorem isDel_delOf {M : ℕ} {T : Set (PlE H)} (h : ∃ d, IsDel H cc l M T d) : IsDel H cc l M T (delOf H cc l M T) := by
  rw [delOf, dite_eq_left h]
  exact h.choose_spec

theorem delOf_laws (M : ℕ) (T : Set (PlE H)) :
    IsOpen ((delOf H cc l M T).ker : Set (G H.E Ω)) ∧ AntiHom cc (delOf H cc l M T) ∧
    (∀ v ∈ placesOver H.E l, ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ σ ∈ Dec (F := H.E) A,
      delOf H cc l M T σ = 1) ∧
    (∀ v, v ∉ T → ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ σ ∈ Ine (F := H.E) A, delOf H cc l M T σ = 1) := by
  by_cases h : ∃ d, IsDel H cc l M T d
  · obtain ⟨h1, h2, h3, h4, -⟩ := isDel_delOf H cc l h
    exact ⟨h1, h2, h3, h4⟩
  · rw [delOf, dite_eq_right h]
    refine ⟨by simp, fun _ _ _ => by simp, fun _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩


open Classical in
def delCoord (Q : Finset (PlE H)) (M : ℕ) (P : PlE H) : G H.E Ω →* Multiplicative (ZMod (l ^ M)) :=
  if pair H P ⊆ ↑Q then delOf H cc l M (pair H P) else 1

def delU (Q : Finset (PlE H)) (M : ℕ) : G H.E Ω →* Multiplicative (DelQM H l Q M) where
  toFun σ := Multiplicative.ofAdd fun P => Multiplicative.toAdd (delCoord H cc l Q M P.1 σ)
  map_one' := by simp only [map_one, toAdd_one]; rfl
  map_mul' g h := by simp only [map_mul, toAdd_mul]; rfl

theorem delU_apply (Q : Finset (PlE H)) (M : ℕ) (σ : G H.E Ω) (P : ↥Q) :
    Multiplicative.toAdd (delU H cc l Q M σ) P = Multiplicative.toAdd (delCoord H cc l Q M P.1 σ) := rfl

theorem delU_eq_one_iff (Q : Finset (PlE H)) (M : ℕ) (σ : G H.E Ω) :
    delU H cc l Q M σ = 1 ↔ ∀ P ∈ Q, delCoord H cc l Q M P σ = 1 :=
  ⟨fun h P hP => Multiplicative.toAdd.injective (congrFun (congrArg Multiplicative.toAdd h) ⟨P, hP⟩),
    fun h => Multiplicative.toAdd.injective (funext fun P => congrArg Multiplicative.toAdd (h P.1 P.2))⟩

theorem delCoord_laws (Q : Finset (PlE H)) (M : ℕ) (P : PlE H) :
    IsOpen ((delCoord H cc l Q M P).ker : Set (G H.E Ω)) ∧ AntiHom cc (delCoord H cc l Q M P) ∧
    (∀ v ∈ placesOver H.E l, ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ σ ∈ Dec (F := H.E) A,
      delCoord H cc l Q M P σ = 1) ∧
    (∀ v, v ∉ Q → ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ σ ∈ Ine (F := H.E) A,
      delCoord H cc l Q M P σ = 1) := by
  unfold delCoord
  split_ifs with h
  · obtain ⟨h1, h2, h3, h4⟩ := delOf_laws H cc l M (pair H P)
    exact ⟨h1, h2, h3, fun v hv => h4 v fun hm => hv (h hm)⟩
  · refine ⟨by simp, fun _ _ _ => by simp, fun _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩

theorem delCoord_of_closed {Q : Finset (PlE H)} (hQ : ∀ P ∈ Q, ∀ P', IsConjPl H P P' → P' ∈ Q) (M : ℕ) {P : PlE H}
    (hP : P ∈ Q) : delCoord H cc l Q M P = delOf H cc l M (pair H P) := by
  refine if_pos ?_
  rintro v (rfl | hv)
  · exact hP
  · exact hQ P hP v hv

def UniversalAnticyclotomicCharLaws : Prop :=
  (∀ Q M v, v ∉ Q → ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ σ ∈ Ine (F := H.E) A, delU H cc l Q M σ = 1) ∧
  (∀ Q M v, v ∈ placesOver H.E l → ∀ A : ValuationSubring Ω, IsPlaceOver A v →
    ∀ σ ∈ Dec (F := H.E) A, delU H cc l Q M σ = 1) ∧
  (∀ Q M, AntiHom cc (delU H cc l Q M)) ∧
  (∀ (Q : Finset (PlE H)) (M : ℕ), IsOpen ((delU H cc l Q M).ker : Set (G H.E Ω))) ∧
  (∀ (M : ℕ) (Q' Q : Finset (PlE H)) (h : Q' ⊆ Q),
    (∀ P ∈ Q', ∀ P', IsConjPl H P P' → P' ∈ Q') → (∀ P ∈ Q, ∀ P', IsConjPl H P P' → P' ∈ Q) →
    ∀ (σ : G H.E Ω) (P : PlE H) (hP : P ∈ Q'),
      Multiplicative.toAdd (delU H cc l Q' M σ) ⟨P, hP⟩ = Multiplicative.toAdd (delU H cc l Q M σ) ⟨P, h hP⟩) ∧
  (∀ (Q : Finset (PlE H)) (M : ℕ) (P : PlE H) (hP : P ∈ Q) (P' : PlE H) (hP' : P' ∈ Q),
    IsConjPl H P P' → ∃ s : ℤˣ, ∀ σ : G H.E Ω,
      Multiplicative.toAdd (delU H cc l Q M σ) ⟨P', hP'⟩ =
        ((s : ℤ) : ZMod (l ^ M)) * Multiplicative.toAdd (delU H cc l Q M σ) ⟨P, hP⟩) ∧
  (∀ (Q : Finset (PlE H)) (M : ℕ), (∀ P ∈ Q, ∀ P', IsConjPl H P P' → P' ∈ Q) → ∀ (P : PlE H) (hP : P ∈ Q) (σ : G H.E Ω),
    Multiplicative.toAdd (delU H cc l Q M σ) ⟨P, hP⟩ = Multiplicative.toAdd (delOf H cc l M (pair H P) σ)) ∧
  ∀ (M : ℕ) (P : PlE H), (∃ d, IsDel H cc l M (pair H P) d) → IsDel H cc l M (pair H P) (delOf H cc l M (pair H P))

theorem universal_anticyclotomic_character_laws : UniversalAnticyclotomicCharLaws H cc l := by
  refine ⟨fun Q M v hv A hA σ hσ => ?_, fun Q M v hv A hA σ hσ => ?_, fun Q M g g' h => ?_, fun Q M => ?_,
    fun M Q' Q h h1 h2 σ P hP => ?_, fun Q M P hP P' hP' h => ⟨1, fun σ => ?_⟩, fun Q M hQ P hP σ => ?_,
    fun M P h => isDel_delOf H cc l h⟩
  · exact (delU_eq_one_iff H cc l Q M σ).2 fun P _ => (delCoord_laws H cc l Q M P).2.2.2 v hv A hA σ hσ
  · exact (delU_eq_one_iff H cc l Q M σ).2 fun P _ => (delCoord_laws H cc l Q M P).2.2.1 v hv A hA σ hσ
  · exact Multiplicative.toAdd.injective (funext fun P =>
      congrArg Multiplicative.toAdd ((delCoord_laws H cc l Q M P.1).2.1 g g' h))
  · have e : ((delU H cc l Q M).ker : Set (G H.E Ω)) = ⋂ P ∈ Q, ((delCoord H cc l Q M P).ker : Set (G H.E Ω)) := by
      ext σ
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, delU_eq_one_iff]
    rw [e]
    exact isOpen_biInter_finset fun P _ => (delCoord_laws H cc l Q M P).1
  · rw [delU_apply, delU_apply, delCoord_of_closed H cc l h1 M hP, delCoord_of_closed H cc l h2 M (h hP)]
  · rw [delU_apply, delU_apply]
    have e : delCoord H cc l Q M P' = delCoord H cc l Q M P := by
      unfold delCoord
      rw [pair_eq h]
    simp only [e, Units.val_one, Int.cast_one, one_mul]
  · rw [delU_apply, delCoord_of_closed H cc l hQ M hP]

end Universal

theorem delUTie_of_exists {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}
    (Y : NExp D.R D.host D.what₂ D.LL0 N X) (hY : ∀ i Q M, Y.delU i Q M = delU D.host X.cc (X.l i) Q M)
    (h : GlobalTheory.TwSys.K1 X) : GlobalTheory.TwSys.DelUTie Y := by
  intro i M _ hM
  obtain ⟨H', S, d, h1, h2, h3, h4⟩ := h i M hM
  refine ⟨H', S, fun P => delOf D.host X.cc (X.l i) M (pair D.host P), ⟨h1, h2, h3, fun P a b c => ?_⟩,
    fun Q hQ P hP σ => ?_⟩
  · exact isDel_delOf D.host X.cc (X.l i) ⟨d P, h4 P a b c⟩
  · rw [hY]
    exact (universal_anticyclotomic_character_laws D.host X.cc (X.l i)).2.2.2.2.2.2.1 Q M hQ P hP σ

end GlobalTheory.GalChar

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsProdInfMulFinPart
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr
open Neutral.B1 hiding localIdele Ideles diagUnits

namespace GlobalTheory.Mem.Chr.Determ

variable {L : Type} [Field L] [NumberField L]

theorem continuous_finSingle (v : HeightOneSpectrum (𝓞 L)) : Continuous (finiteSingle L v) := by
  classical
  have hle : (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 L))) ≤ Filter.principal ({v}ᶜ : Set _) := by
    rw [Filter.le_principal_iff]
    exact (Set.finite_singleton v).compl_mem_cofinite
  let f : v.adicCompletion L → RestrictedProduct (fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L)
      (fun w => (w.adicCompletionIntegers L : Set (w.adicCompletion L))) (Filter.principal ({v}ᶜ : Set _)) :=
    fun x => ⟨Pi.mulSingle v x, by
      rw [Filter.eventually_principal]
      intro w hw
      have h' : w ≠ v := hw
      rw [Pi.mulSingle_eq_of_ne h']
      exact one_mem _⟩
  have hf : Continuous f := by
    rw [RestrictedProduct.continuous_rng_of_principal]
    exact continuous_mulSingle (A := fun w : HeightOneSpectrum (𝓞 L) => w.adicCompletion L) v
  have := (RestrictedProduct.continuous_inclusion hle).comp hf
  exact this

theorem continuous_localIdele (v : HeightOneSpectrum (𝓞 L)) : Continuous (localIdele L v) := by
  apply Continuous.units_map
  exact Continuous.prodMk continuous_const (continuous_finSingle v)

theorem denseRange_atFin (v : HeightOneSpectrum (𝓞 L)) : DenseRange (atFin v) := by
  have hg : Topology.IsOpenEmbedding (Units.val : (v.adicCompletion L)ˣ → v.adicCompletion L) := by
    refine ⟨Units.isEmbedding_val₀, ?_⟩
    have : Set.range (Units.val : (v.adicCompletion L)ˣ → v.adicCompletion L) = {0}ᶜ := by
      ext z
      constructor
      · rintro ⟨u, rfl⟩
        exact u.ne_zero
      · intro hz
        exact ⟨Units.mk0 z hz, rfl⟩
    rw [this]
    exact isOpen_compl_singleton
  rw [DenseRange, dense_iff_inter_open]
  rintro U hU ⟨u, hu⟩
  obtain ⟨k, x, hx, hk⟩ := (HeightOneSpectrum.denseRange_algebraMap L v).exists_mem_open (hg.isOpenMap U hU) ⟨_, u, hu, rfl⟩
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [map_zero] at hk
    exact x.ne_zero hk
  exact ⟨x, hx, Units.mk0 k hk0, Units.ext hk.symm⟩

theorem exists_prod_inf_mul_finPart (a : Ideles L) :
    ∃ y : ∀ w : InfinitePlace L, (w.Completion)ˣ, (∏ w, infIdele L w (y w)) * finPartI L a = a := by
  classical
  let p : ∀ w : InfinitePlace L, AdeleRing (𝓞 L) L →* w.Completion := fun w =>
    { toFun := fun x => x.1 w, map_one' := rfl, map_mul' := fun _ _ => rfl }
  refine ⟨fun w => Units.map (p w) a, ?_⟩
  have h : ((∏ w, infIdele L w (Units.map (p w) a) : Ideles L) : AdeleRing (𝓞 L) L) = ((a : AdeleRing (𝓞 L) L).1, 1) := by
    rw [Units.coe_prod]
    let ι : (∀ w : InfinitePlace L, w.Completion) →* AdeleRing (𝓞 L) L :=
      MonoidHom.inl (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)
    change ∏ w : InfinitePlace L, ι (Pi.mulSingle w ((a : AdeleRing (𝓞 L) L).1 w)) = ι (fun w => (a : AdeleRing (𝓞 L) L).1 w)
    rw [← map_prod]
    exact congrArg ι (Finset.univ_prod_mulSingle (fun w : InfinitePlace L => ((a : AdeleRing (𝓞 L) L).1 w : w.Completion)))
  apply Units.ext
  rw [Units.val_mul, h]
  exact Prod.ext (mul_one _) (one_mul _)

theorem loc_eq_one {ψ : Ideles L →* ℂˣ} (hψ : Continuous ψ) (v : HeightOneSpectrum (𝓞 L))
    (h : ∀ k, ψ (localIdele L v (atFin v k)) = 1) (x : (v.adicCompletion L)ˣ) : ψ (localIdele L v x) = 1 :=
  congrFun ((denseRange_atFin v).equalizer (g := fun x => ψ (localIdele L v x)) (h := fun _ => 1)
    (hψ.comp (continuous_localIdele v)) continuous_const (funext h)) x

theorem inf_eq_one {ψ : Ideles L →* ℂˣ} (hψ : Continuous ψ) (h : ∀ k, ψ (infDiag k) = 1)
    (y : ∀ w : InfinitePlace L, (w.Completion)ˣ) : ψ (∏ w, infIdele L w (y w)) = 1 := by
  refine congrFun ((GlobalTheory.InfTypeLocal.denseRange_atInf L).equalizer
    (g := fun y : ∀ w : InfinitePlace L, (w.Completion)ˣ => ψ (∏ w, infIdele L w (y w))) (h := fun _ => 1)
    (hψ.comp (continuous_finsetProd _ fun w _ =>
      (GlobalTheory.InfTypeLocal.continuous_infIdele L w).comp (continuous_apply w))) continuous_const (funext fun k => ?_)) y
  have h1 := h k
  unfold infDiag at h1
  rw [MonoidHom.finsetProd_apply] at h1
  exact h1

theorem eq_one_of_components {ψ : Ideles L →* ℂˣ} (hψ : Continuous ψ)
    (hf : ∀ v k, ψ (localIdele L v (atFin v k)) = 1) (hi : ∀ k, ψ (infDiag k) = 1) (a : Ideles L) : ψ a = 1 := by
  obtain ⟨S, n, u, hu, rfl, -⟩ := exists_prod_unif_mul_unitIdl L a
  obtain ⟨y, hy⟩ := exists_prod_inf_mul_finPart u
  have h1 : ψ (finPartI L u) = 1 :=
    GlobalTheory.Mem.LocTriv.eq_one_of_local L ψ hψ _ (finPartI_mem_unitIdl.2 hu) (fun _ => rfl) fun v x _ => loc_eq_one hψ v (hf v) x
  rw [← hy, map_mul, map_mul, h1, inf_eq_one hψ hi, map_prod, mul_one, mul_one]
  exact Finset.prod_eq_one fun v _ => by
    rw [map_zpow]
    exact (congrArg (· ^ n v) (hf v (Formalism.L2.Host.unif v))).trans (one_zpow _)

end GlobalTheory.Mem.Chr.Determ
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfTameLoc
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits GlobalTheory.Mem.Chr
open Neutral.B1 hiding localIdele Ideles diagUnits
open ReciprocityTheory.Neutral.Bridge.HCFR hiding infIdele
open Formalism.L2.Host hiding infDiag atInf atFin

namespace GlobalTheory.ModelChar

def argU : ℂˣ →* ℂˣ where
  toFun z := Units.mk0 ((z : ℂ) / ((‖(z : ℂ)‖ : ℝ) : ℂ))
    (div_ne_zero z.ne_zero (by exact_mod_cast norm_ne_zero_iff.2 z.ne_zero))
  map_one' := by ext; simp
  map_mul' x y := by
    ext
    simp only [Units.val_mul, Units.val_mk0, norm_mul, Complex.ofReal_mul]
    rw [mul_div_mul_comm]

theorem argU_val (z : ℂˣ) : ((argU z : ℂˣ) : ℂ) = (z : ℂ) / ((‖(z : ℂ)‖ : ℝ) : ℂ) := rfl

theorem norm_argU (z : ℂˣ) : ‖((argU z : ℂˣ) : ℂ)‖ = 1 := by
  rw [argU_val, norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 z.ne_zero)]

theorem continuous_argU : Continuous argU := by
  rw [Units.isEmbedding_val₀.continuous_iff]
  exact Units.continuous_val.div (Complex.continuous_ofReal.comp Units.continuous_val.norm)
    fun z => by exact_mod_cast norm_ne_zero_iff.2 z.ne_zero

variable {L : Type} [Field L] [NumberField L]

def finEv (v : HeightOneSpectrum (𝓞 L)) : AdeleRing (𝓞 L) L →* v.adicCompletion L where
  toFun a := a.2 v
  map_one' := rfl
  map_mul' _ _ := rfl

def infEv (w : InfinitePlace L) : AdeleRing (𝓞 L) L →* w.Completion where
  toFun a := a.1 w
  map_one' := rfl
  map_mul' _ _ := rfl

theorem continuous_finEv (v : HeightOneSpectrum (𝓞 L)) : Continuous (finEv v) :=
  (RestrictedProduct.continuous_eval v).comp continuous_snd

theorem continuous_infEv (w : InfinitePlace L) : Continuous (infEv w) :=
  (continuous_apply w).comp continuous_fst

theorem finEv_local_self (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) :
    Units.map (finEv v) (localIdele L v x) = x := by
  classical
  apply Units.ext
  exact Function.update_self v (x : v.adicCompletion L) (fun w : HeightOneSpectrum (𝓞 L) => (1 : w.adicCompletion L))

theorem finEv_local_ne {v w : HeightOneSpectrum (𝓞 L)} (h : w ≠ v) (x : (v.adicCompletion L)ˣ) :
    Units.map (finEv w) (localIdele L v x) = 1 := by
  classical
  apply Units.ext
  exact Function.update_of_ne h (x : v.adicCompletion L) (fun w : HeightOneSpectrum (𝓞 L) => (1 : w.adicCompletion L))

theorem infEv_local (w : InfinitePlace L) (v : HeightOneSpectrum (𝓞 L)) (x : (v.adicCompletion L)ˣ) :
    Units.map (infEv w) (localIdele L v x) = 1 := Units.ext rfl

theorem finEv_inf (v : HeightOneSpectrum (𝓞 L)) (w : InfinitePlace L) (x : (w.Completion)ˣ) :
    Units.map (finEv v) (infIdele L w x) = 1 := Units.ext rfl

theorem infEv_inf_self (w : InfinitePlace L) (x : (w.Completion)ˣ) :
    Units.map (infEv w) (infIdele L w x) = x := by
  classical
  apply Units.ext
  exact Pi.mulSingle_eq_same (M := fun w : InfinitePlace L => w.Completion) w (x : w.Completion)

theorem infEv_inf_ne {w u : InfinitePlace L} (h : u ≠ w) (x : (w.Completion)ˣ) :
    Units.map (infEv u) (infIdele L w x) = 1 := by
  classical
  apply Units.ext
  exact Pi.mulSingle_eq_of_ne (M := fun w : InfinitePlace L => w.Completion) h (x : w.Completion)

theorem infEv_infDiag (w : InfinitePlace L) (k : Lˣ) : Units.map (infEv w) (infDiag k) = atInf w k := by
  unfold infDiag
  rw [MonoidHom.finsetProd_apply, map_prod, Finset.prod_eq_single w]
  · exact infEv_inf_self w _
  · intro u _ hu
    exact infEv_inf_ne hu.symm _
  · simp

theorem finEv_infDiag (v : HeightOneSpectrum (𝓞 L)) (k : Lˣ) : Units.map (finEv v) (infDiag k) = 1 := by
  unfold infDiag
  rw [MonoidHom.finsetProd_apply, map_prod]
  exact Finset.prod_eq_one fun w _ => finEv_inf v w _

theorem infEv_diag (w : InfinitePlace L) (k : Lˣ) : Units.map (infEv w) (diagUnits L k) = atInf w k := Units.ext rfl

theorem finEv_diag (v : HeightOneSpectrum (𝓞 L)) (k : Lˣ) : Units.map (finEv v) (diagUnits L k) = atFin v k :=
  Units.ext rfl

theorem continuous_of_tameLoc {v : HeightOneSpectrum (𝓞 L)} {θ : (v.adicCompletion L)ˣ →* ℂˣ} (h : TameLoc v θ) :
    Continuous θ := by
  refine continuous_of_continuousAt_one θ ?_
  have hc : Continuous fun x : (v.adicCompletion L)ˣ => (x : v.adicCompletion L) - 1 :=
    Units.continuous_val.sub continuous_const
  have ho : IsOpen {y : v.adicCompletion L | Valued.v y < 1} := by
    have := Valued.isOpen_ball (v.adicCompletion L) 1
    simpa only [Valuation.restrict_lt_one_iff] using this
  have hn : {x : (v.adicCompletion L)ˣ | Valued.v ((x : v.adicCompletion L) - 1) < 1} ∈ nhds (1 : (v.adicCompletion L)ˣ) :=
    (ho.preimage hc).mem_nhds (by simp)
  refine (continuousAt_const (y := (1 : ℂˣ))).congr ?_
  filter_upwards [hn] with x hx
  refine (h.2 x ?_ ?_).symm
  · have := Valuation.map_one_add_of_lt (Valued.v : Valuation (v.adicCompletion L) _) hx
    rwa [add_sub_cancel] at this
  · have := (WithZero.lt_mul_exp_iff_le (x := Valued.v ((x : v.adicCompletion L) - 1)) (y := WithZero.exp (-1 : ℤ)) WithZero.exp_ne_zero).1
    apply this
    rw [← WithZero.exp_add]
    simpa using hx


open Classical in
theorem exists_modelChar : ∀ (L : Type) [Field L] [NumberField L] (I : Type) [Fintype I] (φ : I → L →+* ℂ), (Function.Bijective fun i => InfinitePlace.mk (φ i)) → ∀ (n : I → ℤ) (S : Finset (HeightOneSpectrum (𝓞 L))) (θ : ∀ v : HeightOneSpectrum (𝓞 L), (v.adicCompletion L)ˣ →* ℂˣ), (∀ v ∈ S, TameLoc v (θ v)) → ∃ ψ : Ideles L →* ℂˣ, Continuous ψ ∧ (∀ x, ‖((ψ x : ℂˣ) : ℂ)‖ = 1) ∧ (∀ i (k : Lˣ), ((ψ (infIdele L (InfinitePlace.mk (φ i)) (atInf _ k)) : ℂˣ) : ℂ) = (φ i (k : L) / ((‖φ i (k : L)‖ : ℝ) : ℂ)) ^ n i) ∧ (∀ v ∈ S, ∀ x, ψ (localIdele L v x) = θ v x) ∧ (∀ v ∉ S, ∀ x, ψ (localIdele L v x) = 1) ∧ ∀ k : Lˣ, ψ (diagUnits L k) = ψ (infDiag k) * ∏ v ∈ S, θ v (atFin v k) := by
  intro L _ _ I _ φ hφ n S θ hθ
  choose e hec he using fun i => GlobalTheory.InfTypeLocal.exists_ext (φ i)
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Ideles L →* ℂˣ, ∀ a, ψ a =
      (∏ i, argU (Units.map (e i).toMonoidHom (Units.map (infEv (InfinitePlace.mk (φ i))) a)) ^ n i) *
        ∏ v ∈ S, θ v (Units.map (finEv v) a) :=
    ⟨{ toFun := fun a =>
        (∏ i, argU (Units.map (e i).toMonoidHom (Units.map (infEv (InfinitePlace.mk (φ i))) a)) ^ n i) *
          ∏ v ∈ S, θ v (Units.map (finEv v) a)
       map_one' := by simp only [map_one, one_zpow, Finset.prod_const_one, mul_one]
       map_mul' := fun a b => by
        simp only [map_mul, mul_zpow, Finset.prod_mul_distrib]
        rw [mul_mul_mul_comm] }, fun _ => rfl⟩
  refine ⟨ψ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show (ψ : Ideles L → ℂˣ) = _ from funext hψ]
    refine Continuous.mul (continuous_finsetProd _ fun i _ => ?_) (continuous_finsetProd _ fun v hv => ?_)
    · exact (continuous_argU.comp ((Continuous.units_map _ (hec i)).comp
        (Continuous.units_map _ (continuous_infEv _)))).zpow _
    · exact (continuous_of_tameLoc (hθ v hv)).comp (Continuous.units_map _ (continuous_finEv v))
  · intro x
    rw [hψ, Units.val_mul, Units.coe_prod, Units.coe_prod, norm_mul, norm_prod, norm_prod,
      Finset.prod_eq_one, Finset.prod_eq_one, one_mul]
    · exact fun v hv => (hθ v hv).1 _
    · intro i _
      rw [Units.val_zpow_eq_zpow_val, norm_zpow, norm_argU, one_zpow]
  · intro i k
    rw [hψ, Finset.prod_eq_one (s := S), mul_one, Finset.prod_eq_single i, infEv_inf_self,
      Units.val_zpow_eq_zpow_val, argU_val, ← he i k]
    · rfl
    · intro j _ hj
      rw [infEv_inf_ne (fun hh => hj (hφ.1 hh)), map_one, map_one, one_zpow]
    · simp
    · intro v _
      rw [finEv_inf, map_one]
  · intro v hv x
    rw [hψ, Finset.prod_eq_one, one_mul, Finset.prod_eq_single_of_mem v hv, finEv_local_self]
    · intro w _ hw
      rw [finEv_local_ne hw, map_one]
    · intro i _
      rw [infEv_local, map_one, map_one, one_zpow]
  · intro v hv x
    rw [hψ, Finset.prod_eq_one, one_mul, Finset.prod_eq_one]
    · intro w hw
      have hne : w ≠ v := fun hh => hv (hh ▸ hw)
      rw [finEv_local_ne hne, map_one]
    · intro i _
      rw [infEv_local, map_one, map_one, one_zpow]
  · intro k
    rw [hψ, hψ]
    simp only [infEv_diag, finEv_diag, infEv_infDiag, finEv_infDiag, map_one, Finset.prod_const_one, mul_one]

end GlobalTheory.ModelChar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOpenConnectedComponentOfOneInf
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

namespace GlobalTheory.HeckeGal

theorem exists_units_hom {Γ K : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Field K] [TopologicalSpace K]
    (F : Γ →* K) (hF : Continuous F) : ∃ f : Γ →* Kˣ, Continuous f ∧ ∀ x, ((f x : Kˣ) : K) = F x :=
  ⟨F.toHomUnits, Units.continuous_iff.mpr ⟨hF, hF.comp continuous_inv⟩, fun _ => rfl⟩

theorem exists_infPow_hom : ∀ (E : Type) [Field E] [NumberField E] (n : (E →+* ℂ) → ℤ), ∃ f : Ideles E →* ℂˣ, Continuous f ∧ ∀ x : Ideles E, ((f x : ℂˣ) : ℂ) = infPow n x := by
  intro E _ _ n
  have h0 : ∀ (x : Ideles E) (w : InfinitePlace E), (x : AdeleRing (𝓞 E) E).1 w ≠ 0 := fun x w =>
    left_ne_zero_of_mul_eq_one (congrArg (fun y : AdeleRing (𝓞 E) E => y.1 w) x.mul_inv)
  haveI : ∀ w : InfinitePlace E, Fintype {i : w.Completion →+* ℂ // Continuous i} := fun w =>
    @Fintype.ofFinite _ (finite_contEmbInf w)
  have e : ∀ x : Ideles E, infPow n x = ∏ w : InfinitePlace E, ∏ i : {i : w.Completion →+* ℂ // Continuous i},
      i.1 ((x : AdeleRing (𝓞 E) E).1 w) ^ n (i.1.comp (algebraMap E w.Completion)) := fun x =>
    Finset.prod_congr rfl fun w _ => finprod_eq_prod_of_fintype _
  let F : Ideles E →* ℂ :=
    { toFun := infPow n
      map_one' := by
        rw [e]
        refine Finset.prod_eq_one fun w _ => Finset.prod_eq_one fun i _ => ?_
        rw [show ((1 : Ideles E) : AdeleRing (𝓞 E) E).1 w = 1 from rfl, map_one, one_zpow]
      map_mul' := fun x y => by
        rw [e, e, e, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun w _ => ?_
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [← mul_zpow, ← map_mul]
        rfl }
  refine exists_units_hom F ?_
  show Continuous (infPow n)
  rw [funext e]
  refine continuous_finsetProd _ fun w _ => continuous_finsetProd _ fun i _ => ?_
  refine Continuous.zpow₀ ?_ _ fun x => Or.inl ((map_ne_zero i.1).mpr (h0 x w))
  exact i.2.comp ((continuous_apply w).comp (continuous_fst.comp Units.continuous_val))

theorem exists_lPow_hom : ∀ (E : Type) [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : (E →+* ℂ) → ℤ), ∃ f : Ideles E →* (Qbar l)ˣ, Continuous f ∧ ∀ x : Ideles E, ((f x : (Qbar l)ˣ) : Qbar l) = lPow ι n x := by
  intro E _ _ l _ ι n
  have hl : l.Prime := Fact.out
  have h0 : ∀ (x : Ideles E) (v : HeightOneSpectrum (𝓞 E)), (x : AdeleRing (𝓞 E) E).2 v ≠ 0 := fun x w =>
    left_ne_zero_of_mul_eq_one (congrArg (fun y : AdeleRing (𝓞 E) E => y.2 w) x.mul_inv)
  haveI : ∀ v : HeightOneSpectrum (𝓞 E), Fintype {j : v.adicCompletion E →+* Qbar l // Continuous j} := fun v =>
    @Fintype.ofFinite _ (finite_contEmb v)
  have hI : Ideal.span {((l : ℕ) : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hl.ne_zero
  have e : ∀ x : Ideles E, lPow ι n x = ∏ v ∈ (Ideal.finite_factors hI).toFinset,
      ∏ j : {j : v.adicCompletion E →+* Qbar l // Continuous j}, j.1 ((x : AdeleRing (𝓞 E) E).2 v) ^
        n ((ι.toRingHom.comp j.1).comp (algebraMap E (v.adicCompletion E))) := fun x => by
    unfold lPow
    rw [finprod_eq_prod_of_mulSupport_subset (s := (Ideal.finite_factors hI).toFinset)]
    · exact Finset.prod_congr rfl fun w _ => finprod_eq_prod_of_fintype _
    · intro v hv
      by_contra h
      refine hv (locPow_of_notMem ι n (fun hm => h ?_) _)
      exact Finset.mem_coe.mpr ((Set.Finite.mem_toFinset _).mpr (Ideal.dvd_span_singleton.mpr hm))
  let F : Ideles E →* Qbar l :=
    { toFun := lPow ι n
      map_one' := by
        rw [e]
        refine Finset.prod_eq_one fun w _ => Finset.prod_eq_one fun i _ => ?_
        rw [show ((1 : Ideles E) : AdeleRing (𝓞 E) E).2 w = 1 from rfl, map_one, one_zpow]
      map_mul' := fun x y => by
        rw [e, e, e, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun w _ => ?_
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [← mul_zpow, ← map_mul]
        rfl }
  refine exists_units_hom F ?_
  show Continuous (lPow ι n)
  rw [funext e]
  refine continuous_finsetProd _ fun w _ => continuous_finsetProd _ fun i _ => ?_
  refine Continuous.zpow₀ ?_ _ fun x => Or.inl ((map_ne_zero i.1).mpr (h0 x w))
  exact i.2.comp ((RestrictedProduct.continuous_eval w).comp (continuous_snd.comp Units.continuous_val))

theorem infPow_diagUnits : ∀ (E : Type) [Field E] [NumberField E] (n : (E →+* ℂ) → ℤ) (k : Eˣ), infPow n (diagUnits E k) = ∏ φ : E →+* ℂ, φ (k : E) ^ n φ := by
  intro E _ _ n k
  classical
  let J : InfinitePlace E → Type := fun w => {i : w.Completion →+* ℂ // Continuous i}
  let res : (Σ w, J w) → (E →+* ℂ) := fun p => p.2.1.comp (algebraMap E p.1.Completion)
  have hd : ∀ w : InfinitePlace E, DenseRange (algebraMap E w.Completion) := fun w => by
    refine Dense.mono ?_ (InfinitePlace.Completion.denseRange_coe w)
    rintro _ ⟨a, rfl⟩
    exact ⟨WithAbs.equiv w.1 a, by simp [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply]⟩
  have hmk : ∀ p : Σ w, J w, InfinitePlace.mk (res p) = p.1 := by
    rintro ⟨w, i⟩
    have hn : ∀ y : w.Completion, ‖i.1 y‖ = ‖y‖ := fun y => by
      rcases w.isReal_or_isComplex with hw | hw
      · let e := InfinitePlace.Completion.ringEquivRealOfIsReal hw
        have he : Isometry e.symm := (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.isometry
        have h1 := Complex.ringHom_eq_ofReal_of_continuous (f := i.1.comp e.symm.toRingHom) (i.2.comp he.continuous)
        obtain ⟨z, rfl⟩ := e.symm.surjective y
        rw [he.norm_map_of_map_zero (map_zero _)]
        exact (congrArg norm (DFunLike.congr_fun h1 z)).trans (Complex.norm_real z)
      · let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
        have he : Isometry e.symm := (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).symm.isometry
        obtain ⟨z, rfl⟩ := e.symm.surjective y
        rw [he.norm_map_of_map_zero (map_zero _)]
        rcases Complex.ringHom_eq_id_or_conj_of_continuous (f := i.1.comp e.symm.toRingHom)
          (i.2.comp he.continuous) with h1 | h1
        · exact congrArg norm (DFunLike.congr_fun h1 z)
        · exact (congrArg norm (DFunLike.congr_fun h1 z)).trans (Complex.norm_conj z)
    refine InfinitePlace.ext _ _ fun a => ?_
    rw [InfinitePlace.apply]
    apply (hn _).trans
    simpa [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply] using
      (InfinitePlace.Completion.norm_coe w (WithAbs.toAbs _ a))
  have hinj : Function.Injective res := by
    rintro ⟨v, j⟩ ⟨v', j'⟩ h
    obtain rfl : v = v' := (hmk ⟨v, j⟩).symm.trans ((congrArg InfinitePlace.mk h).trans (hmk ⟨v', j'⟩))
    congr 1
    apply Subtype.ext
    apply DFunLike.coe_injective
    refine (hd v).equalizer j.2 j'.2 ?_
    funext a
    exact DFunLike.congr_fun h a
  have hsurj : Function.Surjective res := by
    intro φ
    obtain ⟨j, hj, e⟩ := GlobalTheory.InfTypeLocal.exists_ext φ
    exact ⟨⟨_, j, hj⟩, RingHom.ext e⟩
  haveI : ∀ w, Fintype (J w) := fun w => @Fintype.ofFinite _ (finite_contEmbInf w)
  rw [← Fintype.prod_bijective res ⟨hinj, hsurj⟩ (fun p => res p (k : E) ^ n (res p)) _ fun _ => rfl,
    Fintype.prod_sigma]
  exact Finset.prod_congr rfl fun w _ => finprod_eq_prod_of_fintype _

theorem isOpenEmbedding_val_inf (E : Type) [Field E] [NumberField E] :
    Topology.IsOpenEmbedding (Units.val : (InfiniteAdeleRing E)ˣ → InfiniteAdeleRing E) :=
  Units.isOpenEmbedding_val (R := ∀ w : InfinitePlace E, w.Completion)

theorem isOpen_connectedComponentOfOne_inf : ∀ (E : Type) [Field E] [NumberField E], IsOpen ((Subgroup.connectedComponentOfOne (InfiniteAdeleRing E)ˣ : Subgroup (InfiniteAdeleRing E)ˣ) : Set (InfiniteAdeleRing E)ˣ) := by
  intro E _ _
  haveI : ∀ w : InfinitePlace E, LocallyConnectedSpace w.Completion := fun w => by
    rcases w.isReal_or_isComplex with hw | hw
    · exact (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).toHomeomorph.locallyConnectedSpace
    · exact (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).toHomeomorph.locallyConnectedSpace
  haveI : LocallyConnectedSpace (InfiniteAdeleRing E) :=
    inferInstanceAs (LocallyConnectedSpace (∀ w : InfinitePlace E, w.Completion))
  haveI : LocallyConnectedSpace (InfiniteAdeleRing E)ˣ := (isOpenEmbedding_val_inf E).locallyConnectedSpace
  exact isOpen_connectedComponent

theorem denseRange_units_inf : ∀ (E : Type) [Field E] [NumberField E], DenseRange (fun k : Eˣ => (Units.map (algebraMap E (InfiniteAdeleRing E)).toMonoidHom k : (InfiniteAdeleRing E)ˣ)) := by
  intro E _ _
  rw [DenseRange, dense_iff_inter_open]
  rintro U hU ⟨u, hu⟩
  obtain ⟨k, v, hv, hk⟩ := (InfiniteAdeleRing.denseRange_algebraMap E).exists_mem_open
    ((isOpenEmbedding_val_inf E).isOpenMap U hU) ⟨_, u, hu, rfl⟩
  have hk0 : k ≠ 0 := by
    rintro rfl
    obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
    rw [map_zero] at hk
    have h1 := congrFun v.mul_inv w
    rw [hk, zero_mul] at h1
    exact zero_ne_one (α := w.Completion) h1
  exact ⟨v, hv, Units.mk0 k hk0, Units.ext hk.symm⟩

theorem pos_of_mem_connectedComponentOfOne : ∀ (E : Type) [Field E] [NumberField E] (k : Eˣ), (Units.map (algebraMap E (InfiniteAdeleRing E)).toMonoidHom k : (InfiniteAdeleRing E)ˣ) ∈ Subgroup.connectedComponentOfOne (InfiniteAdeleRing E)ˣ → ∀ φ : E →+* ℝ, 0 < φ (k : E) := by
  intro E _ _ k hk φ
  obtain ⟨e, he, hek⟩ := GlobalTheory.InfTypeLocal.exists_ext (Complex.ofRealHom.comp φ)
  let w := InfinitePlace.mk (Complex.ofRealHom.comp φ)
  have hd : DenseRange (algebraMap E w.Completion) := by
    refine Dense.mono ?_ (InfinitePlace.Completion.denseRange_coe w)
    rintro _ ⟨a, rfl⟩
    exact ⟨WithAbs.equiv w.1 a, by simp [AbsoluteValue.Completion.algebraMap_def, WithAbs.algebraMap_right_apply]⟩
  have him : ∀ y : w.Completion, (e y).im = 0 := fun y =>
    congrFun (hd.equalizer (g := fun y => (e y).im) (h := fun _ => 0) (Complex.continuous_im.comp he)
      continuous_const (funext fun a => (congrArg Complex.im (hek a)).trans (by simp))) y
  let g : (InfiniteAdeleRing E)ˣ → ℝ := fun u => (e ((u : InfiniteAdeleRing E) w)).re
  have hg : Continuous g :=
    Complex.continuous_re.comp (he.comp ((continuous_apply w).comp Units.continuous_val))
  have hg0 : ∀ u, g u ≠ 0 := fun u h => by
    have h1 : e ((u : InfiniteAdeleRing E) w) = 0 := Complex.ext h (him _)
    exact left_ne_zero_of_mul_eq_one (congrFun u.mul_inv w) ((map_eq_zero e).mp h1)
  have hg1 : g 1 = 1 := by
    show (e 1).re = 1
    simp
  have hgk : g (Units.map (algebraMap E (InfiniteAdeleRing E)).toMonoidHom k) = φ k := by
    show (e (algebraMap E _ (k : E))).re = _
    rw [hek]
    simp
  by_contra hneg
  have := isPreconnected_connectedComponent.intermediate_value hk mem_connectedComponent hg.continuousOn
    (show (0 : ℝ) ∈ Set.Icc _ _ from ⟨by rw [hgk]; exact not_lt.mp hneg, by rw [hg1]; exact zero_le_one⟩)
  obtain ⟨u, -, hu⟩ := this
  exact hg0 u hu

end GlobalTheory.HeckeGal

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemKDSupUnitIdlIff
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr
open Neutral.B1 hiding localIdele Ideles diagUnits
open GlobalTheory.Mem.Chr.IdlFact

namespace GlobalTheory.Mem.Chr.KDVal

variable {L : Type} [Field L] [NumberField L] (F : Type) [Field F] [NumberField F] [Algebra F L]


open Classical in
theorem valAt_locF (w : HeightOneSpectrum (𝓞 L)) (v : HeightOneSpectrum (𝓞 F)) (k : Fˣ) :
    valAt w (locF (L := L) F v k) =
      if w.under (𝓞 F) = v then WithZero.exp (-ordF w (upF F k)) else 1 := by
  unfold locF
  rw [map_prod]
  change ∏ x ∈ aboveF (L := L) F v, valAt w (localIdele L x (Formalism.L2.Host.atFin x (Formalism.L2.Host.upF F k))) = _
  have hm : ∀ Q : HeightOneSpectrum (𝓞 L), Q ∈ aboveF (L := L) F v ↔ Q.under (𝓞 F) = v := fun Q => by
    simp [aboveF]
  split_ifs with hw
  · rw [Finset.prod_eq_single_of_mem w ((hm w).2 hw) (fun Q _ hQ => valAt_localIdele_ne hQ.symm _),
      valAt_localIdele_self]
    have h0 : w.valuation L ((upF F k : Lˣ) : L) ≠ 0 := by simp
    unfold ordF
    rw [neg_neg, WithZero.exp_log h0]
    exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
  · exact Finset.prod_eq_one fun Q hQ => valAt_localIdele_ne (fun e : w = Q => hw (by rw [e]; exact (hm Q).1 hQ)) _

def balanced : Subgroup (Ideles L) where
  carrier := {a | ∀ w w' : HeightOneSpectrum (𝓞 L), w'.under (𝓞 F) = w.under (𝓞 F) → valAt w a = valAt w' a}
  one_mem' := fun w w' _ => by rw [map_one, map_one]
  mul_mem' := fun {a b} ha hb w w' h => by rw [map_mul, map_mul, ha w w' h, hb w w' h]
  inv_mem' := fun {a} ha w w' h => by rw [map_inv, map_inv, ha w w' h]

theorem unitIdl_le_balanced : unitIdl L ≤ balanced (L := L) F := fun a ha w w' _ =>
  (ha w).trans (ha w').symm

variable {F}

theorem locF_mem_balanced
    (hu : ∀ (P : HeightOneSpectrum (𝓞 L)) (k : Fˣ), ordF P (upF F k) = ordF (P.under (𝓞 F)) k)
    (v : HeightOneSpectrum (𝓞 F)) (k : Fˣ) : locF (L := L) F v k ∈ balanced (L := L) F := fun w w' h => by
  rw [valAt_locF, valAt_locF, hu, hu, h]

theorem mem_sup_of_balanced
    (hu : ∀ (P : HeightOneSpectrum (𝓞 L)) (k : Fˣ), ordF P (upF F k) = ordF (P.under (𝓞 F)) k)
    (G : Subgroup (Ideles L)) (hG : ∀ v k, locF (L := L) F v k ∈ G) (a : Ideles L)
    (ha : a ∈ balanced (L := L) F) : a ∈ G ⊔ unitIdl L := by
  classical
  let T : Finset (HeightOneSpectrum (𝓞 F)) := (finite_valAt_ne_one a).toFinset.image fun w => w.under (𝓞 F)
  let m : HeightOneSpectrum (𝓞 F) → ℤ := fun v =>
    if h : ∃ w : HeightOneSpectrum (𝓞 L), w.under (𝓞 F) = v then -WithZero.log (valAt h.choose a) else 0
  let b : Ideles L := ∏ v ∈ T, locF (L := L) F v (unif v) ^ m v
  have hb : b ∈ G := prod_mem fun v _ => zpow_mem (hG _ _) _
  have hval : ∀ w, valAt w b = valAt w a := fun w => by
    have h1 : ∀ v, v ≠ w.under (𝓞 F) → valAt w (locF (L := L) F v (unif v) ^ m v) = 1 := fun v hv => by
      rw [map_zpow, valAt_locF, if_neg hv.symm, one_zpow]
    simp only [b]
    rw [map_prod]
    by_cases hw : w.under (𝓞 F) ∈ T
    · rw [Finset.prod_eq_single_of_mem _ hw (fun v _ hv => h1 v hv), map_zpow, valAt_locF, if_pos rfl, hu,
        show ordF (w.under (𝓞 F)) (unif (w.under (𝓞 F))) = 1 from ordF_unif_self _, ← WithZero.exp_zsmul]
      have hex : ∃ w' : HeightOneSpectrum (𝓞 L), w'.under (𝓞 F) = w.under (𝓞 F) := ⟨w, rfl⟩
      have hm : m (w.under (𝓞 F)) = -WithZero.log (valAt w a) := by
        simp only [m]
        rw [dite_eq_left hex, ha w hex.choose hex.choose_spec]
      rw [hm]
      simp only [smul_eq_mul, mul_neg, neg_neg, mul_one]
      exact WithZero.exp_log (valAt_ne_zero w a)
    · rw [Finset.prod_eq_one (fun v hv => h1 v (fun e => hw (e ▸ hv)))]
      by_contra hne
      exact hw (Finset.mem_image_of_mem _ (by simpa using fun e => hne e.symm))
  have hu' : b⁻¹ * a ∈ unitIdl L := fun w => by
    rw [← valAt_apply, map_mul, map_inv, hval]
    exact inv_mul_cancel₀ (valAt_ne_zero w a)
  rw [← mul_inv_cancel_left b a]
  exact Subgroup.mul_mem_sup hb hu'

end GlobalTheory.Mem.Chr.KDVal


open GlobalTheory.Mem.Chr.KDVal in
open Classical in
theorem GlobalTheory.Mem.Chr.mem_KD_sup_unitIdl_iff : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (a : Ideles H.E), a ∈ KD H ⊔ unitIdl H.E ↔ ∀ w w', IsConjPl H w w' → Valued.v ((a : AdeleRing (𝓞 H.E) H.E).2 w) = Valued.v ((a : AdeleRing (𝓞 H.E) H.E).2 w') := by
  intro R H a
  obtain ⟨c, hc, hcm, hu, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  have hiff : ∀ w w' : HeightOneSpectrum (𝓞 H.E),
      w'.under (𝓞 H.F) = w.under (𝓞 H.F) ↔ (w' = w ∨ IsConjPl H w w') := fun w w' => by
    rw [under_eq_iff_conjPl c hcm.rank hcm.ne, conjPl_main.2.1 R H w w']
    have : c.toRingEquiv = H.conj.toRingEquiv := RingEquiv.ext hc
    rw [this]
  constructor
  · intro ha w w' h
    have hle : KD H ⊔ unitIdl H.E ≤ balanced (L := H.E) H.F := by
      refine sup_le ((Subgroup.closure_le _).2 ?_) (unitIdl_le_balanced _)
      rintro x (hx | ⟨v, k, rfl⟩)
      · exact unitIdl_le_balanced _ hx.1
      · exact locF_mem_balanced hu v k
    exact hle ha w w' ((hiff w w').2 (Or.inr h))
  · intro h
    refine mem_sup_of_balanced hu _ (locF_mem_KD H) a fun w w' hw => ?_
    rcases (hiff w w').1 hw with rfl | h'
    · rfl
    · exact h w w' h'
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BijectiveCmType
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.FrobeniusOrbits GlobalTheory.HeckeGal

namespace GlobalTheory.Mem.CharAlg

theorem bijective_cmType {L : Type} [Field L] [_root_.NumberField.IsTotallyComplex L] {I : Type} (φ : I → L →+* ℂ)
    (h : Function.Bijective fun i => InfinitePlace.mk (φ i)) :
    Function.Bijective (Sum.elim φ (fun i => ComplexEmbedding.conjugate (φ i))) := by
  have hne : ∀ i j, φ i ≠ ComplexEmbedding.conjugate (φ j) := by
    intro i j hij
    have h1 : i = j := h.1 (by
      show InfinitePlace.mk (φ i) = InfinitePlace.mk (φ j)
      rw [hij, InfinitePlace.mk_conjugate_eq])
    subst h1
    exact IsTotallyComplex.complexEmbedding_not_isReal (φ i) (ComplexEmbedding.isReal_iff.2 hij.symm)
  constructor
  · rintro (i | i) (j | j) hij
    · have hij' : φ i = φ j := hij
      exact congrArg Sum.inl (h.1 (congrArg InfinitePlace.mk hij'))
    · exact absurd hij (hne i j)
    · exact absurd hij.symm (hne j i)
    · have hij' : ComplexEmbedding.conjugate (φ i) = ComplexEmbedding.conjugate (φ j) := hij
      refine congrArg Sum.inr (h.1 ?_)
      show InfinitePlace.mk (φ i) = InfinitePlace.mk (φ j)
      rw [← InfinitePlace.mk_conjugate_eq (φ i), hij', InfinitePlace.mk_conjugate_eq]
  · intro ψ
    obtain ⟨i, hi⟩ := h.2 (InfinitePlace.mk ψ)
    rcases InfinitePlace.mk_eq_iff.1 hi with hi | hi
    · exact ⟨Sum.inl i, hi⟩
    · exact ⟨Sum.inr i, hi⟩

theorem prod_split {L : Type} [Field L] [NumberField L] [_root_.NumberField.IsTotallyComplex L] {I : Type} [Fintype I] (φ : I → L →+* ℂ)
    (h : Function.Bijective fun i => InfinitePlace.mk (φ i)) (f : (L →+* ℂ) → ℂ) :
    ∏ ψ, f ψ = ∏ i, (f (φ i) * f (ComplexEmbedding.conjugate (φ i))) := by
  rw [← (bijective_cmType φ h).prod_comp f, Fintype.prod_sum_type, Finset.prod_mul_distrib]
  rfl

theorem isAlg_of {L : Type} [Field L] [NumberField L] [_root_.NumberField.IsTotallyComplex L] {I : Type} [Fintype I] (φ : I → L →+* ℂ)
    (h : Function.Bijective fun i => InfinitePlace.mk (φ i)) (χ : HChar L) (a b : I → ℤ)
    (hχ : ∀ k : Lˣ, ((χ.inf k : ℂˣ) : ℂ) = ∏ i, (φ i k ^ a i * (starRingEnd ℂ (φ i k)) ^ b i)) :
    ∃ n, χ.IsAlg n := by
  let e := Equiv.ofBijective _ (bijective_cmType φ h)
  refine ⟨fun ψ => Sum.elim a b (e.symm ψ), fun k => ?_⟩
  rw [hχ k, prod_split φ h]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h1 : e.symm (φ i) = Sum.inl i := e.symm_apply_eq.2 rfl
  have h2 : e.symm (ComplexEmbedding.conjugate (φ i)) = Sum.inr i := e.symm_apply_eq.2 rfl
  simp only [h1, h2, Sum.elim_inl, Sum.elim_inr, ComplexEmbedding.conjugate_coe_eq]

theorem even_pow {z : ℂ} (hz : z ≠ 0) (c : ℤ) :
    (z / ((‖z‖ : ℝ) : ℂ)) ^ (2 * c) = z ^ c * (starRingEnd ℂ z) ^ (-c) := by
  have hc : starRingEnd ℂ z ≠ 0 := by simpa using hz
  have h : (z / ((‖z‖ : ℝ) : ℂ)) ^ (2 : ℤ) = z / starRingEnd ℂ z := by
    rw [zpow_ofNat, div_pow, ← Complex.mul_conj', sq, mul_div_mul_left _ _ hz]
  rw [zpow_mul, h, div_zpow, zpow_neg, div_eq_mul_inv]

theorem odd_pow {z : ℂ} (hz : z ≠ 0) (m : ℕ) :
    ((z / ((‖z‖ : ℝ) : ℂ)) ^ (1 : ℤ))⁻¹ *
      (((‖z‖ : ℝ) : ℂ) ^ (((-((2 * m + 1 : ℕ) : ℝ) / 2 : ℝ)) : ℂ) *
        ((‖z‖ : ℝ) : ℂ) ^ (((-((2 * m + 1 : ℕ) : ℝ) / 2 : ℝ)) : ℂ)) =
      z ^ (-1 - (m : ℤ)) * (starRingEnd ℂ z) ^ (-(m : ℤ)) := by
  have hc : starRingEnd ℂ z ≠ 0 := by simpa using hz
  have hn : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by simpa using hz
  have he : (((-((2 * m + 1 : ℕ) : ℝ) / 2 : ℝ)) : ℂ) + (((-((2 * m + 1 : ℕ) : ℝ) / 2 : ℝ)) : ℂ) =
      -((2 * m + 1 : ℕ) : ℂ) := by push_cast; ring
  rw [← Complex.cpow_add _ _ hn, he, Complex.cpow_neg, Complex.cpow_natCast, pow_succ, pow_mul,
    ← Complex.mul_conj', zpow_sub₀ hz, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, zpow_one, zpow_one, mul_pow]
  field_simp

theorem isAlg_even_odd : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R), (∀ (χ : HChar H.E) (c : R.Psi → ℤ), χ.HasInf (embPsi H) (fun τ => 2 * c τ) → ∃ n, χ.IsAlg n) ∧ ∀ (η : HChar H.E), η.HasInf (embPsi H) (fun _ => 1) → ∀ r : ℕ, Odd r → ∃ n, (η⁻¹ * GlobalTheory.HeckeGal.Model.absPow H.E (-(r : ℝ) / 2)).IsAlg n := by
  intro R H
  obtain ⟨c0, -, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  have := hcm.cplx
  have hz : ∀ (i : R.Psi) (k : (H.E)ˣ), embPsi H i (k : H.E) ≠ 0 := fun i k => by simp
  refine ⟨fun χ c hχ => isAlg_of (embPsi H) hcm.bij χ c (fun i => -c i) fun k => ?_, ?_⟩
  · rw [hχ k]
    exact Finset.prod_congr rfl fun i _ => even_pow (hz i k) (c i)
  · rintro η hη r ⟨m, rfl⟩
    refine isAlg_of (embPsi H) hcm.bij _ (fun _ => -1 - (m : ℤ)) (fun _ => -(m : ℤ)) fun k => ?_
    rw [HChar.inf_mul, HChar.inf_inv, Units.val_mul, Units.val_inv_eq_inv_val, hη k,
      (GlobalTheory.HeckeGal.Model.absPow_isAbsPow H.E _).2.2 k, prod_split (embPsi H) hcm.bij, ← Finset.prod_inv_distrib,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj]
    exact odd_pow (hz i k) m

end GlobalTheory.Mem.CharAlg
end
