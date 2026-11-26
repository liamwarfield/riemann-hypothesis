module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ChartChange
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.SelmerDuality.CardCokernelTransposeEqCardKernel
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PlaceDict
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CharFil

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FiniteLevelOfFiniteLevelMod
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

private theorem killed (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module ℤ_[l] M] [Finite M] :
    ∃ r : ℕ, 0 < r ∧ ∀ x : M, (l : ℤ_[l]) ^ r • x = 0 :=
  _root_.UpperTheory.Reformulated.B.Qe12.killed l M

private theorem H0dual_eq {G A V : Type} [Group G] [CommRing A] [AddCommGroup V] [Module A V] (χ : G →* Aˣ)
    (ρ : Representation A G V) : H0dual χ ρ = (coSub χ ρ).dualAnnihilator := by
  ext f
  rw [Submodule.mem_dualAnnihilator]
  constructor
  · intro hf
    have : coSub χ ρ ≤ LinearMap.ker f := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨g, x, rfl⟩
      have := hf g x
      simp [this]
    exact fun w hw => this hw
  · intro hf g x
    have := hf _ (Submodule.subset_span ⟨g, x, rfl⟩)
    rw [map_sub, map_smul, sub_eq_zero] at this
    exact this

private theorem card_co {G Q A V : Type} [Group G] [CommRing Q] [CommRing A] [Algebra Q A] [AddCommGroup V]
    [Module A V] [Module Q V] [IsScalarTower Q A V] (hs : Function.Surjective (algebraMap Q A)) (χ : G →* Qˣ)
    (χ' : G →* Aˣ) (h : ∀ g, ((χ' g : Aˣ) : A) = algebraMap Q A (χ g : Qˣ))
    (ρ : Representation A G V) : Nat.card (V ⧸ coSub χ' ρ) = Nat.card (V ⧸ coSub χ (resCoef Q ρ)) := by
  have e : coSub χ (resCoef Q ρ) = (coSub χ' ρ).restrictScalars Q := by
    unfold coSub
    rw [Submodule.restrictScalars_span Q A hs]
    congr 1
    ext y
    simp only [Set.mem_setOf_eq, h, algebraMap_smul]
    rfl
  rw [e]
  exact Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv Q (coSub χ' ρ)).toEquiv.symm

private def modRep (n : ℕ) {G Q V : Type} [Group G] [CommRing Q] [AddCommGroup V] [Module Q V] [Module (ZMod n) V]
    (ρ : Representation Q G V) : Representation (ZMod n) G V where
  toFun g := (ρ g).toAddMonoidHom.toZModLinearMap n
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

theorem UpperTheory.finite_level_of_finite_level_mod :
    ∀ (l : ℕ) [Fact l.Prime] (G : Type) [Group G] [TopologicalSpace G] (χ : G →* ℤ_[l]ˣ) (d : ℕ), FinLevelMod l G χ d → FinLevel l G χ d := by
  intro l _ G _ _ χ d h M _ _ _ _ _ ρ hρ
  obtain ⟨r, hr, hk⟩ := killed l M
  have hk' : ∀ x : M, (l ^ r) • x = 0 := fun x => by
    rw [← Nat.cast_smul_eq_nsmul ℤ_[l], Nat.cast_pow]; exact hk x
  haveI : NeZero (l ^ r) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨_⟩ : Nonempty (Module (ZMod (l ^ r)) M) := ⟨AddCommGroup.zmodModule hk'⟩
  letI : Algebra ℤ_[l] (ZMod (l ^ r)) := (PadicInt.toZModPow r).toAlgebra
  have hs : Function.Surjective (algebraMap ℤ_[l] (ZMod (l ^ r))) := ZMod.ringHom_surjective _
  haveI : IsScalarTower ℤ_[l] (ZMod (l ^ r)) M := by
    refine IsScalarTower.of_algebraMap_smul fun a x => ?_
    obtain ⟨k, hk2⟩ := ZMod.natCast_zmod_surjective (PadicInt.toZModPow r a)
    have h0 : a - k ∈ RingHom.ker (PadicInt.toZModPow (p := l) r) := by
      rw [RingHom.mem_ker, map_sub, map_natCast, hk2, sub_self]
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton'] at h0
    obtain ⟨b, hb⟩ := h0
    change PadicInt.toZModPow r a • x = a • x
    rw [← hk2, Nat.cast_smul_eq_nsmul, eq_add_of_sub_eq hb.symm, add_smul, mul_smul, hk, smul_zero, zero_add,
      Nat.cast_smul_eq_nsmul]
  let ρ' : Representation (ZMod (l ^ r)) G M := modRep (l ^ r) ρ
  have e : resCoef ℤ_[l] ρ' = ρ := by ext; rfl
  obtain ⟨a1, a2, a3, a4, a5⟩ := h r hr M ρ' hρ
  obtain ⟨⟨e0⟩, ⟨e1⟩, ⟨e2⟩, en⟩ := UpperTheory.nonempty_cohomology_restrictScalars_linearEquiv ℤ_[l] ρ'
  rw [← e]
  refine ⟨Finite.of_equiv _ e1.toEquiv.symm, Finite.of_equiv _ e2.toEquiv.symm, fun n hn => ?_, ?_, ?_⟩
  · obtain ⟨e'⟩ := en n
    have := a3 n hn
    exact e'.toEquiv.subsingleton
  · rw [Nat.card_congr e0.toEquiv, Nat.card_congr e1.toEquiv, Nat.card_congr e2.toEquiv, a4]
  · rw [Nat.card_congr e2.toEquiv, a5, H0dual_eq,
      ← Nat.card_congr (Submodule.dualQuotEquivDualAnnihilator _).toEquiv]
    have : Finite (M ⧸ coSub ((Units.map (PadicInt.toZModPow r : ℤ_[l] →+* ZMod (l ^ r)).toMonoidHom).comp χ) ρ') :=
      Finite.of_surjective _ (Submodule.mkQ_surjective _)
    rw [KStar.Selmer.card_dual_of_baer KStar.Selmer.zmod_baer]
    exact card_co hs χ _ (fun g => rfl) ρ'
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CardCoinvariantsModPowEqModPowCoinvariants
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

theorem UpperTheory.card_coinvariants_mod_pow_eq_mod_pow_coinvariants :
    ∀ {l : ℕ} [Fact l.Prime] {G X : Type} [Group G] [AddCommGroup X] [Module ℤ_[l] X] (χ : G →* ℤ_[l]ˣ) (ρ : Representation ℤ_[l] G X) (m : ℕ), Nat.card ((X ⧸ lSub l X m) ⧸ coSub χ (redRep ρ m)) = Nat.card ((X ⧸ coSub χ ρ) ⧸ lSub l (X ⧸ coSub χ ρ) m) := by
  intro l _ G X _ _ _ χ ρ m
  have hq : ∀ g x, UpperTheory.V.Loc.redRep ρ m g ((lSub l X m).mkQ x) = (lSub l X m).mkQ (ρ g x) :=
    fun g x => rfl
  have hC : coSub χ (UpperTheory.V.Loc.redRep ρ m) = (coSub χ ρ).map (lSub l X m).mkQ := by
    unfold coSub
    rw [Submodule.map_span]
    congr 1
    ext y
    constructor
    · rintro ⟨g, x, rfl⟩
      obtain ⟨x, rfl⟩ := (lSub l X m).mkQ_surjective x
      exact ⟨ρ g x - (χ g : ℤ_[l]) • x, ⟨g, x, rfl⟩, by rw [map_sub, map_smul, hq]⟩
    · rintro ⟨_, ⟨g, x, rfl⟩, rfl⟩
      exact ⟨g, (lSub l X m).mkQ x, by rw [map_sub, map_smul, hq]⟩
  have hL : lSub l (X ⧸ coSub χ ρ) m = (lSub l X m).map (coSub χ ρ).mkQ := by
    ext y
    rw [mem_lSub, Submodule.mem_map]
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨z, rfl⟩ := (coSub χ ρ).mkQ_surjective z
      exact ⟨(l : ℤ_[l]) ^ m • z, mem_lSub.2 ⟨z, rfl⟩, by simp⟩
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨z, rfl⟩ := mem_lSub.1 hx
      exact ⟨(coSub χ ρ).mkQ z, by simp⟩
  rw [hC, hL]
  exact Nat.card_congr ((Submodule.quotientQuotientEquivQuotientSup _ _).toEquiv.trans
    ((Submodule.quotEquivOfEq _ _ (sup_comm _ _)).toEquiv.trans
      (Submodule.quotientQuotientEquivQuotientSup _ _).symm.toEquiv))
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LatticeCohomologyFiniteAndGrowthOfFinGen
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

open ReciprocityTheory.Coh in
private theorem latGrow_bound {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {n : ℕ}
    (ρ : Representation ℤ_[l] G (Fin n → ℤ_[l])) (h : ContAction ρ)
    (hF : Cx.FinGen (TRep.coch ({ V := Fin n → ℤ_[l], rho := ρ, cont := h } : TRep ℤ_[l] G)) 2) (k : ℕ) :
    ∃ C : ℕ, ∀ m : ℕ,
      (length ℤ_[l] (({ V := _, rho := redRep ρ m, cont := contAction_redRep h m } : TRep ℤ_[l] G).H k)).toNat ≤
        m * finrank ℤ_[l] (({ V := Fin n → ℤ_[l], rho := ρ, cont := h } : TRep ℤ_[l] G).H k) + C ∧
      m * finrank ℤ_[l] (({ V := Fin n → ℤ_[l], rho := ρ, cont := h } : TRep ℤ_[l] G).H k) ≤
      (length ℤ_[l] (({ V := _, rho := redRep ρ m, cont := contAction_redRep h m } : TRep ℤ_[l] G).H k)).toNat := by
  let L : TRep ℤ_[l] G := { V := Fin n → ℤ_[l], rho := ρ, cont := h }
  refine ⟨(length ℤ_[l] (Submodule.torsion ℤ_[l] (L.H k))).toNat +
    (length ℤ_[l] (Submodule.torsion ℤ_[l] (L.H (k + 1)))).toNat, fun m => ?_⟩
  let C : TRep ℤ_[l] G := { V := _, rho := redRep ρ m, cont := contAction_redRep h m }
  have hc : Continuous (((l : ℤ_[l]) ^ m) • (LinearMap.id : (Fin n → ℤ_[l]) →ₗ[ℤ_[l]] (Fin n → ℤ_[l]))) :=
    continuous_const_smul ((l : ℤ_[l]) ^ m)
  let i : Pair L L := Pair.ofMap (((l : ℤ_[l]) ^ m) • (LinearMap.id : (Fin n → ℤ_[l]) →ₗ[ℤ_[l]] (Fin n → ℤ_[l]))) hc
    fun g x => (map_smul (ρ g) ((l : ℤ_[l]) ^ m) x).symm
  let p : Pair L C := Pair.ofMap (lSub l (Fin n → ℤ_[l]) m).mkQ (continuous_mkQ _) fun _ _ => rfl
  have hl : (l : ℤ_[l]) ^ m ≠ 0 := pow_ne_zero _ PadicInt.irreducible_p.ne_zero
  have hA : admitted i p := by
    refine ⟨rfl, rfl, ?_, ?_, ?_⟩
    · refine (hc.isClosedEmbedding ?_).isEmbedding
      exact smul_right_injective (Fin n → ℤ_[l]) hl
    · exact LinearMap.exact_map_mkQ_range _
    · exact ⟨Function.surjInv (lSub l (Fin n → ℤ_[l]) m).mkQ_surjective,
        continuous_of_discreteTopology (α := (Fin n → ℤ_[l]) ⧸ lSub l (Fin n → ℤ_[l]) m),
        Function.surjInv_eq _⟩
  have hR := (rankLen_holds ℤ_[l] (l : ℤ_[l]) PadicInt.irreducible_p L.coch C.coch i.hom p.hom m 2
    (fun _ _ => rfl) (admissibility_holds _ _ _ _ _ i p hA) hF).2.2 k
  exact ⟨hR.1.trans (add_assoc _ _ _).le, hR.2⟩

private theorem latGrow_card {l : ℕ} [Fact l.Prime] {M N : Type} [AddCommGroup M] [Module ℤ_[l] M]
    [AddCommGroup N] [Module ℤ_[l] N] [Finite N] (e : M ≃ₗ[ℤ_[l]] N) {a b : ℕ}
    (h : (length ℤ_[l] M).toNat ≤ b ∧ a ≤ (length ℤ_[l] M).toNat) :
    l ^ a ≤ Nat.card N ∧ Nat.card N ≤ l ^ b := by
  obtain ⟨k, hk, hc⟩ := UpperTheory.V.Kum.lenOfCard l N
  rw [e.length_eq, hk, ENat.toNat_coe] at h
  rw [hc]
  have hp : 0 < l := (Fact.out : l.Prime).pos
  exact ⟨Nat.pow_le_pow_right hp h.2, Nat.pow_le_pow_right hp h.1⟩

open ReciprocityTheory.Coh in
theorem UpperTheory.lattice_cohomology_finite_and_growth_of_finGen :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {n : ℕ} (ρ : Representation ℤ_[l] G (Fin n → ℤ_[l])) (h : ContAction ρ), ReciprocityTheory.Coh.Cx.FinGen (ReciprocityTheory.Coh.TRep.coch ({ V := Fin n → ℤ_[l], rho := ρ, cont := h } : ReciprocityTheory.Coh.TRep ℤ_[l] G)) 2 → (∀ m, Finite (H1 (redRep ρ m)) ∧ Finite (H2 (redRep ρ m))) → Module.Finite ℤ_[l] (H1 ρ) ∧ Module.Finite ℤ_[l] (H2 ρ) ∧ Grows l (fun m => Nat.card ↥(H0 (redRep ρ m))) (finrank ℤ_[l] ↥(H0 ρ)) ∧ Grows l (fun m => Nat.card (H1 (redRep ρ m))) (finrank ℤ_[l] (H1 ρ)) ∧ Grows l (fun m => Nat.card (H2 (redRep ρ m))) (finrank ℤ_[l] (H2 ρ)) := by
  intro l _ G _ _ _ n ρ h hF hfin
  obtain ⟨-, ⟨e₀, -⟩, ⟨e₁, -⟩, e₂, -⟩ :=
    low_holds ℤ_[l] G ({ V := Fin n → ℤ_[l], rho := ρ, cont := h } : TRep ℤ_[l] G)
  have hq := fun m => low_holds ℤ_[l] G ({ V := _, rho := redRep ρ m, cont := contAction_redRep h m } : TRep ℤ_[l] G)
  haveI := hF.1 1
  haveI := hF.1 2
  refine ⟨Module.Finite.equiv e₁, Module.Finite.equiv e₂, ?_, ?_, ?_⟩
  · obtain ⟨C, hC⟩ := latGrow_bound ρ h hF 0
    refine ⟨C, fun m _ => ?_⟩
    obtain ⟨-, ⟨q, -⟩, -⟩ := hq m
    rw [e₀.finrank_eq] at hC
    haveI : Finite (H0 (redRep ρ m)) := inferInstance
    exact latGrow_card (N := H0 (redRep ρ m)) q (hC m)
  · obtain ⟨C, hC⟩ := latGrow_bound ρ h hF 1
    refine ⟨C, fun m _ => ?_⟩
    obtain ⟨-, -, ⟨q, -⟩, -⟩ := hq m
    rw [e₁.finrank_eq] at hC
    haveI := (hfin m).1
    exact latGrow_card (N := H1 (redRep ρ m)) q (hC m)
  · obtain ⟨C, hC⟩ := latGrow_bound ρ h hF 2
    refine ⟨C, fun m _ => ?_⟩
    obtain ⟨-, -, -, q, -⟩ := hq m
    rw [e₂.finrank_eq] at hC
    haveI := (hfin m).2
    exact latGrow_card (N := H2 (redRep ρ m)) q (hC m)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LatticeCochainsFinGenOfFinLevel
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

section
open ReciprocityTheory.Coh
variable {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {n : ℕ}

private noncomputable def redT (ρ : Representation ℤ_[l] G (Fin n → ℤ_[l])) (h : ContAction ρ) (m : ℕ) :
    TRep ℤ_[l] G :=
  { V := (Fin n → ℤ_[l]) ⧸ lSub l (Fin n → ℤ_[l]) (m + 1)
    ccs := ⟨fun _ => continuous_of_discreteTopology⟩
    rho := redRep ρ (m + 1)
    cont := contAction_redRep h (m + 1) }

private instance redT_disc (ρ : Representation ℤ_[l] G (Fin n → ℤ_[l])) (h : ContAction ρ) (m : ℕ) :
    DiscreteTopology (redT ρ h m).V := discrete_quot_lSub l n (m + 1)

private instance redT_fin (ρ : Representation ℤ_[l] G (Fin n → ℤ_[l])) (h : ContAction ρ) (m : ℕ) :
    Finite (redT ρ h m).V := finite_quot_lSub l n (m + 1)

private theorem lSub_le {X : Type} [AddCommGroup X] [Module ℤ_[l] X] (m : ℕ) :
    lSub l X (m + 1) ≤ (lSub l X m).comap LinearMap.id := by
  intro x hx
  obtain ⟨y, rfl⟩ := mem_lSub.mp hx
  show (l : ℤ_[l]) ^ (m + 1) • y ∈ lSub l X m
  exact mem_lSub.mpr ⟨(l : ℤ_[l]) • y, by rw [pow_succ, mul_smul]⟩

private noncomputable def tauL (l : ℕ) [Fact l.Prime] (X : Type) [AddCommGroup X] [Module ℤ_[l] X] (m : ℕ) :
    (X ⧸ lSub l X (m + 1)) →ₗ[ℤ_[l]] (X ⧸ lSub l X m) :=
  Submodule.mapQ _ _ LinearMap.id (lSub_le m)

private theorem tauL_mk {X : Type} [AddCommGroup X] [Module ℤ_[l] X] (m : ℕ) (x : X) :
    tauL l X m (Submodule.Quotient.mk x) = Submodule.Quotient.mk x := rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] in
private theorem tauL_equiv {X : Type} [AddCommGroup X] [Module ℤ_[l] X] (ρ : Representation ℤ_[l] G X) (m : ℕ)
    (g : G) (y : X ⧸ lSub l X (m + 1)) : tauL l X m (redRep ρ (m + 1) g y) = redRep ρ m g (tauL l X m y) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [redRep_mk, tauL_mk, tauL_mk, redRep_mk]

private theorem tauL_surj {X : Type} [AddCommGroup X] [Module ℤ_[l] X] (m : ℕ) :
    Function.Surjective (tauL l X m) := by
  intro y
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  exact ⟨Submodule.Quotient.mk x, rfl⟩

private noncomputable def tauT (ρ : Representation ℤ_[l] G (Fin n → ℤ_[l])) (h : ContAction ρ) (m : ℕ) :
    Pair (redT ρ h (m + 1)) (redT ρ h m) :=
  Pair.ofMap (M := redT ρ h (m + 1)) (M' := redT ρ h m)
    (tauL l (Fin n → ℤ_[l]) (m + 1)) continuous_of_discreteTopology (tauL_equiv ρ (m + 1))

private noncomputable def piT (ρ : Representation ℤ_[l] G (Fin n → ℤ_[l])) (h : ContAction ρ) (m : ℕ) :
    Pair ({ V := Fin n → ℤ_[l], rho := ρ, cont := h } : TRep ℤ_[l] G) (redT ρ h m) :=
  Pair.ofMap (M := ({ V := Fin n → ℤ_[l], rho := ρ, cont := h } : TRep ℤ_[l] G)) (M' := redT ρ h m)
    (lSub l (Fin n → ℤ_[l]) (m + 1)).mkQ (continuous_mkQ _) (fun g x => (redRep_mk ρ (m + 1) g x).symm)

private theorem eq_zero_of_lSub (x : Fin n → ℤ_[l]) (hx : ∀ m, x ∈ lSub l (Fin n → ℤ_[l]) (m + 1)) : x = 0 := by
  funext i
  apply PadicInt.ext_of_toZModPow.mp
  intro k
  rw [Pi.zero_apply, map_zero]
  cases k with
  | zero =>
    haveI : Subsingleton (ZMod (l ^ 0)) := ZMod.subsingleton_iff.mpr (pow_zero _)
    exact Subsingleton.elim _ _
  | succ k => exact mem_lSub_pi.mp (hx k) i

private theorem towerLim (ρ : Representation ℤ_[l] G (Fin n → ℤ_[l])) (h : ContAction ρ) :
    Cx.IsTowerLim (fun m => (redT ρ h m).coch) (fun m => (tauT ρ h m).hom)
      (TRep.coch ({ V := Fin n → ℤ_[l], rho := ρ, cont := h } : TRep ℤ_[l] G)) fun m => (piT ρ h m).hom := by
  refine limRep_holds ℤ_[l] G (fun m => redT ρ h m) (tauT ρ h) _ (piT ρ h)
    (fun m => ⟨rfl, rfl, tauL_surj (m + 1), fun x => rfl⟩) ?_ ?_
  · have hc : Continuous fun (x : Fin n → ℤ_[l]) (m : ℕ) => (piT ρ h m).u x :=
      continuous_pi fun m => (piT ρ h m).u_cont
    refine (hc.isClosedEmbedding ?_).isEmbedding
    intro x y hxy
    rw [← sub_eq_zero]
    apply eq_zero_of_lSub
    intro m
    have := congr_fun hxy m
    exact (Submodule.Quotient.eq _).mp this
  · intro y hy
    let S : ℕ → Set (Fin n → ℤ_[l]) := fun m => (piT ρ h m).u ⁻¹' {y m}
    have hS : (⋂ m, S m).Nonempty := by
      apply IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S
      · intro m x hx
        show (piT ρ h m).u x = y m
        have hx' : (piT ρ h (m + 1)).u x = y (m + 1) := hx
        rw [← hy m, ← hx']
        rfl
      · intro m
        obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (y m)
        exact ⟨x, hx⟩
      · exact isCompact_univ.of_isClosed_subset
          ((isClosed_singleton).preimage (piT ρ h 0).u_cont) (Set.subset_univ _)
      · intro m
        exact (isClosed_singleton).preimage (piT ρ h m).u_cont
    obtain ⟨x, hx⟩ := hS
    exact ⟨x, fun m => Set.mem_iInter.mp hx m⟩

private theorem smul_emb (m : ℕ) : IsEmbedding fun x : Fin n → ℤ_[l] => (l : ℤ_[l]) ^ m • x := by
  have hc : (l : ℤ_[l]) ^ m ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero)
  refine (Continuous.isClosedEmbedding (continuous_const_smul _) ?_).isEmbedding
  intro x y hxy
  funext i
  have := congr_fun hxy i
  simp only [Pi.smul_apply, smul_eq_mul] at this
  exact mul_left_cancel₀ hc this

private theorem finH {χ : G →* ℤ_[l]ˣ} {d : ℕ} (hF : FinLevel l G χ d) (M : TRep ℤ_[l] G) [Finite M.V]
    [DiscreteTopology M.V] : (∀ k, Finite (M.H k)) ∧ ∀ k, 2 < k → Subsingleton (M.H k) := by
  obtain ⟨h1, h2, h3, -, -⟩ := hF M.V M.rho M.cont
  obtain ⟨hN, ⟨e0, -⟩, ⟨e1, -⟩, ⟨e2, -⟩⟩ := low_holds ℤ_[l] G M
  refine ⟨fun k => ?_, fun k hk => ?_⟩
  · match k with
    | 0 => exact Finite.of_equiv _ e0.symm.toEquiv
    | 1 => exact Finite.of_equiv _ e1.symm.toEquiv
    | 2 => exact Finite.of_equiv _ e2.symm.toEquiv
    | k + 3 =>
      obtain ⟨e, -⟩ := hN (k + 3)
      haveI := h3 (k + 3) (by omega)
      exact Finite.of_equiv _ e.symm.toEquiv
  · obtain ⟨e, -⟩ := hN k
    haveI := h3 k (by omega)
    exact e.toEquiv.subsingleton

end

theorem UpperTheory.latticeCochains_finGen_of_finLevel :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {χ : G →* ℤ_[l]ˣ} {d : ℕ}, FinLevel l G χ d → ∀ {n : ℕ} (ρ : Representation ℤ_[l] G (Fin n → ℤ_[l])) (h : ContAction ρ), ReciprocityTheory.Coh.Cx.FinGen (ReciprocityTheory.Coh.TRep.coch ({ V := Fin n → ℤ_[l], rho := ρ, cont := h } : ReciprocityTheory.Coh.TRep ℤ_[l] G)) 2 := by
  intro l _ G _ _ _ χ d hF n ρ h
  haveI : IsAdicComplete (Ideal.span {(l : ℤ_[l])}) ℤ_[l] :=
    PadicInt.maximalIdeal_eq_span_p (p := l) ▸ inferInstance
  have hl : (l : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
  have hT := towerLim ρ h
  have htors : ∀ (k : ℕ) (x : (ReciprocityTheory.Coh.TRep.coch ({ V := Fin n → ℤ_[l], rho := ρ, cont := h } : ReciprocityTheory.Coh.TRep ℤ_[l] G)).X k),
      (l : ℤ_[l]) • x = 0 → x = 0 := by
    intro k x hx
    apply Subtype.ext
    funext g
    have := congr_arg (fun z : (ReciprocityTheory.Coh.TRep.coch ({ V := Fin n → ℤ_[l], rho := ρ, cont := h } : ReciprocityTheory.Coh.TRep ℤ_[l] G)).X k =>
      z.1 g) hx
    exact (smul_eq_zero.mp this).resolve_left hl
  have hker : ∀ (m k : ℕ) (x : (ReciprocityTheory.Coh.TRep.coch ({ V := Fin n → ℤ_[l], rho := ρ, cont := h } : ReciprocityTheory.Coh.TRep ℤ_[l] G)).X k),
      ((piT ρ h m).hom.f k) x = 0 ↔ ∃ y, x = (l : ℤ_[l]) ^ (m + 1) • y := by
    intro m k x
    have key : ((piT ρ h m).hom.f k) x = 0 ↔
        ∀ g, x.1 g ∈ lSub l (Fin n → ℤ_[l]) (m + 1) := by
      constructor
      · intro hx g
        have := congr_arg (fun z : (ReciprocityTheory.Coh.TRep.coch (redT ρ h m)).X k =>
          z.1 g) hx
        exact (Submodule.Quotient.mk_eq_zero _).mp this
      · intro hx
        apply Subtype.ext
        funext g
        exact (Submodule.Quotient.mk_eq_zero _).mpr (hx g)
    rw [key]
    constructor
    · intro hx
      choose y hy using fun g => mem_lSub.mp (hx g)
      have hyc : Continuous y := by
        apply (smul_emb (n := n) (l := l) (m + 1)).continuous_iff.mpr
        have : (fun x : Fin n → ℤ_[l] => (l : ℤ_[l]) ^ (m + 1) • x) ∘ y =
            x.1 := funext hy
        rw [this]
        exact x.2
      refine ⟨⟨y, hyc⟩, ?_⟩
      apply Subtype.ext
      funext g
      exact (hy g).symm
    · rintro ⟨y, rfl⟩ g
      exact mem_lSub.mpr ⟨y.1 g, rfl⟩
  have hfin : ∀ m, (∀ k, Finite ((redT ρ h m).H k)) ∧ ∀ k, 2 < k → Subsingleton ((redT ρ h m).H k) :=
    fun m => finH hF (redT ρ h m)
  have hlen0 : ∀ k, IsFiniteLength ℤ_[l] ((redT ρ h 0).coch.H k) := fun k => by
    haveI := (hfin 0).1 k
    exact isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩
  have res := ReciprocityTheory.Coh.finGen_holds ℤ_[l] (l : ℤ_[l]) _ _ _ _ hT htors hker hlen0
  refine ⟨fun k => (res k).1, fun k hk => ?_⟩
  have ext := (ReciprocityTheory.Coh.tower_holds ℤ_[l] _ _ _ _ hT k).2 (fun j _ m => by
    haveI := (hfin m).1 j
    infer_instance)
  refine ⟨fun a b => ?_⟩
  have ha := ext a (fun m => by
    haveI := (hfin m).2 k hk
    exact Subsingleton.elim _ _)
  have hb := ext b (fun m => by
    haveI := (hfin m).2 k hk
    exact Subsingleton.elim _ _)
  rw [ha, hb]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsInvariantLatticeOpenEmbedding
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

private theorem exists_pow_mul_norm_le {l : ℕ} [Fact l.Prime] (C : ℝ) :
    ∃ m : ℕ, ∀ a : ℚ_[l], ‖a‖ ≤ C → ‖(l : ℚ_[l]) ^ m * a‖ ≤ 1 := by
  have h1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt C h1
  refine ⟨m, fun a ha => ?_⟩
  have hp : (0 : ℝ) < (l : ℝ) ^ m := by positivity
  rw [norm_mul, norm_pow, Padic.norm_p, inv_pow, inv_mul_le_iff₀ hp, mul_one]
  exact ha.trans hm.le

theorem UpperTheory.exists_invariant_lattice_openEmbedding :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul ℚ_[l] V] (ρ : Representation ℚ_[l] G V), ContAction ρ → ∃ (ρT : Representation ℤ_[l] G (Fin (finrank ℚ_[l] V) → ℤ_[l])) (j : (Fin (finrank ℚ_[l] V) → ℤ_[l]) →ₗ[ℤ_[l]] V), ContAction ρT ∧ IsOpenEmbedding j ∧ (∀ g x, j (ρT g x) = ρ g (j x)) ∧ ∀ y : V, ∃ m : ℕ, (l : ℤ_[l]) ^ m • y ∈ LinearMap.range j := by
  intro l _ G _ _ _ _ V _ _ _ _ _ _ _ _ _ ρ h
  have hex : ∃ L : Submodule ℤ_[l] V, Submodule.IsFullLattice ℚ_[l] L ∧
      ∀ g, ∀ x ∈ L, ρ g x ∈ L := by
    classical
    let b := Module.finBasis ℚ_[l] V
    let S : Set V := Set.range fun p : G × Fin (finrank ℚ_[l] V) => ρ p.1 (b p.2)
    have hc : Continuous fun g : G => fun i => b.equivFun (ρ g (b i)) := by
      refine continuous_pi fun i => ?_
      exact (IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap).comp
        (h.comp (continuous_id.prodMk continuous_const))
    obtain ⟨C, hC⟩ := (isCompact_range hc).isBounded.exists_norm_le
    obtain ⟨m, hm⟩ := exists_pow_mul_norm_le (l := l) C
    have hl : ((l : ℚ_[l]) ^ m) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : l.Prime).ne_zero)
    refine ⟨Submodule.span ℤ_[l] S, { toIsLattice := ⟨?_, ?_⟩, span_eq_top := ?_ }, ?_⟩
    · let N : Submodule ℤ_[l] V := Submodule.span ℤ_[l] (Set.range fun i => ((l : ℚ_[l]) ^ m)⁻¹ • b i)
      have hN : N.FG := Submodule.fg_span (Set.finite_range _)
      refine hN.of_le ?_
      rw [Submodule.span_le]
      rintro _ ⟨⟨g, i⟩, rfl⟩
      have e := b.sum_repr (ρ g (b i))
      simp only [SetLike.mem_coe]
      rw [← e]
      refine Submodule.sum_mem _ fun k _ => ?_
      have hk : ‖b.repr (ρ g (b i)) k‖ ≤ C :=
        ((norm_le_pi_norm (b.equivFun (ρ g (b i))) k).trans
          (norm_le_pi_norm (fun i => b.equivFun (ρ g (b i))) i)).trans (hC _ ⟨g, rfl⟩)
      let z : ℤ_[l] := ⟨_, hm _ hk⟩
      have : b.repr (ρ g (b i)) k • b k = z • (((l : ℚ_[l]) ^ m)⁻¹ • b k) := by
        rw [← algebraMap_smul ℚ_[l] z, smul_smul]
        congr 1
        change _ = ((l : ℚ_[l]) ^ m * b.repr (ρ g (b i)) k) * _
        field_simp
      rw [this]
      exact N.smul_mem z (Submodule.subset_span ⟨k, rfl⟩)
    · intro s hs hli
      exact (LinearIndependent.iff_fractionRing ℤ_[l] ℚ_[l]).mp hli
    · rw [eq_top_iff, ← b.span_eq]
      refine Submodule.span_mono ?_
      rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨(1, i), by simp⟩
    · intro g x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨⟨g', i⟩, rfl⟩ := hx
        exact Submodule.subset_span ⟨(g * g', i), by simp⟩
      | zero => simp
      | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
      | smul a x _ hx => rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ a hx
  
  obtain ⟨L, hL, hst⟩ := hex
  letI : Module.Free ℤ_[l] L := Submodule.IsLattice.free ℚ_[l] L
  letI : Module.Finite ℤ_[l] L := Submodule.IsLattice.finite ℚ_[l] L
  have hr : finrank ℤ_[l] L = finrank ℚ_[l] V := by
    unfold Module.finrank
    rw [Submodule.IsLattice.rank' ℚ_[l] L]
  let bL : Basis (Fin (finrank ℚ_[l] V)) ℤ_[l] L := Module.finBasisOfFinrankEq ℤ_[l] L hr
  let b : Basis (Fin (finrank ℚ_[l] V)) ℚ_[l] V := bL.extendOfIsFullLattice ℚ_[l]
  let j : (Fin (finrank ℚ_[l] V) → ℤ_[l]) →ₗ[ℤ_[l]] V := L.subtype ∘ₗ bL.equivFun.symm.toLinearMap
  have hj : ∀ x, j x = b.equivFun.symm (fun i => (x i : ℚ_[l])) := fun x => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [j, b, LinearMap.comp_apply, LinearEquiv.coe_coe, Basis.equivFun_symm_apply, map_sum, map_smul,
      Submodule.subtype_apply, Basis.extendOfIsFullLattice_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (algebraMap_smul ℚ_[l] (x i) _).symm
  let e : (Fin (finrank ℚ_[l] V) → ℚ_[l]) ≃ₜ V :=
    { toEquiv := b.equivFun.symm.toEquiv
      continuous_toFun := IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap }
  have hjo : IsOpenEmbedding j := by
    have : (j : _ → V) = e ∘ Pi.map (fun _ => ((↑) : ℤ_[l] → ℚ_[l])) := funext hj
    rw [this]
    exact e.isOpenEmbedding.comp (IsOpenEmbedding.piMap fun _ => PadicInt.isOpenEmbedding_coe)
  let r : G → L →ₗ[ℤ_[l]] L := fun g => ((ρ g).restrictScalars ℤ_[l]).restrict (hst g)
  let ρT : Representation ℤ_[l] G (Fin (finrank ℚ_[l] V) → ℤ_[l]) :=
    { toFun := fun g => bL.equivFun.toLinearMap ∘ₗ r g ∘ₗ bL.equivFun.symm.toLinearMap
      map_one' := by
        refine LinearMap.ext fun x => bL.equivFun.symm.injective (Subtype.ext ?_)
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
        change ρ 1 _ = _
        rw [map_one]; rfl
      map_mul' := fun g g' => by
        refine LinearMap.ext fun x => bL.equivFun.symm.injective (Subtype.ext ?_)
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
          Module.End.mul_apply]
        change ρ (g * g') _ = _
        rw [map_mul]; rfl }
  have hρ : ∀ g x, j (ρT g x) = ρ g (j x) := fun g x => by
    change L.subtype (bL.equivFun.symm (bL.equivFun (r g (bL.equivFun.symm x)))) = _
    rw [LinearEquiv.symm_apply_apply]; rfl
  refine ⟨ρT, j, ?_, hjo, hρ, fun y => ?_⟩
  · unfold ReciprocityTheory.Gal.ContAction
    rw [hjo.isEmbedding.continuous_iff]
    have : (j ∘ fun p : G × (Fin (finrank ℚ_[l] V) → ℤ_[l]) => ρT p.1 p.2) = fun p => ρ p.1 (j p.2) :=
      funext fun p => hρ _ _
    rw [this]
    exact h.comp (continuous_fst.prodMk (hjo.continuous.comp continuous_snd))
  · obtain ⟨m, hm⟩ := exists_pow_mul_norm_le (l := l) ‖b.equivFun y‖
    refine ⟨m, fun i => ⟨_, hm _ (norm_le_pi_norm (b.equivFun y) i)⟩, ?_⟩
    refine (hj _).trans ?_
    rw [LinearEquiv.symm_apply_eq, ← algebraMap_smul ℚ_[l] ((l : ℤ_[l]) ^ m) y, map_smul]
    funext i
    change (l : ℚ_[l]) ^ m * b.equivFun y i = _
    simp
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.CardQuotientPowSubmoduleGrowsFinrank
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

private noncomputable def redMap {l : ℕ} [Fact l.Prime] {X Y : Type} [AddCommGroup X] [Module ℤ_[l] X] [AddCommGroup Y]
    [Module ℤ_[l] Y] (f : X →ₗ[ℤ_[l]] Y) (m : ℕ) : (X ⧸ lSub l X m) →ₗ[ℤ_[l]] (Y ⧸ lSub l Y m) :=
  Submodule.mapQ _ _ f fun x hx => by
    obtain ⟨y, rfl⟩ := mem_lSub.1 hx
    exact mem_lSub.2 ⟨f y, (map_smul _ _ _).symm⟩

private theorem card_quotient_eq_card_of_isReps (l : ℕ) [Fact l.Prime] (k : ℕ) :
    Nat.card (ℤ_[l] ⧸ Ideal.span {(l : ℤ_[l]) ^ k}) = l ^ k := by
  haveI : NeZero (l ^ k) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hs : Function.Surjective (PadicInt.toZModPow (p := l) k) := fun z => by
    obtain ⟨a, rfl⟩ := ZMod.natCast_zmod_surjective z
    exact ⟨a, map_natCast _ a⟩
  rw [← PadicInt.ker_toZModPow, Nat.card_congr (RingHom.quotientKerEquivOfSurjective hs).toEquiv,
    Nat.card_zmod]

private theorem finite_padicInt_quot_span_of_ne_zero (l : ℕ) [Fact l.Prime] {q : ℤ_[l]} (hq : q ≠ 0) :
    Finite (ℤ_[l] ⧸ Ideal.span {q}) := by
  have h : Ideal.span {q} = Ideal.span {(l : ℤ_[l]) ^ q.valuation} := by
    rw [Ideal.span_singleton_eq_span_singleton]
    refine Associated.symm ⟨PadicInt.unitCoeff hq, ?_⟩
    rw [mul_comm]
    exact (PadicInt.unitCoeff_spec hq).symm
  rw [h]
  apply Nat.finite_of_card_ne_zero
  rw [card_quotient_eq_card_of_isReps]
  exact pow_ne_zero _ (Fact.out : l.Prime).ne_zero

private theorem card_pi_padicInt_quot_lSub (l : ℕ) [Fact l.Prime] (n m : ℕ) :
    Nat.card ((Fin n → ℤ_[l]) ⧸ lSub l (Fin n → ℤ_[l]) m) = l ^ (m * n) := by
  let I : Ideal ℤ_[l] := Ideal.span {(l : ℤ_[l]) ^ m}
  let φ : (Fin n → ℤ_[l]) →ₗ[ℤ_[l]] (Fin n → ℤ_[l] ⧸ I) :=
    LinearMap.pi (fun i => (Submodule.mkQ I) ∘ₗ LinearMap.proj i)
  have hsurj : Function.Surjective φ := by
    intro g
    choose y hy using fun i => Submodule.Quotient.mk_surjective I (g i)
    exact ⟨y, funext fun i => hy i⟩
  have hker : LinearMap.ker φ = lSub l (Fin n → ℤ_[l]) m := by
    ext x
    rw [LinearMap.mem_ker, mem_lSub]
    constructor
    · intro hx
      have h2 : ∀ i, ∃ y, (l : ℤ_[l]) ^ m * y = x i := fun i => by
        have h1 : (Submodule.Quotient.mk (x i) : ℤ_[l] ⧸ I) = 0 := congrFun hx i
        rw [Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton'] at h1
        obtain ⟨a, ha⟩ := h1
        exact ⟨a, by rw [mul_comm]; exact ha⟩
      choose y hy using h2
      exact ⟨y, funext fun i => by simp [hy]⟩
    · rintro ⟨y, rfl⟩
      funext i
      show (Submodule.Quotient.mk _ : ℤ_[l] ⧸ I) = 0
      rw [Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton']
      exact ⟨y i, by simp [mul_comm]⟩
  rw [← hker, Nat.card_congr (φ.quotKerEquivOfSurjective hsurj).toEquiv, Nat.card_fun,
    card_quotient_eq_card_of_isReps, Nat.card_eq_fintype_card, Fintype.card_fin, ← pow_mul]

theorem UpperTheory.card_quotient_powSubmodule_grows_finrank :
    ∀ (l : ℕ) [Fact l.Prime] (N : Type) [AddCommGroup N] [Module ℤ_[l] N] [Module.Finite ℤ_[l] N], Grows l (fun m => Nat.card (N ⧸ lSub l N m)) (finrank ℤ_[l] N) := by
  intro l _ N _ _ _
  classical
  obtain ⟨n, ι, _, p, hp, e, ⟨f⟩⟩ := Module.equiv_free_prod_directSum ℤ_[l] N
  set D := DirectSum ι fun i => ℤ_[l] ⧸ ℤ_[l] ∙ p i ^ e i with hD
  let g : N ≃ₗ[ℤ_[l]] (Fin n → ℤ_[l]) × D :=
    f.trans (LinearEquiv.prodCongr (Finsupp.linearEquivFunOnFinite ℤ_[l] ℤ_[l] (Fin n))
      (LinearEquiv.refl _ _))
  haveI : Finite D := by
    haveI : ∀ i, Finite (ℤ_[l] ⧸ ℤ_[l] ∙ p i ^ e i) := fun i =>
      finite_padicInt_quot_span_of_ne_zero l (pow_ne_zero _ (hp i).ne_zero)
    exact Finite.of_injective _ (DirectSum.linearEquivFunOnFintype ℤ_[l] ι _).injective
  have hrank : finrank ℤ_[l] N = n := by
    apply Module.finrank_eq_of_rank_eq
    have h0 : Module.rank ℤ_[l] D = 0 := by
      rw [rank_eq_zero_iff]
      intro x
      refine ⟨(Nat.card D : ℤ_[l]), Nat.cast_ne_zero.2 Nat.card_pos.ne', ?_⟩
      rw [Nat.cast_smul_eq_nsmul]
      exact card_nsmul_eq_zero'
    rw [g.rank_eq, ← LinearMap.rank_range_add_rank_ker (LinearMap.fst ℤ_[l] (Fin n → ℤ_[l]) D),
      LinearMap.range_eq_top.2 LinearMap.fst_surjective, rank_top, LinearMap.ker_fst,
      rank_range_of_injective _ LinearMap.inr_injective, h0, add_zero, rank_fun', Fintype.card_fin]
  rw [hrank]
  refine ⟨Nat.card D, fun m _ => ?_⟩
  let f1 : N →ₗ[ℤ_[l]] (Fin n → ℤ_[l]) := LinearMap.fst _ _ _ ∘ₗ g.toLinearMap
  let f2 : N →ₗ[ℤ_[l]] D := LinearMap.snd _ _ _ ∘ₗ g.toLinearMap
  let Ψ := LinearMap.prod (redMap f1 m) (redMap f2 m)
  have hinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro q hq
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    have e1 : (Submodule.Quotient.mk (f1 x) : (Fin n → ℤ_[l]) ⧸ lSub l _ m) = 0 :=
      congrArg Prod.fst hq
    have e2 : (Submodule.Quotient.mk (f2 x) : D ⧸ lSub l D m) = 0 := congrArg Prod.snd hq
    rw [Submodule.Quotient.mk_eq_zero, mem_lSub] at e1 e2
    obtain ⟨y1, hy1⟩ := e1
    obtain ⟨y2, hy2⟩ := e2
    rw [Submodule.Quotient.mk_eq_zero, mem_lSub]
    refine ⟨g.symm (y1, y2), ?_⟩
    rw [← map_smul, Prod.smul_mk, hy1, hy2]
    simp [f1, f2]
  have hF := card_pi_padicInt_quot_lSub l n m
  haveI : Finite ((Fin n → ℤ_[l]) ⧸ lSub l (Fin n → ℤ_[l]) m) :=
    Nat.finite_of_card_ne_zero (by rw [hF]; exact pow_ne_zero _ (Fact.out : l.Prime).ne_zero)
  haveI : Finite (D ⧸ lSub l D m) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  haveI : Finite (N ⧸ lSub l N m) := Finite.of_injective _ hinj
  have hsurj : Function.Surjective (redMap f1 m) := by
    intro q
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    refine ⟨Submodule.Quotient.mk (g.symm (y, 0)), ?_⟩
    simp [redMap, f1]
  constructor
  · rw [← hF]
    exact Nat.card_le_card_of_surjective _ hsurj
  · calc Nat.card (N ⧸ lSub l N m)
        ≤ Nat.card (((Fin n → ℤ_[l]) ⧸ lSub l (Fin n → ℤ_[l]) m) × (D ⧸ lSub l D m)) :=
          Nat.card_le_card_of_injective _ hinj
      _ = l ^ (m * n) * Nat.card (D ⧸ lSub l D m) := by rw [Nat.card_prod, hF]
      _ ≤ l ^ (m * n) * Nat.card D :=
          Nat.mul_le_mul_left _ (Nat.card_le_card_of_surjective _ (Submodule.Quotient.mk_surjective _))
      _ ≤ l ^ (m * n) * l ^ (Nat.card D) :=
          Nat.mul_le_mul_left _ (Nat.lt_pow_self (Fact.out : l.Prime).one_lt).le
      _ = l ^ (m * n + Nat.card D) := (pow_add _ _ _).symm
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FinrankCoinvariantsEqFinrankLatticeCoinvariants
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

theorem UpperTheory.finrank_coinvariants_eq_finrank_lattice_coinvariants :
    ∀ {l : ℕ} [Fact l.Prime] {G T V : Type} [Group G] [AddCommGroup T] [Module ℤ_[l] T] [AddCommGroup V] [Module ℚ_[l] V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V] (χ : G →* ℤ_[l]ˣ) (ρ : Representation ℚ_[l] G V) (ρT : Representation ℤ_[l] G T) (j : T →ₗ[ℤ_[l]] V), Function.Injective j → (∀ g x, j (ρT g x) = ρ g (j x)) → (∀ y : V, ∃ m : ℕ, (l : ℤ_[l]) ^ m • y ∈ LinearMap.range j) → finrank ℚ_[l] (V ⧸ coSub ((Units.map (algebraMap ℤ_[l] ℚ_[l] : ℤ_[l] →* ℚ_[l])).comp χ) ρ) = finrank ℤ_[l] (T ⧸ coSub χ ρT) := by
  intro l _ G T V _ _ _ _ _ _ _ χ ρ ρT j hj hρ hs
  set N := coSub ((Units.map (algebraMap ℤ_[l] ℚ_[l] : ℤ_[l] →* ℚ_[l])).comp χ) ρ with hN
  have hl : ∀ m : ℕ, (l : ℤ_[l]) ^ m ∈ nonZeroDivisors ℤ_[l] := fun m =>
    mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ (by exact_mod_cast (Fact.out : l.Prime).ne_zero))
  have hgen : ∀ g x, j (ρT g x - ((χ g : ℤ_[l]ˣ) : ℤ_[l]) • x) =
      ρ g (j x) - ((((Units.map (algebraMap ℤ_[l] ℚ_[l] : ℤ_[l] →* ℚ_[l])).comp χ) g : ℚ_[l]ˣ) : ℚ_[l]) • j x := by
    intro g x
    rw [map_sub, hρ, map_smul, ← algebraMap_smul ℚ_[l] ((χ g : ℤ_[l]ˣ) : ℤ_[l]) (j x)]
    rfl
  have hρs : ∀ g (c : ℤ_[l]) (v : V), ρ g (c • v) = c • ρ g v := fun g c v => by
    rw [← algebraMap_smul ℚ_[l] c v, map_smul, algebraMap_smul]
  let q : V →ₗ[ℤ_[l]] (V ⧸ N) := N.mkQ.restrictScalars ℤ_[l]
  have hle : coSub χ ρT ≤ LinearMap.ker (q ∘ₗ j) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, x, rfl⟩
    change N.mkQ (j _) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, hgen]
    exact Submodule.subset_span ⟨g, j x, rfl⟩
  let f : (T ⧸ coSub χ ρT) →ₗ[ℤ_[l]] (V ⧸ N) := (coSub χ ρT).liftQ (q ∘ₗ j) hle
  have key : ∀ v ∈ N, ∃ c ∈ nonZeroDivisors ℤ_[l], c • v ∈ (coSub χ ρT).map j := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨g, x, rfl⟩ := hy
      obtain ⟨m, t, ht⟩ := hs x
      refine ⟨_, hl m, ρT g t - ((χ g : ℤ_[l]ˣ) : ℤ_[l]) • t, Submodule.subset_span ⟨g, t, rfl⟩, ?_⟩
      rw [hgen, ht, hρs, smul_sub, smul_comm]
    | zero => exact ⟨1, one_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, hx⟩ := hx
      obtain ⟨d, hd, hy⟩ := hy
      refine ⟨c * d, mul_mem hc hd, ?_⟩
      rw [smul_add]
      refine add_mem ?_ ?_
      · rw [mul_comm, mul_smul]; exact Submodule.smul_mem _ _ hx
      · rw [mul_smul]; exact Submodule.smul_mem _ _ hy
    | smul a x _ hx =>
      obtain ⟨c, hc, hx⟩ := hx
      obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj (nonZeroDivisors ℤ_[l]) a
      refine ⟨c * s, mul_mem hc s.2, ?_⟩
      have : (s : ℤ_[l]) • a • x = r • x := by
        rw [← algebraMap_smul ℚ_[l] (s : ℤ_[l]), smul_smul, mul_comm, hrs, algebraMap_smul]
      rw [mul_smul, this, smul_comm]
      exact Submodule.smul_mem _ _ hx
  haveI : IsLocalizedModule (nonZeroDivisors ℤ_[l]) f := by
    refine ⟨(isLocalizedModule_id (nonZeroDivisors ℤ_[l]) (V ⧸ N) ℚ_[l]).map_units, ?_, ?_⟩
    · intro y
      obtain ⟨v, rfl⟩ := N.mkQ_surjective y
      obtain ⟨m, t, ht⟩ := hs v
      refine ⟨⟨Submodule.Quotient.mk t, ⟨_, hl m⟩⟩, ?_⟩
      change (l : ℤ_[l]) ^ m • q v = q (j t)
      rw [ht, map_smul]
    · intro x y h
      obtain ⟨x, rfl⟩ := (coSub χ ρT).mkQ_surjective x
      obtain ⟨y, rfl⟩ := (coSub χ ρT).mkQ_surjective y
      have h' : j x - j y ∈ N := (Submodule.Quotient.eq N).1 h
      obtain ⟨c, hc, t, ht, e⟩ := key _ h'
      rw [← map_sub, ← map_smul] at e
      obtain rfl := hj e
      refine ⟨⟨c, hc⟩, ?_⟩
      change c • (coSub χ ρT).mkQ x = c • (coSub χ ρT).mkQ y
      rw [← map_smul, ← map_smul]
      refine (Submodule.Quotient.eq _).2 ?_
      rw [← smul_sub]; exact ht
  rw [IsLocalization.finrank_eq ℚ_[l] (nonZeroDivisors ℤ_[l]) le_rfl,
    IsLocalizedModule.finrank_eq (nonZeroDivisors ℤ_[l]) f le_rfl]
end

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

private theorem grows_le {l : ℕ} (hl : 1 < l) {a : ℕ → ℕ} {s t : ℕ} (h : Grows l a s) (h' : Grows l a t) :
    s ≤ t := by
  obtain ⟨_, h⟩ := h
  obtain ⟨C, h'⟩ := h'
  have := (Nat.pow_le_pow_iff_right hl).1 ((h (C + 1) C.succ_pos).1.trans (h' (C + 1) C.succ_pos).2)
  by_contra hc
  have : (C + 1) * (t + 1) ≤ (C + 1) * s := Nat.mul_le_mul_left _ (by omega)
  nlinarith

private theorem grows_unique {l : ℕ} (hl : 1 < l) {a b : ℕ → ℕ} {s t : ℕ} (h : Grows l a s) (h' : Grows l b t)
    (e : ∀ m, a m = b m) : s = t := by
  obtain rfl : a = b := funext e
  exact le_antisymm (grows_le hl h h') (grows_le hl h' h)

private theorem grows_mul {l : ℕ} {a b : ℕ → ℕ} {s t : ℕ} (h : Grows l a s) (h' : Grows l b t) :
    Grows l (fun m => a m * b m) (s + t) := by
  obtain ⟨C, h⟩ := h
  obtain ⟨D, h'⟩ := h'
  refine ⟨C + D, fun m hm => ⟨?_, ?_⟩⟩
  · rw [mul_add, pow_add]
    exact Nat.mul_le_mul (h m hm).1 (h' m hm).1
  · rw [show m * (s + t) + (C + D) = (m * s + C) + (m * t + D) by ring, pow_add]
    exact Nat.mul_le_mul (h m hm).2 (h' m hm).2

private theorem grows_pow (l n d : ℕ) : Grows l (fun m => (l ^ (m * n)) ^ d) (d * n) :=
  ⟨0, fun m _ => by
    have : (l ^ (m * n)) ^ d = l ^ (m * (d * n)) := by rw [← pow_mul]; congr 1; ring
    simp [this]⟩

private theorem tate_lattice {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {χ : G →* ℤ_[l]ˣ} {d : ℕ} (hF : FinLevel l G χ d) {n : ℕ}
    (ρ : Representation ℤ_[l] G (Fin n → ℤ_[l])) (h : ContAction ρ) :
    Module.Finite ℤ_[l] (H1 ρ) ∧ Module.Finite ℤ_[l] (H2 ρ) ∧
      finrank ℤ_[l] (H1 ρ) = finrank ℤ_[l] ↥(H0 ρ) + finrank ℤ_[l] (H2 ρ) + d * n ∧
      finrank ℤ_[l] (H2 ρ) = finrank ℤ_[l] ((Fin n → ℤ_[l]) ⧸ coSub χ ρ) := by
  have hl : 1 < l := (Fact.out : l.Prime).one_lt
  have hm := fun m => hF _ (redRep ρ m) (contAction_redRep h m)
  obtain ⟨f1, f2, g0, g1, g2⟩ := UpperTheory.lattice_cohomology_finite_and_growth_of_finGen ρ h (UpperTheory.latticeCochains_finGen_of_finLevel hF ρ h) fun m => ⟨(hm m).1, (hm m).2.1⟩
  refine ⟨f1, f2, grows_unique hl g1 (grows_mul (grows_mul g0 g2) (grows_pow l n d)) fun m => ?_,
    grows_unique hl g2 (UpperTheory.card_quotient_powSubmodule_grows_finrank l _) fun m => ?_⟩
  · rw [(hm m).2.2.2.1, card_quot_lSub]
  · rw [(hm m).2.2.2.2, UpperTheory.card_coinvariants_mod_pow_eq_mod_pow_coinvariants]

private theorem tate_Q {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] {χ : G →* ℤ_[l]ˣ} {d : ℕ} (hF : FinLevel l G χ d)
    {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V]
    [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul ℚ_[l] V]
    (ρ : Representation ℚ_[l] G V) (h : ContAction ρ) :
    Module.Finite ℚ_[l] (H1 ρ) ∧ Module.Finite ℚ_[l] (H2 ρ) ∧
      finrank ℚ_[l] (H1 ρ) = finrank ℚ_[l] ↥(H0 ρ) + finrank ℚ_[l] (H2 ρ) + d * finrank ℚ_[l] V ∧
      finrank ℚ_[l] (H2 ρ) =
        finrank ℚ_[l] (V ⧸ coSub ((Units.map (algebraMap ℤ_[l] ℚ_[l] : ℤ_[l] →* ℚ_[l])).comp χ) ρ) := by
  letI : Module ℤ_[l] V := Module.compHom V (algebraMap ℤ_[l] ℚ_[l])
  haveI : IsScalarTower ℤ_[l] ℚ_[l] V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  obtain ⟨ρT, j, hT, hj, he, hs⟩ := UpperTheory.exists_invariant_lattice_openEmbedding ρ h
  obtain ⟨r0, r1, r2⟩ := UpperTheory.rank_cohomology_rational_eq_rank_lattice ρ h ρT j hT hj he hs
  obtain ⟨f1, f2, e1, e2⟩ := tate_lattice hF ρT hT
  have q0 : finrank ℚ_[l] ↥(H0 ρ) = finrank ℤ_[l] ↥(H0 ρT) := congrArg Cardinal.toNat r0
  have q1 : finrank ℚ_[l] (H1 ρ) = finrank ℤ_[l] (H1 ρT) := congrArg Cardinal.toNat r1
  have q2 : finrank ℚ_[l] (H2 ρ) = finrank ℤ_[l] (H2 ρT) := congrArg Cardinal.toNat r2
  refine ⟨Module.rank_lt_aleph0_iff.1 (r1 ▸ Module.rank_lt_aleph0 _ _),
    Module.rank_lt_aleph0_iff.1 (r2 ▸ Module.rank_lt_aleph0 _ _), ?_, ?_⟩
  · rw [q0, q1, q2, e1]
  · rw [q2, e2, UpperTheory.finrank_coinvariants_eq_finrank_lattice_coinvariants χ ρ ρT j hj.injective he hs]

private theorem finrank_H0dual {G E V : Type} [Group G] [Field E] [AddCommGroup V] [Module E V]
    [FiniteDimensional E V] (χ : G →* Eˣ) (ρ : Representation E G V) :
    finrank E ↥(H0dual χ ρ) = finrank E (V ⧸ coSub χ ρ) := by
  have : H0dual χ ρ = (coSub χ ρ).dualAnnihilator := by
    ext f
    rw [Submodule.mem_dualAnnihilator]
    constructor
    · intro hf w hw
      refine (Submodule.span_le (p := LinearMap.ker f)).2 ?_ hw
      rintro _ ⟨g, x, rfl⟩
      simp [hf g x]
    · intro hf g x
      have := hf _ (Submodule.subset_span ⟨g, x, rfl⟩)
      simpa [sub_eq_zero] using this
  rw [this, ← (Submodule.dualQuotEquivDualAnnihilator _).finrank_eq, Subspace.dual_finrank_eq]

private theorem coSub_res {Q E G V : Type} [Field Q] [Field E] [Algebra Q E] [Group G] [AddCommGroup V]
    [Module E V] [Module Q V] [IsScalarTower Q E V] (χ : G →* Qˣ) (χ' : G →* Eˣ)
    (hχ : ∀ g, ((χ' g : Eˣ) : E) = algebraMap Q E (χ g : Qˣ)) (ρ : Representation E G V) :
    coSub χ (resCoef Q ρ) = (coSub χ' ρ).restrictScalars Q := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨g, x, rfl⟩
    exact Submodule.subset_span ⟨g, x, by rw [hχ, algebraMap_smul]; rfl⟩
  · intro y hy
    have key : ∀ c : E, c • y ∈ coSub χ (resCoef Q ρ) := by
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨g, x, rfl⟩ := hy
        intro c
        refine Submodule.subset_span ⟨g, c • x, ?_⟩
        change _ = ρ g (c • x) - _
        rw [hχ, algebraMap_smul, smul_sub, map_smul, smul_comm c (χ g : Q)]
      | zero => intro c; simp
      | add a b _ _ ha hb => intro c; rw [smul_add]; exact add_mem (ha c) (hb c)
      | smul a b _ hb => intro c; rw [smul_smul]; exact hb _
    simpa using key 1

theorem UpperTheory.V.Loc.tateRat :
    LocalPublishedTheorems → ∀ {v l : ℕ} [Fact v.Prime] [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ v) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {V : Type} [AddCommGroup V] [Module E V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] E V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul E V] (ρ : Representation E G V), ContAction ρ → Module.Finite E (H1 ρ) ∧ Module.Finite E (H2 ρ) ∧ finrank E (H1 ρ) = finrank E ↥(H0 ρ) + finrank E (H2 ρ) + (if v = l then φ.range.index * finrank E V else 0) ∧ finrank E (H2 ρ) = finrank E ↥(H0dual ((cycA v l E).comp φ) ρ) := by
  intro hP v l _ _ G _ _ _ φ hφ E _ _ _ _ _ V _ _ _ _ _ _ _ _ _ ρ h
  haveI : CompactSpace G := by
    have hc : IsClosed (φ.range : Set (GQ v)) := φ.range.isClosed_of_isOpen hφ.isOpen_range
    exact (⟨hφ.isEmbedding, hc⟩ : IsClosedEmbedding φ).compactSpace
  haveI : ContinuousConstSMul ℚ_[l] V := ⟨fun c => by
    simpa only [algebraMap_smul] using continuous_const_smul (T := V) (algebraMap ℚ_[l] E c)⟩
  haveI : FiniteDimensional E V := Module.Finite.of_restrictScalars_finite ℚ_[l] E V
  obtain ⟨f1, f2, e1, e2⟩ := tate_Q (UpperTheory.finite_level_of_finite_level_mod l G _ _ (UpperTheory.finiteLevel_cyclotomic_of_openEmbedding hP φ hφ)) (resCoef ℚ_[l] ρ) h
  obtain ⟨⟨a0⟩, ⟨a1⟩, ⟨a2⟩, -⟩ := UpperTheory.nonempty_cohomology_restrictScalars_linearEquiv ℚ_[l] ρ
  haveI := Module.Finite.equiv a1
  haveI := Module.Finite.equiv a2
  have hd : 0 < finrank ℚ_[l] E := finrank_pos
  rw [coSub_res ((Units.map (algebraMap ℤ_[l] ℚ_[l] : ℤ_[l] →* ℚ_[l])).comp ((cyc v l).comp φ))
      ((cycA v l E).comp φ)
      (fun g => IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] E ((cyc v l (φ g) : ℤ_[l]ˣ) : ℤ_[l])) ρ,
    (Submodule.Quotient.restrictScalarsEquiv ℚ_[l] _).finrank_eq, a2.finrank_eq,
    ← finrank_mul_finrank ℚ_[l] E (H2 ρ), ← finrank_mul_finrank ℚ_[l] E (V ⧸ _)] at e2
  rw [a0.finrank_eq, a1.finrank_eq, a2.finrank_eq, ← finrank_mul_finrank ℚ_[l] E (H2 ρ),
    ← finrank_mul_finrank ℚ_[l] E (H1 ρ), ← finrank_mul_finrank ℚ_[l] E ↥(H0 ρ),
    ← finrank_mul_finrank ℚ_[l] E V] at e1
  refine ⟨Module.Finite.of_restrictScalars_finite ℚ_[l] E _, Module.Finite.of_restrictScalars_finite ℚ_[l] E _,
    Nat.eq_of_mul_eq_mul_left hd ?_, ?_⟩
  · rw [e1]
    split_ifs <;> ring
  · rw [finrank_H0dual]
    exact Nat.eq_of_mul_eq_mul_left hd e2
