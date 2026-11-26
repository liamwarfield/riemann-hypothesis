module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.GaloisRepresentationTypes.HidaX
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.HdEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ExistsHeckeIdeal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.SVROrdIrr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.NonemptyUnitaryHeckeParts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LevelUR2LocEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LevelUR2ActEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.VLPiPts

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.HidaLevelX
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.HidaCtrlMu
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.HidaSphRed
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
universe u in
private theorem sr_abs {R A K M W ι ι' : Type} [CommRing R] [CommRing A] [Algebra R A] [Field K]
    [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M]
    [AddCommGroup W] [Module K W] {J : Type u} (Y0 Y : Submodule A M) [Module.Free A Y0] (hle : Y ≤ Y0)
    (op : ι → Module.End A M) [hc : Fact (CommOn Y op)] (s : ι' → ι) (e : Module.End A Y0)
    (hi : IsIdempotentElem e) (hY : ∀ y : Y0, (y : M) ∈ Y ↔ e y = y) (χ : A →+* K) (sp : M → W)
    (hadd : ∀ f ∈ Y0, ∀ f' ∈ Y0, sp (f + f') = sp f + sp f') (hsmul : ∀ f ∈ Y0, ∀ b : A, sp (b • f) = χ b • sp f)
    (hind : ∀ (κ : Type) (b : Module.Basis κ A Y0), LinearIndependent K fun i => sp (b i))
    (opC : ι → Module.End K W) (hop : ∀ i, ∀ f ∈ Y0, sp (op i f) = opC i (sp f))
    (Z : J → Submodule K W) (hZ : ∀ j i, ∃ μ : K, ∀ F ∈ Z j, opC (s i) F = μ • F)
    (hOZ : ∀ f ∈ Y0, sp f ∈ ⨆ j, Z j) (I : Ideal A) (hI : I = RingHom.ker χ)
    (t : heckeAlg Y op) (ht : t ∈ Algebra.adjoin R (Set.range fun i => heckeGen Y op (s i))) (k : ℕ)
    (h : ∀ y : Y, ((t ^ k : heckeAlg Y op) : Module.End A Y) y ∈ (I • ⊤ : Submodule A Y)) (y : Y) :
    (t : Module.End A Y) y ∈ (I • ⊤ : Submodule A Y) := by
  subst hI
  have hk := UpperTheory.V.Th.AnnihilatorQuotientFinite.kerSp Y0 Y e hi hle hY χ sp hadd hsmul hind
  have key : ∃ φ : Module.End K W, (∀ f : Y, sp ((t : Module.End A Y) f : Y) = φ (sp f)) ∧
      ∀ j, ∃ μ : K, ∀ F ∈ Z j, φ F = μ • F := by
    clear h
    induction ht using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact ⟨opC (s i), fun f => hop _ _ (hle f.2), fun j => hZ j i⟩
    | algebraMap r =>
      refine ⟨algebraMap K _ (χ (algebraMap R A r)), fun f => ?_, fun j => ⟨_, fun F _ => rfl⟩⟩
      rw [IsScalarTower.algebraMap_apply R A (heckeAlg Y op)]
      exact hsmul _ (hle f.2) _
    | add a b _ _ ha hb =>
      obtain ⟨φ, h1, h2⟩ := ha
      obtain ⟨ψ, h3, h4⟩ := hb
      refine ⟨φ + ψ, fun f => ?_, fun j => ?_⟩
      · rw [LinearMap.add_apply, ← h1, ← h3]
        exact hadd _ (hle (Subtype.prop _)) _ (hle (Subtype.prop _))
      · obtain ⟨μ, hμ⟩ := h2 j
        obtain ⟨ν, hν⟩ := h4 j
        exact ⟨μ + ν, fun F hF => by rw [LinearMap.add_apply, hμ F hF, hν F hF, add_smul]⟩
    | mul a b _ _ ha hb =>
      obtain ⟨φ, h1, h2⟩ := ha
      obtain ⟨ψ, h3, h4⟩ := hb
      refine ⟨φ * ψ, fun f => ?_, fun j => ?_⟩
      · rw [Module.End.mul_apply, ← h3, ← h1]
        rfl
      · obtain ⟨μ, hμ⟩ := h2 j
        obtain ⟨ν, hν⟩ := h4 j
        exact ⟨ν * μ, fun F hF => by rw [Module.End.mul_apply, hν F hF, map_smul, hμ F hF, smul_smul]⟩
  obtain ⟨φ, h1, h2⟩ := key
  have hp : ∀ (m : ℕ) (f : Y), sp (((t ^ m : heckeAlg Y op) : Module.End A Y) f : Y) = (φ ^ m) (sp f) := by
    intro m
    induction m with
    | zero => intro f; rw [pow_zero, pow_zero]; rfl
    | succ m ih =>
      intro f
      rw [pow_succ, pow_succ, Module.End.mul_apply, ← h1, ← ih]
      rfl
  rw [← hk, h1]
  refine UpperTheory.V.Th.AnnihilatorQuotientFinite.eigKill φ k _ ?_ (by rw [← hp]; exact (hk _).2 (h y))
  refine (iSup_le fun j => ?_ : ⨆ j, Z j ≤ _) (hOZ _ (hle y.2))
  obtain ⟨μ, hμ⟩ := h2 j
  exact fun F hF => Submodule.mem_iSup_of_mem μ (Module.End.mem_eigenspace_iff.2 (hμ F hF))
attribute [local instance 2000] UpperTheory.V.W.coefLocal
attribute [-instance] GlobalTheory.AdmLoc.modFun
set_option maxHeartbeats 800000 in
theorem UpperTheory.V.Th.AnnihilatorQuotientFinite.sphRed_alt :
    ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (ι : Qbar l ≃+* ℂ) (P : Wt L l n → (H.Gq →* GL (Fin n) (Qbar l)) → Prop), H.AutomorphicHeckeSet ι P →
    ∀ (x : A →ₐ[c.O] Qbar l) (lam : Wt L l n), lam ∈ H.admitted → H.Arith θ x.toRingHom lam → ∀ (a : H.Op → c.O) (K : H.Lev) [Fact (CommOn (H.MK θ a K) (H.op A))],
    ∀ t ∈ Algebra.adjoin c.O (Set.range fun p : H.Wp × Fin n => H.gen θ a K (.inl p)), ∀ k : ℕ,
    (∀ y : H.MK θ a K, ((t ^ k : H.TK θ a K) : Module.End A (H.MK θ a K)) y ∈ (RingHom.ker x • ⊤ : Submodule A (H.MK θ a K))) → ∀ y : H.MK θ a K, (t : Module.End A (H.MK θ a K)) y ∈ (RingHom.ker x • ⊤ : Submodule A (H.MK θ a K)) := by
  intro L Ω _ _ _ _ _ l _ n c H hH A _ _ _ θ hθ ι P hP x lam hlam har a K _ t ht k h y
  haveI : Finite (ResidueField c.O) := (UpperTheory.V.abelian₂.dvr_finite l c.O).2.1
  haveI : IsCNL A := IsCNL.ofCO c.O A
  obtain ⟨h0, hfin, hfree, -⟩ := hiComm L Ω l n c H hH A θ hθ K
  obtain ⟨e, -, hi, hY, -⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.locIdem A _ _ _ (H.op A) (fun i => algebraMap c.O A (a i)) h0
  obtain ⟨d, ξ, c0, sp, hsp⟩ := spec L Ω l n c H hH A θ hθ ι x lam har
  have hO := (_root_.UpperTheory.V.Hi.clParts_alt L Ω l n c H hH A θ hθ ι P hP x lam d ξ c0 sp hsp hlam K c0 le_rfl).2
  have hOZ : ∀ f ∈ H.X.Ord (H.τA A) θ (H.lev K), sp f ∈ ⨆ Y : {Y : H.PartAltAlt ι lam ξ // P lam Y.r}, Y.1.Y := fun f hf => by
    have h1 : sp f ∈ H.OrdAt θ ι x.toRingHom lam ξ K c0 := hsp.span K c0 le_rfl ▸ Submodule.subset_span ⟨f, hf, rfl⟩
    exact (hO.le.trans (iSup_mono fun _ => inf_le_left)) h1
  have hI : RingHom.ker x = RingHom.ker (ι.toRingHom.comp x.toRingHom) := by
    ext b
    simp [RingHom.mem_ker]
  exact sr_abs (R := c.O) (H.X.Ord (H.τA A) θ (H.lev K)) (H.MK θ a K) inf_le_left (H.op A) Sum.inl e hi hY
    (ι.toRingHom.comp x.toRingHom) sp (hsp.add K) (hsp.smul K) (hsp.indep K) (H.opC ι lam d) (hsp.op K)
    (fun Y : {Y : H.PartAltAlt ι lam ξ // P lam Y.r} => Y.1.Y) (fun Y i => ⟨_, Y.1.sph i.1 _⟩) hOZ _ hI t ht k h y
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
private theorem lam_map {n : ℕ} {A B G : Type} [CommRing A] [CommRing B] [Group G] (D : W.GDet n A G) (f : A →+* B)
    (g : G) (i : ℕ) : (D.map f).lam i (MonoidAlgebra.single g 1) = f (D.lam i (MonoidAlgebra.single g 1)) := by
  have h0 : (D.map f).chi (MonoidAlgebra.single g 1) = (D.chi (MonoidAlgebra.single g 1)).map f := by
    letI : Algebra A (Polynomial B) := ((algebraMap B (Polynomial B)).comp f).toAlgebra
    let φ : Polynomial A →ₐ[A] Polynomial B :=
      { Polynomial.mapRingHom f with commutes' := fun a => Polynomial.map_C f }
    have h := D.nat (Polynomial A) (Polynomial B) φ
      (MonoidAlgebra.single 1 Polynomial.X - MonoidAlgebra.mapRingHom G Polynomial.C (MonoidAlgebra.single g 1))
    refine Eq.trans ?_ h
    change D.D (Polynomial B) _ = D.D (Polynomial B) (MonoidAlgebra.mapRingHom G (Polynomial.mapRingHom f) _)
    congr 1
    simp [map_sub, MonoidAlgebra.mapRingHom_single]
  simp [W.GDet.lam, h0]
private theorem red_abs {O R T : Type} [CommRing O] [CommRing R] [CommRing T] [Algebra O R] [Algebra O T] (f : R →ₐ[O] T)
    (I : Ideal T) (S : Subalgebra O T) (hS : ∀ s ∈ S, ∀ k : ℕ, s ^ k ∈ I → s ∈ I) (U : Set R)
    (hU : ∀ u ∈ U, ∃ s ∈ S, f u - s ∈ I) (t : R) (ht : t ∈ Algebra.adjoin O U) (k : ℕ) (hk : f (t ^ k) ∈ I) : f t ∈ I := by
  have key : ∃ s ∈ S, f t - s ∈ I := by
    clear hk
    induction ht using Algebra.adjoin_induction with
    | mem x hx => exact hU x hx
    | algebraMap b => exact ⟨_, S.algebraMap_mem b, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨s, hs, h1⟩ := hx
      obtain ⟨s', hs', h2⟩ := hy
      refine ⟨s + s', add_mem hs hs', ?_⟩
      have := I.add_mem h1 h2
      rw [map_add (f := _)]; convert this using 1; ring
    | mul x y _ _ hx hy =>
      obtain ⟨s, hs, h1⟩ := hx
      obtain ⟨s', hs', h2⟩ := hy
      refine ⟨s * s', mul_mem hs hs', ?_⟩
      have := I.add_mem (I.mul_mem_left (f x) h2) (I.mul_mem_left s' h1)
      rw [map_mul]; convert this using 1; ring
  obtain ⟨s, hs, h1⟩ := key
  have e : Ideal.Quotient.mk I (f t) = Ideal.Quotient.mk I s := Ideal.Quotient.eq.2 h1
  have h2 : s ^ k ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_pow, ← e, ← map_pow, ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact hk
  have := I.add_mem h1 (hS s hs k h2)
  simpa using this
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
theorem UpperTheory.V.Th.AnnihilatorQuotientFinite.ctrlMu_of_arith_weight :
    ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
∀ (ι : Qbar l ≃+* ℂ) (P : Wt L l n → (H.Gq →* GL (Fin n) (Qbar l)) → Prop), H.AutomorphicHeckeSet ι P →
    ∀ (x : A →ₐ[c.O] c.O) (lam : Wt L l n), lam ∈ H.admitted → H.Arith θ ((Algebra.ofId c.O (Qbar l)).comp x).toRingHom lam →
    ∀ (a : H.Op → c.O) (K : H.Lev) [Module.Finite A (H.MK θ a K)] (R : Type) [CommRing R] [Algebra c.O R] (D₀ : W.GDet n R H.Gq)
      (ψ₀ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* Rˣ) (μ : R →+* Module.End A (H.MK θ a K)),
      (H.MK θ a K = ⊥ ∨ ∃ (_ : Fact (CommOn (H.MK θ a K) (H.op A))) (_ : Alg.IsCO c.O (H.TK θ a K)) (f : R →ₐ[c.O] H.TK θ a K),
        H.IsMap θ a K D₀ ψ₀ f ∧ ∀ t, μ t = (f t : Module.End A (H.MK θ a K))) →
      ∀ t ∈ Algebra.adjoin c.O {b : R | ∃ i g, b = D₀.lam i (MonoidAlgebra.single g 1)}, ∀ k : ℕ,
        (∀ y, μ (t ^ k) y ∈ (RingHom.ker x • ⊤ : Submodule A (H.MK θ a K))) →
        ∀ y, μ t y ∈ (RingHom.ker x • ⊤ : Submodule A (H.MK θ a K)) := by
  intro L Ω _ _ _ _ _ l _ n c H hH A _ _ _ θ hθ ι P hP x lam hl har a K _ R _ _ D₀ ψ₀ μ hμ t ht k hk y
  rcases hμ with h0 | ⟨_, _, f, hf, hμ⟩
  · have : μ t y = 0 := Subtype.ext ((Submodule.mem_bot A).1 (h0 ▸ (μ t y).2))
    rw [this]
    exact zero_mem _
  haveI := c.dvr
  have hker : RingHom.ker ((Algebra.ofId c.O (Qbar l)).comp x) = RingHom.ker x := by
    ext b
    rw [RingHom.mem_ker, RingHom.mem_ker]
    exact map_eq_zero_iff (algebraMap c.O (Qbar l)) Subtype.val_injective
  obtain ⟨I, hI, hfin⟩ := Th.AnnihilatorQuotientFinite.annFin x (heckeAlg (H.MK θ a K) (H.op A)).val.toRingHom fun o y => by
    rw [IsScalarTower.algebraMap_apply c.O A (H.TK θ a K)]
    rfl
  have h1 := red_abs f I (Algebra.adjoin c.O (Set.range fun p : H.Wp × Fin n => H.gen θ a K (.inl p)))
    (fun s hs k hk => (hI s).2 (by
      have := _root_.UpperTheory.V.Th.AnnihilatorQuotientFinite.sphRed_alt L Ω l n c H hH A θ hθ ι P hP _ lam hl har a K s hs k
      rw [hker] at this
      exact this ((hI _).1 hk))) _ (by
      rintro _ ⟨i, g, rfl⟩
      refine Th.AnnihilatorQuotientFinite.closedSub I _ _ fun N => ?_
      have := Th.AnnihilatorQuotientFinite.frobS L Ω l n c H hH A θ a K _ _ _ hf i g N
      rwa [lam_map] at this) t ht k ((hI _).2 fun y => by
      have := hk y
      rwa [hμ] at this)
  rw [hμ]
  exact (hI _).1 h1 y
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
attribute [local instance 2000] UpperTheory.V.W.coefLocal
open UpperTheory.V.Hi.LvR
private theorem hida_lq_lc {l : ℕ} [Fact l.Prime] {F : W.GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ}
    (r : Resid F O n) : IsLocallyConstant fun g : F.G₀ => r.Dbar.chi (MonoidAlgebra.single g 1) := by
  have h : IsLocallyConstant fun (g : F.G₀) (i : Fin n) => r.chib i g :=
    (IsLocallyConstant.iff_eventually_eq _).2 fun x => by
      have := Filter.eventually_all.2 fun i => (JEx.lc_of_open _ (r.chib_open i)).eventually_eq x
      exact this.mono fun y hy => funext hy
  have e : (fun g : F.G₀ => r.Dbar.chi (MonoidAlgebra.single g 1)) =
      (fun t : Fin n → (ResidueField O)ˣ => (Matrix.diagonal fun i => (t i : ResidueField O)).charpoly) ∘
        fun (g : F.G₀) (i : Fin n) => r.chib i g := by
    funext g
    rw [Resid.Dbar, (AlgebraTools.Det.repApi _).2.1]
    rfl
  rw [e]
  exact h.comp _
private theorem hida_lq_dense {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {p : X → Y} (hc : Continuous p)
    (hs : Function.Surjective p) {S : Set X} (hS : Dense S) {T : Set Y} (h : ∀ x ∈ S, p x ∈ T) : Dense T :=
  (hs.denseRange.dense_image hc hS).mono (by rintro _ ⟨x, hx, rfl⟩; exact h x hx)
private theorem hida_levelUR2LocEq :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n → ∀ (V₀ V : s.Lev) (Q₀ : QData V₀) (Q : QData V) (c : Coef l) (r : Resid V₀.frame c.O n) (ι : Qbar l ≃+* ℂ) (Λ : LamObj r) (R : _root_.UpperTheory.V.Hi.CaseU.UnitaryHeckeData Q₀ ι Λ) (K₀ : (hset Q₀ R.τ₀).Lev) (K : (hset Q R.τ₀).Lev), V₀.S' = s.S → (∀ q, K.1 q = KO ((Q.wq q).adicCompletion L) (Fin n)) → ∀ (p : V.frame.G₀ →* V₀.frame.G₀), Continuous p → Function.Surjective p → (∀ g, p (V.pr g) = V₀.pr g) → ∀ j : (hset Q R.τ₀).Op → (hset Q₀ R.τ₀).Op, (∀ x : Vl l L × Fin n, j (.inr x) = .inr x) → (∀ (w : (hset Q R.τ₀).Wp) (k : Fin n), ∃ hw, j (.inl (w, k)) = .inl (⟨w.1, hw⟩, k)) → (∀ i, (hset Q R.τ₀).op Λ.Λ i = (hset Q₀ R.τ₀).op Λ.Λ (j i)) ∧ ∀ f : (hset Q₀ R.τ₀).X.Fn Λ.Λ R.m, f ∈ (hset Q R.τ₀).MK (A := Λ.Λ) R.θ (fun i => R.a (j i)) K ↔ f ∈ (hset Q₀ R.τ₀).MK R.θ R.a K₀ := by
  intro hP l _ L Ω _ _ _ _ _ _ s n hn V₀ V Q₀ Q c r ι Λ R K₀ K h0 hK p hp hs hpr j hj1 hj2
  have hop : ∀ i, (hset Q R.τ₀).op Λ.Λ i = (hset Q₀ R.τ₀).op Λ.Λ (j i) := by
    rintro (⟨w, k⟩ | x)
    · obtain ⟨hw, e⟩ := hj2 w k
      exact Eq.trans rfl (congrArg ((hset Q₀ R.τ₀).op Λ.Λ) e).symm
    · exact Eq.trans rfl (congrArg ((hset Q₀ R.τ₀).op Λ.Λ) (hj1 x)).symm
  refine ⟨hop, fun f => ?_⟩
  have hAx := _root_.UpperTheory.V.Hi.axU_s hP.litN l L Ω s n hn V₀ Q₀ c _ R.τ₀
  have hAx' := _root_.UpperTheory.V.Hi.axU_s hP.litN l L Ω s n hn V Q c _ R.τ₀
  obtain ⟨hdom, hden⟩ := _root_.UpperTheory.V.Hi.isDomain_and_denseWt_of_isTheta hP.litN l L Ω s n hn V₀ Q₀ c _ R.τ₀ r Λ R.θ R.theta
  let lam : Wt L l n := fun _ => ⟨0, fun _ _ _ => le_rfl⟩
  have haut := _root_.UpperTheory.V.Hi.automorphicHeckeSet_unitaryPointProperties_of_typeFor hP l L Ω s n hn V₀ Q₀ c r ι _ R.τ₀ R.type
  have hlev : (hset Q R.τ₀).lev K = (hset Q₀ R.τ₀).lev K₀ :=
    Subgroup.ext fun u => levelUR2LevEq l L Ω s n hn V₀ V Q₀ Q c _ R.τ₀ K₀ K h0 hK u
  have key := _root_.UpperTheory.V.Hi.levelUR2H3Abs_alt hP.litN L Ω l n c _ hAx Λ.Λ R.θ R.isWt hdom ι _ haut lam trivial (hden lam) R.a K₀
    _ (hida_lq_lc r) R.res.frob _ j (fun x => ⟨.inr x, hj1 x⟩) (hida_lq_dense hp hs hAx'.dense (by
      rintro _ ⟨w, hw, B, σ, hB, hσ, rfl⟩
      obtain ⟨hw0, -⟩ := hj2 ⟨w, hw⟩ ⟨0, hn⟩
      refine ⟨⟨w, hw0⟩, fun k => ?_, B, σ, hB, hσ, hpr _⟩
      obtain ⟨_, e⟩ := hj2 ⟨w, hw⟩ k
      exact ⟨_, e⟩))
  rw [← key]
  have e1 : (hset Q R.τ₀).op Λ.Λ = fun i => (hset Q₀ R.τ₀).op Λ.Λ (j i) := funext hop
  have e2 : (hset Q R.τ₀).MK (A := Λ.Λ) R.θ (fun i => R.a (j i)) K = _ :=
    congrArg₂ (fun U o => locPart ((hset Q₀ R.τ₀).X.Ord ((hset Q₀ R.τ₀).τA Λ.Λ) R.θ U) o
      fun i => algebraMap c.O Λ.Λ (R.a (j i))) hlev e1
  exact SetLike.ext_iff.1 e2 f
private theorem base_object_hom_ext {l : ℕ} [Fact l.Prime] {F : W.GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ}
    {r : Resid F O n} (B : UniversalOrdinaryDeterminantRing r) (T : Type) [CommRing T] [Algebra O T] [Alg.IsCO O T] (f g : B.B →ₐ[O] T)
    (h1 : B.u.D.map f.toRingHom = B.u.D.map g.toRingHom)
    (h2 : ∀ v i, W.pushCh f.toRingHom (B.u.ψ v i) = W.pushCh g.toRingHom (B.u.ψ v i)) : f = g := by
  obtain ⟨p, hp⟩ := W.exists_determinantPair_map_of_algHom l F O n r B.B T g B.u
  exact (B.univ T p).unique ⟨h1.trans hp.1, fun v i => (h2 v i).trans (hp.2 v i)⟩ hp
private theorem lam_val {l : ℕ} [Fact l.Prime] {F : W.GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ}
    {r : Resid F O n} (Λ : LamObj r) {R : Type} [CommRing R] [Algebra O R] [Alg.IsCO O R] (p : Pair r R) (v : F.Vl) (i : Fin n)
    (γ : F.Gv v) (hγ : γ ∈ F.Iv v) (a : O) (x : Λ.Λ) (hx : x = algebraMap O Λ.Λ a * (Λ.κ v i ⟨γ, hγ⟩ : Λ.Λˣ) - 1) :
    Λ.toPair p x = algebraMap O R a * (p.ψ v i γ : R) - 1 := by
  have e : Λ.toPair p (Λ.κ v i ⟨γ, hγ⟩ : Λ.Λˣ) = (p.ψ v i γ : R) :=
    by have h := congrArg Units.val (DFunLike.congr_fun (Λ.toPair_spec r p v i) (⟨γ, hγ⟩ : F.Iv v)); exact h
  rw [hx, map_sub, map_mul, map_one, AlgHom.commutes, e]
private theorem eq_sub {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (P N N₀ : Submodule A M) (Z : Submodule A P)
    (h : Z.map P.subtype = N) (h₀ : ∀ f, f ∈ N ↔ f ∈ N₀) :
    ∃ e : Z ≃+ N₀, ∀ z : Z, (e z : M) = (z : P) ∧ ((z : P) : M) ∈ N := by
  have e2 : Z.map P.subtype = N₀ := h.trans (Submodule.ext h₀)
  exact ⟨((Z.equivMapOfInjective P.subtype P.injective_subtype).trans (LinearEquiv.ofEq _ _ e2)).toAddEquiv,
    fun z => ⟨rfl, h ▸ Submodule.mem_map_of_mem z.2⟩⟩
private theorem under_eq {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    {A : ValuationSubring Ω} {w : Plc L} {v : Plc (Lp L)} (hw : IsPlaceOver A w) (hv : IsPlaceOver A v) :
    w.under (𝓞 (Lp L)) = v := by
  ext x
  exact (hw (algebraMap _ (𝓞 L) x)).symm.trans (hv x)
set_option maxHeartbeats 3000000 in
private theorem umod_abs (hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c) (hax : H.Ax)
    (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ) (hw : H.IsWt θ) (a : H.Op → c.O) [DecidableEq H.Q]
    (ι : Qbar l ≃+* ℂ) (P : Wt L l n → (H.Gq →* GL (Fin n) (Qbar l)) → Prop) (haut : H.AutomorphicHeckeSet ι P) (lam0 : Wt L l n) (hl0 : lam0 ∈ H.admitted) (hd : H.DenseWt θ lam0)
    (hneat : ∀ K, H.X.Neat (H.lev K))
    (hf : ∀ (K : H.Lev) (k : GV n H.wq) (j : GV n H.wq →* H.X.Ub), (∀ q g, j (Pi.mulSingle q g) = H.sec (H.wq q) g) → j k ∈ H.lev K → k ∈ Subgroup.pi Set.univ K.1)
    (R : Type) [CommRing R] [Algebra c.O R] (D₀ : W.GDet n R H.Gq) (ψ₀ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* Rˣ) (lam : A →ₐ[c.O] R)
    (hu : ∀ (T : Type) [CommRing T] [Algebra c.O T] [Alg.IsCO c.O T] (f g : R →ₐ[c.O] T), D₀.map f.toRingHom = D₀.map g.toRingHom → (∀ v i, W.pushCh f.toRingHom (ψ₀ v i) = W.pushCh g.toRingHom (ψ₀ v i)) → f = g)
    (hJ : ∀ K, ∃ J, H.IsJ θ a K D₀ ψ₀ lam J) :
    ∃ (ρ : Representation A (GV n H.wq) (⨆ K, H.MK θ a K : Submodule A (H.X.Fn A H.m))) (α : R →+* Module.End A (⨆ K, H.MK θ a K : Submodule A (H.X.Fn A H.m))), (∀ b z, α (lam b) z = b • z) ∧ (∀ t g z, α t (ρ g z) = ρ g (α t z)) ∧ (∀ K : H.Lev, (fixd ρ (Subgroup.pi Set.univ K.1)).map (Submodule.subtype _) = H.MK θ a K ∧ Module.Finite A (fixd ρ (Subgroup.pi Set.univ K.1))) ∧ (∀ (K K' : H.Lev) [((Subgroup.pi Set.univ K'.1).subgroupOf (Subgroup.pi Set.univ K.1)).Normal], (∀ q, K'.1 q ≤ K.1 q) → ∃ ρ' : Representation A (Subgroup.pi Set.univ K.1 ⧸ (Subgroup.pi Set.univ K'.1).subgroupOf (Subgroup.pi Set.univ K.1)) (fixd ρ (Subgroup.pi Set.univ K'.1)), (∀ (u : Subgroup.pi Set.univ K.1) f, (ρ' (u : _ ⧸ _) f).1 = ρ u.1 f) ∧ Module.Projective (MonoidAlgebra A (Subgroup.pi Set.univ K.1 ⧸ (Subgroup.pi Set.univ K'.1).subgroupOf (Subgroup.pi Set.univ K.1))) ρ'.asModule) ∧ (∀ (K : H.Lev) [Fact (CommOn (H.MK θ a K) (H.op A))] [Alg.IsCO c.O (H.TK θ a K)], ∃ f : R →ₐ[c.O] H.TK θ a K, H.IsMap θ a K D₀ ψ₀ f ∧ ∀ t (y : H.MK θ a K) (z : (⨆ K, H.MK θ a K : Submodule A (H.X.Fn A H.m))), (z : H.X.Fn A H.m) = y → (α t z : H.X.Fn A H.m) = ((f t : Module.End A (H.MK θ a K)) y : H.MK θ a K)) ∧ ∀ z : (⨆ K, H.MK θ a K : Submodule A (H.X.Fn A H.m)), z ≠ 0 → ∃ (x : R →+* Qbar l) (ρx : H.Gq →* GL (Fin n) (Qbar l)) (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (π : Representation ℂ (GV n H.wq) Y) (sp : (⨆ K, H.MK θ a K : Submodule A (H.X.Fn A H.m)) →+ Y) (σ : ∀ q, SmIrr (GLw n (H.wq q))), sp z ≠ 0 ∧ Continuous ρx ∧ D₀.map x = W.GDet.ofRep (W.mat ρx) ∧ (∀ t y, sp (α t y) = ι (x t) • sp y) ∧ (∀ g y, sp (ρ g y) = π g (sp y)) ∧ (∀ q, IsoSum (π.comp (MonoidHom.mulSingle (fun q => GLw n (H.wq q)) q)) ⊤ (σ q)) ∧ ∀ q (Bq : ValuationSubring Ω) (hB : IsPlaceOver Bq (H.wq q)) (rc : IrrGL (k := (H.wq q).adicCompletion L) → WD hB), _root_.UpperTheory.Zero.LLC.IsRecT hB rc → _root_.UpperTheory.V.Z.Win.WOT ι (ρx.comp H.prj) (rc (algNorm (σ q))) := by
  obtain ⟨ρ, h1, h2, h3, h4⟩ := piBasic L Ω l n c H hax A θ hw a
  obtain ⟨α, a1, a2, a3⟩ := _root_.UpperTheory.V.Hi.levelUR2ActEx_alt hN L Ω l n c H hax A θ hw a ρ h1 h2 h3 R D₀ ψ₀ lam hu hJ
  refine ⟨ρ, α, a1, a2, fun K => ⟨h2 K, ?_⟩, fun K K' _ hle => h4 hneat K K' hle fun k _ j hj hk => hf K' k j hj hk, a3, ?_⟩
  · have hfin : Module.Finite A (H.MK θ a K) := ((hiComm L Ω l n c H hax A θ hw K).2.2.2 a).2.1
    rw [← h2 K] at hfin
    exact Module.Finite.equiv (Submodule.equivMapOfInjective _ (Submodule.injective_subtype _) _).symm
  · exact _root_.UpperTheory.V.Hi.piPts_n_alt hN L Ω l n c H hax A θ hw ι P haut lam0 hl0 hd a ρ h1 R D₀ α fun K _ _ => by
      obtain ⟨f, hf1, hf2⟩ := a3 K
      exact ⟨f.toRingHom, _, hf1, hf2⟩
set_option maxHeartbeats 1600000 in
private theorem s1 (P : _root_.UpperTheory.V.Af.HypothesesH') (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ) (hn : 1 ≤ n)
    (V0 : s.Lev) (Q0 : QData V0) (c : Coef l) (r : Resid V0.frame c.O n) (ι : Qbar l ≃+* ℂ)
    (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (κ : ∀ v, Fin n → V0.frame.Iv v →* Aˣ) (hi hu)
    (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O) (ty : _root_.UpperTheory.V.Hi.CaseU.TypeForAlt r ι τ₀) (θ : (hset Q0 τ₀).X.I.T →* Aˣ)
    (th : IsTheta Q0 τ₀ (⟨A, κ, hi, hu⟩ : LamObj r) θ) (hw : (hset Q0 τ₀).IsWt θ) (a : (hset Q0 τ₀).Op → c.O) (rs : IsRes Q0 r τ₀ a) (V : s.Lev) (h : (Pa.globOf r V).Hom (Pa.globOf r V0)) (Q : QData V) [_dq : DecidableEq Q.Q] (hsub : V0.S' ⊆ V.S') (hp : ∀ g, h.p (toGS Ω V.S' g) = toGS Ω V0.S' g) (B' : UniversalOrdinaryDeterminantRing (rUp h)) :
    ∃ (θ' : (hset Q τ₀).X.I.T →* Aˣ) (a' : (hset Q τ₀).Op → c.O) (lam : A →ₐ[c.O] B'.B), (hset Q τ₀).IsWt θ' ∧ @Eq ((hset Q τ₀).X.I.T →* Aˣ) θ' θ ∧
      (∀ i, a' i = a (opUp Q0 Q hsub τ₀ i)) ∧ (∀ v i (γ : V0.frame.Gv v) (hγ : γ ∈ V0.frame.Iv v), lam (κ v i ⟨γ, hγ⟩ : Aˣ) = (@id (Dec (F := L) (s.A v.1) →* B'.Bˣ) (B'.u.ψ v i) γ : B'.Bˣ)) ∧ (∀ w, (hset Q τ₀).DenseWt θ' w) ∧ ∀ K, ∃ J, (hset Q τ₀).IsJ θ' a' K B'.u.D B'.u.ψ lam J := by
  let κ' : ∀ v, Fin n → V.frame.Iv v →* Aˣ := κ
  have hi' : W.IsInert (rUp h) κ' := (lamUp h ⟨A, κ, hi, hu⟩).inert
  have hu' : ∀ (R : Type) [CommRing R] [Algebra c.O R] [Alg.IsCO c.O R] (κ'' : ∀ v, Fin n → V.frame.Iv v →* Rˣ), W.IsInert (rUp h) κ'' →
      ∃! f : A →ₐ[c.O] R, ∀ v i, W.pushCh (f : A →+* R) (κ' v i) = κ'' v i := (lamUp h ⟨A, κ, hi, hu⟩).univ
  let θ' : (hset Q τ₀).X.I.T →* Aˣ := θ
  have th' : IsTheta Q τ₀ (⟨A, κ', hi', hu'⟩ : LamObj (rUp h)) θ' := fun v i x g hg y h1 h2 => th v i x g hg y h1 h2
  have hw' : (hset Q τ₀).IsWt θ' := ⟨cont_up Q0 Q τ₀ θ hw.cont, fun K => free_of_neat _ _ _ _ (neatU l L Ω s n hn V Q c m τ₀ K)⟩
  refine ⟨θ', fun i => a (opUp Q0 Q hsub τ₀ i), LamObj.toPair ⟨A, κ', hi', hu'⟩ B'.u, hw', rfl, fun _ => rfl, fun v i γ hγ => ?_,
    (_root_.UpperTheory.V.Hi.isDomain_and_denseWt_of_isTheta P.litN l L Ω s n hn V Q c m τ₀ (rUp h) ⟨A, κ', hi', hu'⟩ θ' th').2,
    _root_.UpperTheory.V.Hi.exists_hecke_ideal P l L Ω s n hn V Q c (rUp h) ι B' ⟨A, κ', hi', hu'⟩
      ⟨m, τ₀, _root_.UpperTheory.V.Hi.LvR.type_for_r_up_of_type_for h hp ι τ₀ ty, θ', th', hw', fun i => a (opUp Q0 Q hsub τ₀ i), res_up h Q0 Q hsub hp τ₀ a rs⟩⟩
  have e0 := DFunLike.congr_fun (LamObj.toPair_spec (rUp h) ⟨A, κ', hi', hu'⟩ B'.u v i) (⟨γ, hγ⟩ : V.frame.Iv v)
  exact congrArg Units.val e0
set_option maxHeartbeats 1600000 in
private theorem s2 (P : _root_.UpperTheory.V.Af.HypothesesH') (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ) (hn : 1 ≤ n)
    (V0 : s.Lev) (Q0 : QData V0) (c : Coef l) (r : Resid V0.frame c.O n) (ι : Qbar l ≃+* ℂ)
    (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (κ : ∀ v, Fin n → V0.frame.Iv v →* Aˣ) (hi hu)
    (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O) (ty : _root_.UpperTheory.V.Hi.CaseU.TypeForAlt r ι τ₀) (θ : (hset Q0 τ₀).X.I.T →* Aˣ)
    (th : IsTheta Q0 τ₀ (⟨A, κ, hi, hu⟩ : LamObj r) θ) (hw : (hset Q0 τ₀).IsWt θ) (a : (hset Q0 τ₀).Op → c.O) (rs : IsRes Q0 r τ₀ a) (V : s.Lev) (h : (Pa.globOf r V).Hom (Pa.globOf r V0)) (Q : QData V) [_dq : DecidableEq Q.Q] (hsub : V0.S' ⊆ V.S') (hp : ∀ g, h.p (toGS Ω V.S' g) = toGS Ω V0.S' g) (_B' : UniversalOrdinaryDeterminantRing (rUp h)) (hS : V0.S' = s.S) (K0 : (hset Q0 τ₀).Lev)
    (θ' : (hset Q τ₀).X.I.T →* Aˣ) (a' : (hset Q τ₀).Op → c.O) (e1 : @Eq ((hset Q τ₀).X.I.T →* Aˣ) θ' θ) (e2 : ∀ i, a' i = a (opUp Q0 Q hsub τ₀ i)) :
    (∀ i, (hset Q τ₀).op A i = (hset Q0 τ₀).op A (opUp Q0 Q hsub τ₀ i)) ∧
      ∀ f : (hset Q0 τ₀).X.Fn A m, f ∈ (hset Q τ₀).MK θ' a' (kMax Q τ₀) ↔ f ∈ (hset Q0 τ₀).MK θ a K0 := by
  obtain rfl : a' = fun i => a (opUp Q0 Q hsub τ₀ i) := funext e2
  rw [e1]
  exact hida_levelUR2LocEq P l L Ω s n hn V0 V Q0 Q c r ι ⟨A, κ, hi, hu⟩ ⟨m, τ₀, ty, θ, th, hw, a, rs⟩ K0 (kMax Q τ₀) hS (fun _ => rfl)
    (p0 h) (continuous_levelChangeBaseGroupHom h) (surjective_levelChangeBaseGroupHom h) (levelChangeBaseGroupHom_apply_projection h hp) (opUp Q0 Q hsub τ₀) (fun _ => rfl) fun _ _ => ⟨_, rfl⟩
set_option maxHeartbeats 3200000 in
private theorem s3 (P : _root_.UpperTheory.V.Af.HypothesesH') (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ) (hn : 1 ≤ n)
    (V0 : s.Lev) (Q0 : QData V0) (c : Coef l) (r : Resid V0.frame c.O n) (ι : Qbar l ≃+* ℂ)
    (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (κ : ∀ v, Fin n → V0.frame.Iv v →* Aˣ) (hi hu)
    (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O) (ty : _root_.UpperTheory.V.Hi.CaseU.TypeForAlt r ι τ₀) (θ : (hset Q0 τ₀).X.I.T →* Aˣ)
    (th : IsTheta Q0 τ₀ (⟨A, κ, hi, hu⟩ : LamObj r) θ) (hw : (hset Q0 τ₀).IsWt θ) (a : (hset Q0 τ₀).Op → c.O) (rs : IsRes Q0 r τ₀ a) (V : s.Lev) (h : (Pa.globOf r V).Hom (Pa.globOf r V0)) (Q : QData V) [dq : DecidableEq Q.Q] (hsub : V0.S' ⊆ V.S') (hp : ∀ g, h.p (toGS Ω V.S' g) = toGS Ω V0.S' g) (B' : UniversalOrdinaryDeterminantRing (rUp h)) (hS : V0.S' = s.S) (K0 : (hset Q0 τ₀).Lev) (B : UniversalOrdinaryDeterminantRing r) (β : B'.B →ₐ[c.O] B.B) (hβ1 : B'.u.D.map β.toRingHom = B.u.D.comap (p0 h))
    (hβ2 : ∀ (v : Vl l L) i, @Eq (Dec (F := L) (s.A v.1) →* B.Bˣ) (W.pushCh β.toRingHom (B'.u.ψ v i)) (B.u.ψ v i))
    (μ : B.B →+* Module.End A ((hset Q0 τ₀).MK θ a K0))
    (hμ : (hset Q0 τ₀).MK θ a K0 = ⊥ ∨ ∃ (_ : Fact (CommOn ((hset Q0 τ₀).MK θ a K0) ((hset Q0 τ₀).op A))) (_ : Alg.IsCO c.O ((hset Q0 τ₀).TK θ a K0)) (f : B.B →ₐ[c.O] (hset Q0 τ₀).TK θ a K0), (hset Q0 τ₀).IsMap θ a K0 B.u.D B.u.ψ f ∧ ∀ t, μ t = (f t : Module.End A ((hset Q0 τ₀).MK θ a K0))) :
    ∃ (M : Type) (_ : AddCommGroup M) (_ : Module A M) (ρ : Representation A (GV n Q.wq) M) (α : B'.B →+* Module.End A M) (lam : A →ₐ[c.O] B'.B), (∀ v i (γ : V0.frame.Gv v) (hγ : γ ∈ V0.frame.Iv v), lam (κ v i ⟨γ, hγ⟩ : Aˣ) = (@id (Dec (F := L) (s.A v.1) →* B'.Bˣ) (B'.u.ψ v i) γ : B'.Bˣ)) ∧
      (∀ b z, α (lam b) z = b • z) ∧ (∀ t g z, α t (ρ g z) = ρ g (α t z)) ∧
      (∀ K : ∀ q, Subgroup (GLw n (Q.wq q)), (∀ q, IsOpen (K q : Set (GLw n (Q.wq q))) ∧ IsCompact (K q : Set (GLw n (Q.wq q)))) → Module.Finite A (fixd ρ (Subgroup.pi Set.univ K))) ∧
      (∀ K K' : ∀ q, Subgroup (GLw n (Q.wq q)), (∀ q, IsOpen (K q : Set (GLw n (Q.wq q))) ∧ IsCompact (K q : Set (GLw n (Q.wq q)))) → (∀ q, IsOpen (K' q : Set (GLw n (Q.wq q))) ∧ IsCompact (K' q : Set (GLw n (Q.wq q)))) → ∀ [((Subgroup.pi Set.univ K').subgroupOf (Subgroup.pi Set.univ K)).Normal], (∀ q, K' q ≤ K q) →
        ∃ ρ' : Representation A (Subgroup.pi Set.univ K ⧸ (Subgroup.pi Set.univ K').subgroupOf (Subgroup.pi Set.univ K)) (fixd ρ (Subgroup.pi Set.univ K')), (∀ (u : Subgroup.pi Set.univ K) f, (ρ' (u : _ ⧸ _) f).1 = ρ u.1 f) ∧
          Module.Projective (MonoidAlgebra A (Subgroup.pi Set.univ K ⧸ (Subgroup.pi Set.univ K').subgroupOf (Subgroup.pi Set.univ K))) ρ'.asModule) ∧
      (∃ e0 : fixd ρ (Subgroup.pi Set.univ fun q => KO ((Q.wq q).adicCompletion L) (Fin n)) ≃+ (hset Q0 τ₀).MK θ a K0, ∀ t (x x' : fixd ρ (Subgroup.pi Set.univ fun q => KO ((Q.wq q).adicCompletion L) (Fin n))), (x' : M) = α t x → e0 x' = μ (β t) (e0 x)) ∧
      ∀ z : M, z ≠ 0 → ∃ (x : B'.B →+* Qbar l) (ρx : V.frame.G₀ →* GL (Fin n) (Qbar l)) (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (π : Representation ℂ (GV n Q.wq) Y) (sp : M →+ Y) (σ : ∀ q, SmIrr (GLw n (Q.wq q))), sp z ≠ 0 ∧ Continuous ρx ∧ B'.u.D.map x = W.GDet.ofRep (W.mat ρx) ∧ (∀ t y, sp (α t y) = ι (x t) • sp y) ∧ (∀ g y, sp (ρ g y) = π g (sp y)) ∧ (∀ q, IsoSum (π.comp (MonoidHom.mulSingle (fun q => GLw n (Q.wq q)) q)) ⊤ (σ q)) ∧ ∀ q (Bq : ValuationSubring Ω) (hB : IsPlaceOver Bq (Q.wq q)) (rc : IrrGL (k := (Q.wq q).adicCompletion L) → WD hB), _root_.UpperTheory.Zero.LLC.IsRecT hB rc → _root_.UpperTheory.V.Z.Win.WOT ι (ρx.comp V.pr) (rc (algNorm (σ q))) := by
  obtain ⟨θ', a', lam, hw', e1, e2, hl, hd, hJ⟩ := s1 P l L Ω s n hn V0 Q0 c r ι A κ hi hu m τ₀ ty θ th hw a rs V h Q hsub hp B'
  obtain ⟨hop, hM⟩ := s2 P l L Ω s n hn V0 Q0 c r ι A κ hi hu m τ₀ ty θ th hw a rs V h Q hsub hp B' hS K0 θ' a' e1 e2
  obtain ⟨ρ, α, h1, h2, h3, h4, h5, h6⟩ := @umod_abs P.litN L Ω _ _ _ _ _ l _ n c (hset Q τ₀) (_root_.UpperTheory.V.Hi.axU_s P.litN l L Ω s n hn V Q c m τ₀) A _ _ _ θ' hw' a' dq ι (_root_.UpperTheory.V.Hi.CaseU.UnitaryPointProperties (rUp h) ι)
    (_root_.UpperTheory.V.Hi.automorphicHeckeSet_unitaryPointProperties_of_typeFor P l L Ω s n hn V Q c (rUp h) ι m τ₀ (_root_.UpperTheory.V.Hi.LvR.type_for_r_up_of_type_for h hp ι τ₀ ty)) (fun _ => ⟨0, fun _ _ _ => le_rfl⟩) trivial (hd _) (neatU l L Ω s n hn V Q c m τ₀)
    (levelUR2Faith l L Ω s n hn V Q c m τ₀) B'.B _ _ B'.u.D B'.u.ψ lam (base_object_hom_ext B') hJ
  have key := _root_.UpperTheory.V.Hi.levelUR2SmulKey_alt P.litN l L Ω s n hn V0 V Q0 Q c m τ₀ A θ hw a K0 (kMax Q τ₀)
    (p0 h) (continuous_levelChangeBaseGroupHom h) (surjective_levelChangeBaseGroupHom h) (levelChangeBaseGroupHom_apply_projection h hp) (opUp Q0 Q hsub τ₀) (fun _ => rfl) (fun _ _ => ⟨_, rfl⟩)
    θ' a' hw' e1 e2 hop hM B.B B'.B B.u.D B.u.ψ B'.u.D B'.u.ψ β hβ1 hβ2
    (base_object_hom_ext B') μ hμ (fun t y => (α t ⟨y.1, Submodule.mem_iSup_of_mem _ y.2⟩).1) (fun t => congrArg Subtype.val (map_zero (α t)))
    (fun {i1} {i2} => (@h5 (kMax Q τ₀) i1 i2).elim fun f hf => ⟨f, hf.1, fun t y => hf.2 t y _ rfl⟩)
  obtain ⟨e0, he0⟩ := eq_sub _ _ ((hset Q0 τ₀).MK θ a K0) _ (h3 (kMax Q τ₀)).1 hM
  refine ⟨_, _, _, ρ, α, lam, hl, h1, h2, fun K hK => (h3 ⟨K, hK⟩).2, fun K K' hK hK' hN => @h4 ⟨K, hK⟩ ⟨K', hK'⟩ hN, ⟨e0, fun t x x' hx => Subtype.ext ?_⟩, h6⟩
  exact ((he0 x').1.trans (congrArg Subtype.val hx)).trans (key t ⟨x.1.1, (he0 x).2⟩ (e0 x) (he0 x).1.symm)
set_option maxHeartbeats 1600000 in
private theorem s4 (P : _root_.UpperTheory.V.Af.HypothesesH') (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ) (hn : 1 ≤ n)
    (V0 : s.Lev) (Q0 : QData V0) (c : Coef l) (r : Resid V0.frame c.O n) (ι : Qbar l ≃+* ℂ)
    (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (κ : ∀ v, Fin n → V0.frame.Iv v →* Aˣ) (hi hu)
    (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O) (ty : _root_.UpperTheory.V.Hi.CaseU.TypeForAlt r ι τ₀) (θ : (hset Q0 τ₀).X.I.T →* Aˣ)
    (th : IsTheta Q0 τ₀ (⟨A, κ, hi, hu⟩ : LamObj r) θ) (hw : (hset Q0 τ₀).IsWt θ) (a : (hset Q0 τ₀).Op → c.O) (rs : IsRes Q0 r τ₀ a) (B : UniversalOrdinaryDeterminantRing r) (K : (hset Q0 τ₀).Lev) (hS : V0.S' = s.S) (J : Ideal B.B)
    (hJ : (hset Q0 τ₀).IsJ θ a K B.u.D B.u.ψ (LamObj.toPair ⟨A, κ, hi, hu⟩ B.u : A →ₐ[c.O] B.B) J) : _root_.UpperTheory.V.Th.LevelIdealCondition B J := by
  have hN := P.litN
  have hC : Pa.CohP := ⟨hN.coh.lf, hN.coh.lt, hN.coh.le, hN.coh.gf, hN.coh.ge, hN.coh.gw, hN.coh.pt,
    GlobalTheory.Published.TameLocal_of_duality hN.coh.lt⟩
  have hA0 := _root_.UpperTheory.V.Hi.axU_s hN l L Ω s n hn V0 Q0 c m τ₀
  obtain ⟨wv, e, hwt⟩ : ∃ (wt : Pa.WtVars (Pa.locOf r) c.O n (n * Module.finrank ℚ (Lp L))) (e : Pa.abelian₂ c.O Empty (n * Module.finrank ℚ (Lp L)) ≃ₐ[c.O] A), ∀ k, ∃ hγ : wt.γ k ∈ V0.frame.Iv (wt.v k), residue c.O (wt.c k) * (r.psib (wt.v k) (wt.i k) (wt.γ k) : ResidueField c.O) = 1 ∧ e (MvPowerSeries.X (.inr k)) = algebraMap c.O A (wt.c k) * (κ (wt.v k) (wt.i k) ⟨wt.γ k, hγ⟩ : Aˣ) - 1 :=
    levelUR2WtVars l L Ω s n V0 c r B ⟨A, κ, hi, hu⟩ (W.locCFT hN.aut.art hC l L Ω s)
  choose hγ hres hX using hwt
  obtain ⟨μ, hμ1, hμ2, hμ3⟩ := levelUR2BaseAct L Ω l n c _ hA0 A θ hw a K B.B B.u.D B.u.ψ _ J hJ
  obtain ⟨-, hfin, hfree⟩ := (hiComm L Ω l n c _ hA0 A θ hw K).2.2.2 a
  obtain ⟨b, eb, hb, heb, hsub0⟩ := Th.AnnihilatorQuotientFinite.basePack l L Ω s V0 c.O n r B J _ wv A e (LamObj.toPair ⟨A, κ, hi, hu⟩ B.u) hres
    (fun k => lam_val ⟨A, κ, hi, hu⟩ B.u _ _ _ (hγ k) _ _ (hX k)) _ μ hμ1 hμ2
  subst hb
  refine ⟨b, fun V h q v w Bq hp hv hvS hV hw' hBv _ => ?_, hγ, fun x h ha t ht k hk y => ?_⟩
  swap
  · obtain ⟨⟨lam, hl⟩, hb⟩ := _root_.UpperTheory.V.Hi.arith_good_iff_hset_of_theta_incr_weight hN l L Ω s n hn V0 Q0 c m τ₀ r B ⟨A, κ, hi, hu⟩ θ th h ha.1
    have har := (hb lam hl (Th.barPt B x)).1.1 ha
    obtain ⟨y, rfl⟩ := eb.surjective y
    rw [← heb, hsub0]
    exact _root_.UpperTheory.V.Th.AnnihilatorQuotientFinite.ctrlMu_of_arith_weight L Ω l n c _ hA0 A θ hw ι (_root_.UpperTheory.V.Hi.CaseU.UnitaryPointProperties r ι) (_root_.UpperTheory.V.Hi.automorphicHeckeSet_unitaryPointProperties_of_typeFor P l L Ω s n hn V0 Q0 c r ι m τ₀ ty)
      (x.comp (LamObj.toPair ⟨A, κ, hi, hu⟩ B.u)) lam (Set.mem_univ _) har a K B.B B.u.D B.u.ψ μ hμ3 t ht k
      (fun y => (hsub0 x _).1 (by rw [heb]; exact hk _)) y
  obtain rfl : (fun j => (w j).under (𝓞 (Lp L))) = v := funext fun j => under_eq (hw' j) (hBv j)
  have hsub : V0.S' ⊆ V.S' := hS ▸ V.sub
  obtain ⟨p', hp1, hp2⟩ := pairUp h hn hp B.u
  obtain ⟨B'⟩ := W.b0Ex (W.phiAll hC) l L Ω s V c n (rUp h) B.B ⟨p'⟩
  obtain ⟨β, hβ, -⟩ := B'.univ B.B p'
  have hβ1 : B'.u.D.map β.toRingHom = B.u.D.comap (p0 h) := hβ.1.trans hp1
  have hβ2 : ∀ (v : Vl l L) i, @Eq (Dec (F := L) (s.A v.1) →* B.Bˣ) (W.pushCh β.toRingHom (B'.u.ψ v i)) (B.u.ψ v i) :=
    fun v i => (hβ.2 v i).trans (hp2 v i)
  obtain ⟨M, _, _, ρ, α, lam, hl, h1, h2, h3, h4, ⟨e0, he0⟩, h6⟩ := @s3 P l _ L Ω _ _ _ _ _ _ s n hn V0 Q0 c r ι A _ _ _ κ hi hu m τ₀ ty θ th hw a rs
    V h (qUp V w hv hvS hV) (instDecidableEqFin q) hsub hp B' hS K B β hβ1 hβ2 μ hμ3
  obtain ⟨hI, hNm⟩ := levelUR2IwLev l L n q w
  obtain ⟨ρ', h7, h8⟩ := @h4 (fun j => AlgebraTools.iwC _ n ⊤) (fun j => AlgebraTools.iwC _ n (Pa.ellC l _)) (fun j => ⟨(hI j ⊤).1, (hI j ⊤).2.1⟩)
    (fun j => ⟨(hI j _).1, (hI j _).2.1⟩) hNm fun j => (hI j _).2.2
  refine @_root_.UpperTheory.V.Hi.levelUR2ModPack_alt l _ L Ω _ _ _ _ _ _ s V0 c.O _ _ _ n r B J _ b V h q w (rN h) (rN_compat h) B'.B _ _ _ (pairN h B'.u)
    A _ _ e lam (fun k => ?_) β ⟨hβ1, hβ2⟩ M _ _ ρ α h1 h2
    (h3 (fun j => AlgebraTools.iwC _ n (Pa.ellC l _)) fun j => ⟨(hI j _).1, (hI j _).2.1⟩) hNm ρ' h7 h8 (e0.trans eb)
    (fun t x x' hx => (congrArg eb (he0 t x x' hx)).trans (heb (β t) (e0 x))) ι h6
  rw [hX k, map_sub, map_mul, map_one, AlgHom.commutes]
  exact congrArg (fun z => algebraMap c.O B'.B (b.wt.c k) * z - 1) (hl (b.wt.v k) (b.wt.i k) (b.wt.γ k) (hγ k))
set_option maxHeartbeats 800000 in
theorem UpperTheory.V.Th.AnnihilatorQuotientFinite.levelX_of_isJ_unitaryHeckeData :
    _root_.UpperTheory.V.Af.HypothesesH' → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (r : Resid V.frame c.O n) (ι : Qbar l ≃+* ℂ), ∀ (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) (R : _root_.UpperTheory.V.Hi.CaseU.UnitaryHeckeData Q ι Λ) (K : (hset Q R.τ₀).Lev), V.S' = s.S → ∀ J : Ideal B.B, R.IsJ B K J → _root_.UpperTheory.V.Th.LevelIdealCondition B J := by
  intro P l _ L Ω _ _ _ _ _ _ s n hn V0 Q0 c r ι B Λ R K hS J hJ
  obtain ⟨A, κ, hi, hu⟩ := Λ
  obtain ⟨m, τ₀, ty, θ, th, hw, a, rs⟩ := R
  exact s4 P l L Ω s n hn V0 Q0 c r ι A κ hi hu m τ₀ ty θ th hw a rs B K hS J hJ
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.V UpperTheory.V.Th UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
theorem UpperTheory.V.Th.hida_x_of_printed_hida :
    _root_.UpperTheory.V.Af.HypothesesH' → _root_.UpperTheory.V.Th.HidaFamilyCondition := by
  intro P l _ L Ω _ _ _ _ _ _ s V hS c n hn r B Λ ι
  obtain ⟨R⟩ := _root_.UpperTheory.V.Hi.nonempty_unitaryHeckeData P l L Ω s n hn V (QData.empty V hS) c r ι Λ
  let K : (hset (QData.empty V hS) R.τ₀).Lev := ⟨fun q => Empty.elim q, fun q => Empty.elim q⟩
  obtain ⟨J, hJ⟩ := _root_.UpperTheory.V.Hi.exists_hecke_ideal P l L Ω s n hn V _ c r ι B Λ R K
  exact ⟨J, _root_.UpperTheory.V.Hi.hecke_ideal_point_properties P l L Ω s n hn V _ c r ι B Λ R K hS J hJ, _root_.UpperTheory.V.Th.AnnihilatorQuotientFinite.levelX_of_isJ_unitaryHeckeData P l L Ω s n hn V _ c r ι B Λ R K hS J hJ⟩
end
