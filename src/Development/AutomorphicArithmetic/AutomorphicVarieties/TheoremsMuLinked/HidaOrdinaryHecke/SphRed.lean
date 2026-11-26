module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.ClParts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.HiComm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.SpecIntIff

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.HidaOrdinaryHecke.KerSp
open IsLocalRing

theorem UpperTheory.V.Th.AnnihilatorQuotientFinite.kerSp :
    ∀ {A K M W : Type} [CommRing A] [Field K] [AddCommGroup M] [Module A M] [AddCommGroup W] [Module K W] (Y0 Y : Submodule A M) [Module.Free A Y0] (e : Module.End A Y0), IsIdempotentElem e → Y ≤ Y0 → (∀ y : Y0, (y : M) ∈ Y ↔ e y = y) → ∀ (χ : A →+* K) (sp : M → W), (∀ f ∈ Y0, ∀ f' ∈ Y0, sp (f + f') = sp f + sp f') → (∀ f ∈ Y0, ∀ b : A, sp (b • f) = χ b • sp f) → (∀ (κ : Type) (b : Module.Basis κ A Y0), LinearIndependent K fun i => sp (b i)) → ∀ f : Y, sp f = 0 ↔ f ∈ (RingHom.ker χ • ⊤ : Submodule A Y) := by
  intro A K M W _ _ _ _ _ _ Y0 Y _ e he hYY0 hiff χ sp hadd hsmul hli f
  classical
  have hsp0 : sp 0 = 0 := by
    simpa using hadd 0 Y0.zero_mem 0 Y0.zero_mem
  have hsum : ∀ {ι : Type} (s : Finset ι) (g : ι → M), (∀ i, g i ∈ Y0) →
      sp (∑ i ∈ s, g i) = ∑ i ∈ s, sp (g i) := by
    intro ι s g hg
    induction s using Finset.induction_on with
    | empty => simp [hsp0]
    | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        hadd _ (hg a) _ (Y0.sum_mem (fun i _ => hg i)), ih]
  constructor
  · intro h0
    let b := Module.Free.chooseBasis A Y0
    let y0 : Y0 := ⟨f, hYY0 f.2⟩
    have hey : e y0 = y0 := (hiff y0).1 f.2
    have hy0 : y0 = ∑ i ∈ (b.repr y0).support, b.repr y0 i • b i := by
      conv_lhs => rw [← b.linearCombination_repr y0]
      rw [Finsupp.linearCombination_apply]
      rfl
    have hf : (f : M) = ∑ i ∈ (b.repr y0).support, b.repr y0 i • ((b i : Y0) : M) := by
      have h := congrArg (fun z : Y0 => (z : M)) hy0
      rw [show (f : M) = (y0 : M) from rfl]
      refine h.trans ?_
      rw [Submodule.coe_sum]
      simp only [Submodule.coe_smul]
    have hspf : sp (f : M) = ∑ i ∈ (b.repr y0).support, χ (b.repr y0 i) • sp ((b i : Y0) : M) := by
      rw [hf, hsum _ _ (fun i => Y0.smul_mem _ (b i).2)]
      exact Finset.sum_congr rfl (fun i _ => hsmul _ (b i).2 _)
    rw [h0] at hspf
    have hc : ∀ i ∈ (b.repr y0).support, χ (b.repr y0 i) = 0 :=
      linearIndependent_iff'.1 (hli _ b) _ (fun i => χ (b.repr y0 i)) hspf.symm
    have hz : ∀ i, ((e (b i) : Y0) : M) ∈ Y := fun i =>
      (hiff (e (b i))).2 (by rw [← Module.End.mul_apply, he.eq])
    have hfY : f = ∑ i ∈ (b.repr y0).support, b.repr y0 i • (⟨_, hz i⟩ : Y) := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simp only [Submodule.coe_smul]
      have h1 : (f : M) = ((e y0 : Y0) : M) := by rw [hey]
      rw [h1]
      conv_lhs => rw [hy0]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Submodule.coe_sum]
      simp only [map_smul, Submodule.coe_smul]
    rw [hfY]
    refine Submodule.sum_mem _ (fun i hi => ?_)
    exact Submodule.smul_mem_smul ((RingHom.mem_ker).2 (hc i hi)) Submodule.mem_top
  · intro hf
    refine Submodule.smul_induction_on (p := fun g : Y => sp (g : M) = 0) hf ?_ ?_
    · intro r hr y _
      show sp ((r • y : Y) : M) = 0
      rw [Submodule.coe_smul, hsmul _ (hYY0 y.2) r, (RingHom.mem_ker).1 hr, zero_smul]
    · intro y z hy hz
      have hy' : sp (y : M) = 0 := hy
      have hz' : sp (z : M) = 0 := hz
      show sp ((y + z : Y) : M) = 0
      rw [Submodule.coe_add, hadd _ (hYY0 y.2) _ (hYY0 z.2), hy', hz', add_zero]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.HidaOrdinaryHecke.EigKill
open IsLocalRing

theorem UpperTheory.V.Th.AnnihilatorQuotientFinite.eigKill :
    ∀ {K V : Type} [Field K] [AddCommGroup V] [Module K V] (φ : Module.End K V) (k : ℕ) (F : V), F ∈ ⨆ μ : K, φ.eigenspace μ → (φ ^ k) F = 0 → φ F = 0 := by
  intro K V _ _ _ φ k F hF hk
  have hdisj := Module.End.eigenspaces_iSupIndep φ 0
  set S := ⨆ (μ : K) (_ : μ ≠ 0), φ.eigenspace μ with hS
  have hinv : ∀ z ∈ S, φ z ∈ S := by
    have hle : S ≤ S.comap φ := by
      refine iSup₂_le fun μ hμ => ?_
      intro v hv
      rw [Submodule.mem_comap, Module.End.mem_eigenspace_iff.1 hv]
      exact Submodule.mem_iSup_of_mem μ (Submodule.mem_iSup_of_mem hμ (Submodule.smul_mem _ _ hv))
    exact fun z hz => hle hz
  have hinj : ∀ z ∈ S, φ z = 0 → z = 0 := by
    intro z hz h0
    have hz0 : z ∈ φ.eigenspace 0 := by
      rw [Module.End.mem_eigenspace_iff, zero_smul]
      exact h0
    exact Submodule.disjoint_def.1 hdisj z hz0 hz
  have hpow : ∀ n : ℕ, ∀ z ∈ S, (φ ^ n) z = 0 → z = 0 := by
    intro n
    induction n with
    | zero =>
      intro z _ h
      simpa using h
    | succ n ih =>
      intro z hz h
      rw [pow_succ, Module.End.mul_apply] at h
      exact hinj z hz (ih _ (hinv z hz) h)
  rw [iSup_split_single _ (0 : K)] at hF
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hF
  have hy' : φ y = 0 := by
    rw [Module.End.mem_eigenspace_iff, zero_smul] at hy
    exact hy
  cases k with
  | zero =>
    have h0 : y + z = 0 := by simpa using hk
    rw [h0, map_zero]
  | succ k =>
    have hyk : (φ ^ (k + 1)) y = 0 := by
      rw [pow_succ, Module.End.mul_apply, hy', map_zero]
    rw [map_add (f := _), hyk, zero_add] at hk
    rw [map_add (f := _), hy', hpow _ z hz hk, map_zero, add_zero]
end

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
theorem UpperTheory.V.Th.AnnihilatorQuotientFinite.sphRed :
    ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (ι : Qbar l ≃+* ℂ) (P : Wt L l n → (H.Gq →* GL (Fin n) (Qbar l)) → Prop), H.Aut ι P →
    ∀ (x : A →ₐ[c.O] Qbar l) (lam : Wt L l n), lam ∈ H.admitted → H.Arith θ x.toRingHom lam → ∀ (a : H.Op → c.O) (K : H.Lev) [Fact (CommOn (H.MK θ a K) (H.op A))],
    ∀ t ∈ Algebra.adjoin c.O (Set.range fun p : H.Wp × Fin n => H.gen θ a K (.inl p)), ∀ k : ℕ,
    (∀ y : H.MK θ a K, ((t ^ k : H.TK θ a K) : Module.End A (H.MK θ a K)) y ∈ (RingHom.ker x • ⊤ : Submodule A (H.MK θ a K))) → ∀ y : H.MK θ a K, (t : Module.End A (H.MK θ a K)) y ∈ (RingHom.ker x • ⊤ : Submodule A (H.MK θ a K)) := by
  intro L Ω _ _ _ _ _ l _ n c H hH A _ _ _ θ hθ ι P hP x lam hlam har a K _ t ht k h y
  haveI : Finite (ResidueField c.O) := (UpperTheory.V.abelian₂.dvr_finite l c.O).2.1
  haveI : IsCNL A := IsCNL.ofCO c.O A
  obtain ⟨h0, hfin, hfree, -⟩ := hiComm L Ω l n c H hH A θ hθ K
  obtain ⟨e, -, hi, hY, -⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.locIdem A _ _ _ (H.op A) (fun i => algebraMap c.O A (a i)) h0
  obtain ⟨d, ξ, c0, sp, hsp⟩ := spec L Ω l n c H hH A θ hθ ι x lam har
  have hO := (clParts L Ω l n c H hH A θ hθ ι P hP x lam d ξ c0 sp hsp hlam K c0 le_rfl).2
  have hOZ : ∀ f ∈ H.X.Ord (H.τA A) θ (H.lev K), sp f ∈ ⨆ Y : {Y : H.Part ι lam ξ // P lam Y.r}, Y.1.Y := fun f hf => by
    have h1 : sp f ∈ H.OrdAt θ ι x.toRingHom lam ξ K c0 := hsp.span K c0 le_rfl ▸ Submodule.subset_span ⟨f, hf, rfl⟩
    exact (hO.le.trans (iSup_mono fun _ => inf_le_left)) h1
  have hI : RingHom.ker x = RingHom.ker (ι.toRingHom.comp x.toRingHom) := by
    ext b
    simp [RingHom.mem_ker]
  exact sr_abs (R := c.O) (H.X.Ord (H.τA A) θ (H.lev K)) (H.MK θ a K) inf_le_left (H.op A) Sum.inl e hi hY
    (ι.toRingHom.comp x.toRingHom) sp (hsp.add K) (hsp.smul K) (hsp.indep K) (H.opC ι lam d) (hsp.op K)
    (fun Y : {Y : H.Part ι lam ξ // P lam Y.r} => Y.1.Y) (fun Y i => ⟨_, Y.1.sph i.1 _⟩) hOZ _ hI t ht k h y
