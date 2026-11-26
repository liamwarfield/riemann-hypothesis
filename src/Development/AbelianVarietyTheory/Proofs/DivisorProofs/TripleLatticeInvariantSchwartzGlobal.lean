module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.VdHLeNatAbs
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ShortGeneratorPlaceValuationBoundProof
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VwNatCastNonneg
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntAFSmulMemLatOF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchwartzNe

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleLatticeInvariantSchwartzGlobal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleLatticeInvariantSchwartzGlobal
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Classical

open scoped GlobalTheory.VacAny
open Topology

noncomputable section
namespace GlobalTheory.VacAvg

def schrL {K : Type} [CommRing K] [Invertible (2 : K)] (ψ : AddChar K ℂ) {κ : Type} [Fintype κ]
    (z : (κ → K) × (κ → K)) : Module.End ℂ ((κ → K) → ℂ) where
  toFun := schr ψ z
  map_add' f g := by funext x; simp only [schr, Pi.add_apply, mul_add]
  map_smul' r f := by funext x; simp only [schr, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem schrL_apply {K : Type} [CommRing K] [Invertible (2 : K)] (ψ : AddChar K ℂ) {κ : Type} [Fintype κ]
    (z : (κ → K) × (κ → K)) (f : (κ → K) → ℂ) : schrL ψ z f = schr ψ z f := rfl

theorem ops_schrL {K : Type} [CommRing K] [Invertible (2 : K)] (ψ : AddChar K ℂ) {κ : Type} [Fintype κ] :
    GlobalTheory.Published.SvN.Ops (fun z z' : (κ → K) × (κ → K) => ψ (⅟(2 : K) * (z.1 ⬝ᵥ z'.2 - z'.1 ⬝ᵥ z.2))) (schrL ψ) := by
  constructor
  · intro v
    funext x
    simp [schrL_apply, schr]
  · intro x y v
    simp only [schrL_apply]
    exact schr_schr ψ x y v

theorem addChar_ne_zero {A : Type} [AddGroup A] (ψ : AddChar A ℂ) (t : A) : ψ t ≠ 0 := by
  intro h
  have := ψ.map_add_eq_mul t (-t)
  rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at this
  exact one_ne_zero this

theorem eventually_schr_fix {F : Type} [Field F] [NumberField F] (v : Pl (F := F)) (ψ : AddChar (Fv F v) ℂ)
    (hψ : Continuous ψ) {κ : Type} [Fintype κ] {f : (κ → Fv F v) → ℂ} (hf : f ∈ SB (κ → Fv F v)) :
    ∀ᶠ z in 𝓝 (0 : (κ → Fv F v) × (κ → Fv F v)), schr ψ z f = f := by
  obtain ⟨U₀, hU₀⟩ := GlobalTheory.HeisLatVac.lc_exists_open_ker ψ hψ
  obtain ⟨K, hK⟩ := GlobalTheory.WeilM.HaarUniq.exists_invariant hf
  have hc : Continuous fun z : ((κ → Fv F v) × (κ → Fv F v)) × (κ → Fv F v) =>
      z.2 ⬝ᵥ z.1.2 + ⅟(2 : Fv F v) * (z.1.1 ⬝ᵥ z.1.2) :=
    (continuous_snd.dotProduct continuous_fst.snd).add
      (continuous_const.mul (continuous_fst.fst.dotProduct continuous_fst.snd))
  have h1 : ∀ᶠ z : (κ → Fv F v) × (κ → Fv F v) in 𝓝 0, ∀ x ∈ tsupport f,
      x ⬝ᵥ z.2 + ⅟(2 : Fv F v) * (z.1 ⬝ᵥ z.2) ∈ (U₀ : Set (Fv F v)) := by
    refine IsCompact.eventually_forall_of_forall_eventually hf.2
      (P := fun (z : (κ → Fv F v) × (κ → Fv F v)) (x : κ → Fv F v) =>
        x ⬝ᵥ z.2 + ⅟(2 : Fv F v) * (z.1 ⬝ᵥ z.2) ∈ (U₀ : Set (Fv F v))) fun x _ => ?_
    refine (U₀.isOpen.preimage hc).mem_nhds ?_
    simpa using U₀.zero_mem
  have h2 : ∀ᶠ z : (κ → Fv F v) × (κ → Fv F v) in 𝓝 0, z.1 ∈ (K : Set (κ → Fv F v)) :=
    (K.isOpen.preimage continuous_fst).mem_nhds K.zero_mem
  filter_upwards [h1, h2] with z hz1 hz2
  funext x
  show ψ (x ⬝ᵥ z.2 + ⅟(2 : Fv F v) * (z.1 ⬝ᵥ z.2)) * f (x + z.1) = f x
  rw [hK z.1 hz2 x]
  by_cases hx : x ∈ tsupport f
  · rw [hU₀ _ (hz1 x hx), one_mul]
  · rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]

theorem tens_sum {F : Type} [Field F] [NumberField F] {R κ ι : Type} (ev : AF F → R) (s : Finset ι) (c : ι → ℂ)
    (g : ι → (κ → R) → ℂ) (r : (κ → AF F) → ℂ) :
    tens ev (∑ q ∈ s, c q • g q) r = ∑ q ∈ s, c q • tens ev (g q) r := by
  funext x
  simp only [tens, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul, mul_assoc]

theorem tens_smul {F : Type} [Field F] [NumberField F] {R κ : Type} (ev : AF F → R) (c : ℂ) (g : (κ → R) → ℂ)
    (r : (κ → AF F) → ℂ) : tens ev (c • g) r = c • tens ev g r := by
  funext x
  simp only [tens, Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem rho_sum {R : Type} [CommRing R] [Invertible (2 : R)] {W : Type} [AddCommGroup W] [Module R W]
    {B : W → W → R} {κ ι : Type} [Fintype κ] (d : Darboux B κ) (ψ : AddChar R ℂ) (γ : W) (s : Finset ι)
    (Φ : ι → (κ → R) → ℂ) : d.rho ψ γ (∑ q ∈ s, Φ q) = ∑ q ∈ s, d.rho ψ γ (Φ q) := by
  funext x
  simp only [Darboux.rho, schr, Finset.sum_apply, Finset.mul_sum]

theorem avg_eigen : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (w : Pl (F := F)) (Ψ : (Fin a' × Fin (a + a') → AF F) → ℂ), Ψ ∈ schA F (Fin a' × Fin (a + a')) →
    (∀ γ ∈ latAtV G.V' G.W w, ∀ c : ℂ, Acts (evFin F w) (G.M'.co.rho B.ψ γ) (G.M'.vac w) (c • G.M'.vac w) →
      G.M'.co.rho B.ψ γ Ψ = c • Ψ) →
    ∀ (m : ℕ) (f : Fin m → SInf F (Fin a' × Fin (a + a'))) (φ : Fin m → ∀ v : Pl (F := F), (Fin a' × Fin (a + a') → Fv F v) → ℂ),
    (∀ i v, φ i v ∈ SB (Fin a' × Fin (a + a') → Fv F v)) →
    (∀ i, ∀ᶠ v in Filter.cofinite, φ i v = Set.indicator {x | ∀ j, x j ∈ v.adicCompletionIntegers F} 1) →
    Ψ = ∑ i, pure (f i) (φ i) →
    ∃ g : Fin m → (Fin a' × Fin (a + a') → Fv F w) → ℂ, (∀ i, g i ∈ SB (Fin a' × Fin (a + a') → Fv F w)) ∧
      (∀ i, ∀ γ ∈ latAtV G.V' G.W w, ∀ c : ℂ, Acts (evFin F w) (G.M'.co.rho B.ψ γ) (G.M'.vac w) (c • G.M'.vac w) →
        Acts (evFin F w) (G.M'.co.rho B.ψ γ) (g i) (c • g i)) ∧
      Ψ = ∑ i, pure (f i) (Function.update (φ i) w (g i)) := by
  intro _ F E _ _ _ _ _ σ B a a' G X om om' hT w Ψ _ hyp m f φ hSB hstd hsum
  classical
  have hψc : Continuous (GlobalTheory.LatVac.psiAt B.ψ w) := GlobalTheory.SchrSB.continuous_psiAt B.ψ hT.base.std.1 w
  obtain ⟨hvSB, hv0, θ, -, hθ⟩ := hT.geo.hM'.vac w
  have hat : ∀ γ ∈ latAtV G.V' G.W w, At (evFin F w) γ := (GlobalTheory.LatVac.latAtV_at_stable G.V' G.W w).1
  set L := schrL (κ := Fin a' × Fin (a + a')) (GlobalTheory.LatVac.psiAt B.ψ w) with hL
  set vac := G.M'.vac w with hvac
  set Λ := (latAtV G.V' G.W w).map (GlobalTheory.LatVac.locCo G.M'.co w) with hΛ
  obtain ⟨-, hΛc⟩ := GlobalTheory.LatOpenCpt.main σ B G.V' G.W _ _ _ _ hT.geo.hV' hT.geo.hW G.M' hT.geo.hM'.rat w
  have hAct : ∀ γ ∈ latAtV G.V' G.W w, ∀ φ₀ : (Fin a' × Fin (a + a') → Fv F w) → ℂ,
      Acts (evFin F w) (G.M'.co.rho B.ψ γ) φ₀ (L (GlobalTheory.LatVac.locCo G.M'.co w γ) φ₀) :=
    fun γ hγ φ₀ => GlobalTheory.VacBridge.rho_acts_locCo G.M'.co B.ψ w γ (hat γ hγ) φ₀
  have huniq : ∀ γ ∈ latAtV G.V' G.W w, ∀ c₀ : ℂ, Acts (evFin F w) (G.M'.co.rho B.ψ γ) vac (c₀ • vac) →
      L (GlobalTheory.LatVac.locCo G.M'.co w γ) vac = c₀ • vac := fun γ hγ c₀ h =>
    GlobalTheory.TensUniq.eq_of_tens_eq w vac _ _ hvSB fun r hr => (hAct γ hγ vac r hr).symm.trans (h r hr)
  have hinj : ∀ e e' : ℂ, e • vac = e' • vac → e = e' := fun e e' h => smul_left_injective ℂ hv0 h
  have hex : ∀ z ∈ Λ, ∃ e : ℂ, L z vac = e • vac := by
    rintro _ ⟨γ, hγ, rfl⟩
    exact ⟨_, huniq γ hγ _ (hθ γ hγ)⟩
  let α : (Fin a' × Fin (a + a') → Fv F w) × (Fin a' × Fin (a + a') → Fv F w) → ℂ :=
    fun z => if h : ∃ e : ℂ, L z vac = e • vac then h.choose else 1
  have hαspec : ∀ z, (∃ e : ℂ, L z vac = e • vac) → L z vac = α z • vac := fun z h => by
    show _ = (if h : ∃ e : ℂ, L z vac = e • vac then h.choose else 1) • vac
    rw [dite_eq_left h]
    exact h.choose_spec
  let c : (Fin a' × Fin (a + a') → Fv F w) × (Fin a' × Fin (a + a') → Fv F w) →
      (Fin a' × Fin (a + a') → Fv F w) × (Fin a' × Fin (a + a') → Fv F w) → ℂ :=
    fun z z' => GlobalTheory.LatVac.psiAt B.ψ w (⅟(2 : Fv F w) * (z.1 ⬝ᵥ z'.2 - z'.1 ⬝ᵥ z.2))
  have hops : GlobalTheory.Published.SvN.Ops c L := ops_schrL _
  have hαne : ∀ z ∈ Λ, α z ≠ 0 := by
    intro z hz h0
    have h1 := hops.mul (-z) z vac
    rw [hαspec z (hex z hz), h0, zero_smul, map_zero, neg_add_cancel, hops.zero] at h1
    exact hv0 ((smul_eq_zero.1 h1.symm).resolve_left (addChar_ne_zero _ _))
  have hsplit : GlobalTheory.Published.SvN.Splits c Λ α := by
    refine ⟨hαne, fun x hx y hy => hinj _ _ ?_⟩
    have h1 := hops.mul x y vac
    rw [hαspec y (hex y hy), map_smul, hαspec x (hex x hx), hαspec (x + y) (hex _ (Λ.add_mem hx hy)), smul_smul,
      smul_smul] at h1
    rw [mul_comm (α x)]
    exact h1
  have hfix : ∀ᶠ z in 𝓝 (0 : (Fin a' × Fin (a + a') → Fv F w) × (Fin a' × Fin (a + a') → Fv F w)),
      L z vac = vac ∧ ∀ i, L z (φ i w) = φ i w :=
    (eventually_schr_fix w _ hψc hvSB).and (Filter.eventually_all.2 fun i => eventually_schr_fix w _ hψc (hSB i w))
  obtain ⟨U, hU⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ hfix
  have hUα : ∀ u ∈ U.toAddSubgroup, α u = 1 := fun u hu =>
    hinj _ _ (by rw [← hαspec u ⟨1, by rw [one_smul]; exact (hU hu).1⟩, one_smul]; exact (hU hu).1)
  have hfin : Finite (Λ ⧸ U.toAddSubgroup.addSubgroupOf Λ) :=
    GlobalTheory.Published.SvN.finite_quot Λ U.toAddSubgroup U.mem_nhds_zero hΛc subset_rfl
  letI := Fintype.ofFinite (Λ ⧸ U.toAddSubgroup.addSubgroupOf Λ)
  obtain ⟨avg, havg⟩ : ∃ avg : Fin m → (Fin a' × Fin (a + a') → Fv F w) → ℂ, ∀ i,
      avg i = ∑ q : Λ ⧸ U.toAddSubgroup.addSubgroupOf Λ, (α q.out.1)⁻¹ • L q.out.1 (φ i w) := ⟨_, fun _ => rfl⟩
  have heig : ∀ i, ∀ z ∈ Λ, L z (avg i) = α z • avg i := fun i z hz => by
    rw [havg i]
    exact GlobalTheory.Published.SvN.average hops hsplit U.toAddSubgroup hUα (φ i w) (fun u hu => (hU hu).2 i) z hz
  set N := Fintype.card (Λ ⧸ U.toAddSubgroup.addSubgroupOf Λ) with hN
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  choose γq hγq hγqe using fun q : Λ ⧸ U.toAddSubgroup.addSubgroupOf Λ => AddSubgroup.mem_map.1 q.out.2
  choose r hr1 hr2 using fun i => GlobalTheory.PureFactor.exists_rest_factor w (f i) (φ i) (hstd i)
  have hpure : ∀ i, pure (f i) (φ i) = tens (evFin F w) (φ i w) (r i) := fun i => by
    rw [hr2, Function.update_eq_self]
  have hRest : ∀ i, Rest (evFin F w) (φ i w) (r i) := fun i =>
    ⟨hr1 i, hpure i ▸ GlobalTheory.TensUniq.pure_mem_schA (f i) (φ i) (hSB i) (hstd i)⟩
  have hΨ' : Ψ = ∑ i, tens (evFin F w) (φ i w) (r i) := by
    rw [hsum]; exact Finset.sum_congr rfl fun i _ => hpure i
  have hqΨ : ∀ q : Λ ⧸ U.toAddSubgroup.addSubgroupOf Λ, G.M'.co.rho B.ψ (γq q) Ψ = α q.out.1 • Ψ := fun q =>
    hyp _ (hγq q) _ (by
      have := hAct _ (hγq q) vac
      rwa [hγqe q, hαspec _ (hex _ q.out.2)] at this)
  have hqΨ2 : ∀ q : Λ ⧸ U.toAddSubgroup.addSubgroupOf Λ,
      G.M'.co.rho B.ψ (γq q) Ψ = ∑ i, tens (evFin F w) (L q.out.1 (φ i w)) (r i) := fun q => by
    rw [hΨ', rho_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hAct _ (hγq q) (φ i w) (r i) (hRest i), hγqe q]
  have e1 : ∑ q : Λ ⧸ U.toAddSubgroup.addSubgroupOf Λ, (α q.out.1)⁻¹ • G.M'.co.rho B.ψ (γq q) Ψ = (N : ℂ) • Ψ := by
    calc ∑ q : Λ ⧸ U.toAddSubgroup.addSubgroupOf Λ, (α q.out.1)⁻¹ • G.M'.co.rho B.ψ (γq q) Ψ
          = ∑ q : Λ ⧸ U.toAddSubgroup.addSubgroupOf Λ, Ψ :=
          Finset.sum_congr rfl fun q _ => by rw [hqΨ q, smul_smul, inv_mul_cancel₀ (hαne _ q.out.2), one_smul]
      _ = (N : ℂ) • Ψ := by rw [Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
  have e2 : ∑ q : Λ ⧸ U.toAddSubgroup.addSubgroupOf Λ, (α q.out.1)⁻¹ • G.M'.co.rho B.ψ (γq q) Ψ =
      ∑ i, tens (evFin F w) (avg i) (r i) := by
    simp only [hqΨ2, Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [havg i, tens_sum]
  have hgSB : ∀ i, (N : ℂ)⁻¹ • avg i ∈ SB (Fin a' × Fin (a + a') → Fv F w) := fun i => by
    rw [havg i]
    exact (SB _).smul_mem _ (Submodule.sum_mem _ fun q _ => (SB _).smul_mem _
      (GlobalTheory.SchrSB.schr_mem_SB B.ψ hT.base.std.1 w _ _ (hSB i w)))
  refine ⟨fun i => (N : ℂ)⁻¹ • avg i, hgSB, fun i γ hγ c₀ hc => ?_, ?_⟩
  · have hz : GlobalTheory.LatVac.locCo G.M'.co w γ ∈ Λ := AddSubgroup.mem_map_of_mem _ hγ
    have e := huniq γ hγ c₀ hc
    rw [hαspec _ (hex _ hz)] at e
    have hc₀ := hinj _ _ e
    have := hAct γ hγ ((N : ℂ)⁻¹ • avg i)
    rwa [map_smul, heig i _ hz, hc₀, smul_comm] at this
  · calc Ψ = (N : ℂ)⁻¹ • ((N : ℂ) • Ψ) := by rw [smul_smul, inv_mul_cancel₀ hN0, one_smul]
      _ = _ := by
        rw [← e1, e2, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← tens_smul, hr2]

end GlobalTheory.VacAvg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleLatticeInvariantSchwartzGlobalStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.triple_lattice_invariant_schwartz_global : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (w : Pl (F := F)) (Ψ : (Fin a' × Fin (a + a') → AF F) → ℂ), Ψ ∈ schA F (Fin a' × Fin (a + a')) →
    (∀ γ ∈ latAtV G.V' G.W w, ∀ c : ℂ, Acts (evFin F w) (G.M'.co.rho B.ψ γ) (G.M'.vac w) (c • G.M'.vac w) →
      G.M'.co.rho B.ψ γ Ψ = c • Ψ) →
    ∀ (m : ℕ) (f : Fin m → SInf F (Fin a' × Fin (a + a'))) (φ : Fin m → ∀ v : Pl (F := F), (Fin a' × Fin (a + a') → Fv F v) → ℂ),
    (∀ i v, φ i v ∈ SB (Fin a' × Fin (a + a') → Fv F v)) →
    (∀ i, ∀ᶠ v in Filter.cofinite, φ i v = Set.indicator {x | ∀ j, x j ∈ v.adicCompletionIntegers F} 1) →
    Ψ = ∑ i, pure (f i) (φ i) →
    ∃ g : Fin m → (Fin a' × Fin (a + a') → Fv F w) → ℂ, (∀ i, g i ∈ SB (Fin a' × Fin (a + a') → Fv F w)) ∧
      (∀ i, ∀ γ ∈ latAtV G.V' G.W w, ∀ c : ℂ, Acts (evFin F w) (G.M'.co.rho B.ψ γ) (G.M'.vac w) (c • G.M'.vac w) →
        Acts (evFin F w) (G.M'.co.rho B.ψ γ) (g i) (c • g i)) ∧
      Ψ = ∑ i, pure (f i) (Function.update (φ i) w (g i)) := by
  first | exact @GlobalTheory.VacAvg.avg_eigen | exact GlobalTheory.VacAvg.avg_eigen | (intros; apply GlobalTheory.VacAvg.avg_eigen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulNonnegOfShortRule
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt GlobalTheory.PlaceInt.ShortTriv

namespace GlobalTheory.IntCuspLat

theorem nval_natCast_nonneg {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K']
    [Algebra V K'] [IsFractionRing V K'] (e m : ℕ) : 0 ≤ nval V e (m : K') :=
  GlobalTheory.ShortBound.nval_nonneg e (isIntegral_natCast _)

section Point
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem sum_bound_of_trivAt (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (hst : ∀ a : 𝓞 E, star a = H.bar a)
    (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y) (hC : Good3 C)
    (nab : NabV Xo c) (hnab : IsNab Xo c nab) (e : ℕ) (ρ : ℝ) (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (he : 0 < e)
    (hb : ChBound C e ρ w n) (ℓ : ℕ) (hℓ : ℓ.Prime) (hlu : ¬ IsUnit (ℓ : T.V)) (Λ : GenLat E n) (N M : ℕ)
    (hU : Λ.Unimod) (hL : Λ.LevOK N M) (P : MvPolynomial (LtN Dw n) c.F) (hP : P ∈ harmL c Λ w)
    (z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G))
    (tp : Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G))
    (F : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n →
      LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo (xOf y))))
    (hz : ∀ i, InZh Xo Λ N (z i)) (hg : GeoInj Xo (xOf y) z) (ht : ∀ b, tp b ^ (N ^ 2) = 1)
    (hF : ∀ i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N (sOf1 y) (z i b) (tp b) (F i b)) (htr : Λ.TrivAt ℓ)
    (n' A Bn j : ℕ) (α β₀ : 𝓞 E) (hn' : Nat.Coprime n' ℓ) (hfac : (N : 𝓞 E) = β₀ * α * n')
    (hA : α * H.bar α = (A : 𝓞 E)) (hB : β₀ * H.bar β₀ = (Bn : 𝓞 E)) (hAB : A * Bn = ℓ ^ j)
    (htp : ∀ b, (tp b ≫ Xo.univ.t.act.act β₀) ^ (n' ^ 2 * A) = 1) :
    letI := io.toAlgebra
    ((-ρ : ℝ) : EReal) ≤ nval T.V e (io (nrm Dw c w α * (((Λ.mIdx N (Dw.p + Dw.q) : c.F))⁻¹ *
      ((N : c.F) ^ P.totalDegree)⁻¹)) * ∑ i, hv Xo c nab y.1 (N ^ 2) (fun b => sqN Xo N (F i b)) P) := by
  letI := io.toAlgebra
  have hN : Odd N := hL.1
  obtain ⟨hfz, hm0, hT⟩ := GlobalTheory.TrivLattice.trivAt_units E H Dw l c n Λ N M ℓ hU hL hℓ htr
  obtain ⟨-, hFF⟩ := hT T io hlu
  obtain ⟨J, J', _, _, a, a', σ, -, haZ, ⟨m, hm, ha'⟩, hzs, hcard⟩ :=
    GlobalTheory.T.isotropic_group_primary_decomposition E H Dw l Xo T.Fr (xOf y) n Λ N M ℓ hU hL hℓ z hz hg
  have hlev : N ^ 2 = n' ^ 2 * ℓ ^ j := by
    have h2 : (N : 𝓞 E) = H.bar β₀ * H.bar α * n' := by
      have := congrArg H.bar hfac
      simpa only [map_mul, map_natCast] using this
    have h3 : ((N ^ 2 : ℕ) : 𝓞 E) = ((n' ^ 2 * (A * Bn) : ℕ) : 𝓞 E) := by
      push_cast
      rw [← hA, ← hB, sq]
      nth_rewrite 1 [hfac]
      rw [h2]; ring
    rw [← hAB]
    exact_mod_cast h3
  have hUU : ∀ i i' b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N (sOf1 y) (a' i' b) (tp b) (F (σ (i, i')) b) := by
    intro i i' b
    obtain ⟨hi, hi2⟩ := (haZ (a i)).1 ⟨i, rfl⟩
    obtain ⟨k, hk⟩ := hi2 b
    have h1 := hF (σ (i, i')) b
    rw [hzs] at h1
    exact isUUOver_of_mul Xo hN _ (a i b) (a' i' b) (tp b) (pow_eq_one_of_trivAt Xo htr hi b hk) (ha' i' b).2 (ht b)
      (hm.pow_right k) hk (ha' i' b).1 _ h1
  obtain ⟨i₀⟩ : Nonempty J := Fintype.card_pos_iff.1 (by rw [hcard]; exact pow_pos hℓ.pos _)
  have hsum : ∑ i, hv Xo c nab y.1 (N ^ 2) (fun b => sqN Xo N (F i b)) P =
      (Fintype.card J : T.Fr) * ∑ i', hv Xo c nab y.1 (N ^ 2) (fun b => sqN Xo N (F (σ (i₀, i')) b)) P := by
    rw [← σ.sum_comp, Fintype.sum_prod_type, ← nsmul_eq_mul, ← Finset.card_univ, ← Finset.sum_const]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
    congr 1
    funext b
    exact sqN_eq_of_isUUOver Xo hN _ _ _ (ha' i' b).2 (ht b) _ _ (hUU i i' b) (hUU i₀ i' b)
  have hterm : ∀ i', ((-ρ : ℝ) : EReal) ≤ nval T.V e (io (nrm Dw c w α * ((N : c.F) ^ P.totalDegree)⁻¹) *
      hv Xo c nab y.1 (N ^ 2) (fun b => sqN Xo N (F (σ (i₀, i')) b)) P) := fun i' => by
    refine GlobalTheory.T.harmonicValue_translated_product_valuation_bound E H Dw l Xo c hst T io y C hC nab hnab e ρ w n he hb N n' A Bn α β₀ hN hfac hA hB
      (isUnit_of_coprime T hn' hlu) (a' i') tp _ (fun b => ⟨(ha' i' b).2, ht b, ?_, htp b, hUU i₀ i' b⟩) P hP.1
      (hFF w P hP)
    have h1 : (a' i' b ^ (n' ^ 2)) ^ m = 1 := by rw [← pow_mul, _root_.mul_comm, pow_mul, (ha' i' b).1, one_pow]
    have h2 : (a' i' b ^ (n' ^ 2)) ^ (ℓ ^ j) = 1 := by rw [← pow_mul, ← hlev, (ha' i' b).2]
    have h3 := pow_gcd_eq_one.2 ⟨h1, h2⟩
    rw [(hm.pow_right j).gcd_eq_one, pow_one] at h3
    have := Xo.univ.t.act.hom (α * β₀)
    rw [← MonObj.pow_comp, h3, MonObj.one_comp]
  obtain ⟨m', hm'c, hm'⟩ : ∃ m' : ℕ, Nat.Coprime m' ℓ ∧ Λ.mIdx N (Dw.p + Dw.q) = Fintype.card J * m' :=
    ⟨_, (Nat.coprime_ordCompl hℓ hm0).symm, by rw [hcard, hfz, Nat.ordProj_mul_ordCompl_eq_self]⟩
  have hm'u := isUnit_of_coprime T hm'c hlu
  haveI : CharZero T.Fr := algebraRat.charZero _
  have hm'0 : (m' : T.Fr) ≠ 0 := by
    have : m' ≠ 0 := by rintro rfl; simp at hm'u
    exact_mod_cast this
  have hJ0 : (Fintype.card J : T.Fr) ≠ 0 := by
    have : Fintype.card J ≠ 0 := by rw [hcard]; exact (pow_pos hℓ.pos _).ne'
    exact_mod_cast this
  have hre : ∀ s : T.Fr, io (nrm Dw c w α * (((Λ.mIdx N (Dw.p + Dw.q) : c.F))⁻¹ * ((N : c.F) ^ P.totalDegree)⁻¹)) *
      ((Fintype.card J : T.Fr) * s) =
      (m' : T.Fr)⁻¹ * (io (nrm Dw c w α * ((N : c.F) ^ P.totalDegree)⁻¹) * s) := fun s => by
    rw [hm']
    simp only [map_mul, map_inv₀, map_natCast, Nat.cast_mul]
    generalize (io ((N : c.F) ^ P.totalDegree))⁻¹ = q
    field_simp
  rw [hsum, hre, nval_mul_unit e (inv_ne_zero hm'0) (vV_inv_eq_zero T (vV_natCast T hm'u)), Finset.mul_sum]
  exact le_nval_sum T _ e _ _ fun i' _ => hterm i'

theorem class_bound_of_trivAt (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (hst : ∀ a : 𝓞 E, star a = H.bar a)
    (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y) (hC : Good3 C)
    (nab : NabV Xo c) (hnab : IsNab Xo c nab) (e : ℕ) (ρ : ℝ) (w : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (he : 0 < e)
    (hb : ChBound C e ρ w n) (ℓ : ℕ) (hℓ : ℓ.Prime) (hlu : ¬ IsUnit (ℓ : T.V)) (Λ : GenLat E n) (N : ℕ)
    (hU : Λ.Unimod) (hL : Λ.LevOK N l.M) (P : MvPolynomial (LtN Dw n) c.F) (hP : P ∈ harmL c Λ w)
    (z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G))
    (tp : Fin n → (ptO Xo (xOf y) ⟶ Xo.univ.t.G))
    (F : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n →
      LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo (xOf y))))
    (hz : ∀ i, InZh Xo Λ N (z i)) (hg : GeoInj Xo (xOf y) z) (a : Fin n → Dw.La)
    (htp : ∀ b, tp b ^ N = levPt Xo (xOf y) (a b) ∧ ∃ j : ℕ, KilledBy Xo (l.Mb ^ j) (tp b))
    (hF : ∀ i b, IsUUOver Xo.univ.t.G Xo.univ.t.PP N (sOf1 y) (z i b) (tp b) (F i b)) (htr : Λ.TrivAt ℓ)
    (hsq : ¬ ℓ ^ 2 ∣ l.M) :
    letI := io.toAlgebra
    ((-ρ : ℝ) : EReal) ≤ nval T.V e (((l.M ^ Formalism.L2.Pj.DF Dw w : ℕ) : T.Fr) *
      (io (((Λ.mIdx N (Dw.p + Dw.q) : c.F))⁻¹ * ((N : c.F) ^ P.totalDegree)⁻¹) *
        ∑ i, hv Xo c nab y.1 (N ^ 2) (fun b => sqN Xo N (F i b)) P)) := by
  letI := io.toAlgebra
  have hk : ∀ b, KilledBy Xo l.Mb (tp b ^ N) := fun b => by rw [(htp b).1]; exact GlobalTheory.ShortBound.levPt_killed Xo _ _
  obtain ⟨t1, t2⟩ := GlobalTheory.TorsFac.factorisation E H Dw l Xo N ℓ hL.1 hL.2.1 hℓ
  have key : ∃ u : ℕ, u ∣ l.M ∧ ((-ρ : ℝ) : EReal) ≤ nval T.V e (io (nrm Dw c w (u : 𝓞 E) *
      (((Λ.mIdx N (Dw.p + Dw.q) : c.F))⁻¹ * ((N : c.F) ^ P.totalDegree)⁻¹)) *
        ∑ i, hv Xo c nab y.1 (N ^ 2) (fun b => sqN Xo N (F i b)) P) := by
    by_cases hd : ℓ ∣ l.M
    · have hA : (ℓ : 𝓞 E) * H.bar (ℓ : 𝓞 E) = ((ℓ ^ 2 : ℕ) : 𝓞 E) := by rw [map_natCast]; push_cast; ring
      obtain ⟨n', Bn, j, β₀, h1, h2, h3, h4, h5⟩ := t2 (ℓ : 𝓞 E) (ℓ ^ 2) hA hsq (Or.inr ⟨rfl, hd⟩)
      exact ⟨ℓ, hd, sum_bound_of_trivAt Xo c hst T io y C hC nab hnab e ρ w n he hb ℓ hℓ hlu Λ N l.M hU hL P hP z tp F
        hz hg (fun b => (h5 _ _ (hk b) (htp b).2).1) hF htr n' (ℓ ^ 2) Bn j _ β₀ h1 h2 hA h3 h4
        (fun b => (h5 _ _ (hk b) (htp b).2).2)⟩
    · obtain ⟨n', j, h1, h2, h5⟩ := t1 hd
      refine ⟨1, one_dvd _, sum_bound_of_trivAt Xo c hst T io y C hC nab hnab e ρ w n he hb ℓ hℓ hlu Λ N l.M hU hL P hP
        z tp F hz hg (fun b => (h5 _ _ (hk b) (htp b).2).1) hF htr n' 1 (ℓ ^ (2 * j)) (2 * j) _ ((ℓ : 𝓞 E) ^ j) h1
        ?_ (by simp) ?_ (_root_.one_mul _) (fun b => (h5 _ _ (hk b) (htp b).2).2.1)⟩
      · rw [h2]; push_cast; ring
      · rw [map_pow, map_natCast]; push_cast; ring
  obtain ⟨u, ⟨m, hm⟩, h⟩ := key
  rw [GlobalTheory.ShortBound.nrm_nat, map_mul, map_pow, map_natCast, _root_.mul_assoc] at h
  rw [hm, mul_pow, Nat.cast_mul, _root_.mul_comm ((u ^ _ : ℕ) : T.Fr), _root_.mul_assoc, nval_mul, Nat.cast_pow u]
  calc ((-ρ : ℝ) : EReal) = 0 + ((-ρ : ℝ) : EReal) := (zero_add _).symm
    _ ≤ _ := add_le_add (nval_natCast_nonneg e _) h

end Point

theorem vV_prod_pow (T : CDVR) (X : ℕ) (S : Finset ℕ) (hS : ∀ p ∈ S, p ≠ 0) :
    vV T.V ((∏ p ∈ S, p ^ X : ℕ) : T.Fr) = ∑ p ∈ S, (X : ℤ) * vV T.V (p : T.Fr) := by
  classical
  haveI : CharZero T.Fr := algebraRat.charZero _
  induction S using Finset.induction_on with
  | empty => simp [GlobalTheory.ShortBound.vV_one]
  | insert p S hp ih =>
    have h1 : (p : T.Fr) ≠ 0 := by exact_mod_cast hS p (Finset.mem_insert_self _ _)
    have h2 : ((∏ p ∈ S, p ^ X : ℕ) : T.Fr) ≠ 0 := by
      exact_mod_cast Finset.prod_ne_zero_iff.2 fun q hq => pow_ne_zero _ (hS q (Finset.mem_insert_of_mem hq))
    rw [Finset.prod_insert hp, Finset.sum_insert hp, Nat.cast_mul, Nat.cast_pow, vV_mul (pow_ne_zero _ h1) h2,
      GlobalTheory.ShortBound.vV_pow h1, ih fun q hq => hS q (Finset.mem_insert_of_mem hq)]

theorem vLa_pos_of_mem {K : Type} [Field K] [NumberField K] (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) {ℓ : ℕ}
    (h0 : ℓ ≠ 0) (h : (ℓ : 𝓞 K) ∈ la.asIdeal) : 0 < vLa la (ℓ : K) := by
  have h1 : la.valuation K (algebraMap (𝓞 K) K (ℓ : 𝓞 K)) < 1 := (la.valuation_lt_one_iff_mem _).2 h
  rw [map_natCast] at h1
  have h2 : la.valuation K (ℓ : K) ≠ 0 := (Valuation.ne_zero_iff _).2 (by exact_mod_cast h0)
  have := (WithZero.log_lt_log h2 one_ne_zero).2 h1
  rw [WithZero.log_one] at this
  unfold vLa
  omega


open IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions in
theorem exists_smul_nonneg_of_shortRule (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n) [StarRing (𝓞 D.host.E)] (hlev : d.IsLev)
    (hnab : IsNab d.Xo₂ d.c₂ d.nab₂)
    (hroot : ∀ (k : Type) [Field k] [Algebra d.c₂.F k] (y₂ : FrPt d.Xo₂ d.c₂ k), evR d.Xo₂ d.c₂ d.cδ y₂ ^ 1 = 1)
    (hwi : ∀ (x0 : Fin n → Dw.La) (q : Fin n → LevQ Dw d.l₂), IsIntegral ℤ (d.w x0 q)) (hsf : Squarefree d.l₂.M)
    (Λ : GenLat D.host.E n) (N : ℕ) (hU : Λ.Unimod) (hTM : Λ.TrivAt d.l₂.M) (hN : Λ.LevOK N d.l₂.M)
    (w : (D.host.E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F) (hP : P ∈ harmL c Λ w) (x0 : Fin n → Dw.La)
    (g : Rul Xo c) (hsec : g ∈ sec Xo c w n) (hR : IsShortRule Xo c d Λ N x0 P g) :
    ∃ t : c.F, t ≠ 0 ∧ ∀ (la : HeightOneSpectrum (𝓞 c.F)) (ℓ : ℕ), ℓ.Prime → (ℓ : 𝓞 c.F) ∈ la.asIdeal → Λ.TrivAt ℓ →
      ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v (t • g) := by
  have hβ : betaH (Dw := Dw) c Λ ≠ 0 := by
    unfold betaH
    split_ifs with h
    · exact h.choose_spec.1
    · exact one_ne_zero
  have hM0 : d.l₂.M ≠ 0 := hsf.ne_zero
  have hc0 : Nat.card (Fin n → LevQ Dw d.l₂) ≠ 0 := by
    rw [GlobalTheory.PlaceInt.card_fun_levQ]; exact pow_ne_zero _ hM0
  haveI := Nat.finite_of_card_ne_zero hc0
  have hS : ∀ p ∈ D.host.condN.primeFactors, p ≠ 0 := fun p hp =>
    (Nat.prime_of_mem_primeFactors hp).ne_zero
  obtain ⟨X, hX⟩ : ∃ X : ℕ, X = (NumberField.discr D.host.E).natAbs * Formalism.L2.Pj.DF Dw w := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : ℕ, Q = ∏ p ∈ D.host.condN.primeFactors, p ^ X := ⟨_, rfl⟩
  have hQ0 : Q ≠ 0 := hQ ▸ Finset.prod_ne_zero_iff.2 fun q hq => pow_ne_zero _ (hS q hq)
  refine ⟨betaH (Dw := Dw) c Λ * ((Nat.card (Fin n → LevQ Dw d.l₂) * (Q * d.l₂.M ^ Formalism.L2.Pj.DF Dw w) : ℕ) : c.F),
    mul_ne_zero hβ (by exact_mod_cast mul_ne_zero hc0 (mul_ne_zero hQ0 (pow_ne_zero _ hM0))), ?_⟩
  rintro la ℓ hℓ hmem htr _ ⟨⟨_, Tc, io, e, ho, yI, hy, eta, heta, rfl⟩, rfl⟩
  show 0 ≤ nval Tc.V e (evI yI _)
  obtain ⟨-, ef2, -⟩ := GlobalTheory.PlaceInt.eF_transfer _ _ _ _ Xo c n d Λ
  obtain ⟨T', iT, r, io₂, y₂, C, ζ, z, tp, F, hr, hiT, hfr, hio, hC, hrat, hζ, hz, hgi, htp, hF, hval⟩ :=
    GlobalTheory.PlaceInt.short_value_on_cover _ _ _ _ Xo c n d hlev hnab 1 hroot Λ N hU hTM hN w P hP x0 g hsec hR Tc io yI hy
  haveI : CharZero T'.Fr := algebraRat.charZero _
  have ho' := ho.bc iT hr hiT
  have he' : 0 < r * e := ho'.1
  have hu : ¬ IsUnit (ℓ : T'.V) := fun hu => by
    have h1 := vV_natCast T' hu
    have h2 := ho'.2 (ℓ : c.F)
    rw [map_natCast, h1] at h2
    have h3 := vLa_pos_of_mem la hℓ.ne_zero hmem
    have h4 : (0 : ℤ) < ((r * e : ℕ) : ℤ) := by exact_mod_cast he'
    exact (mul_pos h4 h3).ne h2
  have hch := GlobalTheory.PlaceInt.HostChart.chBound_host D _ Dw _ d.Xo₂ d.c₂ hnab.1 T' io₂ y₂ C (r * e) he' w n _ le_rfl
  have hsq : ¬ ℓ ^ 2 ∣ d.l₂.M := fun hd => hℓ.prime.not_unit (hsf ℓ (by rwa [← pow_two]))
  have key := fun q => class_bound_of_trivAt d.Xo₂ d.c₂ hnab.1 T' io₂ y₂ C hC _ hnab (r * e) _ w n he' hch ℓ hℓ
      hu Λ N hU hN _ (ef2 _ P hP).1 z (tp q) (F q) hz hgi (fun b => levRep (q b)) (htp q) (hF q) htr hsq
  rw [pow_one] at hζ
  rw [← nval_bc iT hr hiT e, evI_smul, map_mul, hval, ← hio, hζ, _root_.one_mul]
  have := Fintype.ofFinite (Fin n → LevQ Dw d.l₂)
  rw [finsum_eq_sum_of_fintype, Finset.mul_sum, Finset.mul_sum]
  refine le_nval_sum T' _ _ _ _ fun q _ => ?_
  have hq := key q
  letI := io₂.toAlgebra
  generalize (∑ i, hv d.Xo₂ d.c₂ d.nab₂ y₂.1 (N ^ 2) (fun b => sqN d.Xo₂ N (F q i b))
    (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P)) = Sm at hq ⊢
  have hb0 : io₂ (d.eF (betaH (Dw := Dw) c Λ)) ≠ 0 := (map_ne_zero io₂).2 ((map_ne_zero d.eF).2 hβ)
  have hc1 : ((Nat.card (Fin n → LevQ Dw d.l₂) : ℕ) : T'.Fr) ≠ 0 := by exact_mod_cast hc0
  have hQ1 : (Q : T'.Fr) ≠ 0 := by exact_mod_cast hQ0
  have hQv : 0 ≤ nval T'.V (r * e) ((Q : T'.Fr) * (((d.l₂.M ^ Formalism.L2.Pj.DF Dw w : ℕ) : T'.Fr) *
      (io₂ (((Λ.mIdx N (Dw.p + Dw.q) : d.c₂.F))⁻¹ *
        ((N : d.c₂.F) ^ (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P).totalDegree)⁻¹) * Sm))) := by
    rw [nval_mul, nval_of_ne hQ1]
    refine le_trans ?_ (add_le_add le_rfl hq)
    rw [← EReal.coe_add, EReal.coe_nonneg, ← sub_eq_add_neg, sub_nonneg, hQ, vV_prod_pow T' X _ hS, Int.cast_sum,
      Finset.sum_div]
    refine Finset.sum_le_sum fun p _ => ?_
    have h1 : (0 : ℝ) ≤ (vV T'.V (p : T'.Fr) : ℝ) / ((r * e : ℕ) : ℝ) :=
      div_nonneg (by exact_mod_cast GlobalTheory.PlaceInt.HostChart.vV_nat_nonneg T' p) (Nat.cast_nonneg _)
    have h2 := D.host.vdH_le_natAbs p
    have h3 := D.host.vdH_nonneg p
    have h4 : (0 : ℝ) ≤ (Formalism.L2.Pj.DF Dw w : ℝ) := Nat.cast_nonneg _
    rw [Int.cast_mul, Int.cast_natCast, mul_div_assoc (X : ℝ), hX, Nat.cast_mul (NumberField.discr D.host.E).natAbs]
    have h5 := mul_nonneg (mul_nonneg h1 h3) h4
    have h6 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 h1) h4
    linarith
  refine le_trans (add_nonneg (GlobalTheory.ShortBound.nval_nonneg (V := T'.V) (r * e) (map_isIntegral_int io₂ (hwi x0 q))) hQv)
    (le_of_eq ?_)
  rw [← nval_mul]
  congr 1
  simp only [map_mul, map_inv₀, map_natCast, Nat.cast_mul]
  generalize (io₂ ((N : d.c₂.F) ^ (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P).totalDegree))⁻¹ = a1
  generalize ((Λ.mIdx N (Dw.p + Dw.q) : ℕ) : T'.Fr)⁻¹ = a2
  field_simp

end GlobalTheory.IntCuspLat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StdCharFiniteAdeleRationalEqExpTrace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StdCharFiniteAdeleRationalEqExpTrace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.PsiFinRat

theorem psi_pairA_zero_algebraMap {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1))
    (q : D.host.F) :
    ψ (pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) q)) =
      Complex.exp (2 * Real.pi * Complex.I * ∑ τ, tauE D τ (q : D.host.E)) := by
  obtain ⟨hchar, ⟨θ, hθ⟩, hall⟩ := hψ
  have hinf := hall θ hθ
  have hsplit : pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) q) =
      algebraMap D.host.F (AF D.host.F) q +
        pairA D.host.F (-(algebraMap D.host.F (Ainf D.host.F) q)) 0 := by
    refine Prod.ext ?_ ?_
    · show (0 : Ainf D.host.F) = algebraMap D.host.F (Ainf D.host.F) q + -(algebraMap D.host.F (Ainf D.host.F) q)
      rw [add_neg_cancel]
    · show algebraMap D.host.F (Af D.host.F) q = algebraMap D.host.F (Af D.host.F) q + 0
      rw [add_zero]
  rw [hsplit, AddChar.map_add_eq_mul, hchar.2.2.1, one_mul]
  have h1 := hinf (-(algebraMap D.host.F (Ainf D.host.F) q))
  simp only [psiInf] at h1
  rw [h1]
  have htm : ∀ τ, θ τ ((-(algebraMap D.host.F (Ainf D.host.F) q)) ⊗ₜ[D.host.F] (1 : D.host.E)) =
      -tauE D τ (q : D.host.E) := by
    intro τ
    have e : (-(algebraMap D.host.F (Ainf D.host.F) q)) ⊗ₜ[D.host.F] (1 : D.host.E) =
        -((1 : Ainf D.host.F) ⊗ₜ[D.host.F] (algebraMap D.host.F D.host.E q)) := by
      have e0 : (algebraMap D.host.F (Ainf D.host.F) q) ⊗ₜ[D.host.F] (1 : D.host.E) =
          (1 : Ainf D.host.F) ⊗ₜ[D.host.F] (algebraMap D.host.F D.host.E q) :=
        (Algebra.TensorProduct.includeLeft (R := D.host.F) (S := D.host.F) (A := Ainf D.host.F)
          (B := D.host.E)).commutes q |>.trans
          ((Algebra.TensorProduct.includeRight (R := D.host.F) (A := Ainf D.host.F)
            (B := D.host.E)).commutes q).symm
      rw [TensorProduct.neg_tmul, e0]
    rw [e, map_neg, (hθ τ).1]
    rfl
  simp only [htm, Finset.sum_neg_distrib]
  congr 1
  push_cast
  ring

end GlobalTheory.PsiFinRat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StdCharFiniteAdeleRationalEqExpTraceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stdChar_finiteAdele_rational_eq_exp_trace : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ q : D.host.F, ψ (pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) q)) = Complex.exp (2 * Real.pi * Complex.I * ∑ τ, tauE D τ (q : D.host.E)) := by
  first | exact @GlobalTheory.PsiFinRat.psi_pairA_zero_algebraMap | exact GlobalTheory.PsiFinRat.psi_pairA_zero_algebraMap | (intros; apply GlobalTheory.PsiFinRat.psi_pairA_zero_algebraMap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacOfMemSchwartzA
open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ResAniso.VacSchwartz


open Classical in
theorem realPar_ne_zero (D : D7) (θ : InfFam D) (hθ : IsInfFam θ) (ψ : AddChar (AF D.host.F) ℂ)
    (hψ : IsCharAF D.host.F ψ) (l : D.what₂.Tau → ℝ) (hl : StdUnn.HasRealPar ψ θ l) (τ₀ : D.what₂.Tau) : l τ₀ ≠ 0 := by
  intro h0
  obtain ⟨a, ha, hinf⟩ := GlobalTheory.AdeleCharConductor.exists_scaling hψ
  have hbij := GlobalTheory.CMTypePlaces.places_bijective D
  let w : D.what₂.Tau → InfinitePlace D.host.F := fun τ =>
    InfinitePlace.mk ((tauE D τ).comp (algebraMap D.host.F D.host.E))
  have hemb : ∀ τ, (w τ).embedding = (tauE D τ).comp (algebraMap D.host.F D.host.E) := fun τ =>
    InfinitePlace.embedding_mk_eq_of_isReal (InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal _))
  have hθ' : ∀ τ (x : Ainf D.host.F), θ τ (x ⊗ₜ[D.host.F] (1 : D.host.E)) =
      InfinitePlace.Completion.extensionEmbedding (w τ) (x (w τ)) := fun τ =>
    congrFun ((InfiniteAdeleRing.denseRange_algebraMap D.host.F).equalizer (hθ τ).2
      ((InfinitePlace.Completion.isometry_extensionEmbedding (w τ)).continuous.comp (continuous_apply (w τ)))
      (funext fun b => by
        show θ τ (algebraMap D.host.F (Ainf D.host.F) b ⊗ₜ[D.host.F] (1 : D.host.E)) = _
        rw [GlobalTheory.StdRat.tmul_one_eq, (hθ τ).1, Function.comp_apply]
        erw [GlobalTheory.AdeleCharConductor.extensionEmbedding_algebraMap (w τ) b, hemb]
        rfl))
  set e : ℝ := ((w τ₀).embedding a).re with he
  have hre : ((w τ₀).embedding a).im = 0 := by
    have hr : NumberField.ComplexEmbedding.IsReal (w τ₀).embedding :=
      InfinitePlace.isReal_iff.1 (IsTotallyReal.isReal _)
    have := congrArg (fun φ : D.host.F →+* ℂ => φ a) hr
    exact Complex.conj_eq_iff_im.1 this
  have he0 : e ≠ 0 := by
    intro h
    apply ha
    have : (w τ₀).embedding a = 0 := Complex.ext (by simpa [he] using h) (by simpa using hre)
    exact (map_eq_zero_iff _ (w τ₀).embedding.injective).1 this
  obtain ⟨x, hx⟩ := GlobalTheory.StdUnn.RealPar.exists_real_point hθ τ₀ (1 / (2 * e))
  have e1 := hl x
  simp only [hx, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, h0, Complex.ofReal_zero,
    zero_mul, Complex.exp_zero] at e1
  have e2 := hinf x
  have hsum : ∑ u : InfinitePlace D.host.F, (u.embedding a).re *
      (InfinitePlace.Completion.extensionEmbedding u (x u)).re = e * (1 / (2 * e)) := by
    rw [← hbij.sum_comp (fun u : InfinitePlace D.host.F => (u.embedding a).re *
      (InfinitePlace.Completion.extensionEmbedding u (x u)).re)]
    have hterm : ∀ τ, ((w τ).embedding a).re * (InfinitePlace.Completion.extensionEmbedding (w τ) (x (w τ))).re =
        if τ = τ₀ then e * (1 / (2 * e)) else 0 := fun τ => by
      rw [← hθ' τ x, hx τ]
      split_ifs with h
      · subst h; simp [he]
      · simp
    refine (Finset.sum_congr rfl fun τ _ => hterm τ).trans ?_
    simp
  rw [hsum, e1] at e2
  have h2 : e * (1 / (2 * e)) = 1 / 2 := by field_simp
  rw [h2] at e2
  have h3 : (2 * Real.pi * Complex.I * (((1 / 2 : ℝ)) : ℂ)) = Real.pi * Complex.I := by push_cast; ring
  rw [h3, Complex.exp_pi_mul_I] at e2
  norm_num at e2

end GlobalTheory.ResAniso.VacSchwartz
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIntertwinerRepContinuousGroup
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIntertwinerRepContinuousGroup
open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil

namespace GlobalTheory.FinLatF

theorem latRepF_cont : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (hc : GlobalTheory.FinLatF.HeisClosedF σ JS JT ξ₀ B.ψ) (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) (w : 𝓞 E)
        (lam : ℕ →* ℂ) (Om : GAF σ JS × GAF σ JT →* Module.End ℂ (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ)),
        GlobalTheory.FinLatF.IsLatRepF σ JS JT ξ₀ B.ψ hc Λ w lam Om →
        ∀ f (w : WOF F E nS nT), Continuous fun p : GAF σ JS × GAF σ JT => (Om p f : WOF F E nS nT → ℂ) w := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ _ hξ hc Λ w lam Om h f u
  have hσ : ∀ x, σ (σ x) = x := fun x => GlobalTheory.AdelicU.cm_conj_conj hB.cm x
  have H := isHeis_opFF hσ hS hT hξ hc h.hw
  have hfix : ∀ p : GAF σ JS × GAF σ JT, (∀ a ∈ latF F E nS nT Λ, rhoFF σ JS JT p a ∈ latF F E nS nT Λ) →
      ∀ e, Fixes (opFF hc w) (latF F E nS nT Λ) e → Om p e = e := by
    intro p hp e he
    rw [h.vac p e he]
    exact GlobalTheory.FinWeilO.normOp_of_le H lam (h.sd' p) (by rintro _ ⟨a, ha, rfl⟩; exact hp a ha) he
  have hev : ∀ f : GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ, ∀ᶠ p in 𝓝 (1 : GAF σ JS × GAF σ JT), Om p f = f := by
    intro f
    have hf : f ∈ Submodule.span ℂ {m | ∃ x e, Fixes (opFF hc w) (latF F E nS nT Λ) e ∧ m = opFF hc w x e} := by
      rw [h.span]; trivial
    induction hf using Submodule.span_induction with
    | mem _ hm =>
      obtain ⟨x, e, he, rfl⟩ := hm
      obtain ⟨N, hN, hNl⟩ := h.lev (w • x)
      filter_upwards [h.near, h.near' x N hN] with p hp hp'
      obtain ⟨l, hl, hl'⟩ := hp'
      have e2 : gamFF σ JS JT ξ₀ B.ψ (w • x) (N • l) = 1 := by
        rw [gamFF, ← symplOHF_add_self, AddChar.map_add_eq_mul, XFF.coe_nsmul, hNl l hl, one_mul]
      have e4 := H.comp x (N • l) e
      rw [he _ (nsmul_mem hl N), e2, one_smul] at e4
      rw [h.op, hfix p hp e he, hl', ← e4]
    | zero => exact Filter.Eventually.of_forall fun p => map_zero _
    | add u v _ _ hu hv => filter_upwards [hu, hv] with p h3 h4 using by rw [map_add (f := _), h3, h4]
    | smul c u _ hu => filter_upwards [hu] with p h3 using by rw [map_smul, h3]
  haveI : IsTopologicalGroup (GAF σ JS) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : IsTopologicalGroup (GAF σ JT) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  refine continuous_iff_continuousAt.2 fun q => ?_
  have h1 : Filter.Tendsto (fun p => q⁻¹ * p) (𝓝 q) (𝓝 1) :=
    (continuous_const.mul continuous_id).tendsto' q 1 (inv_mul_cancel q)
  refine continuousAt_const.congr (f := fun _ => (Om q f : WOF F E nS nT → ℂ) u) ?_
  filter_upwards [h1.eventually (hev f)] with p hp
  conv_rhs => rw [← mul_inv_cancel_left q p, map_mul, Module.End.mul_apply, hp]

end GlobalTheory.FinLatF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIntertwinerRepContinuousGroupStatement
open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeIntertwinerRep_continuous_group : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (hc : GlobalTheory.FinLatF.HeisClosedF σ JS JT ξ₀ B.ψ) (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) (w : 𝓞 E)
        (lam : ℕ →* ℂ) (Om : GAF σ JS × GAF σ JT →* Module.End ℂ (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ)),
        GlobalTheory.FinLatF.IsLatRepF σ JS JT ξ₀ B.ψ hc Λ w lam Om →
        ∀ f (w : WOF F E nS nT), Continuous fun p : GAF σ JS × GAF σ JT => (Om p f : WOF F E nS nT → ℂ) w := by
  first | exact @GlobalTheory.FinLatF.latRepF_cont | exact GlobalTheory.FinLatF.latRepF_cont | (intros; apply GlobalTheory.FinLatF.latRepF_cont <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMapPartRightEquivariant
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DoublingEv

noncomputable section

namespace GlobalTheory.DoublingEvLaw

theorem elim_dot {R : Type} [CommRing R] {κ κ' : Type} [Fintype κ] [Fintype κ'] (u v : κ → R) (x y : κ' → R) :
    Sum.elim u x ⬝ᵥ Sum.elim v y = u ⬝ᵥ v + x ⬝ᵥ y := by
  simp [dotProduct, Fintype.sum_sum_type]

theorem star_schr' {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) (hψ : ∀ x, ‖ψ x‖ = 1)
    {κ : Type} [Fintype κ] (w : (κ → R) × (κ → R)) (φ : (κ → R) → ℂ) :
    star (schr ψ (w.1, -w.2) φ) = schr ψ w (star φ) := by
  funext x
  simp only [schr, Pi.star_apply, star_mul', dotProduct_neg, mul_neg, ← neg_add, AddChar.map_neg_eq_inv]
  rw [Complex.inv_eq_conj (hψ _), Complex.star_def, Complex.conj_conj]

variable {F : Type} [Field F] [NumberField F]

theorem sliceL {κ κ' : Type} [Fintype κ] [Fintype κ'] {Φ : (κ ⊕ κ' → AF F) → ℂ} (hΦ : Φ ∈ schA F (κ ⊕ κ'))
    (b : κ' → AF F) : (fun x => Φ (Sum.elim x b)) ∈ schA F κ := by
  have e1 : (fun x => Φ (Sum.elim x b)) = fun x => Φ (GlobalTheory.ThK.Adapt.glue (Equiv.sumComm κ κ') b x) :=
    funext fun x => congrArg Φ (funext fun k => by cases k <;> rfl)
  rw [e1]
  exact GlobalTheory.ThK.Adapt.slice_mem_schA (Equiv.sumComm κ κ') b hΦ

theorem sliceR {κ κ' : Type} [Fintype κ] [Fintype κ'] {Φ : (κ ⊕ κ' → AF F) → ℂ} (hΦ : Φ ∈ schA F (κ ⊕ κ'))
    (a : κ → AF F) : (fun x => Φ (Sum.elim a x)) ∈ schA F κ' :=
  GlobalTheory.ThK.Adapt.slice_mem_schA (Equiv.refl (κ ⊕ κ')) a hΦ

theorem main : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), (∀ x, ‖ψ x‖ = 1) →
    ∀ (κ κ₁ : Type) [Fintype κ] [Fintype κ₁] (T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ₁ → AF F) → ℂ))
      (A₁ B₁ A₂ B₂ : κ → AF F) (a b : κ₁ → AF F),
      (∀ Φ ∈ schA F κ, T (schr ψ (A₁, B₁) Φ) = schr ψ (a, b) (T Φ)) →
      (∀ Φ ∈ schA F κ, T (schr ψ (A₂, B₂) Φ) = schr ψ (a, b) (T Φ)) →
      (∀ φ ∈ schA F (κ ⊕ κ), partR (conjMap T) φ ∈ schA F (κ ⊕ κ₁)) →
      ∀ φ ∈ schA F (κ ⊕ κ), evDbl T (schr ψ (Sum.elim A₁ A₂, Sum.elim B₁ (-B₂)) φ) =
        schr ψ (Sum.elim a a, Sum.elim b (-b)) (evDbl T φ) := by
  intro F _ _ ψ hψ κ κ₁ _ _ T A₁ B₁ A₂ B₂ a b h1 h2 h3 φ hφ
  have hconj : ∀ g ∈ schA F κ, conjMap T (schr ψ (A₂, -B₂) g) = schr ψ (a, -b) (conjMap T g) := by
    intro g hg
    have hs : star g ∈ schA F κ := GlobalTheory.SchAConj.star_mem_schA F κ g hg
    rw [conjMap_apply, conjMap_apply, star_schr' ψ hψ (A₂, B₂) g, h2 _ hs]
    have := star_schr' ψ hψ (a, -b) (T (star g))
    simpa only [neg_neg] using this
  funext s
  have hΨ := h3 φ hφ
  have hslice := sliceL hΨ (s ∘ Sum.inr + a)
  have hinner : (fun x₁ => conjMap T (fun x₂ => schr ψ (Sum.elim A₁ A₂, Sum.elim B₁ (-B₂)) φ (Sum.elim x₁ x₂))
      (s ∘ Sum.inr)) = ψ (-((s ∘ Sum.inr) ⬝ᵥ b) - ⅟(2 : AF F) * (a ⬝ᵥ b)) •
        schr ψ (A₁, B₁) (fun x₁ => partR (conjMap T) φ (Sum.elim x₁ (s ∘ Sum.inr + a))) := by
    funext x₁
    have e1 : (fun x₂ => schr ψ (Sum.elim A₁ A₂, Sum.elim B₁ (-B₂)) φ (Sum.elim x₁ x₂)) =
        ψ (x₁ ⬝ᵥ B₁ + ⅟(2 : AF F) * (A₁ ⬝ᵥ B₁)) • schr ψ (A₂, -B₂) (fun x₂ => φ (Sum.elim (x₁ + A₁) x₂)) := by
      funext x₂
      simp only [schr, Pi.smul_apply, smul_eq_mul, elim_dot, Sum.elim_add_add]
      rw [← mul_assoc, ← AddChar.map_add_eq_mul]
      congr 2
      ring
    rw [e1, map_smul, hconj _ (sliceR hφ _)]
    simp only [Pi.smul_apply, smul_eq_mul, schr, partR_apply, Sum.elim_comp_inl, Sum.elim_comp_inr]
    rw [dotProduct_neg, dotProduct_neg]
    rw [show ∀ p q r : ℂ, p * (q * r) = q * (p * r) from fun p q r => by ring]
    congr 2
    ring_nf
  rw [evDbl_apply, hinner, map_smul, h1 _ hslice]
  simp only [schr, Pi.smul_apply, smul_eq_mul, evDbl_apply, elim_dot, partR_apply, Sum.elim_comp_inl,
    Sum.elim_comp_inr, dotProduct_neg]
  rw [← mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2
  have hs : s ⬝ᵥ Sum.elim b (-b) = (s ∘ Sum.inl) ⬝ᵥ b - (s ∘ Sum.inr) ⬝ᵥ b := by
    rw [← Sum.elim_comp_inl_inr s, elim_dot, dotProduct_neg, Sum.elim_comp_inl, Sum.elim_comp_inr, sub_eq_add_neg]
  rw [hs]
  ring

end GlobalTheory.DoublingEvLaw
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicCompletionComapRationalMatrix
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicCompletionComapRationalMatrix
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HatPullback

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem fm_mulVec_tmul (M : Matrix (Fin n) (Fin n) E) (a : FiniteAdeleRing (𝓞 F) F) (x : Fin n → E) :
    GlobalTheory.UnRep.fm F M *ᵥ (fun i => a ⊗ₜ[F] x i) = fun i => a ⊗ₜ[F] (M *ᵥ x) i := by
  funext i
  simp [GlobalTheory.UnRep.fm, Matrix.mulVec, dotProduct, TensorProduct.tmul_sum]

theorem fm_mul' (A B : Matrix (Fin n) (Fin n) E) :
    GlobalTheory.UnRep.fm F (A * B) = GlobalTheory.UnRep.fm F A * GlobalTheory.UnRep.fm F B :=
  Matrix.map_mul (f := (Algebra.TensorProduct.includeRight :
    E →ₐ[F] FiniteAdeleRing (𝓞 F) F ⊗[F] E).toRingHom)

theorem fm_one' : GlobalTheory.UnRep.fm F (1 : Matrix (Fin n) (Fin n) E) = 1 :=
  Matrix.map_one _ (by simp) rfl

theorem fm_mulVec_mem_hat (M : Matrix (Fin n) (Fin n) E) {L L' : Set (Fin n → E)}
    (h : ∀ x ∈ L, M *ᵥ x ∈ L') {w : Fin n → GlobalTheory.AdLat.RA F E} (hw : w ∈ GlobalTheory.AdLat.hat F L) :
    GlobalTheory.UnRep.fm F M *ᵥ w ∈ GlobalTheory.AdLat.hat F L' := by
  induction hw using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    rw [fm_mulVec_tmul]
    exact AddSubgroup.subset_closure ⟨a, ha, M *ᵥ x, h x hx, rfl⟩
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.mulVec_neg]; exact neg_mem hx

theorem main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (A : GL (Fin n) E)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (w : Fin n → GlobalTheory.AdLat.RA F E),
    GlobalTheory.UnRep.fm F A.1 *ᵥ w ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)) ↔
      w ∈ GlobalTheory.AdLat.hat F ((Λ.comap ((Matrix.mulVecLin A.1).restrictScalars (𝓞 E)) : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) := by
  intro F E _ _ _ _ _ n A Λ w
  have hmem : ∀ x : Fin n → E, x ∈ ((Λ.comap ((Matrix.mulVecLin A.1).restrictScalars (𝓞 E)) :
      Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) ↔ A.1 *ᵥ x ∈ Λ := fun x => by
    simp [Matrix.mulVecLin_apply]
  constructor
  · intro hw
    have h2 := fm_mulVec_mem_hat (F := F) (A⁻¹).1
      (L := (Λ : Set (Fin n → E)))
      (L' := ((Λ.comap ((Matrix.mulVecLin A.1).restrictScalars (𝓞 E)) :
        Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)))
      (fun y hy => by
        rw [hmem, Matrix.mulVec_mulVec, A.mul_inv, Matrix.one_mulVec]
        exact hy) hw
    rwa [Matrix.mulVec_mulVec, ← fm_mul', A.inv_mul, fm_one', Matrix.one_mulVec] at h2
  · intro hw
    exact fm_mulVec_mem_hat (F := F) A.1 (fun x hx => (hmem x).1 hx) hw

end GlobalTheory.HatPullback
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicCompletionComapRationalMatrixStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicCompletion_comap_rational_matrix : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (A : GL (Fin n) E)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (w : Fin n → GlobalTheory.AdLat.RA F E),
    GlobalTheory.UnRep.fm F A.1 *ᵥ w ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)) ↔
      w ∈ GlobalTheory.AdLat.hat F ((Λ.comap ((Matrix.mulVecLin A.1).restrictScalars (𝓞 E)) : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) := by
  first | exact @GlobalTheory.HatPullback.main | exact GlobalTheory.HatPullback.main | (intros; apply GlobalTheory.HatPullback.main <;> assumption)
end
end
