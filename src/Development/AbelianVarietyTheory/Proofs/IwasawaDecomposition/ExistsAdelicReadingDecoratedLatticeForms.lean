module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowFormsAdelicDecoratedLattices
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLiftFormsAdelicDecoratedLattices

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjIdealEqConjP
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoeffFieldRootsOfUnityTypePrimesHermitianStages
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Cls

theorem coeffField_rootsOfUnity_typePrimes_hermitianStages : ∀ X : Stages, GlobalTheory.Core.Cls.RootsG X.toD7 := by
  intro X i
  have hp : Nat.Prime (X.B.host.g i) := X.B.host.g_prime i
  obtain ⟨z, -, hz⟩ := X.B.roots_Ks (X.B.host.g i * (X.B.host.g i - 1)) (by fin_cases i <;> simp)
  have hne : X.B.host.g i * (X.B.host.g i - 1) ≠ 0 :=
    mul_ne_zero hp.ne_zero (by have := hp.two_le; omega)
  have hprim : IsPrimitiveRoot z (X.B.host.g i * (X.B.host.g i - 1)) := by
    refine IsPrimitiveRoot.of_map_of_injective (f := X.B.embLL) ?_ X.B.embLL.injective
    rw [hz]
    exact_mod_cast Complex.isPrimitiveRoot_exp _ hne
  have hpos : 0 < X.B.host.g i * (X.B.host.g i - 1) := Nat.pos_of_ne_zero hne
  exact ⟨⟨z ^ (X.B.host.g i - 1), hprim.pow hpos (mul_comm _ _)⟩, ⟨z ^ X.B.host.g i, hprim.pow hpos rfl⟩⟩

end GlobalTheory.Core.Cls
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3.Brg


open _root_.Formalism.L2.Col in
theorem conjIdeal_eq_conjP {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) :
    Formalism.HermitianLatticesTheory.conjIdeal (K := E) P.asIdeal = (conjPrime₂ P).asIdeal := by
  apply le_antisymm
  · refine Ideal.span_le.2 ?_
    rintro r ⟨s, hs, e⟩
    show r ∈ (conjPrime₂ P).asIdeal
    rw [mem_conjP]
    have : cO E r = s := RingOfIntegers.ext (by
      show star (r : E) = (s : E)
      have e' : (r : E) = star (s : E) := e
      rw [e', star_star])
    rw [this]; exact hs
  · intro r hr
    rw [mem_conjP] at hr
    refine Ideal.subset_span ⟨cO E r, hr, ?_⟩
    show (r : E) = star (star (r : E))
    rw [star_star]


open _root_.Formalism.L2.Col in
theorem g_notMem_of_levOff {X : Fields} {Pr : Primes X} (hPr : Pr.Ok)
    (P : letI := X.starE; LevOff (E := X.E) ∅ Pr.vGs ∅) (k : Fin 2) :
    ((Pr.g k : ℕ) : 𝓞 X.E) ∉ P.1.asIdeal := by
  classical
  letI := X.starE
  intro hk
  have h0 : X.conjO (Pr.piG k) ≠ 0 := by
    refine right_ne_zero_of_mul (a := Pr.piG k) ?_
    rw [hPr.piG_norm k]
    exact_mod_cast (hPr.g_prime k).ne_zero
  have hsub : ∀ Q, Q ∈ Pr.vG k → Q ∈ Pr.vGs := fun Q hQ => by
    unfold Primes.vGs
    rw [Finset.mem_union]
    fin_cases k
    exacts [Or.inl hQ, Or.inr hQ]
  rw [← hPr.piG_norm k] at hk
  rcases P.1.isPrime.mem_or_mem hk with h | h
  · have hc : conjPrime₂ P.1 ∈ Pr.vG k := by
      refine (mem_divs h0 _).2 ?_
      rw [mem_conjP]
      show cO X.E (X.conjO (Pr.piG k)) ∈ P.1.asIdeal
      exact (cO_cO (Pr.piG k)).symm ▸ h
    exact P.2.2.2 (conjPrime₂ P.1) (Or.inr (hsub _ hc)) (conjIdeal_eq_conjP P.1).symm
  · exact P.2.2.1 (Or.inr (hsub _ ((mem_divs h0 _).2 h)))

end GlobalTheory.Mem.R3.Brg

namespace GlobalTheory.Mem.R3.Brg

theorem muVal_eq {B : Base} {px : PreX B.toPre} (I : ColIn B px) (hI : I.Ok) (hV : ValsIn I) (i : Fin B.R.m) {a : I.ι}
    {τ : Tup B.fields.F B.fields.E B.fields.K I.S} (hτ : I.tup a = τ) (P : HeightOneSpectrum (𝓞 B.fields.E))
    (hg : ∀ k, ((B.host.g k : ℕ) : 𝓞 B.fields.E) ∉ P.asIdeal) (hu : (I.xi a).UnrAt P) :
    B.embLL ((I.Ch.muVal i P * xiValOf I τ P : B.LLˣ) : B.LL) = (((I.C.mu0 i * I.xi a).val P : ℂˣ) : ℂ) := by
  subst hτ
  rw [Formalism.L2.Host.HChar.val_mul, Units.val_mul, Units.val_mul, map_mul, hV.embLL_xiValOf a P hu]
  congr 1
  exact hI.ch_tied.muVal i P hg

theorem values : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG →
    (∀ (i : Fin X.toD7.R.m) t, ∀ P ∈ (famR X I hX U Xg tr).A.ok t,
      X.toD7.what₂.embLL ((famR X I hX U Xg tr).A.muVal i t P : X.toD7.what₂.LL) =
        (((L.C.mu0 i * L.xiH t).val (P.1 : Pl X.toD7.host.E) : ℂˣ) : ℂ)) ∧
    (∀ P ∈ (famR X I hX U Xg tr).A.ok (famR X I hX U Xg tr).A.μ0,
      X.toD7.what₂.embLL ((famR X I hX U Xg tr).A.etaVal P : X.toD7.what₂.LL) =
        Formalism.L2.Host.etaAlg X.toD7.host L.C.eta (P.1 : Pl X.toD7.host.E)) ∧
    ∀ t PP, PP ∈ L.Pg ∨ PP ∈ L.Q t → ∃ z : X.toD7.what₂.LL, IsPrimitiveRoot z (Nat.card (kP PP)) := by
  intro X px I hX U Xg tr L eG hI hV hL _
  classical
  letI := X.B.fields.starE
  have hPr : (X.B.primes px).Ok := (GlobalTheory.Mem.Col2.base_fields_primes_ok X.B px).2.1
  refine ⟨fun i t P hP => ?_, fun P _ => ?_, fun t PP hPP => ?_⟩
  · have hP' : P.1 ∈ Formalism.L2.DIV.offSet (E := X.B.fields.E) ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) ∅ := hP
    have hQ : ∀ PP, PP ∈ I.Q (ixOf I U t) → PP ∈ Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1 := fun PP h =>
      Finset.mem_union_right _ (by rw [← tup_ixOf I t]; exact h)
    have hg : ∀ k, ((X.B.host.g k : ℕ) : 𝓞 X.B.fields.E) ∉ P.1.asIdeal := g_notMem_of_levOff hPr P
    have hunr : (I.xi (ixOf I U t)).UnrAt P.1 := by
      by_contra hn
      rw [← hL.xiH t] at hn
      rcases (hL.is.Q_ram t P.1).1 hn with h | ⟨PP', h, hc⟩
      · rw [hL.Q t] at h
        exact hP'.2.1 (Or.inr (Finset.mem_coe.2 (hQ _ h)))
      · rw [hL.Q t] at h
        have hle : PP'.asIdeal ≤ (Formalism.L2.Col.conjPrime₂ P.1).asIdeal := fun c hcm => by
          obtain ⟨c', hc', e⟩ := hc c hcm
          refine (Formalism.L2.Col.mem_conjP (E := X.B.fields.E) P.1 c).2 ?_
          have : Formalism.L2.Col.cO X.B.fields.E c = c' := RingOfIntegers.ext e.symm
          rw [this]; exact hc'
        have heq : PP'.asIdeal = (Formalism.L2.Col.conjPrime₂ P.1).asIdeal :=
          PP'.isMaximal.eq_of_le (Formalism.L2.Col.conjPrime₂ P.1).isPrime.ne_top hle
        exact hP'.2.2 PP' (Or.inr (Finset.mem_coe.2 (hQ _ h))) (heq.trans (conjIdeal_eq_conjP P.1).symm)
    rw [hL.C, hL.xiH t]
    exact muVal_eq I hI hV i (tup_ixOf I t) P.1 hg hunr
  · show X.B.embLL (I.Ch.etaVal P.1 : X.B.LL) = _
    rw [hL.C]
    exact hI.ch_tied.etaVal P.1
  · rcases hPP with h | h
    · rw [hL.Pg] at h
      obtain ⟨k, hk⟩ : ∃ k, PP ∈ (X.B.primes px).vG k := by
        rcases Finset.mem_union.1 h with h | h
        exacts [⟨0, h⟩, ⟨1, h⟩]
      have hn : Ideal.absNorm PP.asIdeal = X.B.host.g k := hPr.vG_norm k PP hk
      have hcard : Nat.card (kP PP) = X.B.host.g k := by
        rw [← hn, Ideal.absNorm_apply, Submodule.cardQuot_apply]
      rw [hcard]
      exact (GlobalTheory.Core.Cls.coeffField_rootsOfUnity_typePrimes_hermitianStages X k).1
    · rw [hL.Q t] at h
      exact hV.2 _ PP h

end GlobalTheory.Mem.R3.Brg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FamRPlaces
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3

theorem famR_places : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG →
    (∀ t P, P ∈ (famR X I hX U Xg tr).A.ok t ↔
      Bridge.SplitOff (P.1 : Pl X.toD7.host.E) ((L.Pg : Set (Pl X.toD7.host.E)) ∪ (L.Q t : Set (Pl X.toD7.host.E)))) ∧
    (∀ PP, Bridge.SplitOff PP (L.Pg : Set (Pl X.toD7.host.E)) → ∃ P : PlS X.B px, (P.1 : Pl X.toD7.host.E) = PP) ∧
    Bridge.InertTie (famR X I hX U Xg tr) (fun Q : PlI X.B px => (Q.1 : Pl X.toD7.host.E)) (L.Pg : Set (Pl X.toD7.host.E)) L.Q ∧
    (∀ PP, Bridge.InertOff PP (L.Pg : Set (Pl X.toD7.host.E)) → ∃ Q : PlI X.B px, (Q.1 : Pl X.toD7.host.E) = PP) := by
  intro X px I hX U Xg tr L eG _ _ hL _
  have hS : ∀ t : TupU I U, ((∅ : Set (HeightOneSpectrum (𝓞 X.B.fields.E))) ∪
      ((∅ : Finset (HeightOneSpectrum (𝓞 X.B.fields.E))) : Set (HeightOneSpectrum (𝓞 X.B.fields.E))) ∪
      ((Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1 : Finset (HeightOneSpectrum (𝓞 X.B.fields.E))) :
        Set (HeightOneSpectrum (𝓞 X.B.fields.E)))) =
      (L.Pg : Set (Pl X.toD7.host.E)) ∪ (L.Q t : Set (Pl X.toD7.host.E)) := by
    intro t
    rw [hL.Pg, hL.Q t]
    have e : I.Q (ixOf I U t) = Formalism.L2.Col.QE I.sel (t.1 : Chr X.B.fields.F X.B.fields.E X.B.fields.K) := by
      show Formalism.L2.Col.QE I.sel (I.tup (ixOf I U t) : Chr X.B.fields.F X.B.fields.E X.B.fields.K) = _
      rw [tup_ixOf I t]
    rw [e]
    simp [Formalism.L2.Col.rowSG, Formalism.L2.Col.uSG]
    rfl
  have hS0 : ((∅ : Set (HeightOneSpectrum (𝓞 X.B.fields.E))) ∪
      ((∅ : Finset (HeightOneSpectrum (𝓞 X.B.fields.E))) : Set (HeightOneSpectrum (𝓞 X.B.fields.E))) ∪
      (((X.B.primes px).vGs : Finset (HeightOneSpectrum (𝓞 X.B.fields.E))) : Set (HeightOneSpectrum (𝓞 X.B.fields.E)))) =
      (L.Pg : Set (Pl X.toD7.host.E)) := by
    rw [hL.Pg]
    simp
    rfl
  refine ⟨fun t P => ?_, fun PP hPP => ?_, ⟨Subtype.val_injective, fun t Q => ?_⟩, fun PP hPP => ?_⟩
  · show P.1 ∈ Formalism.L2.DIV.offSet ∅ (Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) ∅ ↔ _
    unfold Formalism.L2.DIV.offSet Formalism.IndefR.Bridge.SplitOff
    rw [Set.mem_setOf_eq, hS t]
    exact Iff.rfl
  · obtain ⟨h1, h2, h3⟩ := hPP
    refine ⟨⟨PP, h1, ?_, fun Q hQ => h3 Q ?_⟩, rfl⟩
    · rw [hS0]; exact h2
    · rw [← hS0]; exact hQ
  · show Q.1 ∉ _ ↔ _
    unfold Formalism.IndefR.Bridge.InertOff
    rw [hS t]
    have hc : ∀ P : Pl X.toD7.host.E, Formalism.L2.Col.conjPrime₂ P = P →
        Formalism.HermitianLatticesTheory.conjIdeal (K := X.toD7.host.E) P.asIdeal = P.asIdeal := fun P hP => by
      rw [Formalism.L2.Col.conjIdeal_asIdeal, hP]
    exact ⟨fun h => ⟨hc Q.1 Q.2.1, h⟩, fun h => h.2⟩
  · obtain ⟨h1, h2⟩ := hPP
    have hc : Formalism.L2.Col.conjPrime₂ PP = PP := HeightOneSpectrum.ext (by rw [← Formalism.L2.Col.conjIdeal_asIdeal]; exact h1)
    have hin : ∃ x : 𝓞 X.toD7.host.E, Formalism.L2.Col.cO X.toD7.host.E x - x ∉ PP.asIdeal := by
      obtain ⟨θ, t, ht, hθ⟩ := X.toD7.sp.cm.cmUnram.2.2 PP.asIdeal PP.isMaximal
      have e : Formalism.L2.Col.cO X.toD7.host.E θ = t := RingOfIntegers.ext ht.symm
      refine ⟨θ, fun h => hθ ?_⟩
      rw [e] at h
      rw [← neg_sub]
      exact PP.asIdeal.neg_mem h
    refine ⟨⟨PP, hc, hin, ?_⟩, rfl⟩
    rw [hS0]; exact h2

end GlobalTheory.Mem.R3

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSmulPrIso
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.PrIsoScale

section Alg

variable {T : Type} [Fintype T] [DecidableEq T] {E : T → Type}
  [∀ τ, NormedAddCommGroup (E τ)] [∀ τ, InnerProductSpace ℂ (E τ)]

def pSum (ι : T → Type) [∀ τ, Fintype (ι τ)] (b : ∀ τ, OrthonormalBasis (ι τ) ℂ (E τ))
    (φ ψ : (⨂[ℂ] τ, E τ) →ₗ[ℂ] ℂ) : ℂ :=
  ∑ f : (∀ τ, ι τ), starRingEnd ℂ (φ (PiTensorProduct.tprod ℂ fun τ => b τ (f τ))) *
    ψ (PiTensorProduct.tprod ℂ fun τ => b τ (f τ))

theorem tprod_expand {ι κ : T → Type} [∀ τ, Fintype (ι τ)] [∀ τ, Fintype (κ τ)]
    (b : ∀ τ, OrthonormalBasis (ι τ) ℂ (E τ)) (b' : ∀ τ, OrthonormalBasis (κ τ) ℂ (E τ)) (f : ∀ τ, ι τ) :
    (PiTensorProduct.tprod ℂ fun τ => b τ (f τ)) =
      ∑ g : (∀ τ, κ τ), (∏ τ, ⟪b' τ (g τ), b τ (f τ)⟫_ℂ) • PiTensorProduct.tprod ℂ fun τ => b' τ (g τ) := by
  have h : (fun τ => b τ (f τ)) = fun τ => ∑ j, ⟪b' τ j, b τ (f τ)⟫_ℂ • b' τ j :=
    funext fun τ => ((b' τ).sum_repr' _).symm
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h, MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  exact MultilinearMap.map_smul_univ _ _ _

theorem pSum_indep {ι κ : T → Type} [∀ τ, Fintype (ι τ)] [∀ τ, Fintype (κ τ)]
    (b : ∀ τ, OrthonormalBasis (ι τ) ℂ (E τ)) (b' : ∀ τ, OrthonormalBasis (κ τ) ℂ (E τ))
    (φ ψ : (⨂[ℂ] τ, E τ) →ₗ[ℂ] ℂ) : pSum ι b φ ψ = pSum κ b' φ ψ := by
  classical
  unfold pSum
  set U : (∀ τ, ι τ) → (∀ τ, κ τ) → ℂ := fun f g => ∏ τ, ⟪b' τ (g τ), b τ (f τ)⟫_ℂ with hU
  set t' : (∀ τ, κ τ) → ⨂[ℂ] τ, E τ := fun g => PiTensorProduct.tprod ℂ fun τ => b' τ (g τ) with ht'
  have hχ : ∀ (χ : (⨂[ℂ] τ, E τ) →ₗ[ℂ] ℂ) (f : ∀ τ, ι τ),
      χ (PiTensorProduct.tprod ℂ fun τ => b τ (f τ)) = ∑ g, U f g * χ (t' g) := by
    intro χ f
    set_option synthInstance.maxHeartbeats 100000 in
      rw [tprod_expand b b' f, map_sum]
    simp only [map_smul, smul_eq_mul, U, t']
  have horth : ∀ g g' : (∀ τ, κ τ), ∑ f, starRingEnd ℂ (U f g) * U f g' = if g = g' then 1 else 0 := by
    intro g g'
    calc ∑ f, starRingEnd ℂ (U f g) * U f g'
        = ∑ f : (∀ τ, ι τ), ∏ τ, (⟪b τ (f τ), b' τ (g τ)⟫_ℂ * ⟪b' τ (g' τ), b τ (f τ)⟫_ℂ) := by
          refine Finset.sum_congr rfl fun f _ => ?_
          simp only [U, map_prod, inner_conj_symm, Finset.prod_mul_distrib]
      _ = ∏ τ, ∑ i, ⟪b τ i, b' τ (g τ)⟫_ℂ * ⟪b' τ (g' τ), b τ i⟫_ℂ := by
          rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
      _ = ∏ τ, ⟪b' τ (g' τ), b' τ (g τ)⟫_ℂ := by
          refine Finset.prod_congr rfl fun τ _ => ?_
          rw [← (b τ).sum_inner_mul_inner]
          exact Finset.sum_congr rfl fun i _ => mul_comm _ _
      _ = ∏ τ, if g' τ = g τ then (1 : ℂ) else 0 := by
          refine Finset.prod_congr rfl fun τ _ => ?_
          exact (b' τ).inner_eq_ite _ _
      _ = if g = g' then 1 else 0 := by
          rw [Finset.prod_boole]
          simp only [Finset.mem_univ, true_implies]
          by_cases h : g = g'
          · subst h; simp
          · rw [if_neg h, if_neg]
            intro h'
            exact h (funext fun τ => (h' τ).symm)
  simp_rw [hχ φ, hχ ψ]
  calc ∑ f, starRingEnd ℂ (∑ g, U f g * φ (t' g)) * ∑ g', U f g' * ψ (t' g')
      = ∑ g, ∑ g', starRingEnd ℂ (φ (t' g)) * ψ (t' g') * ∑ f, starRingEnd ℂ (U f g) * U f g' := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
        conv_rhs => rw [Finset.sum_comm]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun g' _ => ?_
        refine Finset.sum_congr rfl fun f _ => ?_
        ring
    _ = ∑ g, starRingEnd ℂ (φ (t' g)) * ψ (t' g) := by
        refine Finset.sum_congr rfl fun g _ => ?_
        simp only [horth, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]

end Alg

section Alg2

variable {T : Type} [Fintype T] [DecidableEq T] {E : T → Type}
  [∀ τ, NormedAddCommGroup (E τ)] [∀ τ, InnerProductSpace ℂ (E τ)]

theorem pSum_of_iso {ι : T → Type} [∀ τ, Fintype (ι τ)] (b : ∀ τ, OrthonormalBasis (ι τ) ℂ (E τ)) (τ : T)
    (A : E τ ≃ₗᵢ[ℂ] E τ) (φ ψ φ' ψ' : (⨂[ℂ] ρ, E ρ) →ₗ[ℂ] ℂ)
    (hφ : ∀ v : ∀ ρ, E ρ, φ' (PiTensorProduct.tprod ℂ (Function.update v τ (A (v τ)))) = φ (PiTensorProduct.tprod ℂ v))
    (hψ : ∀ v : ∀ ρ, E ρ, ψ' (PiTensorProduct.tprod ℂ (Function.update v τ (A (v τ)))) = ψ (PiTensorProduct.tprod ℂ v)) :
    pSum ι b φ' ψ' = pSum ι b φ ψ := by
  let b1 : ∀ ρ, OrthonormalBasis (ι ρ) ℂ (E ρ) := Function.update b τ ((b τ).map A)
  have hv : ∀ f : (∀ ρ, ι ρ), (fun ρ => b1 ρ (f ρ)) = Function.update (fun ρ => b ρ (f ρ)) τ (A (b τ (f τ))) := by
    intro f
    funext ρ
    by_cases h : ρ = τ
    · subst h
      simp [b1, OrthonormalBasis.map_apply]
    · simp [b1, Function.update_of_ne h]
  rw [← pSum_indep b1 b]
  unfold pSum
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [hv f, hφ, hψ]

end Alg2

section Model

variable {D : D7}

def smIso {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    {g : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hg : g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) : M.sm τ →ₗᵢ[ℂ] M.sm τ where
  toLinearMap := (M.rep τ g : M.H τ →ₗ[ℂ] M.H τ).restrict
    (fun w hw => GlobalTheory.SmoothStable.rep_mem_sm D V S M τ g hg w hw)
  norm_map' x := (M.ds τ).2.2.1.2.1 _ (Formalism.IndefR.SchurOrthogonalityAlt.conj_mem M τ hg) x

end Model


set_option maxHeartbeats 1000000 in
theorem exists_smul_prIso (D : D7) (θ : InfFam D) (MX : DSModel D.sp.X' (parB (Ptw D) D.R.m))
    (cX : CoefA D.sp.X') (prX : cX.W →ₗ[ℂ] SmT MX →ₗ[ℂ] ℂ) (hθ : IsInfFam θ) (hc : cX.Is)
    (hpr : IsDualPair θ MX cX prX) : ∃ c : ℂ, c ≠ 0 ∧ Seed.PrIso MX cX (c • prX) := by
  classical
  by_cases hfin : ∀ τ, FiniteDimensional ℂ (MX.sm τ)
  swap
  · refine ⟨1, one_ne_zero, ?_⟩
    intro ι _ b
    exact absurd (fun τ => Module.Finite.of_basis (b τ).toBasis) hfin
  obtain ⟨b0⟩ : Nonempty (∀ τ, OrthonormalBasis (Fin (Module.finrank ℂ (MX.sm τ))) ℂ (MX.sm τ)) :=
    ⟨fun τ => stdOrthonormalBasis ℂ (MX.sm τ)⟩
  obtain ⟨u, hu'⟩ : ∃ u : (∀ τ, Fin (Module.finrank ℂ (MX.sm τ))) → cX.W, ∀ f x,
      ⟪u f, x⟫_ℂ = prX x (PiTensorProduct.tprod ℂ fun τ => b0 τ (f τ)) :=
    ⟨fun f => (InnerProductSpace.toDual ℂ cX.W).symm
      (LinearMap.toContinuousLinearMap (prX.flip (PiTensorProduct.tprod ℂ fun τ => b0 τ (f τ)))),
      fun f x => by rw [InnerProductSpace.toDual_symm_apply]; rfl⟩
  obtain ⟨T, hTdef⟩ : ∃ T : Module.End ℂ cX.W,
      T = ∑ f, (prX.flip (PiTensorProduct.tprod ℂ fun τ => b0 τ (f τ))).smulRight (u f) := ⟨_, rfl⟩
  have hT : ∀ w w', ⟪w, T w'⟫_ℂ = pSum _ b0 (prX w) (prX w') := by
    intro w w'
    rw [hTdef, LinearMap.sum_apply, inner_sum]
    unfold pSum
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [LinearMap.smulRight_apply]
    simp only [inner_smul_right, LinearMap.flip_apply]
    have e2 : ⟪w, u f⟫_ℂ = starRingEnd ℂ (prX w (PiTensorProduct.tprod ℂ fun τ => b0 τ (f τ))) := by
      rw [← hu' f w, inner_conj_symm]
    simp only [e2]
    ring

  have hinv : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D D.sp.X' τ), ∀ w w',
      pSum _ b0 (prX (cX.ρ (atTau θ D.sp.X' τ g) w)) (prX (cX.ρ (atTau θ D.sp.X' τ g) w')) =
        pSum _ b0 (prX w) (prX w') := by
    intro τ g hg w w'
    obtain ⟨A, hA⟩ : ∃ A : MX.sm τ ≃ₗᵢ[ℂ] MX.sm τ, ∀ x, ((A x : MX.sm τ) : MX.H τ) = MX.rep τ g x :=
      ⟨(smIso MX τ hg).toLinearIsometryEquiv rfl, fun x => rfl⟩
    exact pSum_of_iso b0 τ A _ _ _ _ (fun v => hpr.2 τ g hg w v (A (v τ)) (hA _))
      (fun v => hpr.2 τ g hg w' v (A (v τ)) (hA _))

  have hρinv : ∀ (h : GA D D.sp.X') (z : cX.W), cX.ρ h (cX.ρ h⁻¹ z) = z := by
    intro h z
    have e : cX.ρ h * cX.ρ h⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    exact congrArg (fun F : Module.End ℂ cX.W => F z) e
  have hcommAt : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D D.sp.X' τ),
      T * cX.ρ (atTau θ D.sp.X' τ g) = cX.ρ (atTau θ D.sp.X' τ g) * T := by
    intro τ g hg
    apply LinearMap.ext
    intro w'
    apply ext_inner_left ℂ
    intro z
    obtain ⟨w, rfl⟩ : ∃ w, cX.ρ (atTau θ D.sp.X' τ g) w = z :=
      ⟨cX.ρ (atTau θ D.sp.X' τ g)⁻¹ z, hρinv _ z⟩
    have e1 := hT (cX.ρ (atTau θ D.sp.X' τ g) w) (cX.ρ (atTau θ D.sp.X' τ g) w')
    have e2 := hinv τ g hg w w'
    have e3 := hT w w'
    have e4 := hc.2.1 (atTau θ D.sp.X' τ g) w (T w')
    simp only [Module.End.mul_apply]
    rw [e1, e2, ← e3, e4]
  let U : Submonoid (GA D D.sp.X') := (Submonoid.centralizer ({T} : Set (Module.End ℂ cX.W))).comap cX.ρ
  have hU : ∀ h, h ∈ U ↔ T * cX.ρ h = cX.ρ h * T := by
    intro h
    simp [U, Submonoid.mem_centralizer_iff]
  have hall : ∀ h, T * cX.ρ h = cX.ρ h * T := by
    intro h
    obtain ⟨a, ha, k, hk, rfl⟩ := (GlobalTheory.UnitarySplit.real_finite_split D D.sp.X').1 h
    have h1 : a ∈ U := GlobalTheory.DefiniteMult.real_le hθ U (fun τ g hg => (hU _).2 (hcommAt τ g hg)) ha
    have h2 : k ∈ U := (hU k).2 (by rw [hc.1 k hk, mul_one, one_mul])
    exact (hU _).1 (U.mul_mem h1 h2)

  haveI : Nontrivial cX.W := hc.2.2.2.1
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue T
  have hstab : ∀ h, (T.eigenspace μ).map (cX.ρ h) ≤ T.eigenspace μ := by
    intro h y hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff] at hx
    rw [Module.End.mem_eigenspace_iff]
    have e := congrArg (fun F : Module.End ℂ cX.W => F x) (hall h)
    simp only [Module.End.mul_apply] at e
    rw [e, hx, map_smul]
  have hE : T.eigenspace μ = ⊤ := by
    rcases hc.2.2.2.2 (T.eigenspace μ) hstab with h | h
    · exact absurd h (Module.End.hasEigenvalue_iff.1 hμ)
    · exact h
  have hTμ : ∀ x, T x = μ • x := fun x =>
    Module.End.mem_eigenspace_iff.1 (hE ▸ Submodule.mem_top)

  obtain ⟨w, hw⟩ : ∃ w, prX w ≠ 0 := by
    by_contra h
    push_neg at h
    exact hpr.1 (LinearMap.ext h)
  obtain ⟨f0, hf0⟩ : ∃ f : (∀ τ, Fin (Module.finrank ℂ (MX.sm τ))),
      prX w (PiTensorProduct.tprod ℂ fun τ => b0 τ (f τ)) ≠ 0 := by
    by_contra h
    push_neg at h
    apply hw
    refine (Basis.piTensorProduct fun τ => (b0 τ).toBasis).ext fun f => ?_
    rw [Basis.piTensorProduct_apply]
    simpa using h f
  have hw0 : w ≠ 0 := by
    rintro rfl
    exact hw (map_zero prX)
  have hsq : ∀ z : ℂ, starRingEnd ℂ z * z = (‖z‖ : ℂ) ^ 2 := fun z => Complex.conj_mul' z
  obtain ⟨s, hs0, hs⟩ : ∃ s : ℝ, 0 < s ∧ pSum _ b0 (prX w) (prX w) = (s : ℂ) := by
    refine ⟨∑ f : (∀ τ, Fin (Module.finrank ℂ (MX.sm τ))),
      ‖prX w (PiTensorProduct.tprod ℂ fun τ => b0 τ (f τ))‖ ^ 2, ?_, ?_⟩
    · exact Finset.sum_pos' (fun f _ => sq_nonneg _) ⟨f0, Finset.mem_univ _, pow_pos (norm_pos_iff.2 hf0) 2⟩
    · unfold pSum
      push_cast
      exact Finset.sum_congr rfl fun f _ => hsq _
  have hwpos : 0 < ‖w‖ ^ 2 := pow_pos (norm_pos_iff.2 hw0) 2
  set r : ℝ := s / ‖w‖ ^ 2 with hr
  have hr0 : 0 < r := div_pos hs0 hwpos
  have hμr : μ = (r : ℂ) := by
    have e1 := hT w w
    have e2 : ⟪w, T w⟫_ℂ = μ * ((‖w‖ ^ 2 : ℝ) : ℂ) := by
      have hww : ⟪w, w⟫_ℂ = ((‖w‖ ^ 2 : ℝ) : ℂ) := by
        first
          | (rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl)
          | exact_mod_cast inner_self_eq_norm_sq_to_K (𝕜 := ℂ) w
          | simp [inner_self_eq_norm_sq_to_K]
      rw [hTμ, inner_smul_right, hww]
    rw [e2, hs] at e1
    have hn : ((‖w‖ ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hwpos.ne'
    rw [hr, Complex.ofReal_div, eq_div_iff hn]
    exact e1

  refine ⟨((Real.sqrt r)⁻¹ : ℝ), Complex.ofReal_ne_zero.2 (inv_ne_zero (Real.sqrt_ne_zero'.2 hr0)), ?_⟩
  have hcc : starRingEnd ℂ (((Real.sqrt r)⁻¹ : ℝ) : ℂ) * (((Real.sqrt r)⁻¹ : ℝ) : ℂ) = ((r⁻¹ : ℝ) : ℂ) := by
    rw [hsq, Complex.norm_real, Real.norm_eq_abs, ← Complex.ofReal_pow, sq_abs, inv_pow, Real.sq_sqrt hr0.le]
  intro ι _ b w₁ w₂
  have e : (starRingEnd ℂ (((Real.sqrt r)⁻¹ : ℝ) : ℂ) * (((Real.sqrt r)⁻¹ : ℝ) : ℂ)) * pSum ι b (prX w₁) (prX w₂) =
      ∑ f : (∀ τ, ι τ), starRingEnd ℂ (((((Real.sqrt r)⁻¹ : ℝ) : ℂ) • prX) w₁ (PiTensorProduct.tprod ℂ fun τ => b τ (f τ))) *
        ((((Real.sqrt r)⁻¹ : ℝ) : ℂ) • prX) w₂ (PiTensorProduct.tprod ℂ fun τ => b τ (f τ)) := by
    unfold pSum
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun f _ => ?_
    simp only [LinearMap.smul_apply, smul_eq_mul, map_mul]
    ring
  refine Eq.trans ?_ e
  have e3 : pSum ι b (prX w₁) (prX w₂) = μ * ⟪w₁, w₂⟫_ℂ := by
    rw [pSum_indep b b0, ← hT, hTμ, inner_smul_right]
  rw [e3, hcc, hμr, ← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hr0.ne', Complex.ofReal_one, one_mul]

end GlobalTheory.PrIsoScale
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicReadingDecoratedLatticeForms
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3.BrgRead

set_option maxHeartbeats 1000000

theorem embLL_labLL_eq {D : D7} (τ : D.what₂.Tau) (x : D.host.E) : D.what₂.embLL (labLL D τ x) = tauE D τ x :=
  DFunLike.congr_fun D.embE_φ₀ (D.host.sigmaOf (D.eTau τ).1 x)

theorem gram_V (X : Stages) (h : DiagSpaces X.toD7.sp) (i : Fin X.toD7.R.m) : (Vc X.toD7 i).gram = 1 := by
  obtain ⟨hs, -, -, -, -, hV⟩ := h
  have h1 := hV ((i : ℕ) + 1)
  have hn : X.toD7.sp.Vneg ((i : ℕ) + 1) = false := X.B.V_pos _ (by omega) i.2
  rw [hn] at h1
  change (X.toD7.sp.V ((i : ℕ) + 1)).gram = 1
  rw [h1]
  refine Matrix.ext fun a b => (Formalism.BasicNotions.Examples₂.stdSpace_gram_apply hs _ _ _ _ a b).trans ?_
  simp [Matrix.one_apply, Formalism.BasicNotions.Examples₂.sgn]

theorem isDualPair_smul {D : D7} {θ : InfFam D} {MX : DSModel D.sp.X' (parB (Ptw D) D.R.m)} {cX : CoefA D.sp.X'}
    {prX : cX.W →ₗ[ℂ] SmT MX →ₗ[ℂ] ℂ} (h : IsDualPair θ MX cX prX) {c : ℂ} (hc : c ≠ 0) :
    IsDualPair θ MX cX (c • prX) := by
  refine ⟨smul_ne_zero hc h.1, fun τ g hg w v u hu => ?_⟩
  simp only [LinearMap.smul_apply]
  rw [h.2 τ g hg w v u hu]

theorem exists_coefData : ∀ (D : D7), Seed.VPos D → ∀ θ : InfFam D, IsInfFam θ → ∀ MX : DSModel D.sp.X' (parB (Ptw D) D.R.m),
  ∃ (cX : CoefA D.sp.X') (cV : ∀ i, CoefA (Vc D i)) (prX : cX.W →ₗ[ℂ] SmT MX →ₗ[ℂ] ℂ)
    (gramR : Matrix (Fin D.sp.X'.rank) (Fin D.sp.X'.rank) D.host.E)
    (c0R : VV D.what₂.LL (fun τ => Bridge.lamRdef (Ptw D) τ) →ₛₗ[D.what₂.embLL] cX.W)
    (c0L : ∀ i : Fin D.R.m, VV D.what₂.LL (fun τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) →ₛₗ[D.what₂.embLL] (cV i).W),
    cX.Is ∧ (∀ i, (cV i).Is) ∧ IsDualPair θ MX cX prX ∧ Seed.PrIso MX cX prX ∧
    (gramR = D.sp.X'.gram ∨ gramR = -D.sp.X'.gram) ∧
    Bridge.CoefMapTie D.sp.X' cX.coef c0R (rhoV (labLL D) _) ∧
    (∀ i, Bridge.CoefMapTie (Vc D i) (cV i).coef (c0L i) (rhoVr (labLL D) _)) ∧
    (∀ x y, inner ℂ (c0R x) (c0R y) = D.what₂.embLL (pairV (labLL D) _ gramR x y)) ∧
    ∀ i x y, inner ℂ (c0L i x) (c0L i y) = D.what₂.embLL (pairVr (labLL D) _
      (if D.sp.Vneg ((i : ℕ) + 1) then -(Vc D i).gram else (Vc D i).gram) x y) := by
  intro D hV θ hθ MX
  obtain ⟨cX, prX, c0R, gramR, hcX, hdual, hg, hmap, hin⟩ := GlobalTheory.CoefSpace.exists_coef_dualPair D θ MX hθ
  have hL := fun i => GlobalTheory.CoefModel.exists_coef_lift D i (hV i)
  choose cV c0L hcV hmapL hinL using hL
  obtain ⟨c, hc, hiso⟩ := GlobalTheory.PrIsoScale.exists_smul_prIso D θ MX cX prX hθ hcX hdual
  exact ⟨cX, cV, c • prX, gramR, c0R, c0L, hcX, hcV, isDualPair_smul hdual hc, hiso, hg, hmap, hmapL, hin, hinL⟩
theorem hecke_degrees : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px),
    (∀ t P, (famR X I hX U Xg tr).A.heckeR t (P, 0) = 1 ∧
      ∀ k, X.toD7.sp.X'.rank < k → (famR X I hX U Xg tr).A.heckeR t (P, k) = 0) ∧
    (∀ i t P, (famR X I hX U Xg tr).A.heckeL i t (P, 0) = 1 ∧
      ∀ k, (Vc X.toD7 i).rank < k → (famR X I hX U Xg tr).A.heckeL i t (P, k) = 0) := by
  intro X px I hX U Xg tr
  have hk3 := X.B.R.m_add_three_le_k
  refine ⟨fun t P => ⟨heckeCSD_zero _ _ _ _ _ _, fun k hk => ?_⟩, fun i t P => ⟨heckeCSD_zero _ _ _ _ _ _, fun k hk => ?_⟩⟩
  · refine (congrArg _ (Formalism.L2.Col.heckeFam_eq_zero_of_lt _ _ _ ?_)).trans (LinearEquiv.map_zero _)
    have e := X.toD7.sp.X'_rank
    change X.toD7.sp.X'.rank < k at hk
    rw [e] at hk
    change _ < k
    unfold Ranks.rankX' at hk
    unfold Ranks.N
    simp only [Ranks.r] at hk ⊢
    change X.B.R.k + X.B.R.m - 1 + X.B.R.m * X.B.R.t < k at hk
    rw [Nat.mul_add, Nat.mul_one]
    omega
  · refine (congrArg _ (Formalism.L2.Col.heckeFam_eq_zero_of_lt _ _ _ ?_)).trans (LinearEquiv.map_zero _)
    have e := X.toD7.sp.V_rank _ (by omega) i.2
    change (X.toD7.sp.V ((i : ℕ) + 1)).rank < k at hk
    rw [e] at hk
    exact hk

theorem exists_brgL : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → L.βX = 1 → (∀ i, L.βV i = 1) → Seed.FrmC.StdLat X.toD7.sp.X' → (∀ i, Seed.FrmC.StdLat (Vc X.toD7 i)) → ∀ θ : InfFam X.toD7, IsInfFam θ → ∀ MX : DSModel X.toD7.sp.X' (parB (Ptw X.toD7) X.toD7.R.m), ∃ (cX : CoefA X.toD7.sp.X') (cV : ∀ i, CoefA (Vc X.toD7 i)) (pl : PlS X.B px → Pl X.toD7.host.E) (Sb : Finset (Pl X.toD7.host.E)) (Bd : Seed.BType (famR X I hX U Xg tr) L cX cV pl) (plI : PlI X.B px → Pl X.toD7.host.E) (SF : Finset (HeightOneSpectrum (𝓞 X.toD7.host.F))) (prX : cX.W →ₗ[ℂ] SmT MX →ₗ[ℂ] ℂ), cX.Is ∧ (∀ i, (cV i).Is) ∧ IsDualPair θ MX cX prX ∧ Seed.PrIso MX cX prX ∧ Seed.BrgL (famR X I hX U Xg tr) L eG cX cV pl Sb Bd plI SF ∧ BrgStdR X I hX U Xg tr L cX (fun t φ => Bd.jR t φ) ∧ ∀ i, BrgStdV X I hX U Xg tr L i (cV i) fun t φ => Bd.jL i t φ := by
  intro X px I hX U Xg tr L eG hI hV hL hG hβX hβV hsX hsV θ hθ MX
  have hVP : Seed.VPos X.toD7 := fun i => X.B.V_posDef _ (by omega) i.2
  obtain ⟨cX, cV, prX, gramR, c0R, c0L, hcX, hcV, hdual, hiso, hgram, hmapR, hmapL, hinR, hinL⟩ :=
    exists_coefData X.toD7 hVP θ hθ MX
  have hR := GlobalTheory.T.exists_rowForms_adelic_decoratedLattices X px I hX U Xg tr L eG hI hV hL hG cX gramR c0R hcX hgram hmapR hinR hβX hsX
  have hLf := fun i => GlobalTheory.T.exists_liftForms_adelic_decoratedLattices X px I hX U Xg tr L eG hI hV hL hG cV i (c0L i) (hcV i) (hmapL i) (hinL i) (hβV i)
    (gram_V X hI.spaces i) (hsV i)
  obtain ⟨sR, hsR, hstR⟩ := hR
  choose sL hsL hstL using hLf
  obtain ⟨hok, hon, hit, hion⟩ := GlobalTheory.Mem.R3.famR_places X px I hX U Xg tr L eG hI hV hL hG
  obtain ⟨hmu, heta, hroots⟩ := GlobalTheory.Mem.R3.Brg.values X px I hX U Xg tr L eG hI hV hL hG
  obtain ⟨hdR, hdL⟩ := hecke_degrees X px I hX U Xg tr
  have hrk : X.toD7.sp.X'.rank = (famR X I hX U Xg tr).A.r + X.toD7.R.m * (famR X I hX U Xg tr).A.t := X.toD7.sp.X'_rank
  have hrkL : ∀ i : Fin X.toD7.R.m, (Vc X.toD7 i).rank = (famR X I hX U Xg tr).A.r + (famR X I hX U Xg tr).A.t :=
    fun i => X.toD7.sp.V_rank _ (by omega) i.2
  let B : Seed.BType (famR X I hX U Xg tr) L cX cV (fun P : PlS X.B px => (P.1 : Pl X.toD7.host.E)) :=
    { R := sR, L := fun i t => sL i t, rankR := hrk, rankL := hrkL }
  classical
  refine ⟨cX, cV, fun P => P.1, L.Pg, B, fun Q => Q.1, L.Pg.image (fun PP => PP.under (𝓞 X.toD7.host.F)), prX,
    hcX, hcV, hdual, hiso, ?_, hstR, hstL⟩
  exact
    { red_R := fun t q => (hsR t).1 q
      red_L := fun i t q => (hsL i t).1 q
      tie := ⟨gramR, c0R, c0L,
        { ranks := ⟨rfl, rfl, rfl⟩
          v0 := rfl
          tauL_ok := fun τ => RingHom.ext fun x => embLL_labLL_eq τ x
          pl_inj := fun a b h => Subtype.ext h
          q := fun P => rfl
          S_fin := Set.toFinite _
          ok := hok
          gramR_eq := hgram
          mapR := hmapR
          mapL := hmapL
          coefR := fun t => (hsR t).2.1
          coefL := fun i t => (hsL i t).2.1 }⟩
      sb := rfl
      roots := hroots
      pl_onto := hon
      degR := hdR
      degL := hdL
      muVal := hmu
      etaVal := heta
      in_tie := hit
      in_onto := hion
      in_R := fun t => (hsR t).2.2
      in_L := fun i t => (hsL i t).2.2
      in_SF := fun v => by
        simp only [Finset.mem_image]
        refine exists_congr fun PP => and_congr_right fun _ => ?_
        rw [HeightOneSpectrum.ext_iff, HeightOneSpectrum.under_asIdeal, Ideal.under_def] }

end GlobalTheory.Mem.R3.BrgRead

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicReadingDecoratedLatticeFormsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelicReading_decoratedLatticeForms : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → L.βX = 1 → (∀ i, L.βV i = 1) → Seed.FrmC.StdLat X.toD7.sp.X' → (∀ i, Seed.FrmC.StdLat (Vc X.toD7 i)) → ∀ θ : InfFam X.toD7, IsInfFam θ → ∀ MX : DSModel X.toD7.sp.X' (parB (Ptw X.toD7) X.toD7.R.m), ∃ (cX : CoefA X.toD7.sp.X') (cV : ∀ i, CoefA (Vc X.toD7 i)) (pl : PlS X.B px → Pl X.toD7.host.E) (Sb : Finset (Pl X.toD7.host.E)) (Bd : Seed.BType (famR X I hX U Xg tr) L cX cV pl) (plI : PlI X.B px → Pl X.toD7.host.E) (SF : Finset (HeightOneSpectrum (𝓞 X.toD7.host.F))) (prX : cX.W →ₗ[ℂ] SmT MX →ₗ[ℂ] ℂ), cX.Is ∧ (∀ i, (cV i).Is) ∧ IsDualPair θ MX cX prX ∧ Seed.PrIso MX cX prX ∧ Seed.BrgL (famR X I hX U Xg tr) L eG cX cV pl Sb Bd plI SF ∧ BrgStdR X I hX U Xg tr L cX (fun t φ => Bd.jR t φ) ∧ ∀ i, BrgStdV X I hX U Xg tr L i (cV i) fun t φ => Bd.jL i t φ := by
  first | exact @GlobalTheory.Mem.R3.BrgRead.exists_brgL | exact GlobalTheory.Mem.R3.BrgRead.exists_brgL | (intros; apply GlobalTheory.Mem.R3.BrgRead.exists_brgL <;> assumption)
end
