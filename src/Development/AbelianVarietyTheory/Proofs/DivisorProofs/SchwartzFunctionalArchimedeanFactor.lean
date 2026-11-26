module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledLatticeTranslationInvariant

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledLatticeFourierInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledLatticeCharacterTrivial
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledLatticeCharacterTrivial
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct Classical

namespace GlobalTheory.TraceDualChar

theorem psi_trivial_on_scaledInt : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ] (a : F), a ≠ 0 →
    ∀ b : κ → F, (∀ ξ : κ → F, (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ GlobalTheory.EvAdm.scaledInt F κ a →
        ∃ k : ℤ, Algebra.trace ℚ F (∑ i, ξ i * b i) = k) →
    ∀ z ∈ GlobalTheory.EvAdm.scaledInt F κ a,
      ψ (((0 : InfiniteAdeleRing F), ∑ i, z i * algebraMap F (FiniteAdeleRing (𝓞 F) F) (b i)) : AF F) = 1 := by
  intro F _ _ ψ hψ κ _ a _ b hb z hz

  have hrat : ∀ ξ : κ → F, (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ GlobalTheory.EvAdm.scaledInt F κ a →
      ψ (((0 : InfiniteAdeleRing F), ∑ i, algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i) *
        algebraMap F (FiniteAdeleRing (𝓞 F) F) (b i)) : AF F) = 1 := by
    intro ξ hξ
    obtain ⟨k, hk⟩ := hb ξ hξ
    set q : F := ∑ i, ξ i * b i with hq
    have e1 : (∑ i, algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i) * algebraMap F (FiniteAdeleRing (𝓞 F) F) (b i)) =
        algebraMap F (FiniteAdeleRing (𝓞 F) F) q := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hq, map_sum]; simp only [map_mul]
    rw [e1]
    set y : AF F := (((algebraMap F (InfiniteAdeleRing F) q), (0 : FiniteAdeleRing (𝓞 F) F)) : AF F) with hy
    have e2 : (show AF F from ((0 : InfiniteAdeleRing F), algebraMap F (FiniteAdeleRing (𝓞 F) F) q)) + y =
        algebraMap F (AF F) q := by
      rw [hy]
      show (show AF F from ((0 : InfiniteAdeleRing F) + algebraMap F (InfiniteAdeleRing F) q,
        algebraMap F (FiniteAdeleRing (𝓞 F) F) q + 0)) = algebraMap F (AF F) q
      rw [zero_add, add_zero]
      rfl
    have hAt : At (evI F) y := by
      intro u hu
      have hu1 : u.1 = 0 := by
        have : InfiniteAdeleRing.ringEquiv_mixedSpace F u.1 = 0 := hu
        exact (map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective).1 this
      show (u.1 * algebraMap F (InfiniteAdeleRing F) q, u.2 * 0) = ((0 : InfiniteAdeleRing F), (0 : FiniteAdeleRing (𝓞 F) F))
      rw [hu1, zero_mul, mul_zero]
    have hev : evI F y = mixedEmbedding F q := by
      rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
      rfl
    have hyv : ψ y = 1 := by
      rw [hψ.2.2 y hAt, hev, GlobalTheory.PsiNontriv.trace_mixedEmbedding, hk]
      rw [show ((((k : ℚ) : ℝ) : ℂ)) = (k : ℂ) by push_cast; ring]
      rw [show -(2 * (Real.pi : ℂ) * Complex.I) * (k : ℂ) = ((-k : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I (-k)
    have h3 := congrArg ψ e2
    rw [AddChar.map_add_eq_mul, hyv, mul_one, hψ.2.1] at h3
    exact h3

  by_contra hne
  set G : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ := fun z =>
    ψ (((0 : InfiniteAdeleRing F), ∑ i, z i * algebraMap F (FiniteAdeleRing (𝓞 F) F) (b i)) : AF F) with hG
  have hGc : Continuous G := by
    refine hψ.1.comp ?_
    refine Continuous.prodMk continuous_const ?_
    exact continuous_finsetSum _ fun i _ => (continuous_apply i).mul continuous_const
  have hU : IsOpen ((GlobalTheory.EvAdm.scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)) ∩ G ⁻¹' {1}ᶜ) :=
    (GlobalTheory.EvAdm.isOpen_scaledInt a).inter (isOpen_compl_singleton.preimage hGc)
  have hd : DenseRange (fun ξ : κ → F => fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) :=
    DenseRange.piMap fun _ => GlobalTheory.AdeleCharTwist.denseRange_fin
  obtain ⟨ξ, hξ1, hξ2⟩ := hd.exists_mem_open hU ⟨z, hz, hne⟩
  exact hξ2 (hrat ξ hξ1)

end GlobalTheory.TraceDualChar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledLatticeCharacterTrivialStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scaled_lattice_character_trivial : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ] (a : F), a ≠ 0 →
    ∀ b : κ → F, (∀ ξ : κ → F, (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ GlobalTheory.EvAdm.scaledInt F κ a →
        ∃ k : ℤ, Algebra.trace ℚ F (∑ i, ξ i * b i) = k) →
    ∀ z ∈ GlobalTheory.EvAdm.scaledInt F κ a,
      ψ (((0 : InfiniteAdeleRing F), ∑ i, z i * algebraMap F (FiniteAdeleRing (𝓞 F) F) (b i)) : AF F) = 1 := by
  first | exact @GlobalTheory.TraceDualChar.psi_trivial_on_scaledInt | exact GlobalTheory.TraceDualChar.psi_trivial_on_scaledInt | (intros; apply GlobalTheory.TraceDualChar.psi_trivial_on_scaledInt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledLatticeFourierInvariant
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct Classical
namespace GlobalTheory.SchrCharPure

theorem main : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ] (a : F), a ≠ 0 →
    ∀ b : κ → F, (∀ ξ : κ → F, (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ GlobalTheory.EvAdm.scaledInt F κ a →
        ∃ k : ℤ, Algebra.trace ℚ F (∑ i, ξ i * b i) = k) →
    ∀ f f' : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      (∀ x, f' x = Complex.exp (-(2 * Real.pi * Complex.I) *
          ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * mixedEmbedding F (b i)) : ℝ) : ℂ)) * f x) →
      schr ψ (0, fun i => algebraMap F (AF F) (b i))
          (pureA F f ((GlobalTheory.EvAdm.scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)).indicator (fun _ => (1 : ℂ)))) =
        pureA F f' ((GlobalTheory.EvAdm.scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)).indicator (fun _ => (1 : ℂ))) := by
  intro F _ _ ψ hψ κ _ a ha b hb f f' hf'
  funext x
  simp only [schr, pureA, add_zero, zero_dotProduct, mul_zero]
  rw [hf']
  by_cases hz : (fun i => (x i).2) ∈ GlobalTheory.EvAdm.scaledInt F κ a
  · rw [Set.indicator_of_mem (s := (GlobalTheory.EvAdm.scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F))) hz]
    set u : AF F := x ⬝ᵥ fun i => algebraMap F (AF F) (b i) with hu
    have hsplit : u = (show AF F from (u.1, 0)) + (show AF F from (0, u.2)) := by
      show u = ((u.1 + 0, 0 + u.2) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F)
      rw [add_zero, zero_add]
      rfl
    have hu2 : u.2 = ∑ i, (x i).2 * algebraMap F (FiniteAdeleRing (𝓞 F) F) (b i) := by
      have e : u.2 = (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) u := rfl
      rw [e, hu, dotProduct]
      exact (map_sum (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))
        (fun i => x i * algebraMap F (AF F) (b i)) Finset.univ).trans
        (Finset.sum_congr rfl fun i _ => rfl)
    have hu1 : u.1 = ∑ i, (x i).1 * algebraMap F (InfiniteAdeleRing F) (b i) := by
      have e : u.1 = (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) u := rfl
      rw [e, hu, dotProduct]
      exact (map_sum (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))
        (fun i => x i * algebraMap F (AF F) (b i)) Finset.univ).trans
        (Finset.sum_congr rfl fun i _ => rfl)
    have hfin : ψ (show AF F from (0, u.2)) = 1 := by
      have := GlobalTheory.T.scaled_lattice_character_trivial F ψ hψ κ a ha b hb _ hz
      rw [← hu2] at this
      exact this
    have hAt : At (evI F) (show AF F from (u.1, 0)) := by
      intro w hw
      have h1 : w.1 = 0 := by
        have : InfiniteAdeleRing.ringEquiv_mixedSpace F w.1 = 0 := hw
        exact (map_eq_zero_iff _ (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective).mp this
      show ((w.1 * u.1, w.2 * 0) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F) = (0, 0)
      rw [h1, zero_mul, mul_zero]
    have hinf := hψ.2.2 _ hAt
    have hev : evI F (show AF F from (u.1, 0)) = ∑ i, InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1 * mixedEmbedding F (b i) := by
      show InfiniteAdeleRing.ringEquiv_mixedSpace F u.1 = _
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hu1, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp, map_mul]
    rw [hsplit, AddChar.map_add_eq_mul, hfin, hinf, hev]
    ring
  · rw [Set.indicator_of_notMem (s := (GlobalTheory.EvAdm.scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F))) hz]
    simp

end GlobalTheory.SchrCharPure
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledLatticeFourierInvariantStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scaled_lattice_fourier_invariant : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ] (a : F), a ≠ 0 →
    ∀ b : κ → F, (∀ ξ : κ → F, (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ GlobalTheory.EvAdm.scaledInt F κ a →
        ∃ k : ℤ, Algebra.trace ℚ F (∑ i, ξ i * b i) = k) →
    ∀ f f' : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      (∀ x, f' x = Complex.exp (-(2 * Real.pi * Complex.I) *
          ((Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * mixedEmbedding F (b i)) : ℝ) : ℂ)) * f x) →
      schr ψ (0, fun i => algebraMap F (AF F) (b i))
          (pureA F f ((GlobalTheory.EvAdm.scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)).indicator (fun _ => (1 : ℂ)))) =
        pureA F f' ((GlobalTheory.EvAdm.scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)).indicator (fun _ => (1 : ℂ))) := by
  first | exact @GlobalTheory.SchrCharPure.main | exact GlobalTheory.SchrCharPure.main | (intros; apply GlobalTheory.SchrCharPure.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledIndicatorCosetSum
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledIndicatorCosetSum
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct Classical

noncomputable section

namespace GlobalTheory.EvAdm.CosetSum

variable {F : Type} [Field F] [NumberField F]

theorem finAdele_algebraMap_apply (x : F) (v : HeightOneSpectrum (𝓞 F)) :
    (algebraMap F (FiniteAdeleRing (𝓞 F) F) x) v = algebraMap F (v.adicCompletion F) x := rfl

theorem algebraMap_mem_iff (v : HeightOneSpectrum (𝓞 F)) (x : F) :
    algebraMap F (v.adicCompletion F) x ∈ v.adicCompletionIntegers F ↔ v.valuation F x ≤ 1 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  exact iff_of_eq (congrArg (· ≤ 1) (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x))

theorem int_mem (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F) :
    algebraMap F (v.adicCompletion F) (x : F) ∈ v.adicCompletionIntegers F := by
  rw [algebraMap_mem_iff]
  exact v.valuation_le_one x

variable {κ : Type}

theorem mul_int_mem {b : F} (hb : b ≠ 0) (x : κ → 𝓞 F) :
    (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (b * (x i : F))) ∈ scaledInt F κ b := by
  rw [mem_scaledInt]
  intro i v
  rw [finAdele_algebraMap_apply, map_mul, ← mul_assoc,
    inv_mul_cancel₀ ((map_ne_zero (algebraMap F (v.adicCompletion F))).2 hb), one_mul]
  exact int_mem v (x i)

theorem scaledInt_mul_le {a : F} (ha : a ≠ 0) {m : 𝓞 F} (hm : m ≠ 0) :
    scaledInt F κ (a * m) ≤ scaledInt F κ a := by
  intro z hz
  rw [mem_scaledInt] at hz ⊢
  intro i v
  have hm' : algebraMap F (v.adicCompletion F) (m : F) ≠ 0 :=
    (map_ne_zero _).2 (by exact_mod_cast hm)
  have e : (algebraMap F (v.adicCompletion F) a)⁻¹ * (z i) v =
      algebraMap F (v.adicCompletion F) (m : F) *
        ((algebraMap F (v.adicCompletion F) (a * m))⁻¹ * (z i) v) := by
    set A := algebraMap F (v.adicCompletion F) a
    set M := algebraMap F (v.adicCompletion F) (m : F)
    rw [map_mul, mul_inv, ← mul_assoc, ← mul_assoc, mul_comm M A⁻¹, mul_assoc A⁻¹ M M⁻¹,
      mul_inv_cancel₀ hm', mul_one]
  rw [e]
  exact mul_mem (int_mem v m) (hz i v)

theorem rat_mem {b : F} (hb : b ≠ 0) (ξ : κ → F)
    (h : (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ scaledInt F κ b) (i : κ) :
    ∃ x : 𝓞 F, (x : F) = ξ i / b := by
  rw [mem_scaledInt] at h
  have hv : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F (ξ i / b) ≤ 1 := fun v => by
    rw [← algebraMap_mem_iff, div_eq_inv_mul, map_mul, map_inv₀]
    exact h i v
  obtain ⟨x, hx⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F (ξ i / b) hv
  exact ⟨x, hx⟩

theorem indicator_scaledInt_eq_sum : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F), a ≠ 0 →
    ∀ m : 𝓞 F, m ≠ 0 →
    ∃ R : Finset (κ → F), (GlobalTheory.EvAdm.scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)).indicator (fun _ => (1 : ℂ)) =
      ∑ ξ ∈ R, {y | y - (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ GlobalTheory.EvAdm.scaledInt F κ (a * m)}.indicator
        (fun _ => (1 : ℂ)) := by
  intro F _ _ κ _ a ha m hm
  set I : Ideal (𝓞 F) := Ideal.span {m} with hIdef
  have hI : I ≠ ⊥ := by
    rw [hIdef, Ne, Ideal.span_singleton_eq_bot]; exact hm
  haveI : Finite (𝓞 F ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI
  haveI : Fintype (κ → 𝓞 F ⧸ I) := Fintype.ofFinite _
  let out : 𝓞 F ⧸ I → 𝓞 F := fun q => (Ideal.Quotient.mk_surjective q).choose
  have hout : ∀ q, Ideal.Quotient.mk I (out q) = q := fun q => (Ideal.Quotient.mk_surjective q).choose_spec
  let rep : (κ → 𝓞 F ⧸ I) → (κ → F) := fun c i => a * ((out (c i) : 𝓞 F) : F)
  let ι : (κ → F) → (κ → FiniteAdeleRing (𝓞 F) F) := fun ξ i => algebraMap F _ (ξ i)
  have hrep_inj : Function.Injective rep := by
    intro c c' h
    funext i
    have h1 := congrFun h i
    simp only [rep, mul_right_inj' ha] at h1
    have h2 : out (c i) = out (c' i) := by exact_mod_cast h1
    rw [← hout (c i), ← hout (c' i), h2]
  have hrepS : ∀ c, ι (rep c) ∈ scaledInt F κ a := fun c => mul_int_mem ha (fun i => out (c i))
  have hsub := scaledInt_mul_le (κ := κ) ha hm
  have hm0 : (m : F) ≠ 0 := by exact_mod_cast hm
  have ham : a * (m : F) ≠ 0 := mul_ne_zero ha hm0
  have huniq : ∀ c c' (y : κ → FiniteAdeleRing (𝓞 F) F), y - ι (rep c) ∈ scaledInt F κ (a * m) →
      y - ι (rep c') ∈ scaledInt F κ (a * m) → c = c' := by
    intro c c' y h h'
    have hd : ι (fun i => rep c' i - rep c i) ∈ scaledInt F κ (a * m) := by
      have := sub_mem h h'
      convert this using 1
      funext i
      simp only [ι, Pi.sub_apply, map_sub]
      abel
    funext i
    obtain ⟨z, hz⟩ := rat_mem ham _ hd i
    have h3 : ((out (c' i) - out (c i) : 𝓞 F) : F) = ((z * m : 𝓞 F) : F) := by
      have hz' : (z : F) * (a * m) = rep c' i - rep c i := by rw [hz, div_mul_cancel₀ _ ham]
      simp only [rep] at hz'
      push_cast
      apply mul_left_cancel₀ ha
      linear_combination (-1 : F) * hz'
    have h4 : out (c' i) - out (c i) ∈ I := by
      rw [hIdef, Ideal.mem_span_singleton']
      exact ⟨z, by exact_mod_cast h3.symm⟩
    have h5 := (Ideal.Quotient.eq).2 h4
    rw [hout, hout] at h5
    exact h5.symm
  have hexist : ∀ y ∈ scaledInt F κ a, ∃ c, y - ι (rep c) ∈ scaledInt F κ (a * m) := by
    intro y hy
    have hd : DenseRange ι :=
      DenseRange.piMap (fun _ => GroundTheory.Automorphic.AdelicGLn.denseRange_algebraMap_finiteAdeleRing F)
    have hopen : IsOpen {z | y - z ∈ (scaledInt F κ (a * m) : Set (κ → FiniteAdeleRing (𝓞 F) F))} :=
      (isOpen_scaledInt (a * m)).preimage (continuous_const.sub continuous_id)
    obtain ⟨ξ, hξ⟩ := hd.exists_mem_open hopen ⟨y, by simp [zero_mem]⟩
    have hξ' : y - ι ξ ∈ scaledInt F κ (a * m) := hξ
    have hξa : ι ξ ∈ scaledInt F κ a := by
      have := sub_mem hy (hsub hξ')
      simpa using this
    choose x hx using fun i => rat_mem ha ξ hξa i
    have ht : ∀ i, ∃ t : 𝓞 F, t * m = out (Ideal.Quotient.mk I (x i)) - x i := fun i => by
      have := (Ideal.Quotient.eq).1 (hout (Ideal.Quotient.mk I (x i)))
      exact Ideal.mem_span_singleton'.1 this
    choose t htm using ht
    refine ⟨fun i => Ideal.Quotient.mk I (x i), ?_⟩
    have hF : ∀ i, rep (fun i => Ideal.Quotient.mk I (x i)) i = ξ i + a * m * (t i : F) := fun i => by
      have e1 : ((t i * m : 𝓞 F) : F) = ((out (Ideal.Quotient.mk I (x i)) - x i : 𝓞 F) : F) := by rw [htm i]
      push_cast at e1
      have e2 : ξ i = a * (x i : F) := by rw [hx i]; field_simp
      simp only [rep]
      rw [e2]
      linear_combination (-a) * e1
    have hw : ι (fun i => a * m * (t i : F)) ∈ scaledInt F κ (a * m) := mul_int_mem ham t
    have e : y - ι (rep (fun i => Ideal.Quotient.mk I (x i))) = (y - ι ξ) - ι (fun i => a * m * (t i : F)) := by
      funext i
      simp only [ι, Pi.sub_apply]
      rw [hF i, map_add (f := _)]
      abel
    rw [e]
    exact sub_mem hξ' hw
  refine ⟨Finset.univ.image rep, ?_⟩
  rw [Finset.sum_image (fun c _ c' _ h => hrep_inj h)]
  funext y
  rw [Finset.sum_apply]
  by_cases hy : y ∈ scaledInt F κ a
  · obtain ⟨c0, hc0⟩ := hexist y hy
    rw [Set.indicator_of_mem (by exact hy), Finset.sum_eq_single c0]
    · rw [Set.indicator_of_mem (by exact hc0)]
    · intro c _ hc
      rw [Set.indicator_of_notMem]
      intro h
      exact hc (huniq c c0 y h hc0)
    · intro h
      exact absurd (Finset.mem_univ c0) h
  · rw [Set.indicator_of_notMem (by exact hy)]
    symm
    apply Finset.sum_eq_zero
    intro c _
    rw [Set.indicator_of_notMem]
    intro h
    apply hy
    rw [show y = (y - ι (rep c)) + ι (rep c) from (sub_add_cancel _ _).symm]
    exact add_mem (hsub h) (hrepS c)

end GlobalTheory.EvAdm.CosetSum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledIndicatorCosetSumStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scaled_indicator_coset_sum : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F), a ≠ 0 → ∀ m : 𝓞 F, m ≠ 0 →
    ∃ R : Finset (κ → F), (GlobalTheory.EvAdm.scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)).indicator (fun _ => (1 : ℂ)) =
      ∑ ξ ∈ R, {y | y - (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ GlobalTheory.EvAdm.scaledInt F κ (a * m)}.indicator
        (fun _ => (1 : ℂ)) := by
  first | exact @GlobalTheory.EvAdm.CosetSum.indicator_scaledInt_eq_sum | exact GlobalTheory.EvAdm.CosetSum.indicator_scaledInt_eq_sum | (intros; apply GlobalTheory.EvAdm.CosetSum.indicator_scaledInt_eq_sum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdeleApproxScaled
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdeleApproxScaled
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct Classical

namespace GlobalTheory.EvAdm

theorem exists_rational_rep_scaledInt : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F), a ≠ 0 →
    ∀ r : κ → FiniteAdeleRing (𝓞 F) F, ∃ ξ : κ → F,
      r - (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ GlobalTheory.EvAdm.scaledInt F κ a := by
  intro F _ _ κ _ a _ r
  have hd : DenseRange (Pi.map fun (_ : κ) => algebraMap F (FiniteAdeleRing (𝓞 F) F)) :=
    DenseRange.piMap fun _ => PI.UnipApproxD.IntegersDenseFiniteAdeles.denseRange (R := 𝓞 F) (K := F)
  have hop : IsOpen {y : κ → FiniteAdeleRing (𝓞 F) F | r - y ∈ GlobalTheory.EvAdm.scaledInt F κ a} :=
    (GlobalTheory.EvAdm.isOpen_scaledInt a).preimage (continuous_const.sub continuous_id)
  have hr : r ∈ {y : κ → FiniteAdeleRing (𝓞 F) F | r - y ∈ GlobalTheory.EvAdm.scaledInt F κ a} := by
    show r - r ∈ GlobalTheory.EvAdm.scaledInt F κ a
    rw [sub_self]
    exact zero_mem _
  obtain ⟨ξ, hξ⟩ := hd.exists_mem_open hop ⟨r, hr⟩
  exact ⟨ξ, hξ⟩

end GlobalTheory.EvAdm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdeleApproxScaledStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_adele_approx_scaled : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F), a ≠ 0 →
    ∀ r : κ → FiniteAdeleRing (𝓞 F) F, ∃ ξ : κ → F,
      r - (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ GlobalTheory.EvAdm.scaledInt F κ a := by
  exact @GlobalTheory.EvAdm.exists_rational_rep_scaledInt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSumIndicatorNonzero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSumIndicatorNonzero
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct Classical

noncomputable section

namespace GlobalTheory.ThetaScaledNe

theorem normAtPlace_le_norm {F : Type} [Field F] [NumberField F] (w : InfinitePlace F)
    (y : mixedEmbedding.mixedSpace F) : mixedEmbedding.normAtPlace w y ≤ ‖y‖ := by
  by_cases hw : w.IsReal
  · rw [mixedEmbedding.normAtPlace_apply_of_isReal hw]
    exact (norm_le_pi_norm _ _).trans (norm_fst_le _)
  · have hc : w.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hw
    rw [mixedEmbedding.normAtPlace_apply_of_isComplex hc]
    exact (norm_le_pi_norm _ _).trans (norm_snd_le _)

theorem one_le_norm_mixedEmbedding {F : Type} [Field F] [NumberField F] {y : 𝓞 F} (hy : y ≠ 0) :
    1 ≤ ‖mixedEmbedding F (y : F)‖ := by
  by_contra h
  push_neg at h
  have hlt : ∀ z : InfinitePlace F, z (y : F) < 1 := fun z => by
    have := normAtPlace_le_norm z (mixedEmbedding F (y : F))
    rw [mixedEmbedding.normAtPlace_apply] at this
    exact this.trans_lt h
  let w : InfinitePlace F := Classical.arbitrary _
  have := InfinitePlace.one_le_of_lt_one (w := w) hy (fun z _ => hlt z)
  exact absurd (hlt w) (not_lt.mpr this)

theorem exists_int_of_mem_scaledInt {F : Type} [Field F] [NumberField F] {κ : Type} {a : F} (ha : a ≠ 0)
    {ξ : κ → F} (h : (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ GlobalTheory.EvAdm.scaledInt F κ a)
    (i : κ) : ∃ y : 𝓞 F, ξ i = a * (y : F) := by
  have hv : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F (a⁻¹ * ξ i) ≤ 1 := fun v => by
    have h1 := h i v
    have e : (algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) v = algebraMap F (v.adicCompletion F) (ξ i) := rfl
    rw [e, HeightOneSpectrum.mem_adicCompletionIntegers, Valuation.map_mul, map_inv₀] at h1
    rw [Valuation.map_mul, map_inv₀]
    have e1 : Valued.v (algebraMap F (v.adicCompletion F) a) = v.valuation F a :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v a
    have e2 : Valued.v (algebraMap F (v.adicCompletion F) (ξ i)) = v.valuation F (ξ i) :=
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (ξ i)
    rw [e1, e2] at h1
    exact h1
  obtain ⟨y, hy⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F _ hv
  refine ⟨y, ?_⟩
  have hy' : (y : F) = a⁻¹ * ξ i := hy
  rw [hy', mul_inv_cancel_left₀ ha]

theorem exists_thetaSum_scaledInt_ne_zero : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F), a ≠ 0 →
    ∃ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      thetaSum F (pureA F f ((GlobalTheory.EvAdm.scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)).indicator
        (fun _ => (1 : ℂ)))) ≠ 0 := by
  intro F _ _ κ _ a ha
  let V := κ → mixedEmbedding.mixedSpace F
  set c : mixedEmbedding.mixedSpace F := mixedEmbedding F a⁻¹ with hc
  set ε : ℝ := 1 / (‖c‖ + 1) with hε
  have hε0 : 0 < ε := by positivity
  let b : ContDiffBump (0 : V) := ⟨ε / 2, ε, half_pos hε0, half_lt_self hε0⟩
  have h1 : HasCompactSupport (fun x => ((b x : ℝ) : ℂ)) :=
    b.hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
  let f : SchwartzMap V ℂ := h1.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff)
  have hf : ∀ x, f x = ((b x : ℝ) : ℂ) := fun x => rfl
  refine ⟨f, ?_⟩
  set g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ :=
    (GlobalTheory.EvAdm.scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)).indicator (fun _ => (1 : ℂ)) with hg
  have hzero : ∀ ξ : κ → F, ξ ≠ 0 → pureA F f g (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) = 0 := by
    intro ξ hξ
    rw [pureA_algebraMap]
    by_cases hm : (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ GlobalTheory.EvAdm.scaledInt F κ a
    · refine mul_eq_zero_of_left ?_ _
      obtain ⟨i, hi⟩ : ∃ i, ξ i ≠ 0 := by
        by_contra h; push_neg at h; exact hξ (funext h)
      obtain ⟨y, hy⟩ := exists_int_of_mem_scaledInt ha hm i
      have hy0 : y ≠ 0 := by
        rintro rfl
        exact hi (by simpa using hy)
      have hn1 := one_le_norm_mixedEmbedding hy0
      have e : mixedEmbedding F (y : F) = c * mixedEmbedding F (ξ i) := by
        rw [hc, ← map_mul, hy, inv_mul_cancel_left₀ ha]
      have h2 : ‖mixedEmbedding F (ξ i)‖ ≤ ‖(fun j => mixedEmbedding F (ξ j) : V)‖ :=
        norm_le_pi_norm (fun j => mixedEmbedding F (ξ j)) i
      have h3 : 1 ≤ ‖c‖ * ‖(fun j => mixedEmbedding F (ξ j) : V)‖ := by
        rw [e] at hn1
        exact hn1.trans ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left h2 (norm_nonneg _)))
      rw [hf, b.zero_of_le_dist, Complex.ofReal_zero]
      show ε ≤ dist (fun j => mixedEmbedding F (ξ j) : V) 0
      rw [dist_zero_right, hε, div_le_iff₀ (by positivity)]
      nlinarith [norm_nonneg c, norm_nonneg (fun j => mixedEmbedding F (ξ j) : V)]
    · refine mul_eq_zero_of_right _ ?_
      rw [hg]
      exact Set.indicator_of_notMem hm _
  have h0 : pureA F f g (fun i => algebraMap F (AdeleRing (𝓞 F) F) ((0 : κ → F) i)) = 1 := by
    rw [pureA_algebraMap]
    have hx : (fun i : κ => mixedEmbedding F ((0 : κ → F) i)) = 0 := by
      funext i; exact map_zero _
    have hm : (fun i : κ => algebraMap F (FiniteAdeleRing (𝓞 F) F) ((0 : κ → F) i)) ∈
        GlobalTheory.EvAdm.scaledInt F κ a := by
      have e : (fun i : κ => algebraMap F (FiniteAdeleRing (𝓞 F) F) ((0 : κ → F) i)) = 0 := by
        funext i; exact map_zero _
      rw [e]; exact zero_mem _
    rw [hx, hf, b.one_of_mem_closedBall (Metric.mem_closedBall_self (half_pos hε0).le), hg,
      Set.indicator_of_mem hm]
    simp
  show (∑' ξ : κ → F, pureA F f g (fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i))) ≠ 0
  rw [tsum_eq_single 0 hzero, h0]
  exact one_ne_zero

end GlobalTheory.ThetaScaledNe

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSumIndicatorNonzeroStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_sum_indicator_nonzero : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F), a ≠ 0 →
    ∃ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      thetaSum F (pureA F f ((GlobalTheory.EvAdm.scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)).indicator
        (fun _ => (1 : ℂ)))) ≠ 0 := by
  first | exact @GlobalTheory.ThetaScaledNe.exists_thetaSum_scaledInt_ne_zero | exact GlobalTheory.ThetaScaledNe.exists_thetaSum_scaledInt_ne_zero | (intros; apply GlobalTheory.ThetaScaledNe.exists_thetaSum_scaledInt_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFunctionalArchimedeanFactor
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct Classical

noncomputable section

namespace GlobalTheory.ThetaFunctionalUnique

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]


variable (F κ) in
abbrev boxInd (a : F) : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ :=
  (GlobalTheory.EvAdm.scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)).indicator (fun _ => (1 : ℂ))


variable (F κ) in
abbrev cosInd (a : F) (r : κ → FiniteAdeleRing (𝓞 F) F) : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ :=
  {y | y - r ∈ GlobalTheory.EvAdm.scaledInt F κ a}.indicator (fun _ => (1 : ℂ))

theorem inf_rat (q : F) :
    InfiniteAdeleRing.ringEquiv_mixedSpace F (algebraMap F (AF F) q).1 = mixedEmbedding F q := by
  simp [InfiniteAdeleRing.ringEquiv_mixedSpace]
  rfl

theorem boxInd_mem_SB {a : F} (ha : a ≠ 0) : boxInd F κ a ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) := by
  have h := GlobalTheory.T.scaled_coset_indicator_schwartz F κ a ha 0
  convert h using 2
  ext y
  simp

theorem pure_mem (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) : pureA F f g ∈ schA F κ :=
  Submodule.subset_span ⟨f, g, hg, rfl⟩

theorem schr_trans (ψ : AddChar (AF F) ℂ) (ξ : κ → F) (Φ : (κ → AF F) → ℂ) :
    schr ψ ((fun i => algebraMap F (AF F) (ξ i)), (fun i => algebraMap F (AF F) ((0 : κ → F) i))) Φ =
      fun x => Φ (x + fun i => algebraMap F (AF F) (ξ i)) := by
  funext x
  simp [schr, dotProduct]

theorem pure_shift (f f' : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (ξ : κ → F)
    (g g' : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (hf : ∀ x, f' x = f (x + fun i => mixedEmbedding F (ξ i)))
    (hg : ∀ y, g' y = g (y + fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i))) :
    (fun x => pureA F f g (x + fun i => algebraMap F (AF F) (ξ i))) = pureA F f' g' := by
  funext x
  simp only [pureA, hf, hg]
  congr 2
  funext i
  show InfiniteAdeleRing.ringEquiv_mixedSpace F ((x i + algebraMap F (AF F) (ξ i)).1) =
    InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1 + mixedEmbedding F (ξ i)
  rw [← inf_rat]
  exact map_add _ _ _

theorem L_shift (ψ : AddChar (AF F) ℂ) (L : ((κ → AF F) → ℂ) → ℂ)
    (hinv : ∀ a b : κ → F, ∀ Φ ∈ schA F κ,
      L (schr ψ ((fun i => algebraMap F (AF F) (a i)), (fun i => algebraMap F (AF F) (b i))) Φ) = L Φ)
    (ξ : κ → F) {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    L (fun x => Φ (x + fun i => algebraMap F (AF F) (ξ i))) = L Φ := by
  have h := hinv ξ 0 Φ hΦ
  rwa [schr_trans] at h

theorem theta_shift (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (ξ : κ → F) (Φ : (κ → AF F) → ℂ) :
    thetaSum F (fun x => Φ (x + fun i => algebraMap F (AF F) (ξ i))) = thetaSum F Φ := by
  have h := GlobalTheory.ThetaQuasiRat.thetaSum_schr_rat F ψ hψ.2.1 ξ 0 Φ
  rwa [schr_trans] at h

theorem box_eq (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (L : ((κ → AF F) → ℂ) → ℂ)
    (hinv : ∀ a b : κ → F, ∀ Φ ∈ schA F κ,
      L (schr ψ ((fun i => algebraMap F (AF F) (a i)), (fun i => algebraMap F (AF F) (b i))) Φ) = L Φ)
    {a : F} (ha : a ≠ 0) (T : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] ℂ)
    (hT : ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, L (pureA F f (boxInd F κ a)) = T f) :
    ∃ c : ℂ, ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, L (pureA F f (boxInd F κ a)) = c * thetaSum F (pureA F f (boxInd F κ a)) := by
  obtain ⟨c, hc⟩ := GlobalTheory.T.scaled_lattice_translation_invariant F κ a ha T (fun ξ hξ f f' hf => by
      rw [← hT, ← hT]
      have e := pure_shift f f' ξ (boxInd F κ a) (boxInd F κ a) hf (fun y => by
        simp only [Set.indicator_apply, SetLike.mem_coe, AddSubgroup.add_mem_cancel_right _ hξ])
      rw [← e]
      exact L_shift ψ L hinv ξ (pure_mem f (boxInd_mem_SB ha)))
    (fun b hb f f' hf => by
      rw [← hT, ← hT, ← GlobalTheory.T.scaled_lattice_fourier_invariant F ψ hψ κ a ha b hb f f' hf]
      have h := hinv 0 b _ (pure_mem f (boxInd_mem_SB ha))
      have e0 : (fun i => algebraMap F (AF F) ((0 : κ → F) i)) = 0 := by funext i; simp
      rw [e0] at h
      exact h)
  refine ⟨c, fun f => ?_⟩
  rw [hT, hc f]
  congr 1
  unfold thetaSum
  refine tsum_congr fun ξ => ?_
  have e1 : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F
      ((fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) i).1) = fun i => mixedEmbedding F (ξ i) := by
    funext i; exact inf_rat (ξ i)
  have e2 : (fun i => ((fun i => algebraMap F (AdeleRing (𝓞 F) F) (ξ i)) i).2) =
      fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i) := rfl
  simp only [pureA, e1, e2, Set.indicator_apply, SetLike.mem_coe, Set.mem_setOf_eq]
  split_ifs <;> simp

end GlobalTheory.ThetaFunctionalUnique

namespace GlobalTheory.ThetaFunctionalUnique

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem cosInd_mem_SB {a : F} (ha : a ≠ 0) (r : κ → FiniteAdeleRing (𝓞 F) F) :
    cosInd F κ a r ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) :=
  GlobalTheory.T.scaled_coset_indicator_schwartz F κ a ha r

theorem cos_eq (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (L : ((κ → AF F) → ℂ) → ℂ)
    (hinv : ∀ a b : κ → F, ∀ Φ ∈ schA F κ,
      L (schr ψ ((fun i => algebraMap F (AF F) (a i)), (fun i => algebraMap F (AF F) (b i))) Φ) = L Φ)
    {a : F} (ha : a ≠ 0) {c : ℂ}
    (hc : ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      L (pureA F f (boxInd F κ a)) = c * thetaSum F (pureA F f (boxInd F κ a)))
    (r : κ → FiniteAdeleRing (𝓞 F) F) (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) :
    L (pureA F f (cosInd F κ a r)) = c * thetaSum F (pureA F f (cosInd F κ a r)) := by
  obtain ⟨ξ, hξ⟩ := GlobalTheory.T.finite_adele_approx_scaled F κ a ha r
  have hs : {y | y - r ∈ GlobalTheory.EvAdm.scaledInt F κ a} =
      {y | y - (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) ∈ GlobalTheory.EvAdm.scaledInt F κ a} := by
    ext y
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h
      have := add_mem h hξ
      rwa [sub_add_sub_cancel] at this
    · intro h
      have := sub_mem h hξ
      rwa [sub_sub_sub_cancel_right] at this
  have hr : cosInd F κ a r = cosInd F κ a (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)) := by
    simp only [cosInd, hs]
  rw [hr]
  set f' := SchwartzMap.compSubConstCLM ℂ (-(fun i => mixedEmbedding F (ξ i))) f with hf'def
  have hf' : ∀ x, f' x = f (x + fun i => mixedEmbedding F (ξ i)) := by
    intro x
    simp [hf'def, SchwartzMap.compSubConstCLM_apply, sub_neg_eq_add]
  have e := pure_shift f f' ξ (cosInd F κ a (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)))
    (boxInd F κ a) hf' (fun y => by simp only [Set.indicator_apply, SetLike.mem_coe, Set.mem_setOf_eq, add_sub_cancel_right])
  have hm := pure_mem f (cosInd_mem_SB ha (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i)))
  rw [← L_shift ψ L hinv ξ hm, ← theta_shift ψ hψ ξ, e, hc f']

theorem L_sum (L : ((κ → AF F) → ℂ) → ℂ) (hadd : ∀ Φ ∈ schA F κ, ∀ Ψ ∈ schA F κ, L (Φ + Ψ) = L Φ + L Ψ)
    (hsmul : ∀ (c : ℂ), ∀ Φ ∈ schA F κ, L (c • Φ) = c * L Φ) {ι : Type} (s : Finset ι)
    (Φ : ι → (κ → AF F) → ℂ) (hΦ : ∀ j ∈ s, Φ j ∈ schA F κ) : L (∑ j ∈ s, Φ j) = ∑ j ∈ s, L (Φ j) := by
  have hL0 : L 0 = 0 := by
    have h := hsmul 0 0 (zero_mem _)
    simpa using h
  induction s using Finset.induction_on with
  | empty => simpa using hL0
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj,
      hadd _ (hΦ j (Finset.mem_insert_self _ _)) _ (Submodule.sum_mem _ fun k hk => hΦ k (Finset.mem_insert_of_mem hk)),
      ih fun k hk => hΦ k (Finset.mem_insert_of_mem hk)]

theorem theta_sum {ι : Type} (s : Finset ι) (Φ : ι → (κ → AF F) → ℂ) (hΦ : ∀ j ∈ s, Φ j ∈ schA F κ) :
    thetaSum F (∑ j ∈ s, Φ j) = ∑ j ∈ s, thetaSum F (Φ j) := by
  induction s using Finset.induction_on with
  | empty => simp [thetaSum]
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj,
      GlobalTheory.WeilM.thetaSum_add F (hΦ j (Finset.mem_insert_self _ _))
        (Submodule.sum_mem _ fun k hk => hΦ k (Finset.mem_insert_of_mem hk)),
      ih fun k hk => hΦ k (Finset.mem_insert_of_mem hk)]

theorem pure_sum (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) {ι : Type} (s : Finset ι)
    (w : ι → ℂ) (g : ι → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    pureA F f (∑ j ∈ s, w j • g j) = ∑ j ∈ s, w j • pureA F f (g j) := by
  funext x
  simp only [pureA, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem const_mul (L : ((κ → AF F) → ℂ) → ℂ) (hadd : ∀ Φ ∈ schA F κ, ∀ Ψ ∈ schA F κ, L (Φ + Ψ) = L Φ + L Ψ)
    (hsmul : ∀ (c : ℂ), ∀ Φ ∈ schA F κ, L (c • Φ) = c * L Φ) (c : F → ℂ)
    (hc : ∀ a : F, a ≠ 0 → ∀ (r : κ → FiniteAdeleRing (𝓞 F) F) (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ),
      L (pureA F f (cosInd F κ a r)) = c a * thetaSum F (pureA F f (cosInd F κ a r)))
    {a : F} (ha : a ≠ 0) (m : 𝓞 F) (hm : m ≠ 0) : c a = c (a * m) := by
  obtain ⟨R, hR⟩ := GlobalTheory.T.scaled_indicator_coset_sum F κ a ha m hm
  obtain ⟨f, hf⟩ := GlobalTheory.T.theta_sum_indicator_nonzero F κ a ha
  have ham : a * (m : F) ≠ 0 := mul_ne_zero ha (by simpa using hm)
  have hb : boxInd F κ a = cosInd F κ a 0 := by
    unfold boxInd cosInd
    congr 1
    ext y
    simp
  have hsplit : pureA F f (boxInd F κ a) = ∑ ξ ∈ R, (1 : ℂ) •
      pureA F f (cosInd F κ (a * m) (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i))) := by
    rw [← pure_sum]
    congr 1
    rw [show boxInd F κ a = _ from hR]
    simp
  have hmem : ∀ ξ ∈ R, (1 : ℂ) •
      pureA F f (cosInd F κ (a * m) (fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ i))) ∈ schA F κ :=
    fun ξ _ => Submodule.smul_mem _ _ (pure_mem f (cosInd_mem_SB ham _))
  have h1 := hc a ha 0 f
  rw [← hb] at h1
  have h2 : L (pureA F f (boxInd F κ a)) = c (a * m) * thetaSum F (pureA F f (boxInd F κ a)) := by
    rw [hsplit, L_sum L hadd hsmul R _ hmem, theta_sum R _ hmem, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    rw [one_smul, hc _ ham]
  exact mul_right_cancel₀ hf (h1.symm.trans h2)

end GlobalTheory.ThetaFunctionalUnique

namespace GlobalTheory.ThetaFunctionalUnique

theorem main : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    (L : ((κ → AF F) → ℂ) → ℂ),
    (∀ Φ ∈ schA F κ, ∀ Ψ ∈ schA F κ, L (Φ + Ψ) = L Φ + L Ψ) →
    (∀ (c : ℂ), ∀ Φ ∈ schA F κ, L (c • Φ) = c * L Φ) →
    (∀ g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F), ∃ T : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] ℂ,
      ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, L (pureA F f g) = T f) →
    (∀ a b : κ → F, ∀ Φ ∈ schA F κ,
      L (schr ψ ((fun i => algebraMap F (AF F) (a i)), (fun i => algebraMap F (AF F) (b i))) Φ) = L Φ) →
    ∃ c : ℂ, ∀ Φ ∈ schA F κ, L Φ = c * thetaSum F Φ := by
  intro F _ _ ψ hψ κ _ L hadd hsmul hadm hinv
  have hbox : ∀ a : F, ∃ c : ℂ, a ≠ 0 → ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ,
      L (pureA F f (boxInd F κ a)) = c * thetaSum F (pureA F f (boxInd F κ a)) := by
    intro a
    by_cases ha : a = 0
    · exact ⟨0, fun h => absurd ha h⟩
    obtain ⟨T, hT⟩ := hadm _ (boxInd_mem_SB ha)
    obtain ⟨c, hc⟩ := box_eq ψ hψ L hinv ha T hT
    exact ⟨c, fun _ => hc⟩
  choose c hc using hbox
  have hcos : ∀ a : F, a ≠ 0 → ∀ (r : κ → FiniteAdeleRing (𝓞 F) F) (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ),
      L (pureA F f (cosInd F κ a r)) = c a * thetaSum F (pureA F f (cosInd F κ a r)) :=
    fun a ha r f => cos_eq ψ hψ L hinv ha (hc a ha) r f
  have hall : ∀ a : F, a ≠ 0 → c a = c 1 := by
    intro a ha
    obtain ⟨p, q, hq, hpq⟩ := IsFractionRing.div_surjective (A := 𝓞 F) a
    have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
    have hqF : (algebraMap (𝓞 F) F q) ≠ 0 := by simpa using hq0
    have hp0 : p ≠ 0 := by
      rintro rfl
      apply ha
      rw [← hpq]
      simp
    have e : a * (q : F) = 1 * (p : F) := by
      rw [← hpq]
      have : (algebraMap (𝓞 F) F q) = (q : F) := rfl
      have : (algebraMap (𝓞 F) F p) = (p : F) := rfl
      field_simp
    calc c a = c (a * q) := const_mul L hadd hsmul c hcos ha q hq0
      _ = c (1 * p) := by rw [e]
      _ = c 1 := (const_mul L hadd hsmul c hcos one_ne_zero p hp0).symm
  refine ⟨c 1, fun Φ hΦ => ?_⟩
  have hΦ' : Φ ∈ Submodule.span ℂ {Φ | ∃ (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ)
      (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ), g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) ∧ Φ = pureA F f g} := hΦ
  induction hΦ' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    obtain ⟨a, ha, R, hR⟩ := GlobalTheory.EvAdm.exists_sum_cosets hg
    have hsplit : pureA F f g = ∑ r ∈ R, g r • pureA F f (cosInd F κ a r) := by
      rw [← pure_sum]
      congr 1
    have hmem : ∀ r ∈ R, g r • pureA F f (cosInd F κ a r) ∈ schA F κ :=
      fun r _ => Submodule.smul_mem _ _ (pure_mem f (cosInd_mem_SB ha r))
    rw [hsplit, L_sum L hadd hsmul R _ hmem, theta_sum R _ hmem, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hsmul _ _ (pure_mem f (cosInd_mem_SB ha r)), GlobalTheory.WeilM.thetaSum_smul F, hcos a ha r f, hall a ha]
    ring
  | zero =>
    have h := hsmul 0 0 (zero_mem _)
    simp only [zero_smul, zero_mul] at h
    rw [h]
    simp [thetaSum]
  | add x y hx hy ihx ihy =>
    rw [hadd x hx y hy, GlobalTheory.WeilM.thetaSum_add F hx hy, ihx hx, ihy hy]
    ring
  | smul t x hx ih =>
    rw [hsmul t x hx, GlobalTheory.WeilM.thetaSum_smul F, ih hx]
    ring

end GlobalTheory.ThetaFunctionalUnique
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFunctionalArchimedeanFactorStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_functional_archimedean_factor : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    (L : ((κ → AF F) → ℂ) → ℂ),
    (∀ Φ ∈ schA F κ, ∀ Ψ ∈ schA F κ, L (Φ + Ψ) = L Φ + L Ψ) →
    (∀ (c : ℂ), ∀ Φ ∈ schA F κ, L (c • Φ) = c * L Φ) →
    (∀ g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F), ∃ T : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] ℂ,
      ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, L (pureA F f g) = T f) →
    (∀ a b : κ → F, ∀ Φ ∈ schA F κ,
      L (schr ψ ((fun i => algebraMap F (AF F) (a i)), (fun i => algebraMap F (AF F) (b i))) Φ) = L Φ) →
    ∃ c : ℂ, ∀ Φ ∈ schA F κ, L Φ = c * thetaSum F Φ := by
  first | exact @GlobalTheory.ThetaFunctionalUnique.main | exact GlobalTheory.ThetaFunctionalUnique.main | (intros; apply GlobalTheory.ThetaFunctionalUnique.main <;> assumption)
end
