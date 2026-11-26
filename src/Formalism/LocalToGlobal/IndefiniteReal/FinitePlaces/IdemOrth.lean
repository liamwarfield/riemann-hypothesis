module

public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemUniq
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FactorizationBis

@[expose] public section

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemOrth
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField Polynomial
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 160000

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem idemAt_eq_split {P : HeightOneSpectrum (𝓞 D.host.E)} (hP : ¬ Lev.IsConjPl (D := D) P P) {e e' : AE D}
    (he : Formalism.L2.NTheta.IsIdemAt e P) (he' : Formalism.L2.NTheta.IsIdemAt e' P) : e = e' := by
  obtain ⟨e₀, ι, he₀, -, hs₀, hz, hκ⟩ := idem_data P hP (belowPl P) rfl
  have key : ∀ f : AE D, Formalism.L2.NTheta.IsIdemAt f P → f = e₀ := by
    intro f hf
    rcases idem_class P hP e₀ ι hs₀ hz hκ he₀.1.1 he₀.1.2.1 f hf.1.1 hf.1.2.1 (below_of_idemAt hf) with h | h
    · exact h
    exfalso
    exact hP (conj_of_cA he₀ hf h)
  rw [key e he, key e' he']

theorem idem_orth {P Q : HeightOneSpectrum (𝓞 D.host.E)} (hP : ¬ Lev.IsConjPl (D := D) P P) {e e' : AE D}
    (he : Formalism.L2.NTheta.IsIdemAt e P) (he' : Formalism.L2.NTheta.IsIdemAt e' Q) (hPQ : P ≠ Q) : e * e' = 0 := by
  have hs := below_of_idemAt he
  have hs' := below_of_idemAt he'
  have heps : e * phiE (belowPl P) 1 = e := by rw [← hs, mul_add, he.1.1, he.1.2.1, add_zero]
  have heps' : e' * phiE (belowPl Q) 1 = e' := by rw [← hs', mul_add, he'.1.1, he'.1.2.1, add_zero]
  by_cases hv : belowPl P = belowPl Q
  · obtain ⟨e₀, ι, he₀, -, hs₀, hz, hκ⟩ := idem_data P hP (belowPl P) rfl
    have h0 : e = e₀ := idemAt_eq_split hP he he₀
    rw [← hv] at hs'
    rcases idem_class P hP e₀ ι hs₀ hz hκ he₀.1.1 he₀.1.2.1 e' he'.1.1 he'.1.2.1 hs' with h | h
    · exfalso
      apply hPQ
      apply HeightOneSpectrum.ext
      ext x
      by_cases hx0 : x = 0
      · subst hx0; simp only [zero_mem]
      rw [he.2 x hx0, he'.2 x hx0, h0, h]
    · rw [h, h0]; exact he₀.1.2.1
  · rw [← heps, ← heps']
    calc e * phiE (belowPl P) 1 * (e' * phiE (belowPl Q) 1) = e * e' * (phiE (belowPl P) 1 * phiE (belowPl Q) 1) := by ring
      _ = 0 := by rw [phiE_orth hv, mul_zero]

theorem idem_orth_conj {P Q : HeightOneSpectrum (𝓞 D.host.E)} (hP : ¬ Lev.IsConjPl (D := D) P P) {e e' : AE D}
    (he : Formalism.L2.NTheta.IsIdemAt e P) (he' : Formalism.L2.NTheta.IsIdemAt e' Q) (hPQ : ¬ Lev.IsConjPl (D := D) P Q) :
    e * cA D e' = 0 := by
  have hs := below_of_idemAt he
  have hs' := below_of_idemAt he'
  have heps : e * phiE (belowPl P) 1 = e := by rw [← hs, mul_add, he.1.1, he.1.2.1, add_zero]
  have heps' : cA D e' * phiE (belowPl Q) 1 = cA D e' := by
    rw [← hs', mul_add, mul_comm (cA D e') e', he'.1.2.1, zero_add, ← map_mul, he'.1.1]
  by_cases hv : belowPl P = belowPl Q
  · obtain ⟨e₀, ι, he₀, -, hs₀, hz, hκ⟩ := idem_data P hP (belowPl P) rfl
    have h0 : e = e₀ := idemAt_eq_split hP he he₀
    rw [← hv] at hs'
    rcases idem_class P hP e₀ ι hs₀ hz hκ he₀.1.1 he₀.1.2.1 e' he'.1.1 he'.1.2.1 hs' with h | h
    · rw [h, h0]; exact he₀.1.2.1
    · exfalso
      exact hPQ (conj_of_cA he he' (h.trans (congrArg (cA D) h0.symm)))
  · rw [← heps, ← heps']
    calc e * phiE (belowPl P) 1 * (cA D e' * phiE (belowPl Q) 1) =
        e * cA D e' * (phiE (belowPl P) 1 * phiE (belowPl Q) 1) := by ring
      _ = 0 := by rw [phiE_orth hv, mul_zero]

theorem not_two_primes {I : Ideal (𝓞 D.host.E)} (hI : I ≠ ⊤) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (hpI : (p : 𝓞 D.host.E) ∈ I) (hqI : (q : 𝓞 D.host.E) ∈ I) : False := by
  have hc : IsCoprime (p : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hq).2 hne)
  obtain ⟨a, b, hab⟩ := hc.map (Int.castRingHom (𝓞 D.host.E))
  apply hI
  rw [Ideal.eq_top_iff_one, ← hab]
  simp only [eq_intCast, Int.cast_natCast]
  exact add_mem (I.mul_mem_left _ hpI) (I.mul_mem_left _ hqI)

theorem nat_mem_of_conj {P Q : HeightOneSpectrum (𝓞 D.host.E)} (h : Lev.IsConjPl (D := D) P Q) {n : ℕ}
    (hn : (n : 𝓞 D.host.E) ∈ P.asIdeal) : (n : 𝓞 D.host.E) ∈ Q.asIdeal := by
  obtain ⟨c, hc, hce⟩ := h _ hn
  have : c = (n : 𝓞 D.host.E) := by
    apply FaithfulSMul.algebraMap_injective (𝓞 D.host.E) D.host.E
    show (c : D.host.E) = ((n : 𝓞 D.host.E) : D.host.E)
    rw [hce]; push_cast; exact star_natCast n
  rwa [← this]

theorem char_mem {P : HeightOneSpectrum (𝓞 D.host.E)} {q : ℕ} (hq : q.Prime)
    (hc : Nat.card (Formalism.L2.DIV.kP P) = q) : (q : 𝓞 D.host.E) ∈ P.asIdeal := by
  have hfin : Finite (Formalism.L2.DIV.kP P) := Nat.finite_of_card_ne_zero (by rw [hc]; exact hq.ne_zero)
  have h0 : (Nat.card (Formalism.L2.DIV.kP P)) • (1 : Formalism.L2.DIV.kP P) = 0 := card_nsmul_eq_zero'
  rw [hc, nsmul_one] at h0
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  simpa using h0

end Formalism.IndefR.Fin

end
end

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FstACoordOfInfPart
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open Filter Topology Classical
open scoped TensorProduct
open Formalism.IndefR.Datum

set_option synthInstance.maxHeartbeats 160000

namespace Formalism.IndefR.Fin.LevelGroupLemmas

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Adeles

variable {F : Type} [Field F] [NumberField F]

def sglS (A : Finset (HeightOneSpectrum (𝓞 F))) : Af F := ∑ v ∈ A, sglV v 1

theorem evalV_sglS (A : Finset (HeightOneSpectrum (𝓞 F))) (w : HeightOneSpectrum (𝓞 F)) :
    evalV F w (sglS A) = if w ∈ A then 1 else 0 := by
  classical
  unfold sglS
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  have : ∀ v ∈ A, evalV F w (sglV v (1 : v.adicCompletion F)) = if w = v then 1 else 0 := by
    intro v _
    by_cases h : w = v
    · subst h; rw [sglV_same, if_pos rfl]
    · rw [sglV_ne v _ h, if_neg h]
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq]

def idemS (A : Finset (HeightOneSpectrum (𝓞 F))) : AF F := pairA F 0 (sglS A)

theorem sglS_mul_self (A : Finset (HeightOneSpectrum (𝓞 F))) : sglS A * sglS A = sglS A := by
  apply af_ext; intro w
  rw [map_mul, evalV_sglS]
  split_ifs <;> simp

theorem idemS_idem (A : Finset (HeightOneSpectrum (𝓞 F))) : IsIdempotentElem (idemS A) :=
  Prod.ext (by show (0 : InfiniteAdeleRing F) * 0 = 0; rw [mul_zero]) (sglS_mul_self A)

theorem idemS_empty : idemS (∅ : Finset (HeightOneSpectrum (𝓞 F))) = 0 :=
  Prod.ext rfl (by show sglS ∅ = 0; simp [sglS])

theorem idemS_insert {A : Finset (HeightOneSpectrum (𝓞 F))} {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ A) :
    idemS (insert v A) = idemS A + sA v 1 := by
  refine Prod.ext (by show (0 : InfiniteAdeleRing F) = 0 + 0; rw [add_zero]) ?_
  show sglS (insert v A) = sglS A + sglV v 1
  unfold sglS
  rw [Finset.sum_insert hv, add_comm]

theorem idemS_mul_sA {A : Finset (HeightOneSpectrum (𝓞 F))} {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ A) :
    idemS A * sA v 1 = 0 := by
  refine Prod.ext (by show (0 : InfiniteAdeleRing F) * 0 = 0; rw [mul_zero]) ?_
  show sglS A * sglV v 1 = 0
  apply af_ext; intro w
  rw [map_mul, evalV_sglS, map_zero]
  by_cases h : w = v
  · subst h; rw [if_neg hv, zero_mul]
  · rw [sglV_ne v _ h, mul_zero]

theorem sA_idem (v : HeightOneSpectrum (𝓞 F)) : IsIdempotentElem (sA v (1 : v.adicCompletion F)) := by
  show sA v 1 * sA v 1 = sA v 1
  rw [← map_mul, mul_one]

theorem tendsto_fin (y : Af F) : Tendsto (fun A : Finset (HeightOneSpectrum (𝓞 F)) => (1 - sglS A) * y) atTop (𝓝 0) :=
  _root_.UpperTheory.Reformulated.B.Qi11.tendsto_fin y

theorem tendsto_AF (a : AF F) (ha : fstA F a = 0) :
    Tendsto (fun A : Finset (HeightOneSpectrum (𝓞 F)) => (1 - idemS A) * a) atTop (𝓝 0) := by
  have heq : ∀ A : Finset (HeightOneSpectrum (𝓞 F)), (1 - idemS A) * a = ((0 : InfiniteAdeleRing F), (1 - sglS A) * a.2) := by
    intro A
    refine Prod.ext ?_ rfl
    have : a.1 = 0 := ha
    show (1 - 0) * a.1 = 0
    rw [this, mul_zero]
  simp only [heq]
  exact tendsto_const_nhds.prodMk_nhds (tendsto_fin a.2)

end Adeles

variable {D : D7}

theorem fstA_coord_of_infPart {z : AE D} (hz : infPart D z = 0) {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι D.host.F D.host.E) (i : ι) :
    fstA D.host.F ((Algebra.TensorProduct.basis (AF D.host.F) b).repr z i) = 0 := by
  set c := fun i => (Algebra.TensorProduct.basis (AF D.host.F) b).repr z i
  set bI := Algebra.TensorProduct.basis (Ainf D.host.F) b
  have hz' : z = ∑ i, c i • ((1 : AF D.host.F) ⊗ₜ[D.host.F] b i) := by
    conv_lhs => rw [← (Algebra.TensorProduct.basis (AF D.host.F) b).sum_repr z]
    simp only [Algebra.TensorProduct.basis_apply, c]
  have hinf : infPart D z = ∑ i, fstA D.host.F (c i) • bI i := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hz', map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one, Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul',
      smul_eq_mul, mul_one]
    show (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)) (c i ⊗ₜ[D.host.F] b i) = _
    rw [Algebra.TensorProduct.map_tmul]
    rfl
  have h := bI.repr_sum_self (fun i => fstA D.host.F (c i))
  rw [← hinf, hz, map_zero] at h
  exact (congrFun h i).symm

instance instIsModTopAE : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩

theorem tendsto_AE (z : AE D) (hz : infPart D z = 0) :
    Tendsto (fun A : Finset (HeightOneSpectrum (𝓞 D.host.F)) =>
      algebraMap (AF D.host.F) (AE D) (1 - idemS A) * z) atTop (𝓝 0) := by
  classical
  let b := Module.finBasis D.host.F D.host.E
  let bA := Algebra.TensorProduct.basis (AF D.host.F) b
  have hz' : ∀ A : Finset (HeightOneSpectrum (𝓞 D.host.F)), algebraMap (AF D.host.F) (AE D) (1 - idemS A) * z =
      ∑ i, ((1 - idemS A) * bA.repr z i) • bA i := by
    intro A
    conv_lhs => rw [← bA.sum_repr z]
    rw [← Algebra.smul_def, Finset.smul_sum]
    simp only [smul_smul]
  have : ContinuousAdd (AE D) := IsModuleTopology.toContinuousAdd (AF D.host.F) (AE D)
  have : ContinuousSMul (AF D.host.F) (AE D) := IsModuleTopology.toContinuousSMul (AF D.host.F) (AE D)
  simp only [hz']
  have : (0 : AE D) = ∑ i, (0 : AF D.host.F) • bA i := by simp
  rw [this]
  refine tendsto_finsetSum _ fun i _ => ?_
  exact (tendsto_AF _ (fstA_coord_of_infPart hz b i)).smul_const _

theorem tendsto_GA {V : HSp D} {ι : Type*} {l : Filter ι} (k : ι → GA D V) (g : GA D V)
    (h1 : ∀ i j, Tendsto (fun a => Formalism.L2.Theta.mt V (k a) i j) l (𝓝 (Formalism.L2.Theta.mt V g i j)))
    (h2 : ∀ i j, Tendsto (fun a => Formalism.L2.Theta.mt V (k a)⁻¹ i j) l (𝓝 (Formalism.L2.Theta.mt V g⁻¹ i j))) :
    Tendsto k l (𝓝 g) := by
  have hemb : Topology.IsEmbedding (fun x : GA D V => (matHom V x : GL (Fin V.rank) (AE D))) :=
    Topology.IsEmbedding.subtypeVal
  refine hemb.tendsto_nhds_iff.2 ?_
  refine Units.isEmbedding_embedProduct.tendsto_nhds_iff.2 ?_
  simp only [Function.comp_def, Units.embedProduct_apply]
  refine Tendsto.prodMk_nhds ?_ ?_
  · refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    exact h1 i j
  · refine (MulOpposite.continuous_op.tendsto _).comp ?_
    have hinv : ∀ x : GA D V, ((matHom V x)⁻¹ : GL (Fin V.rank) (AE D)) = matHom V x⁻¹ := fun x => (map_inv _ x).symm
    simp only [hinv]
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
    exact h2 i j

theorem om_fix_of_tendsto {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om) {f₀ : WO S T → ℂ}
    (hf₀ : IsThetaFunO ψ S T f₀) {ι : Type*} {l : Filter ι} [l.NeBot] (k : ι → GA D S × GA D T)
    (p : GA D S × GA D T) (hk : Tendsto k l (𝓝 p)) (hfix : ∀ a, om (k a) f₀ = f₀) : om p f₀ = f₀ := by
  funext w
  have hc := hW.om_cont f₀ hf₀ w
  have h := (hc.tendsto p).comp hk
  have h' : Tendsto (fun _ : ι => f₀ w) l (𝓝 ((om p) f₀ w)) := by
    refine h.congr fun a => ?_
    simp only [Function.comp_apply, hfix a]
  exact (tendsto_nhds_unique tendsto_const_nhds h').symm

theorem infPart_mt_sub_one {V : HSp D} {g : GA D V} (hg : g ∈ GfC V) (i j : Fin V.rank) :
    infPart D (Formalism.L2.Theta.mt V g i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) = 0 := by
  have h1 : infHom V g = 1 := hg
  have h2 := congrArg (fun x : GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E) => x.1 i j) h1
  simp only [Units.val_one] at h2
  have h3 : infPart D (Formalism.L2.Theta.mt V g i j) =
      (1 : Matrix (Fin V.rank) (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E)) i j := h2
  rw [map_sub, h3]
  by_cases hij : i = j
  · subst hij; simp
  · simp [Matrix.one_apply_ne hij]

theorem tendsto_trunc_entry {n : ℕ} (M : Matrix (Fin n) (Fin n) (AE D))
    (hM : ∀ i j, infPart D (M i j - (1 : Matrix (Fin n) (Fin n) (AE D)) i j) = 0) (i j : Fin n) :
    Tendsto (fun A : Finset (HeightOneSpectrum (𝓞 D.host.F)) =>
      ((1 : Matrix (Fin n) (Fin n) (AE D)) + algebraMap (AF D.host.F) (AE D) (idemS A) • (M - 1)) i j) atTop
      (𝓝 (M i j)) := by
  have heq : ∀ A : Finset (HeightOneSpectrum (𝓞 D.host.F)),
      ((1 : Matrix (Fin n) (Fin n) (AE D)) + algebraMap (AF D.host.F) (AE D) (idemS A) • (M - 1)) i j =
        M i j + algebraMap (AF D.host.F) (AE D) (1 - idemS A) * ((1 : Matrix (Fin n) (Fin n) (AE D)) i j - M i j) := by
    intro A
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, map_sub, map_one]
    ring
  have hz : infPart D ((1 : Matrix (Fin n) (Fin n) (AE D)) i j - M i j) = 0 := by
    rw [← neg_sub, map_neg, hM i j, neg_zero]
  have : ContinuousAdd (AE D) := IsModuleTopology.toContinuousAdd (AF D.host.F) (AE D)
  simp only [heq]
  have h := (tendsto_const_nhds (x := M i j)).add (tendsto_AE _ hz)
  simpa using h

theorem tendsto_trunc {V : HSp D} {g : GA D V} (hg : g ∈ GfC V) (k : Finset (HeightOneSpectrum (𝓞 D.host.F)) → GA D V)
    (hk : ∀ A, Formalism.L2.Theta.mt V (k A) = 1 + algebraMap (AF D.host.F) (AE D) (idemS A) • (Formalism.L2.Theta.mt V g - 1))
    (hk' : ∀ A, Formalism.L2.Theta.mt V (k A)⁻¹ =
      1 + algebraMap (AF D.host.F) (AE D) (idemS A) • (Formalism.L2.Theta.mt V g⁻¹ - 1)) :
    Tendsto k atTop (𝓝 g) := by
  apply tendsto_GA
  · intro i j
    simp only [hk]
    exact tendsto_trunc_entry _ (infPart_mt_sub_one hg) i j
  · intro i j
    simp only [hk']
    exact tendsto_trunc_entry _ (infPart_mt_sub_one (Subgroup.inv_mem _ hg)) i j

theorem om_fix_of_trunc {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om) {f₀ : WO S T → ℂ}
    (hf₀ : IsThetaFunO ψ S T f₀) {g : GA D S} {h : GA D T} (hg : g ∈ GfC S) (hh : h ∈ GfC T)
    (k : Finset (HeightOneSpectrum (𝓞 D.host.F)) → GA D S) (k' : Finset (HeightOneSpectrum (𝓞 D.host.F)) → GA D T)
    (hk : ∀ A, Formalism.L2.Theta.mt S (k A) = 1 + algebraMap (AF D.host.F) (AE D) (idemS A) • (Formalism.L2.Theta.mt S g - 1))
    (hki : ∀ A, Formalism.L2.Theta.mt S (k A)⁻¹ =
      1 + algebraMap (AF D.host.F) (AE D) (idemS A) • (Formalism.L2.Theta.mt S g⁻¹ - 1))
    (hk' : ∀ A, Formalism.L2.Theta.mt T (k' A) = 1 + algebraMap (AF D.host.F) (AE D) (idemS A) • (Formalism.L2.Theta.mt T h - 1))
    (hki' : ∀ A, Formalism.L2.Theta.mt T (k' A)⁻¹ =
      1 + algebraMap (AF D.host.F) (AE D) (idemS A) • (Formalism.L2.Theta.mt T h⁻¹ - 1))
    (hfix : ∀ A, om (k A, k' A) f₀ = f₀) : om (g, h) f₀ = f₀ :=
  om_fix_of_tendsto hW hf₀ (fun A => (k A, k' A)) (g, h)
    ((tendsto_trunc hg k hk hki).prodMk_nhds (tendsto_trunc hh k' hk' hki')) hfix

end Formalism.IndefR.Fin.LevelGroupLemmas

end
end
