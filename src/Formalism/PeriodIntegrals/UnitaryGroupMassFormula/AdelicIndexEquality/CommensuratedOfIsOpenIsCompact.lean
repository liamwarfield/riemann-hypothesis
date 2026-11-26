module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.Commensurated
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.ConstructionA
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.ConstructionD

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.CommensuratedOfIsOpenIsCompact
noncomputable section

namespace PI.UnitaryGroupMassFormula.AdIndexEq

open Formalism.MainNotions.S

theorem commensurated_of_isOpen_isCompact {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (K : Subgroup G) (ho : IsOpen (K : Set G)) (hc : IsCompact (K : Set G)) :
    Commensurated K := by
  intro x
  have hmo : IsOpen ((K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) := by
    have hset : ((K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G) =
        (fun y => x⁻¹ * y * x) ⁻¹' (K : Set G) := by
      ext y
      simp only [Subgroup.coe_map, Set.mem_image, Set.mem_preimage, SetLike.mem_coe,
        MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      constructor
      · rintro ⟨k, hk, rfl⟩
        simpa [mul_assoc] using hk
      · intro h
        exact ⟨_, h, by group⟩
    rw [hset]
    exact ho.preimage (by fun_prop)
  have : CompactSpace K := isCompact_iff_compactSpace.mp hc
  have hso : IsOpen (((K.map (MulAut.conj x).toMonoidHom).subgroupOf K : Subgroup K) : Set K) := by
    rw [Subgroup.coe_subgroupOf]
    exact hmo.preimage continuous_subtype_val
  have : Finite (K ⧸ (K.map (MulAut.conj x).toMonoidHom).subgroupOf K) :=
    Subgroup.quotient_finite_of_isOpen _ hso
  exact Subgroup.index_ne_zero_of_finite

theorem ksub_isOpen (I : AutInst) : IsOpen ((PI.AdIndexEq.Ksub I : Subgroup I.Gf) : Set I.Gf) :=
  PI.WAU.kset_open I

theorem ksub_isCompact (I : AutInst) : IsCompact ((PI.AdIndexEq.Ksub I : Subgroup I.Gf) : Set I.Gf) :=
  PI.WAU.maximal_compact_isCompact I

theorem compact_commensurated : KComm := fun I =>
  commensurated_of_isOpen_isCompact _ (ksub_isOpen I) (ksub_isCompact I)

end PI.UnitaryGroupMassFormula.AdIndexEq

end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.InertPowDefs
noncomputable section

namespace PI.UnitaryGroupMassFormula.AdIndexEq

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.MainNotions.S

def incL (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v →+* Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E :=
  Algebra.TensorProduct.includeLeftRingHom

def TraceInt : Prop :=
  ∀ (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)), IsFieldAt I v →
    ∀ α : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E, sigV I v α * α = 1 →
      ∃ t ∈ v.adicCompletionIntegers I.F, α + sigV I v α = incL I v t

end PI.UnitaryGroupMassFormula.AdIndexEq

end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.ChiEqOneOfClosure
noncomputable section

namespace PI.UnitaryGroupMassFormula.AdIndexEq

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.MainNotions.S

def IsQRefl (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)) (s : Uv I v) : Prop :=
  ∃ (P : Matrix (Fin I.n) (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E))
    (α : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E),
    P * P = P ∧ sigV I v α * α = 1 ∧
      (((s : GL (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E)) :
        Matrix (Fin I.n) (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E)) = 1 + (α - 1) • P)

def QReflGen : Prop :=
  ∀ (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)), IsFieldAt I v →
    ∀ g : Uv I v, g ∈ Subgroup.closure {s : Uv I v | IsQRefl I v s}

def QReflPow : Prop :=
  ∀ (I : AutInst) (v : HeightOneSpectrum (𝓞 I.F)), IsFieldAt I v →
    ∀ s : Uv I v, IsQRefl I v s →
      ∃ m : ℕ, 1 ≤ m ∧ (((s ^ m : Uv I v) : GL (Fin I.n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv I.F v ⊗[I.F] I.E)) ∈ Kv I v)

end PI.UnitaryGroupMassFormula.AdIndexEq

end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.SplitGL
noncomputable section

namespace PI.UnitaryGroupMassFormula.AdIndexEq.SplitGL

open Matrix

variable {R k : Type} [CommRing R] [Field k] {n : Type} [Fintype n] [DecidableEq n]

def p1 (π : R ≃+* k × k) : R →+* k := (RingHom.fst k k).comp π.toRingHom

def p2 (π : R ≃+* k × k) : R →+* k := (RingHom.snd k k).comp π.toRingHom

theorem ext_p (π : R ≃+* k × k) {r s : R} (h1 : p1 π r = p1 π s) (h2 : p2 π r = p2 π s) : r = s := by
  apply π.injective
  exact Prod.ext h1 h2

theorem mat_ext_p (π : R ≃+* k × k) {M N : Matrix n n R} (h1 : M.map (p1 π) = N.map (p1 π))
    (h2 : M.map (p2 π) = N.map (p2 π)) : M = N := by
  ext i j
  exact ext_p π (congrFun (congrFun h1 i) j) (congrFun (congrFun h2 i) j)

variable (σ : R →+* R) (π : R ≃+* k × k) (hπ : ∀ r, π (σ r) = (π r).swap)
include hπ

theorem p1_sigma_eq_p2 (r : R) : p1 π (σ r) = p2 π r := by
  show (π (σ r)).1 = (π r).2
  rw [hπ]
  rfl

theorem snd_conj (r : R) : p2 π (σ r) = p1 π r := by
  show (π (σ r)).2 = (π r).1
  rw [hπ]
  rfl

theorem map_conjTranspose_fst (M : Matrix n n R) : (Formalism.UG.cT σ M).map (p1 π) = (M.map (p2 π))ᵀ := by
  ext i j
  exact p1_sigma_eq_p2 σ π hπ (M j i)

theorem map_conjTranspose_snd (M : Matrix n n R) : (Formalism.UG.cT σ M).map (p2 π) = (M.map (p1 π))ᵀ := by
  ext i j
  exact snd_conj σ π hπ (M j i)

theorem unitary_iff (J M : Matrix n n R) :
    Formalism.UG.cT σ M * J * M = J ↔
      (M.map (p2 π))ᵀ * J.map (p1 π) * M.map (p1 π) = J.map (p1 π) ∧
      (M.map (p1 π))ᵀ * J.map (p2 π) * M.map (p2 π) = J.map (p2 π) := by
  have e1 : (Formalism.UG.cT σ M * J * M).map (p1 π) = (M.map (p2 π))ᵀ * J.map (p1 π) * M.map (p1 π) := by
    rw [Matrix.map_mul, Matrix.map_mul, map_conjTranspose_fst σ π hπ]
  have e2 : (Formalism.UG.cT σ M * J * M).map (p2 π) = (M.map (p1 π))ᵀ * J.map (p2 π) * M.map (p2 π) := by
    rw [Matrix.map_mul, Matrix.map_mul, map_conjTranspose_snd σ π hπ]
  constructor
  · intro h
    rw [← e1, ← e2, h]
    exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    exact mat_ext_p π (by rw [e1, h1]) (by rw [e2, h2])

theorem hermitian_map_snd (J : Matrix n n R) (hJ : Formalism.UG.cT σ J = J) : J.map (p2 π) = (J.map (p1 π))ᵀ := by
  have h := map_conjTranspose_fst σ π hπ J
  rw [hJ] at h
  rw [h, Matrix.transpose_transpose]


omit hπ in
def proj (J : Matrix n n R) : Formalism.UG.UJ σ J →* GL n k :=
  (Units.map ((p1 π).mapMatrix : Matrix n n R →+* Matrix n n k).toMonoidHom).comp (Formalism.UG.UJ σ J).subtype

theorem proj_bijective (J : Matrix n n R) (hJ : Formalism.UG.cT σ J = J) (hdet : IsUnit J.det) :
    Function.Bijective (proj σ π J) := by
  have hJ1 : IsUnit (J.map (p1 π)).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hdet.map _
  have hunit : ∀ x : Formalism.UG.UJ σ J,
      (((x : GL n R) : Matrix n n R).map (p2 π))ᵀ * J.map (p1 π) * ((x : GL n R) : Matrix n n R).map (p1 π) =
        J.map (p1 π) :=
    fun x => ((unitary_iff σ π hπ J ((x : GL n R) : Matrix n n R)).1 x.2).1
  have hinv1 : ∀ x : GL n R,
      (x : Matrix n n R).map (p1 π) * ((x⁻¹ : GL n R) : Matrix n n R).map (p1 π) = 1 := by
    intro x
    rw [← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  constructor
  · intro g h hgh
    have h1 : ((g : GL n R) : Matrix n n R).map (p1 π) = ((h : GL n R) : Matrix n n R).map (p1 π) :=
      congrArg (fun u : GL n k => (u : Matrix n n k)) hgh
    have h2 : ((g : GL n R) : Matrix n n R).map (p2 π) = ((h : GL n R) : Matrix n n R).map (p2 π) := by
      have hg := hunit g
      have hh := hunit h
      rw [h1] at hg
      have e : (((g : GL n R) : Matrix n n R).map (p2 π))ᵀ * J.map (p1 π) =
          (((h : GL n R) : Matrix n n R).map (p2 π))ᵀ * J.map (p1 π) := by
        have := congrArg (fun X => X * (((h : GL n R)⁻¹ : GL n R) : Matrix n n R).map (p1 π)) (hg.trans hh.symm)
        simp only [Matrix.mul_assoc, hinv1, Matrix.mul_one] at this
        simpa only [Matrix.mul_assoc] using this
      have e' := congrArg (fun X => X * (J.map (p1 π))⁻¹) e
      simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hJ1, Matrix.mul_one] at e'
      have := congrArg Matrix.transpose e'
      simpa only [Matrix.transpose_transpose] using this
    exact Subtype.ext (Units.ext (mat_ext_p π h1 h2))
  · intro A
    let J1 : Matrix n n k := J.map (p1 π)
    let A1 : Matrix n n k := (A : Matrix n n k)
    let B : Matrix n n k := (J1 * ((A⁻¹ : GL n k) : Matrix n n k) * J1⁻¹)ᵀ
    let M : Matrix n n R := Matrix.of fun i j => π.symm (A1 i j, B i j)
    have hM1 : M.map (p1 π) = A1 := by
      ext i j
      simp [M, p1]
    have hM2 : M.map (p2 π) = B := by
      ext i j
      simp [M, p2]
    have hJ1' : IsUnit J1.det := hJ1
    have key : Bᵀ * J1 * A1 = J1 := by
      simp only [B, Matrix.transpose_transpose, Matrix.mul_assoc]
      rw [Matrix.nonsing_inv_mul_cancel_left _ _ hJ1', Units.inv_mul, Matrix.mul_one]
    have hU : Formalism.UG.cT σ M * J * M = J := by
      rw [unitary_iff σ π hπ J M, hM1, hM2, hermitian_map_snd σ π hπ J hJ]
      refine ⟨key, ?_⟩
      have := congrArg Matrix.transpose key
      rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, ← Matrix.mul_assoc] at this
      exact this
    have hdetM : IsUnit M.det := by
      have h := congrArg Matrix.det hU
      rw [Matrix.det_mul, Matrix.det_mul] at h
      have h' : IsUnit ((Formalism.UG.cT σ M).det * J.det * M.det) := by rw [h]; exact hdet
      exact isUnit_of_mul_isUnit_right h'
    refine ⟨⟨((Matrix.isUnit_iff_isUnit_det M).2 hdetM).unit, hU⟩, ?_⟩
    exact Units.ext hM1

end PI.UnitaryGroupMassFormula.AdIndexEq.SplitGL

end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.SplitIso
noncomputable section

namespace PI.UnitaryGroupMassFormula.AdIndexEq.SplitIso

open scoped TensorProduct

variable {F E K : Type} [Field F] [Field E] [Algebra F E] [Field K] [Algebra F K]

def sigT (σ : E →ₐ[F] E) : K ⊗[F] E →ₐ[F] K ⊗[F] E := Algebra.TensorProduct.map (AlgHom.id F K) σ

theorem sigT_algebraMap (σ : E →ₐ[F] E) (x : K) :
    sigT σ (algebraMap K (K ⊗[F] E) x) = algebraMap K (K ⊗[F] E) x := by
  simp [sigT, Algebra.TensorProduct.algebraMap_apply]

theorem sigT_tmul_one (σ : E →ₐ[F] E) (a : E) : sigT (K := K) σ ((1 : K) ⊗ₜ[F] a) = (1 : K) ⊗ₜ[F] σ a := by
  simp [sigT]

theorem exists_alpha (σ : E →ₐ[F] E) (hσσ : ∀ a, σ (σ a) = a)
    (hfix : ∀ a, σ a = a → a ∈ (algebraMap F E).range) (h2 : Module.finrank F E = 2) :
    ∃ α : E, α ≠ 0 ∧ σ α = -α := by
  have : ∃ a : E, a ∉ (algebraMap F E).range := by
    by_contra hall
    push Not at hall
    have hr : LinearMap.range (Algebra.linearMap F E) = ⊤ := by
      rw [eq_top_iff]
      intro a _
      obtain ⟨f, rfl⟩ := hall a
      exact ⟨f, rfl⟩
    have := (Algebra.linearMap F E).finrank_range_le
    rw [hr, finrank_top, h2, Module.finrank_self] at this
    omega
  obtain ⟨a, ha⟩ := this
  refine ⟨a - σ a, ?_, ?_⟩
  · intro h0
    exact ha (hfix a (by linear_combination -h0))
  · rw [map_sub, hσσ]; ring

variable (σ : E →ₐ[F] E) (hσσ : ∀ a, σ (σ a) = a)
    (hfix : ∀ a, σ a = a → a ∈ (algebraMap F E).range) (h2 : Module.finrank F E = 2)
    (h2K : (2 : K) ≠ 0)

include hσσ hfix h2 h2K in
theorem exists_split (hnf : ¬ IsField (K ⊗[F] E)) :
    ∃ π : K ⊗[F] E ≃+* K × K, ∀ r, π (sigT σ r) = (π r).swap := by
  have h2F : (2 : F) ≠ 0 := by
    intro h
    apply h2K
    have := congrArg (algebraMap F K) h
    rwa [map_ofNat, map_zero] at this
  obtain ⟨α, hα0, hσα⟩ := exists_alpha σ hσσ hfix h2

  have hli : LinearIndependent F ![(1 : E), α] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h' := congrArg σ hst
    simp only [map_add (f := _), map_smul, map_one, hσα, map_zero, smul_neg] at h'
    have ht : (2 * t) • α = 0 := by
      rw [mul_smul, two_smul]
      linear_combination hst - h'
    have ht0 : t = 0 := by
      rcases smul_eq_zero.1 ht with h | h
      · exact (mul_eq_zero.1 h).resolve_left h2F
      · exact absurd h hα0
    subst ht0
    refine ⟨?_, rfl⟩
    simpa using hst
  let bE : Module.Basis (Fin 2) F E := basisOfLinearIndependentOfCardEqFinrank hli (by simp [h2])
  have hbE0 : bE 0 = 1 := by simp [bE]
  have hbE1 : bE 1 = α := by simp [bE]
  let bR : Module.Basis (Fin 2) K (K ⊗[F] E) := Algebra.TensorProduct.basis K bE
  set A : K ⊗[F] E := (1 : K) ⊗ₜ[F] α with hAdef
  have hbR0 : bR 0 = 1 := by
    simp [bR, Algebra.TensorProduct.basis_apply, hbE0, Algebra.TensorProduct.one_def]
  have hbR1 : bR 1 = A := by
    simp [bR, Algebra.TensorProduct.basis_apply, hbE1, hAdef]
  have hdec : ∀ r : K ⊗[F] E, ∃ x y : K,
      r = algebraMap K (K ⊗[F] E) x + algebraMap K (K ⊗[F] E) y * A := by
    intro r
    refine ⟨bR.repr r 0, bR.repr r 1, ?_⟩
    conv_lhs => rw [← bR.sum_repr r]
    rw [Fin.sum_univ_two, hbR0, hbR1, Algebra.smul_def, Algebra.smul_def, mul_one]

  obtain ⟨b0, hb0⟩ := hfix (α * α) (by rw [map_mul, hσα]; ring)
  have hb00 : b0 ≠ 0 := by
    rintro rfl
    rw [map_zero] at hb0
    exact hα0 (mul_self_eq_zero.1 hb0.symm)
  set bK : K := algebraMap F K b0 with hbK
  have hbK0 : bK ≠ 0 := by
    rw [hbK]; exact (map_ne_zero _).2 hb00
  have hA : A * A = algebraMap K (K ⊗[F] E) bK := by
    rw [hAdef, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← hb0, Algebra.TensorProduct.algebraMap_apply, hbK,
      Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
      TensorProduct.smul_tmul']
    congr 1
    rw [smul_eq_mul, mul_one, Algebra.algebraMap_eq_smul_one]
  have hnt : (1 : K ⊗[F] E) ≠ 0 := by
    rw [← hbR0]; exact bR.ne_zero 0

  have hsq : ∃ c : K, c * c = bK := by
    by_contra hno
    push Not at hno
    apply hnf
    refine ⟨⟨0, 1, hnt.symm⟩, mul_comm, ?_⟩
    intro r hr
    obtain ⟨x, y, rfl⟩ := hdec r
    set N : K := x * x - bK * y * y with hN
    have hN0 : N ≠ 0 := by
      intro h0
      by_cases hy : y = 0
      · subst hy
        have hx : x = 0 := by simpa [hN] using h0
        subst hx
        exact hr (by simp)
      · apply hno (x / y)
        field_simp
        linear_combination h0
    refine ⟨algebraMap K (K ⊗[F] E) N⁻¹ *
      (algebraMap K (K ⊗[F] E) x - algebraMap K (K ⊗[F] E) y * A), ?_⟩
    have hNN : algebraMap K (K ⊗[F] E) N⁻¹ *
        (algebraMap K (K ⊗[F] E) x * algebraMap K (K ⊗[F] E) x -
          algebraMap K (K ⊗[F] E) bK * algebraMap K (K ⊗[F] E) y * algebraMap K (K ⊗[F] E) y) = 1 := by
      rw [← map_mul, ← map_mul, ← map_mul, ← map_sub, ← map_mul, ← hN, inv_mul_cancel₀ hN0, map_one]
    linear_combination (-(algebraMap K (K ⊗[F] E) N⁻¹ * algebraMap K (K ⊗[F] E) y *
      algebraMap K (K ⊗[F] E) y)) * hA + hNN
  obtain ⟨c, hc⟩ := hsq
  have hc0 : c ≠ 0 := by
    rintro rfl; exact hbK0 (by simpa using hc.symm)
  set ac := algebraMap K (K ⊗[F] E) c
  set aci := algebraMap K (K ⊗[F] E) c⁻¹
  set a2i := algebraMap K (K ⊗[F] E) (2⁻¹ : K)
  have hci : aci * ac = 1 := by rw [← map_mul, inv_mul_cancel₀ hc0, map_one]
  have h2i : a2i * 2 = 1 := by
    have : a2i * algebraMap K (K ⊗[F] E) 2 = 1 := by rw [← map_mul, inv_mul_cancel₀ h2K, map_one]
    rwa [map_ofNat] at this
  have hcc : ac * ac = algebraMap K (K ⊗[F] E) bK := by rw [← map_mul, hc]
  obtain ⟨e, he⟩ : ∃ e : K ⊗[F] E, e = a2i * (1 + aci * A) := ⟨_, rfl⟩
  have hee : e * e = e := by
    rw [he]
    linear_combination (a2i ^ 2 * aci ^ 2) * hA - (a2i ^ 2 * aci ^ 2) * hcc +
      (a2i ^ 2 * (aci * ac + 1)) * hci + ((1 + aci * A) * a2i) * h2i
  have hsA : sigT σ A = -A := by
    rw [hAdef, sigT_tmul_one, hσα, TensorProduct.tmul_neg]
  have hse : sigT σ e = 1 - e := by
    rw [he, map_mul, map_add (f := _), map_one, map_mul, hsA]
    simp only [a2i, aci, sigT_algebraMap]
    linear_combination h2i

  let ψ : K × K →+* K ⊗[F] E :=
    { toFun := fun p => algebraMap K (K ⊗[F] E) p.1 * e + algebraMap K (K ⊗[F] E) p.2 * (1 - e)
      map_one' := by simp only [Prod.fst_one, Prod.snd_one, map_one]; ring
      map_mul' := by
        intro p q
        simp only [Prod.fst_mul, Prod.snd_mul, map_mul]
        linear_combination (-(algebraMap K (K ⊗[F] E) p.1 - algebraMap K (K ⊗[F] E) p.2) *
          (algebraMap K (K ⊗[F] E) q.1 - algebraMap K (K ⊗[F] E) q.2)) * hee
      map_zero' := by simp
      map_add' := by
        intro p q
        simp only [Prod.fst_add, Prod.snd_add, map_add (f := _)]
        ring }
  have hψ : ∀ p, ψ p = algebraMap K (K ⊗[F] E) p.1 * e + algebraMap K (K ⊗[F] E) p.2 * (1 - e) :=
    fun p => rfl
  have he0 : e ≠ 0 := by
    intro h0
    have := hse
    rw [h0, map_zero, sub_zero] at this
    exact hnt this.symm
  have he1 : 1 - e ≠ 0 := by
    intro h0
    have h1 : e = 1 := by linear_combination -h0
    have := hse
    rw [h1, map_one, sub_self] at this
    exact hnt this
  have hinj : Function.Injective ψ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro p hp
    rw [hψ] at hp
    have h1 : algebraMap K (K ⊗[F] E) p.1 * e = 0 := by
      have := congrArg (· * e) hp
      simp only [zero_mul] at this
      linear_combination this - (algebraMap K (K ⊗[F] E) p.1 - algebraMap K (K ⊗[F] E) p.2) * hee
    have h2' : algebraMap K (K ⊗[F] E) p.2 * (1 - e) = 0 := by
      linear_combination hp - h1
    rw [← Algebra.smul_def] at h1 h2'
    have e1 := (smul_eq_zero.1 h1).resolve_right he0
    have e2 := (smul_eq_zero.1 h2').resolve_right he1
    exact Prod.ext e1 e2
  have hsurj : Function.Surjective ψ := by
    intro r
    obtain ⟨x, y, rfl⟩ := hdec r
    refine ⟨(x + y * c, x - y * c), ?_⟩
    rw [hψ, he]
    simp only [map_add (f := _), map_sub, map_mul]
    linear_combination (algebraMap K (K ⊗[F] E) y * (ac - A) + 2 * algebraMap K (K ⊗[F] E) y * A) * h2i +
      (2 * algebraMap K (K ⊗[F] E) y * a2i * A) * hci
  let Ψ : K × K ≃+* K ⊗[F] E := RingEquiv.ofBijective ψ ⟨hinj, hsurj⟩
  refine ⟨Ψ.symm, ?_⟩
  intro r
  obtain ⟨p, rfl⟩ := hsurj r
  have : sigT σ (ψ p) = ψ p.swap := by
    rw [hψ, hψ, map_add (f := _), map_mul, map_mul, sigT_algebraMap, sigT_algebraMap, map_sub, map_one, hse]
    simp only [Prod.fst_swap, Prod.snd_swap]
    ring
  have hΨ : ∀ q, Ψ.symm (ψ q) = q := fun q => Ψ.symm_apply_apply q
  rw [this, hΨ, hΨ]

end PI.UnitaryGroupMassFormula.AdIndexEq.SplitIso

end
end
