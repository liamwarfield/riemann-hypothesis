module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelStandardCharacter
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CentralEigenThetaIsFockVectorBoundedDegree
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BilinearVacuumNonzeroCuspForm
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealCentreActsByCharacterOnIsotypicSlices
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BilinearVacuumCentralCharacter
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleThetaUnfoldingEquivariantUnitaryGroups
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SemicharacterSqEqOneOnHalfA
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.LatLevel
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.LatSelf

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RepresentsOfLink
section -- merged from Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.UnimodularTower
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChainOnto
open scoped TensorProduct InnerProductSpace ComplexConjugate

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnimodularTower

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev Fn (D : D7) (u : D.what₂.Word) (i : ℕ) : Type := Formalism.MainNotions.product_first_zeroth_parts.Fn D u i

abbrev Fm (D : D7) (u : D.what₂.Word) (i : ℕ) : Submodule ℂ (Fn D u i) := (D.fm u).Fi i

abbrev Ram (D : D7) (u : D.what₂.Word) (i : ℕ) : Submodule ℂ (Fn D u i) := Formalism.MainNotions.product_first_zeroth_parts.MramI D u i

abbrev Eps (D : D7) (u : D.what₂.Word) : Type := ∀ v : (D.mem u).A.vT, ((D.mem u).A.Fv v)ˣ

def colPar (D : D7) (u : D.what₂.Word) (j : ℕ) : D.what₂.Tau → SPar :=
  (TPar.ofWord D u (Ptw D).eta (Ptw D).eta_half).Xpar j

def dcos {V : HSp D} (R : Subgroup (GA D V)) (b : GA D V) (K : Subgroup (GA D V)) : Set (GA D V) :=
  {h | ∃ r ∈ R, ∃ x ∈ GinfC V, ∃ κ ∈ K, h = r * x * b * κ}

structure RowOn (V : HSp D) where
  par : D.what₂.Tau → SPar
  M : DSModel V par
  Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)
  β : GL (Fin V.rank) (Lev.EAf D)
  L : LevDat D.host.E ℂ V.rank
  ν : Measure (GA D V)
  fd : Set (GA D V)

abbrev RowOn.st {V : HSp D} (r : RowOn V) : PiLocalization₂ D := ⟨V, r.par, r.M, r.Λ, r.β, r.L, r.ν, r.fd⟩

structure ColOn (c : Com D) (u : D.what₂.Word) (X : HSp D) (j : ℕ) where
  M : DSModel X (colPar D u j)
  K : Subgroup (GA D X)
  a : Fm D u j →ₗ[ℂ] MultT c.θ M (K : Set (GA D X)) (fun _ => 1)

variable {c : Com D} {u : D.what₂.Word}

structure ColStep {X X' : HSp D} {j : ℕ} (A : ColOn c u X j) (A' : ColOn c u X' (j + 1)) where
  om : Om X X'
  f : WO X X' → ℂ
  it : PolF D X'.rank X.rank →ₗ[ℂ] SmT A.M →ₗ[ℂ] SmT A'.M

section ColStep

variable {X X' : HSp D} {j : ℕ} {A : ColOn c u X j} {A' : ColOn c u X' (j + 1)}

end ColStep

structure Node (c : Com D) (u : D.what₂.Word) (ρ j : ℕ) where
  B : BesLev D ρ
  row : RowOn B.V
  col : ColOn c u B.A j
  b : GA D B.V

structure Dbl {σ j : ℕ} (N : Node c u (σ + 1) j) (N' : Node c u σ (j + 1 + 1)) where
  J : JacLev D (σ + 1)
  row : RowOn J.W
  col : ColOn c u J.W₀ (j + 1)
  b : GA D J.W
  s₁ : StepBF c.ψ N.B J
  s₂ : StepFB c.ψ J N'.B
  l : Link N.B N'.B.L N'.B.ζ
  vL : VolM D N'.B.L.rank J.W₀.rank
  p₁ : ChainOnto.Step c N.row.st row.st
  p₂ : ChainOnto.Step c row.st N'.row.st
  k₁ : ColStep N.col col
  k₂ : ColStep col N'.col
  ε : Eps D u

section Dbl

variable {σ j : ℕ} {N : Node c u (σ + 1) j} {N' : Node c u σ (j + 1 + 1)}

end Dbl

structure Fin2 {j : ℕ} (N : Node c u 0 j) {T : HSp D} (top : RowOn T) where
  t : Last c.ψ T N.B
  row : RowOn t.J.W
  col₁ : ColOn c u t.J.W (j + 1)
  X : HSp D
  L : HSp D
  o : OrthDec X T L
  col₂ : ColOn c u X (j + 1 + 1)
  p₁ : ChainOnto.Step c N.row.st row.st
  p₂ : ChainOnto.Step c row.st top.st
  k₁ : ColStep N.col col₁
  k₂ : ColStep col₁ col₂
  ε : Eps D u
  ι : (D.mem u).P.Mt ≃ₗ[ℂ] top.st.CC c
  br : SmT col₂.M →ₗ[ℂ] SmT top.M →ₗ[ℂ] ℂ

section Fin2

variable {j : ℕ} {N : Node c u 0 j} {T : HSp D} {top : RowOn T}

end Fin2

end GlobalTheory.IndefiniteRowSideFullHecke.UnimodularTower

end
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.IndefiniteRowSideFullHecke.UnimodularTower
open GlobalTheory.ChainOnto (Com PiLocalization₂)
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSawCompare

variable {D : D7} {u : D.what₂.Word}

theorem defSp_is {V : HSp D} (hs : V.SigOK) (hp : V.IsPosDef) {S : D.what₂.Tau → SPar} (M : DSModel V S) (x : DefSp V)
    (h1 : x.s = cart M) (h2 : x.B = onb M) (h3 : IsSelfDualC V x.L) : x.Is := by
  have hs' : ∀ τ, Formalism.UG.HasSignature (gramAt D V τ) V.rank 0 := fun τ => by
    have := hs (tauE D τ)
    rw [hp (tauE D τ)] at this
    exact this
  have hJ : ∀ τ, Formalism.REAL.Jm (M.ε τ) = 1 := fun τ => by
    have := signs_pos_of_frame_gram_posdef (M.ε τ) (M.fr τ) _ (M.fr_gram τ) (hs' τ)
    unfold Formalism.REAL.Jm; simp [this]
  have hd := fun τ => (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have hc : ∀ τ, x.s τ = 1 := fun τ => by rw [h1, cart, hJ, Matrix.mul_one, Matrix.nonsing_inv_mul _ (hd τ)]
  refine ⟨hs, Inh.coCpt_of_isDefinite hs fun τ => Or.inl (hp τ), fun τ => ?_, fun τ => Or.inl (hc τ), fun τ => ?_, h3⟩
  · rw [hc]
    exact ⟨by simp, by simp, by simpa using Formalism.IndefR.Fin.Lifts.posDef_of_sig _ (hs' τ)⟩
  · refine ⟨V.rank, fun _ => 1, fun a => Or.inl ⟨rfl, a.2⟩, ?_, by simp [hc]⟩
    rw [h2, onb, ← M.fr_gram τ, hJ, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul,
      Matrix.mul_nonsing_inv _ (hd τ), Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_nonsing_inv _ (hd τ)]
    simp

abbrev Live (D : D7) (u : D.what₂.Word) : Type := ∀ j, Submodule ℂ (Fn D u j)

variable (W : Live D u) {c : Com D}

section Dbl

variable {σ j : ℕ} {N : Node c u (σ + 1) j} {N' : Node c u σ (j + 1 + 1)} (d : Dbl N N')

end Dbl

section Fin2

variable {j : ℕ} {N : Node c u 0 j} {T : HSp D} {top : RowOn T} (e : Fin2 N top)

end Fin2

variable {W}

section Step

variable {X X' : HSp D} {j : ℕ} {A : ColOn c u X j} {A' : ColOn c u X' (j + 1)} {k : ColStep A A'} {vol : Vol X}

end Step

end GlobalTheory.SeeSawCompare

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubMemOfMkEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinDecomp

section Quot

variable {V : Type} [AddCommGroup V]

abbrev mLat (m : ℕ) (Λ : AddSubgroup V) : AddSubgroup V := Λ.map (nsmulAddMonoidHom m)

abbrev Qm (m : ℕ) (Λ : AddSubgroup V) : Type := Λ ⧸ (mLat m Λ).addSubgroupOf Λ

def repm {m : ℕ} {Λ : AddSubgroup V} (q : Qm m Λ) : V := ((Quotient.out q : Λ) : V)

theorem mem_mLat {m : ℕ} {Λ : AddSubgroup V} {x : V} : x ∈ mLat m Λ ↔ ∃ l ∈ Λ, m • l = x := by
  simp [mLat]

theorem repm_mem {m : ℕ} {Λ : AddSubgroup V} (q : Qm m Λ) : repm q ∈ Λ := (Quotient.out q : Λ).2

theorem mk_repm {m : ℕ} {Λ : AddSubgroup V} (q : Qm m Λ) :
    (QuotientAddGroup.mk (⟨repm q, repm_mem q⟩ : Λ) : Qm m Λ) = q := by
  have : (⟨repm q, repm_mem q⟩ : Λ) = Quotient.out q := rfl
  rw [this]
  exact QuotientAddGroup.out_eq' q

theorem sub_mem_of_mk_eq {m : ℕ} {Λ : AddSubgroup V} {a b : V} (ha : a ∈ Λ) (hb : b ∈ Λ)
    (h : (QuotientAddGroup.mk (⟨a, ha⟩ : Λ) : Qm m Λ) = QuotientAddGroup.mk (⟨b, hb⟩ : Λ)) : b - a ∈ mLat m Λ := by
  rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at h
  simpa [sub_eq_neg_add] using h

theorem repm_mk_sub {m : ℕ} {Λ : AddSubgroup V} {a : V} (ha : a ∈ Λ) :
    repm (QuotientAddGroup.mk (⟨a, ha⟩ : Λ) : Qm m Λ) - a ∈ mLat m Λ :=
  sub_mem_of_mk_eq (m := m) ha (repm_mem _) (mk_repm _).symm

theorem repm_add_sub {m : ℕ} {Λ : AddSubgroup V} (q q' : Qm m Λ) :
    repm (q + q') - (repm q + repm q') ∈ mLat m Λ := by
  refine sub_mem_of_mk_eq (m := m) (Λ.add_mem (repm_mem q) (repm_mem q')) (repm_mem (q + q')) ?_
  rw [mk_repm]
  conv_rhs => rw [← mk_repm q, ← mk_repm q']
  rfl

theorem repm_zero_mem {m : ℕ} {Λ : AddSubgroup V} : repm (0 : Qm m Λ) ∈ mLat m Λ := by
  have h := repm_mk_sub (m := m) (Λ := Λ) Λ.zero_mem
  have h0 : (QuotientAddGroup.mk (⟨0, Λ.zero_mem⟩ : Λ) : Qm m Λ) = 0 := rfl
  rw [h0, sub_zero] at h
  exact h

end Quot

variable {D : D7}

def lamE (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (e : AE D) (x : WO S T) : ℂ :=
  ψ (symplOH S T (e • x) (cA D e • x))

end GlobalTheory.FinDecomp

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OrientedThetaEqFiniteHeisenbergTranslatesVacua
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymplOSmulAddSmulAdd
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum NumberField GlobalTheory.FinDecomp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinDecomp

theorem mem_of_compl_smul {D : D7} {S T : HSp D} {Λ : AddSubgroup (WO S T)} {e : AE D}
    (he : ∀ u ∈ Λ, e • u ∈ Λ) (hc : ∀ u ∈ Λ, cA D e • u ∈ Λ) {y : WO S T} (hy : y ∈ Λ) :
    (1 - e - cA D e) • y ∈ Λ := by
  rw [sub_smul, sub_smul, one_smul]
  exact Λ.sub_mem (Λ.sub_mem hy (he y hy)) (hc y hy)

theorem half_mul_two (D : D7) : algebraMap D.host.F (AF D.host.F) (1 / 2) * 2 = 1 := by
  rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul]
  norm_num

theorem symplO_split_two {D : D7} {S T : HSp D} {e : AE D} (h1 : e * e = e) (h2 : e * cA D e = 0)
    {x y z : WO S T} (hzx : (1 - e - cA D e) • x = 2 • z) :
    symplO S T x y = symplO S T (e • x) (cA D e • y) + symplO S T (cA D e • x) (e • y) +
      (symplO S T z ((1 - e - cA D e) • y) + symplO S T z ((1 - e - cA D e) • y)) := by
  have hsplit := GlobalTheory.AdForm.HalfASign.symplO_split (S := S) (T := T) h1 h2 x y
  rw [hzx, two_nsmul, GlobalTheory.PlaceModel.symplO_add_left S T] at hsplit
  exact hsplit

theorem symplO_smul_add_smul_add {D : D7} (S T : HSp D) (e : AE D) (x y : WO S T) :
    symplO S T (e • (x + y)) (cA D e • (x + y)) = symplO S T (e • x) (cA D e • x) + symplO S T (e • x) (cA D e • y) +
      (symplO S T (e • y) (cA D e • x) + symplO S T (e • y) (cA D e • y)) := by
  rw [smul_add, smul_add, GlobalTheory.PlaceModel.symplO_add_left S T, GlobalTheory.PlaceModel.symplO_add_right S T,
    GlobalTheory.PlaceModel.symplO_add_right S T]

theorem symplOH_lamE_arg {D : D7} {S T : HSp D} {e : AE D} (h1 : e * e = e) (h2 : e * cA D e = 0)
    {x y z : WO S T} (hzx : (1 - e - cA D e) • x = 2 • z) :
    symplOH S T (e • x) (cA D e • x) + symplOH S T (e • y) (cA D e • y) + symplOH S T x y =
      symplOH S T (e • (x + y)) (cA D e • (x + y)) +
        (symplO S T (cA D e • x) (e • y) + symplO S T z ((1 - e - cA D e) • y)) := by
  unfold symplOH
  rw [symplO_split_two h1 h2 hzx, symplO_smul_add_smul_add S T e x y,
    GlobalTheory.PlaceModel.symplO_skew S T (cA D e • x) (e • y)]
  have hh := half_mul_two D
  generalize algebraMap D.host.F (AF D.host.F) (1 / 2) = h at hh ⊢
  generalize symplO S T (e • x) (cA D e • x) = a1
  generalize symplO S T (e • y) (cA D e • y) = a2
  generalize symplO S T (e • x) (cA D e • y) = a3
  generalize symplO S T (cA D e • x) (e • y) = a4
  generalize symplO S T z ((1 - e - cA D e) • y) = a5
  linear_combination (a4 + a5) * hh

theorem lamE_add_of_lattice : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Λ : AddSubgroup (WO S T)) (e : AE D), e * e = e → e * cA D e = 0 → (∀ x ∈ Λ, ∀ y ∈ Λ, ψ (symplO S T x y) = 1) → (∀ u ∈ Λ, e • u ∈ Λ) → (∀ u ∈ Λ, cA D e • u ∈ Λ) → (∀ u ∈ Λ, ∃ z ∈ Λ, (1 - e - cA D e) • u = 2 • z) → ∀ x ∈ Λ, ∀ y ∈ Λ, lamE ψ S T e (x + y) = lamE ψ S T e x * lamE ψ S T e y * ψ (symplOH S T x y) := by
  intro D ψ S T Λ e h1 h2 hψ he hc hr x hx y hy
  obtain ⟨z, hz, hzx⟩ := hr x hx
  have key := symplOH_lamE_arg (y := y) h1 h2 hzx
  have k1 : ψ (symplO S T (cA D e • x) (e • y)) = 1 := hψ _ (hc x hx) _ (he y hy)
  have k2 : ψ (symplO S T z ((1 - e - cA D e) • y)) = 1 := hψ _ hz _ (mem_of_compl_smul he hc hy)
  have := congrArg ψ key
  rw [AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, k1, k2,
    mul_one, mul_one] at this
  unfold lamE
  exact this.symm

end GlobalTheory.FinDecomp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceIdemEqSingle
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum NumberField GlobalTheory.FinDecomp IsDedekindDomain
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwoPlaceIdem

variable {D : D7}

theorem AF_ext {F : Type} [Field F] [NumberField F] {x y : AF F} (h1 : fstA F x = fstA F y)
    (h2 : sndA F x = sndA F y) : x = y := Prod.ext h1 h2

theorem fstA_pairA {F : Type} [Field F] [NumberField F] (a : Ainf F) (b : Af F) : fstA F (pairA F a b) = a := rfl

theorem sndA_pairA {F : Type} [Field F] [NumberField F] (a : Ainf F) (b : Af F) : sndA F (pairA F a b) = b := rfl

theorem placeIdem_eq_single
    (hsv : ∀ v : HeightOneSpectrum (𝓞 D.host.F), singleV D.host.F v 1 ∈ intAf D.host.F ∧
      evalV D.host.F v (singleV D.host.F v 1) = 1 ∧ ∀ v', v' ≠ v → evalV D.host.F v' (singleV D.host.F v 1) = 0)
    {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (h : IsPlaceIdem D v ε) :
    ε = pairA D.host.F 0 (singleV D.host.F v 1) := by
  obtain ⟨α, rfl, h1, h0⟩ := h
  congr 1
  refine Subtype.ext (funext fun u => ?_)
  change evalV D.host.F u α = evalV D.host.F u (singleV D.host.F v 1)
  by_cases huv : u = v
  · subst huv; rw [h1, (hsv u).2.1]
  · rw [h0 u huv, (hsv v).2.2 u huv]

theorem single_mul_single
    (hsv : ∀ v : HeightOneSpectrum (𝓞 D.host.F), singleV D.host.F v 1 ∈ intAf D.host.F ∧
      evalV D.host.F v (singleV D.host.F v 1) = 1 ∧ ∀ v', v' ≠ v → evalV D.host.F v' (singleV D.host.F v 1) = 0)
    {v w : HeightOneSpectrum (𝓞 D.host.F)} (hvw : v ≠ w) :
    pairA D.host.F 0 (singleV D.host.F v 1) * pairA D.host.F 0 (singleV D.host.F w 1) = 0 := by
  refine AF_ext ?_ ?_
  · rw [map_mul, fstA_pairA, fstA_pairA, map_zero, mul_zero]
  · rw [map_mul, sndA_pairA, sndA_pairA, map_zero]
    refine Subtype.ext (funext fun u => ?_)
    change evalV D.host.F u (singleV D.host.F v 1 * singleV D.host.F w 1) = evalV D.host.F u 0
    rw [map_mul, map_zero]
    by_cases huv : u = v
    · subst huv; rw [(hsv w).2.2 u hvw, mul_zero]
    · rw [(hsv v).2.2 u huv, zero_mul]

theorem finPart_algebraMap (x : AF D.host.F) :
    finPart D (algebraMap (AF D.host.F) (AE D) x) = sndA D.host.F x ⊗ₜ[D.host.F] (1 : D.host.E) := by
  change (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E))
      (algebraMap (AF D.host.F) (AE D) x) = _
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.map_tmul]
  rfl

set_option maxHeartbeats 1000000 in
theorem exists_idem_half : ∀ (D : D7), ∃ e : AE D, e * e = e ∧ e * cA D e = 0 ∧ finPart D e ∈ intAE D ∧
    finPart D (cA D e) ∈ intAE D ∧ ∃ h : AE D, finPart D h ∈ intAE D ∧ 2 * h = 1 - e - cA D e := by
  intro D
  obtain ⟨P, hP2, hsv, β, hβ, h1⟩ := GlobalTheory.LatVac.one_eq_sum_singleV_add_two_mul D.host.F
  have H : ∀ v ∈ P, ∃ e : AE D, e * e = e ∧ e * cA D e = 0 ∧
      e + cA D e = algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleV D.host.F v 1)) := by
    intro v hv
    obtain ⟨e, ε, he, hε, hs⟩ := Formalism.IndefR.Fin.twoSplitIdem D v (hP2 v hv)
    exact ⟨e, he.1, he.2.1, by rw [hs, placeIdem_eq_single hsv hε]⟩
  choose! E hEE hEc hEs using H
  have absE : ∀ v ∈ P, E v = E v * algebraMap _ (AE D) (pairA D.host.F 0 (singleV D.host.F v 1)) := by
    intro v hv; rw [← hEs v hv, mul_add, hEE v hv, hEc v hv, add_zero]
  have absC : ∀ v ∈ P, cA D (E v) = cA D (E v) * algebraMap _ (AE D) (pairA D.host.F 0 (singleV D.host.F v 1)) := by
    intro v hv
    rw [← hEs v hv, mul_add, mul_comm (cA D (E v)) (E v), hEc v hv, ← map_mul, hEE v hv, zero_add]
  have cross : ∀ (x y : AE D) (v w : HeightOneSpectrum (𝓞 D.host.F)), v ≠ w →
      x = x * algebraMap _ (AE D) (pairA D.host.F 0 (singleV D.host.F v 1)) →
      y = y * algebraMap _ (AE D) (pairA D.host.F 0 (singleV D.host.F w 1)) → x * y = 0 := by
    intro x y v w hvw hx hy
    calc x * y = (x * algebraMap _ (AE D) (pairA D.host.F 0 (singleV D.host.F v 1))) *
          (y * algebraMap _ (AE D) (pairA D.host.F 0 (singleV D.host.F w 1))) := by rw [← hx, ← hy]
      _ = x * y * algebraMap _ (AE D) (pairA D.host.F 0 (singleV D.host.F v 1) *
          pairA D.host.F 0 (singleV D.host.F w 1)) := by rw [map_mul]; ring
      _ = 0 := by rw [single_mul_single hsv hvw, map_zero, mul_zero]
  have hee : (∑ v ∈ P, E v) * (∑ v ∈ P, E v) = ∑ v ∈ P, E v := by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [Finset.sum_eq_single v (fun w hw hwv => cross _ _ v w (Ne.symm hwv) (absE v hv) (absE w hw))
      (fun h => absurd hv h), hEE v hv]
  have hec : (∑ v ∈ P, E v) * cA D (∑ v ∈ P, E v) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_eq_zero fun v hv => ?_
    rw [Finset.sum_eq_single v (fun w hw hwv => cross _ _ v w (Ne.symm hwv) (absE v hv) (absC w hw))
      (fun h => absurd hv h), hEc v hv]
  have hsum : (∑ v ∈ P, E v) + cA D (∑ v ∈ P, E v) =
      algebraMap (AF D.host.F) (AE D) (∑ v ∈ P, pairA D.host.F 0 (singleV D.host.F v 1)) := by
    have hcs : cA D (∑ v ∈ P, E v) = ∑ v ∈ P, cA D (E v) := map_sum (cA D) E P
    calc (∑ v ∈ P, E v) + cA D (∑ v ∈ P, E v) = (∑ v ∈ P, E v) + ∑ v ∈ P, cA D (E v) := congrArg (fun z => (∑ v ∈ P, E v) + z) hcs
      _ = ∑ v ∈ P, (E v + cA D (E v)) := Finset.sum_add_distrib.symm
      _ = ∑ v ∈ P, algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 (singleV D.host.F v 1)) :=
          Finset.sum_congr rfl fun v hv => hEs v hv
      _ = algebraMap (AF D.host.F) (AE D) (∑ v ∈ P, pairA D.host.F 0 (singleV D.host.F v 1)) := (map_sum _ _ _).symm
  have hi1 : finPart D (∑ v ∈ P, E v) ∈ intAE D :=
    GlobalTheory.AdIdem.idempotent_mem_intAE D _ ((map_mul (finPart D) _ _).symm.trans (congrArg (finPart D) hee))
  have hi2 : finPart D (cA D (∑ v ∈ P, E v)) ∈ intAE D :=
    GlobalTheory.AdIdem.idempotent_mem_intAE D _ ((map_mul (finPart D) _ _).symm.trans
      (congrArg (finPart D) ((map_mul (cA D) _ _).symm.trans (congrArg (cA D) hee))))
  refine ⟨∑ v ∈ P, E v, hee, hec, hi1, hi2, ?_⟩
  refine ⟨algebraMap (AF D.host.F) (AE D) (pairA D.host.F (algebraMap D.host.F _ (1 / 2)) β), ?_, ?_⟩
  · rw [finPart_algebraMap, sndA_pairA]
    exact AddSubgroup.subset_closure ⟨β, hβ, 1, by simp⟩
  · have key : 2 * pairA D.host.F (algebraMap D.host.F _ (1 / 2)) β =
        1 - ∑ v ∈ P, pairA D.host.F 0 (singleV D.host.F v 1) := by
      refine AF_ext ?_ ?_
      · set_option synthInstance.maxHeartbeats 100000 in
          rw [map_mul, map_sub, map_sum, map_one, map_ofNat, fstA_pairA]
        simp only [fstA_pairA, Finset.sum_const_zero, sub_zero]
        rw [← map_ofNat (algebraMap D.host.F (Ainf D.host.F)) 2, ← map_mul]
        norm_num
      · set_option synthInstance.maxHeartbeats 100000 in
          rw [map_mul, map_sub, map_sum, map_one, map_ofNat, sndA_pairA]
        simp only [sndA_pairA]
        linear_combination -h1
    calc (2 : AE D) * algebraMap (AF D.host.F) (AE D) (pairA D.host.F (algebraMap D.host.F _ (1 / 2)) β)
        = algebraMap (AF D.host.F) (AE D) (2 * pairA D.host.F (algebraMap D.host.F _ (1 / 2)) β) := by
          rw [show (2 : AE D) = algebraMap (AF D.host.F) (AE D) 2 from (map_ofNat _ 2).symm]
          exact (map_mul _ _ _).symm
      _ = algebraMap (AF D.host.F) (AE D) (1 - ∑ v ∈ P, pairA D.host.F 0 (singleV D.host.F v 1)) :=
          congrArg _ key
      _ = 1 - algebraMap (AF D.host.F) (AE D) (∑ v ∈ P, pairA D.host.F 0 (singleV D.host.F v 1)) := by
          rw [map_sub, map_one]
      _ = 1 - ((∑ v ∈ P, E v) + cA D (∑ v ∈ P, E v)) := by rw [hsum]
      _ = 1 - ∑ v ∈ P, E v - cA D (∑ v ∈ P, E v) := by rw [sub_sub]

end GlobalTheory.TwoPlaceIdem
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymplOInvSmulNsmul
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum NumberField GlobalTheory.FinDecomp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinDecomp

variable {D : D7} {S T : HSp D}

theorem cA_incA_inv_natCast (m : ℕ) : cA D (incA D ((m : D.host.E)⁻¹)) = incA D ((m : D.host.E)⁻¹) := by
  rw [GlobalTheory.DualPairCheck.cA_incA, star_inv₀, star_natCast]

theorem symplO_inv_smul_nsmul {m : ℕ} (hm : 0 < m) (y l : WO S T) :
    symplO S T (incA D ((m : D.host.E)⁻¹) • y) (m • l) = symplO S T y l := by
  rw [GlobalTheory.PlaceModel.symplO_smul, cA_incA_inv_natCast, GlobalTheory.PlaceModel.inv_smul_nsmul S T hm]

theorem symplO_inv_smul_swap (m : ℕ) (x u : WO S T) :
    symplO S T (incA D ((m : D.host.E)⁻¹) • x) u = -symplO S T (incA D ((m : D.host.E)⁻¹) • u) x := by
  rw [GlobalTheory.PlaceModel.symplO_skew S T x (incA D ((m : D.host.E)⁻¹) • u), neg_neg, GlobalTheory.PlaceModel.symplO_smul,
    cA_incA_inv_natCast]

theorem map_infPart_smul (a : AE D) {r : WO S T} (hr : r.map (infPart D) = 0) : (a • r).map (infPart D) = 0 := by
  ext i j
  have hij := congrFun (congrFun hr i) j
  simp only [Matrix.map_apply, Matrix.zero_apply] at hij ⊢
  rw [Matrix.smul_apply, smul_eq_mul, map_mul, hij, mul_zero]

theorem nsmul_inv_smul {m : ℕ} (hm : 0 < m) (x : WO S T) : m • (incA D ((m : D.host.E)⁻¹) • x) = x := by
  rw [smul_comm, GlobalTheory.PlaceModel.inv_smul_nsmul S T hm]

theorem psi_shift {ψ : AddChar (AF D.host.F) ℂ} {Λ : AddSubgroup (WO S T)} {m : ℕ} (hm : 0 < m)
    (hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, ψ (symplO S T x y) = 1) {r : WO S T} (hr : r ∈ Λ) {x : WO S T} (hx : x ∈ mLat m Λ) :
    ψ (symplO S T (incA D ((m : D.host.E)⁻¹) • x) r) = 1 := by
  obtain ⟨l, hl, rfl⟩ := mem_mLat.1 hx
  rw [GlobalTheory.PlaceModel.inv_smul_nsmul S T hm]
  exact hΛ l hl r hr

def qCharM (ψ : AddChar (AF D.host.F) ℂ) (Λ : AddSubgroup (WO S T)) (m : ℕ) (hm : 0 < m)
    (hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, ψ (symplO S T x y) = 1) (r : WO S T) (hr : r ∈ Λ) : AddChar (Qm m Λ) ℂ where
  toFun u := ψ (symplO S T (incA D ((m : D.host.E)⁻¹) • repm u) r)
  map_zero_eq_one' := psi_shift hm hΛ hr repm_zero_mem
  map_add_eq_mul' a b := by
    have h := psi_shift hm hΛ hr (repm_add_sub a b)
    have e : repm (a + b) = (repm (a + b) - (repm a + repm b)) + repm a + repm b := by abel
    rw [e, smul_add, smul_add, GlobalTheory.PlaceModel.symplO_add_left, GlobalTheory.PlaceModel.symplO_add_left,
      AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, h, one_mul]

theorem qCharM_apply (ψ : AddChar (AF D.host.F) ℂ) (Λ : AddSubgroup (WO S T)) (m : ℕ) (hm : 0 < m)
    (hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, ψ (symplO S T x y) = 1) (r : WO S T) (hr : r ∈ Λ) (u : Qm m Λ) :
    qCharM ψ Λ m hm hΛ r hr u = ψ (symplO S T (incA D ((m : D.host.E)⁻¹) • repm u) r) := rfl

theorem qCharM_mk (ψ : AddChar (AF D.host.F) ℂ) (Λ : AddSubgroup (WO S T)) (m : ℕ) (hm : 0 < m)
    (hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, ψ (symplO S T x y) = 1) (r : WO S T) (hr : r ∈ Λ) {u : WO S T} (hu : u ∈ Λ) :
    qCharM ψ Λ m hm hΛ r hr (QuotientAddGroup.mk (⟨u, hu⟩ : Λ)) = ψ (symplO S T (incA D ((m : D.host.E)⁻¹) • u) r) := by
  rw [qCharM_apply]
  have h := psi_shift hm hΛ hr (repm_mk_sub (m := m) hu)
  have e : repm (QuotientAddGroup.mk (⟨u, hu⟩ : Λ) : Qm m Λ) =
      (repm (QuotientAddGroup.mk (⟨u, hu⟩ : Λ) : Qm m Λ) - u) + u := by abel
  rw [e, smul_add, GlobalTheory.PlaceModel.symplO_add_left, AddChar.map_add_eq_mul, h, one_mul]

theorem qCharM_eq_zero_iff {ψ : AddChar (AF D.host.F) ℂ} {Λ : AddSubgroup (WO S T)} {m : ℕ} (hm : 0 < m)
    (hinf : ∀ u ∈ Λ, u.map (infPart D) = 0) (hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, ψ (symplO S T x y) = 1)
    (hmax : ∀ x : WO S T, x.map (infPart D) = 0 → (∀ u ∈ Λ, ψ (symplO S T x u) = 1) → x ∈ Λ)
    {r : WO S T} (hr : r ∈ Λ) : qCharM ψ Λ m hm hΛ r hr = 0 ↔ r ∈ mLat m Λ := by
  constructor
  · intro h0
    have hx : incA D ((m : D.host.E)⁻¹) • r ∈ Λ := by
      refine hmax _ (map_infPart_smul _ (hinf r hr)) fun u hu => ?_
      have h1 := qCharM_mk ψ Λ m hm hΛ r hr hu
      rw [h0, AddChar.zero_apply] at h1
      rw [symplO_inv_smul_swap, AddChar.map_neg_eq_inv, ← h1, inv_one]
    exact mem_mLat.2 ⟨_, hx, nsmul_inv_smul hm r⟩
  · intro hrm
    obtain ⟨l, hl, rfl⟩ := mem_mLat.1 hrm
    refine DFunLike.ext _ _ (fun u => ?_)
    rw [qCharM_apply, AddChar.zero_apply, symplO_inv_smul_nsmul hm]
    exact hΛ _ (repm_mem u) _ hl

theorem charSum_selfAnn : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Λ : AddSubgroup (WO S T)) (m : ℕ), 0 < m →
    (∀ u ∈ Λ, u.map (infPart D) = 0) → (∀ x ∈ Λ, ∀ y ∈ Λ, ψ (symplO S T x y) = 1) →
    (∀ x : WO S T, x.map (infPart D) = 0 → (∀ u ∈ Λ, ψ (symplO S T x u) = 1) → x ∈ Λ) →
    ∀ [Fintype (Qm m Λ)] [DecidableEq (Qm m Λ)] (q : Qm m Λ),
      ∑ u : Qm m Λ, ψ (symplO S T (incA D ((m : D.host.E)⁻¹) • repm u) (repm q)) =
        if q = 0 then (Fintype.card (Qm m Λ) : ℂ) else 0 := by
  intro D ψ S T Λ m hm hinf hΛ hmax _ _ q
  have key : qCharM ψ Λ m hm hΛ (repm q) (repm_mem q) = 0 ↔ q = 0 := by
    rw [qCharM_eq_zero_iff hm hinf hΛ hmax (repm_mem q)]
    conv_rhs => rw [← mk_repm q]
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
  classical
  have hs := AddChar.sum_eq_ite (qCharM ψ Λ m hm hΛ (repm q) (repm_mem q))
  simp only [qCharM_apply, key] at hs
  convert hs
end GlobalTheory.FinDecomp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisAvgInvariant
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum NumberField GlobalTheory.FinDecomp
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinDecomp

theorem heisAvg_invariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (Λ : AddSubgroup (WO S T)) (m : ℕ)
    (lam : WO S T → ℂ), (∀ x ∈ Λ, ∀ y ∈ Λ, lam (x + y) = lam x * lam y * ψ (symplOH S T x y)) →
    ∀ [Fintype (Qm m Λ)] (g : WO S T → ℂ), (∀ l ∈ Λ, lam (m • l) • heisO ψ S T (m • l) g = g) →
    ∀ b ∈ Λ, lam b • heisO ψ S T b (∑ q : Qm m Λ, lam (repm q) • heisO ψ S T (repm q) g) =
      ∑ q : Qm m Λ, lam (repm q) • heisO ψ S T (repm q) g := by
  intro D ψ S T Λ m lam hlam _ g hg b hb
  have hsm : ∀ (x : WO S T) (c : ℂ) (f : WO S T → ℂ), heisO ψ S T x (c • f) = c • heisO ψ S T x f := by
    intro x c f; funext w; simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring
  have hsumlin : ∀ (x : WO S T) (F : Qm m Λ → WO S T → ℂ),
      heisO ψ S T x (∑ q, F q) = ∑ q, heisO ψ S T x (F q) := by
    intro x F; funext w; simp only [heisO, Finset.sum_apply, Finset.mul_sum]
  have hmul : ∀ x ∈ Λ, ∀ y ∈ Λ, lam x • heisO ψ S T x (lam y • heisO ψ S T y g) =
      lam (x + y) • heisO ψ S T (x + y) g := by
    intro x hx y hy
    rw [hsm, GlobalTheory.FinTranslate.heisO_heisO, smul_smul, smul_smul, hlam x hx y hy]
  have key : ∀ q : Qm m Λ, lam b • heisO ψ S T b (lam (repm q) • heisO ψ S T (repm q) g) =
      lam (repm ((QuotientAddGroup.mk (⟨b, hb⟩ : Λ) : Qm m Λ) + q)) •
        heisO ψ S T (repm ((QuotientAddGroup.mk (⟨b, hb⟩ : Λ) : Qm m Λ) + q)) g := by
    intro q
    have hbq : b + repm q ∈ Λ := Λ.add_mem hb (repm_mem q)
    rw [hmul b hb _ (repm_mem q)]
    have hmk : (QuotientAddGroup.mk (⟨b + repm q, hbq⟩ : Λ) : Qm m Λ) =
        (QuotientAddGroup.mk (⟨b, hb⟩ : Λ) : Qm m Λ) + q := by
      conv_rhs => rw [← mk_repm q]
      rfl
    have h1 := repm_mk_sub (m := m) hbq
    rw [hmk] at h1
    obtain ⟨l, hl, hl'⟩ := mem_mLat.1 h1
    have he : repm ((QuotientAddGroup.mk (⟨b, hb⟩ : Λ) : Qm m Λ) + q) = (b + repm q) + m • l := by
      rw [hl']; abel
    rw [he, ← hmul _ hbq _ (Λ.nsmul_mem hl m), hg l hl]
  calc lam b • heisO ψ S T b (∑ q : Qm m Λ, lam (repm q) • heisO ψ S T (repm q) g)
      = ∑ q : Qm m Λ, lam (repm ((QuotientAddGroup.mk (⟨b, hb⟩ : Λ) : Qm m Λ) + q)) •
          heisO ψ S T (repm ((QuotientAddGroup.mk (⟨b, hb⟩ : Λ) : Qm m Λ) + q)) g := by
        rw [hsumlin, Finset.smul_sum]
        exact Finset.sum_congr rfl fun q _ => key q
    _ = _ := Equiv.sum_comp (Equiv.addLeft (QuotientAddGroup.mk (⟨b, hb⟩ : Λ) : Qm m Λ))
          (fun q => lam (repm q) • heisO ψ S T (repm q) g)

end GlobalTheory.FinDecomp

end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinDecomp

open GlobalTheory.PlaceModel GlobalTheory.SeeSaw

variable {D : D7} {S T : HSp D}

theorem comb_eq_linearCombination (ψ : AddChar (AF D.host.F) ℂ) (c : WO S T →₀ ℂ) (f : WO S T → ℂ) :
    comb ψ S T c f = Finsupp.linearCombination ℂ (fun u => heisO ψ S T u f) c := by
  rw [Finsupp.linearCombination_apply]; rfl

theorem comb_sum_single {ι : Type} [Fintype ι] (ψ : AddChar (AF D.host.F) ℂ) (x : ι → WO S T) (a : ι → ℂ)
    (f : WO S T → ℂ) :
    comb ψ S T (∑ i, Finsupp.single (x i) (a i)) f = ∑ i, a i • heisO ψ S T (x i) f := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [comb_eq_linearCombination, map_sum]
  exact Finset.sum_congr rfl fun i _ => Finsupp.linearCombination_single _ _ _

theorem isFinComb_sum_single {ι : Type} [Fintype ι] (x : ι → WO S T) (a : ι → ℂ)
    (hx : ∀ i, (x i).map (infPart D) = 0) : IsFinComb (∑ i, Finsupp.single (x i) (a i)) := by
  classical
  intro u hu
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 (Finsupp.support_finsetSum hu)
  have hui : u = x i := Finset.mem_singleton.1 (Finsupp.support_single_subset hi)
  rw [hui]
  exact hx i

theorem map_infPart_add_neg {x y : WO S T} (hx : x.map (infPart D) = 0) (hy : y.map (infPart D) = 0) :
    (x + -y).map (infPart D) = 0 := by
  ext i j
  have h1 : infPart D (x i j) = 0 := congrFun (congrFun hx i) j
  have h2 : infPart D (y i j) = 0 := congrFun (congrFun hy i) j
  show infPart D (x i j + -y i j) = 0
  rw [map_add (f := _), map_neg, h1, h2, neg_zero, add_zero]

theorem symplO_neg_right (x y : WO S T) : symplO S T x (-y) = -symplO S T x y := by
  have h := symplO_add_right S T x y (-y)
  rw [add_neg_cancel, symplO_zero_right] at h
  linear_combination -h

theorem symplO_self (x : WO S T) : symplO S T x x = 0 := by
  have h := symplO_skew S T x x
  have hh := half_mul_two D
  linear_combination (algebraMap D.host.F (AF D.host.F) (1 / 2)) * h - symplO S T x x * hh

theorem heisL_cancel (ψ : AddChar (AF D.host.F) ℂ) (x : WO S T) (f : WO S T → ℂ) :
    heisL S T ψ x (heisL S T ψ (-x) f) = f := by
  rw [heisL_heisL, symplOH, symplO_neg_right, symplO_self, neg_zero, mul_zero, AddChar.map_zero_eq_one, one_smul,
    add_neg_cancel]
  funext w
  change ψ (symplOH S T w 0) * f (w + 0) = f w
  rw [symplOH, symplO_zero_right, mul_zero, AddChar.map_zero_eq_one, one_mul, add_zero]

theorem lamE_two_nsmul {ψ : AddChar (AF D.host.F) ℂ} {Λ : AddSubgroup (WO S T)} {e : AE D}
    (hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, ψ (symplO S T x y) = 1) (he : ∀ u ∈ Λ, e • u ∈ Λ) (hc : ∀ u ∈ Λ, cA D e • u ∈ Λ)
    {u : WO S T} (hu : u ∈ Λ) : lamE ψ S T e (2 • u) = 1 := by
  have h := hΛ _ (he u hu) _ (hc _ (Λ.nsmul_mem hu 2))
  rw [← h]
  unfold lamE symplOH
  congr 1
  rw [two_nsmul u, smul_add e, symplO_add_left]
  have hh := half_mul_two D
  linear_combination (symplO S T (e • u) (cA D e • (u + u))) * hh

theorem lamE_half {ψ : AddChar (AF D.host.F) ℂ} (e : AE D) {e' : AE D} (he' : e' * cA D e' = 0) {u : WO S T}
    (hu : IsHalf e' u) : lamE ψ S T e u = 1 := by
  have h : e' • u = u := (isHalf_iff S T).1 hu
  have h1 : e • u = e' • (e • u) := by rw [smul_comm, h]
  have h2 : cA D e' • (cA D e • u) = 0 := by
    rw [smul_comm, ← h, smul_smul (cA D e'), mul_comm, he', zero_smul, smul_zero]
  unfold lamE symplOH
  rw [h1, symplO_smul, h2, symplO_zero_right, mul_zero, AddChar.map_zero_eq_one]

theorem finite_Qm {V : Type} [AddCommGroup V] {Λ : AddSubgroup V} {m : ℕ} {R : Set V} (hR : R.Finite)
    (h : ∀ t ∈ Λ, ∃ r ∈ R, ∃ u ∈ Λ, t = r + m • u) : Finite (Qm m Λ) := by
  classical
  haveI : Finite R := hR
  refine Finite.of_surjective
    (fun r : R => if hr : (r : V) ∈ Λ then (QuotientAddGroup.mk (⟨r, hr⟩ : Λ) : Qm m Λ) else 0) fun q => ?_
  obtain ⟨r, hr, u, hu, ht⟩ := h _ (repm_mem q)
  have hrΛ : r ∈ Λ := by
    have := Λ.sub_mem (repm_mem q) (Λ.nsmul_mem hu m)
    rwa [ht, add_sub_cancel_right] at this
  refine ⟨⟨r, hr⟩, ?_⟩
  simp only [dif_pos hrΛ]
  rw [← mk_repm q, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
  refine mem_mLat.2 ⟨u, hu, ?_⟩
  change m • u = -r + repm q
  rw [ht]; abel

theorem decomp_of_lam (ψ : AddChar (AF D.host.F) ℂ) (Λ : AddSubgroup (WO S T)) (m : ℕ) (hm : 0 < m)
    (hinf : ∀ u ∈ Λ, u.map (infPart D) = 0) (hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, ψ (symplO S T x y) = 1)
    (hmax : ∀ x : WO S T, x.map (infPart D) = 0 → (∀ u ∈ Λ, ψ (symplO S T x u) = 1) → x ∈ Λ)
    (lam : WO S T → ℂ) (hlam : ∀ x ∈ Λ, ∀ y ∈ Λ, lam (x + y) = lam x * lam y * ψ (symplOH S T x y))
    (hlm : ∀ l ∈ Λ, lam (m • l) = 1) [Fintype (Qm m Λ)] (f : WO S T → ℂ) (hf : ∀ l ∈ Λ, heisO ψ S T (m • l) f = f) :
    ∃ (u : Qm m Λ → WO S T) (c : Qm m Λ → WO S T →₀ ℂ), (∀ i, (u i).map (infPart D) = 0) ∧ (∀ i, IsFinComb (c i)) ∧
      (∀ i, ∀ b ∈ Λ, lam b • heisO ψ S T b (comb ψ S T (c i) f) = comb ψ S T (c i) f) ∧
      f = ∑ i, heisO ψ S T (u i) (comb ψ S T (c i) f) := by
  classical
  obtain ⟨s, hs⟩ : ∃ s : Qm m Λ → WO S T, ∀ a, s a = incA D ((m : D.host.E)⁻¹) • repm a := ⟨_, fun _ => rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : ℂ, N = (Fintype.card (Qm m Λ) : ℂ) := ⟨_, rfl⟩
  have hN0 : N ≠ 0 := by rw [hN]; exact_mod_cast Fintype.card_ne_zero
  have hsinf : ∀ a, (s a).map (infPart D) = 0 := fun a => by
    rw [hs]; exact map_infPart_smul _ (hinf _ (repm_mem a))
  have hcomb : ∀ a, comb ψ S T (∑ q : Qm m Λ, Finsupp.single (repm q + -s a)
      (lam (repm q) * N⁻¹ * ψ (symplOH S T (repm q) (-s a)))) f =
      ∑ q : Qm m Λ, lam (repm q) • heisO ψ S T (repm q) (N⁻¹ • heisL S T ψ (-s a) f) := by
    intro a
    rw [comb_sum_single]
    refine Finset.sum_congr rfl fun q _ => ?_
    change _ = lam (repm q) • heisL S T ψ (repm q) (N⁻¹ • heisL S T ψ (-s a) f)
    rw [map_smul, heisL_heisL, smul_smul, smul_smul]
    rfl
  refine ⟨s, fun a => ∑ q : Qm m Λ, Finsupp.single (repm q + -s a)
      (lam (repm q) * N⁻¹ * ψ (symplOH S T (repm q) (-s a))), hsinf,
    fun a => isFinComb_sum_single _ _ fun q => map_infPart_add_neg (hinf _ (repm_mem q)) (hsinf a), fun a b hb => ?_, ?_⟩
  · rw [hcomb]
    refine heisAvg_invariant D ψ S T Λ m lam hlam _ (fun l hl => ?_) b hb
    change lam (m • l) • heisL S T ψ (m • l) (N⁻¹ • heisL S T ψ (-s a) f) = _
    have h1 : ψ (symplO S T (m • l) (-s a)) = 1 := by
      rw [symplO_neg_right, ← symplO_skew, hs, symplO_inv_smul_nsmul hm]
      exact hΛ _ (repm_mem a) _ hl
    have h2 : heisL S T ψ (m • l) f = f := hf l hl
    rw [hlm l hl, one_smul, map_smul, heisL_comm, h1, one_smul, h2]
  · have h3 : ∀ a, heisO ψ S T (s a) (comb ψ S T (∑ q : Qm m Λ, Finsupp.single (repm q + -s a)
        (lam (repm q) * N⁻¹ * ψ (symplOH S T (repm q) (-s a)))) f) =
        ∑ q : Qm m Λ, ψ (symplO S T (s a) (repm q)) • ((lam (repm q) * N⁻¹) • heisL S T ψ (repm q) f) := by
      intro a
      rw [hcomb]
      change heisL S T ψ (s a) (∑ q : Qm m Λ, lam (repm q) • heisL S T ψ (repm q) (N⁻¹ • heisL S T ψ (-s a) f)) = _
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [map_smul, map_smul, map_smul, heisL_comm, heisL_cancel, smul_smul, smul_smul, smul_smul]
      congr 1
      ring
    simp only [h3]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, hs, charSum_selfAnn D ψ S T Λ m hm hinf hΛ hmax, ← hN, ite_smul, zero_smul]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
    obtain ⟨l, hl, hl'⟩ := mem_mLat.1 (repm_zero_mem (m := m) (Λ := Λ))
    have h2 : heisL S T ψ (m • l) f = f := hf l hl
    rw [← hl', hlm l hl, h2, one_mul, smul_smul, mul_inv_cancel₀ hN0, one_smul]

theorem theta_eq_sum_latVac : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ), IsSelfDualC S LS → IsSelfDualC T LT → IsVacO ψ θ S T sS sT LS LT f₀ → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → ∃ (n : ℕ) (u : Fin n → WO S T) (c : Fin n → WO S T →₀ ℂ), (∀ i, (u i).map (infPart D) = 0) ∧ (∀ i, GlobalTheory.SeeSaw.IsFinComb (c i)) ∧ (∀ i, IsLatVac (heisO ψ S T) (latO S T LS LT fun _ => True) (GlobalTheory.SeeSaw.comb ψ S T (c i) f)) ∧ f = ∑ i, heisO ψ S T (u i) (GlobalTheory.SeeSaw.comb ψ S T (c i) f) := by
  intro D ψ θ S T sS sT LS LT f₀ hS hT hv f hf
  have hψ := hv.1
  obtain ⟨k, hk, hfk⟩ := Formalism.IndefR.Fin.latLevel_of (Formalism.IndefR.Fin.latSelfDual D) ψ hψ S T LS LT hS hT f hf
  obtain ⟨-, -, hmod, hdual⟩ := Formalism.IndefR.Fin.latSelfDual D ψ hψ S T LS LT hS hT
  have hinf := fun u (hu : u ∈ latO S T LS LT fun _ => True) => Formalism.IndefR.Fin.latAll_inf S T LS LT hu
  obtain ⟨R, hR, hRc⟩ := GlobalTheory.LatFinMod.latO_finite_mod D S T _ _ hS.1.fg hT.1.fg (fun _ => True) (2 * k) (by omega)
  change ∀ u ∈ latO S T LS LT fun _ => True, _ at hfk
  generalize latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (fun _ => True) = Λ
    at hfk hmod hdual hinf hRc ⊢
  haveI : Finite (Qm (2 * k) Λ) := finite_Qm hR hRc
  letI : Fintype (Qm (2 * k) Λ) := Fintype.ofFinite _
  obtain ⟨e, h1, h2, hi, hi', h, hh, h3⟩ := GlobalTheory.TwoPlaceIdem.exists_idem_half D
  have hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, ψ (symplO S T x y) = 1 := fun x hx => (hdual x (hinf x hx)).1 hx
  have hr : ∀ u ∈ Λ, ∃ z ∈ Λ, (1 - e - cA D e) • u = 2 • z := fun u hu =>
    ⟨h • u, hmod h hh u hu, by rw [← h3, two_mul, add_smul, two_nsmul]⟩
  have hl2 : ∀ u ∈ Λ, lamE ψ S T e (2 • u) = 1 := fun u hu => lamE_two_nsmul hΛ (hmod e hi) (hmod _ hi') hu
  obtain ⟨u, c, hu, hc, hfix, hsum⟩ := decomp_of_lam ψ Λ (2 * k) (by omega) hinf hΛ (fun x hx h => (hdual x hx).2 h)
    (lamE ψ S T e) (lamE_add_of_lattice D ψ S T Λ e h1 h2 hΛ (hmod e hi) (hmod _ hi') hr)
    (fun l hl => by rw [mul_nsmul']; exact hl2 _ (Λ.nsmul_mem hl k)) f
    (fun l hl => by rw [mul_nsmul]; exact hfk _ (Λ.nsmul_mem hl 2))
  let ι := (Fintype.equivFin (Qm (2 * k) Λ)).symm
  refine ⟨_, fun i => u (ι i), fun i => c (ι i), fun i => hu _, fun i => hc _, fun i => ⟨fun b hb => ?_, fun e' he' b hb hb' => ?_⟩, ?_⟩
  · have := hfix (ι i) _ (Λ.nsmul_mem hb 2)
    rwa [hl2 b hb, one_smul] at this
  · have := hfix (ι i) b hb
    rwa [lamE_half e he'.2.1 hb', one_smul] at this
  · exact hsum.trans (Equiv.sum_comp ι fun q => heisO ψ S T (u q) (comb ψ S T (c q) f)).symm

end GlobalTheory.FinDecomp

end

theorem _root_.GlobalTheory.T.orientedTheta_eq_finite_heisenbergTranslates_vacua : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ), IsSelfDualC S LS → IsSelfDualC T LT → IsVacO ψ θ S T sS sT LS LT f₀ → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → ∃ (n : ℕ) (u : Fin n → WO S T) (c : Fin n → WO S T →₀ ℂ), (∀ i, (u i).map (infPart D) = 0) ∧ (∀ i, GlobalTheory.SeeSaw.IsFinComb (c i)) ∧ (∀ i, IsLatVac (heisO ψ S T) (latO S T LS LT fun _ => True) (GlobalTheory.SeeSaw.comb ψ S T (c i) f)) ∧ f = ∑ i, heisO ψ S T (u i) (GlobalTheory.SeeSaw.comb ψ S T (c i) f) :=
  GlobalTheory.FinDecomp.theta_eq_sum_latVac
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CentreEigenThetaFunctionFiniteSumFockPolynomials
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.CenFockGen

open GlobalTheory.SeeSaw

theorem isFockVacAt_heisO_fin {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {θ : InfFam D}
    (hθ : IsInfFam θ) {S T : HSp D} {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (τ : D.what₂.Tau)
    (J : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ) (hv : IsFockVacAt (heisO ψ S T) θ τ J f)
    {u : WO S T} (hu : u.map (infPart D) = 0) : IsFockVacAt (heisO ψ S T) θ τ J (heisO ψ S T u f) := by
  have h := GlobalTheory.FockTranslate.isFockVacAt_sum D ψ θ S T hψ.1 hθ f hf τ J hv Unit Finset.univ (fun _ => u) (fun _ => 1)
    (fun _ _ => hu)
  simpa using h

private theorem heisO_aPlus {D : D7} (ψ : AddChar (AF D.host.F) ℂ) {θ : InfFam D} (hθ : IsInfFam θ) {S T : HSp D} {u : WO S T}
    (hu : u.map (infPart D) = 0) (τ : D.what₂.Tau)
    (J : Matrix (Fin T.rank) (Fin S.rank) ℂ → Matrix (Fin T.rank) (Fin S.rank) ℂ)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (g : WO S T → ℂ) :
    heisO ψ S T u (aPlus (heisO ψ S T) θ τ J z g) =
      aPlus (heisO ψ S T) θ τ J z (heisO ψ S T u g) := by
  simp only [aPlus, crea]
  change GlobalTheory.Hk3.FiniteHeis.heisLin ψ S T u _ = _
  rw [map_smul, map_sub, map_smul]
  show _ • (heisO ψ S T u (Formalism.IndefR.Datum.dRho _ _ _ _ _) - _ • heisO ψ S T u (Formalism.IndefR.Datum.dRho _ _ _ _ _)) = _
  rw [GlobalTheory.Hk3.FiniteHeis.heisO_dRho ψ hθ hu, GlobalTheory.Hk3.FiniteHeis.heisO_dRho ψ hθ hu]

theorem heisO_pureTensorO_fin {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {θ : InfFam D}
    (hθ : IsInfFam θ) {S T : HSp D} (sS BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) {u : WO S T} (hu : u.map (infPart D) = 0)
    {x : WO S T → ℂ} (hx : IsThetaFunO ψ S T x) (P : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    heisO ψ S T u (pureTensorO ψ θ S T sS sT BS BT x P) = pureTensorO ψ θ S T sS sT BS BT (heisO ψ S T u x) P := by
  let Φ : Module.End ℂ (WO S T → ℂ) := GlobalTheory.Hk3.FiniteHeis.heisLin ψ S T u
  have hΦ : ∀ g, Φ g = heisO ψ S T u g := fun _ => rfl
  have h := (GlobalTheory.OrientedHeis.pureTensorL_intertwine (IsThetaFunO ψ S T) GlobalTheory.OrientedHeis.theta_zero
    (fun _ _ ha hb => GlobalTheory.OrientedHeis.theta_add ha hb) (fun a _ h => GlobalTheory.OrientedHeis.theta_smul a h)
    (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT)
    (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT) Φ
    (fun k g hg => ⟨GlobalTheory.AdTh.SourceBasis.aPlus_th hψ hθ _ _ _ hg, by
      obtain ⟨τ, i, j⟩ := k
      simp only [aPlusAll, hΦ]
      exact heisO_aPlus ψ hθ hu τ _ _ g⟩) x hx P).2
  exact h

theorem comb_smul' {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (c : WO S T →₀ ℂ) (r : ℂ) (f : WO S T → ℂ) :
    comb ψ S T c (r • f) = r • comb ψ S T c f := by
  funext w
  simp only [comb, heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem theta_comb {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {c : WO S T →₀ ℂ}
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (comb ψ S T c f) :=
  Finset.sum_induction _ (IsThetaFunO ψ S T) (fun _ _ => GlobalTheory.OrientedHeis.theta_add) GlobalTheory.OrientedHeis.theta_zero
    fun u _ => GlobalTheory.OrientedHeis.theta_smul _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf u)

theorem exists_defData {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : GlobalTheory.Grid.Node D} {νS νT : ℕ}
    {PS PT : D.what₂.Tau → SPar} (hS : S.Is νS 0 PS) (hT : T.Is νT 0 PT) {a : GlobalTheory.Grid.ArrT S T}
    {χS χT : (AE D)ˣ →* Circle} (ha : a.Is ψ θ false χS χT) :
    ∃ (x : DefSp S.V) (y : DefSp T.V) (k : KerDat S.V T.V), x.Is ∧ y.Is ∧ k.Is ψ θ x y ∧ x.s = cart S.M ∧
      y.s = cart T.M ∧ x.B = onb S.M ∧ y.B = onb T.M ∧ k.om = a.ω ∧ k.vac = a.vac := by
  obtain ⟨vS⟩ := GlobalTheory.Unf.VolExist.nonempty_vol S.V
  obtain ⟨vT⟩ := GlobalTheory.Unf.VolExist.nonempty_vol T.V
  have pS : S.V.IsPosDef := fun τ => by rw [hS.sig τ, hS.rank, Nat.sub_zero]
  have pT : T.V.IsPosDef := fun τ => by rw [hT.sig τ, hT.rank, Nat.sub_zero]
  let x : DefSp S.V := ⟨cart S.M, onb S.M, S.Λ, vS⟩
  let y : DefSp T.V := ⟨cart T.M, onb T.M, T.Λ, vT⟩
  have hx : x.Is := GlobalTheory.SeeSawCompare.defSp_is hS.sigOK pS S.M x rfl rfl
    (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D S.V S.β S.Λ 1 hS.frame)
  have hy : y.Is := GlobalTheory.SeeSawCompare.defSp_is hT.sigOK pT T.M y rfl rfl
    (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D T.V T.β T.Λ 1 hT.frame)
  let k : KerDat S.V T.V := ⟨a.ω, a.vac, 0⟩
  have hk : k.Is ψ θ x y :=
    ⟨⟨χS, χT, (GlobalTheory.Grid.isWeil_false ψ S.V T.V χS χT a.ω).1 ha.weil⟩, ha.vac, fun u hu => (Finsupp.mem_support_iff.1 hu Finsupp.zero_apply).elim⟩
  exact ⟨x, y, k, hx, hy, hk, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem cenFock_fin : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (S T : GlobalTheory.Grid.Node D) (νS νT : ℕ) (PS PT : D.what₂.Tau → SPar), S.Is νS 0 PS → T.Is νT 0 PT → ∀ (a : GlobalTheory.Grid.ArrT S T) (χS χT : (AE D)ˣ →* Circle), a.Is ψ θ false χS χT → ∀ (χ : GA D S.V → ℂ) (f : WO S.V T.V → ℂ), IsThetaFunO ψ S.V T.V f → (∀ z ∈ GinfC S.V, z ∈ Subgroup.center (GA D S.V) → a.ω (z, 1) f = χ z • f) → ∃ (k : ℕ) (g : Fin k → WO S.V T.V → ℂ) (p : Fin k → GlobalTheory.Grid.Pol S T), (∀ l, GlobalTheory.Grid.IsFinVec ψ θ false S T (g l)) ∧ f = ∑ l, GlobalTheory.Grid.fock ψ θ false S T (g l) (p l) := by
  intro D ψ θ hθ S T νS νT PS PT hS hT a χS χT ha χ f hf hχ
  classical
  obtain ⟨x, y, k, hx, hy, hk, hxs, hys, hxB, hyB, hkom, hkvac⟩ := exists_defData hS hT ha
  have hstd : IsStdChar D ψ (-1) := hk.vac.1
  obtain ⟨χS', χT', hW⟩ := hk.weil
  obtain ⟨Wf, -, hWf⟩ := GlobalTheory.SeeSaw.CenFockPf.cenFock D ψ θ hθ S.V T.V x y hx hy k hk χ
  obtain ⟨n, u, c, hu, hc, hlat, hsum⟩ :=
    GlobalTheory.T.orientedTheta_eq_finite_heisenbergTranslates_vacua D ψ θ S.V T.V x.s y.s x.L y.L k.vac hx.sd hy.sd hk.vac f hf
  have hg : ∀ i, ∃ P, comb ψ S.V T.V (c i) f = pureTensorO ψ θ S.V T.V x.s y.s x.B y.B k.vac P := by
    intro i
    have he : ∀ z ∈ GinfC S.V, z ∈ Subgroup.center (GA D S.V) →
        k.om (z, 1) (comb ψ S.V T.V (c i) f) = χ z • comb ψ S.V T.V (c i) f := by
      intro z hz hzc
      rw [GlobalTheory.SeeSaw.RealComm.om_comb D ψ S.V T.V χS' χT' k.om hW z hz (c i) (hc i) f hf, hkom, hχ z hz hzc,
        comb_smul']
    obtain ⟨P, -, hP⟩ := hWf _ (theta_comb hstd hf) (hlat i) he
    exact ⟨P, hP⟩
  choose P hP using hg
  have hvth : IsThetaFunO ψ S.V T.V a.vac := hkvac ▸ hk.vac.2.theta
  refine ⟨n, fun i => heisO ψ S.V T.V (u i) a.vac, P, fun i => ⟨GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hstd hvth (u i),
    fun τ => isFockVacAt_heisO_fin hstd hθ hvth τ _ (ha.vac.2.fock τ) (hu i)⟩, ?_⟩
  refine hsum.trans (Finset.sum_congr rfl fun i _ => ?_)
  rw [hP i, heisO_pureTensorO_fin hstd hθ _ _ _ _ (hu i) hk.vac.2.theta, hxs, hys, hxB, hyB, hkvac]
  rfl

end GlobalTheory.CenFockGen

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CentreEigenThetaFunctionFiniteSumFockPolynomialsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centreEigen_thetaFunction_finite_sum_fockPolynomials : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (S T : GlobalTheory.Grid.Node D) (νS νT : ℕ) (PS PT : D.what₂.Tau → SPar), S.Is νS 0 PS → T.Is νT 0 PT → ∀ (a : GlobalTheory.Grid.ArrT S T) (χS χT : (AE D)ˣ →* Circle), a.Is ψ θ false χS χT → ∀ (χ : GA D S.V → ℂ) (f : WO S.V T.V → ℂ), IsThetaFunO ψ S.V T.V f → (∀ z ∈ GinfC S.V, z ∈ Subgroup.center (GA D S.V) → a.ω (z, 1) f = χ z • f) → ∃ (k : ℕ) (g : Fin k → WO S.V T.V → ℂ) (p : Fin k → GlobalTheory.Grid.Pol S T), (∀ l, GlobalTheory.Grid.IsFinVec ψ θ false S T (g l)) ∧ f = ∑ l, GlobalTheory.Grid.fock ψ θ false S T (g l) (p l) := by
  first | exact @GlobalTheory.CenFockGen.cenFock_fin | exact GlobalTheory.CenFockGen.cenFock_fin | (intros; apply GlobalTheory.CenFockGen.cenFock_fin <;> assumption)
end
