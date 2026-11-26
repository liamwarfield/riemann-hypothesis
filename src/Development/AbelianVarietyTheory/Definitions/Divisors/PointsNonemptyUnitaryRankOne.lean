module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousIntegralInvMulOfLocallyIntegrable

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKCx

variable {p : ℕ} [Fact p.Prime]

def grp (G : HTGroup p) (β : G.Cˣ) : Subgroup (G.Cˣ × ℚˣ) where
  carrier := {y | (y.1 : G.C) * β * sh G y.1 = algebraMap ℚ G.C y.2 * β ∧ 0 < (y.2 : ℚ)}
  one_mem' := ⟨by simp [sh], by simp⟩
  mul_mem' := by
    rintro ⟨y, s⟩ ⟨y', s'⟩ ⟨h2, hs⟩ ⟨h2', hs'⟩
    refine ⟨?_, ?_⟩
    · change (y : G.C) * β * sh G y = algebraMap ℚ G.C s * β at h2
      change (y' : G.C) * β * sh G y' = algebraMap ℚ G.C s' * β at h2'
      change ((y * y' : G.Cˣ) : G.C) * β * sh G ((y * y' : G.Cˣ) : G.C) =
        algebraMap ℚ G.C ((s * s' : ℚˣ) : ℚ) * β
      have e : sh G ((y * y' : G.Cˣ) : G.C) = sh G y' * sh G y := by
        simp only [sh, Units.val_mul, map_mul, MulOpposite.unop_mul]
      rw [e, Units.val_mul, Units.val_mul, map_mul]
      calc (y : G.C) * y' * β * (sh G y' * sh G y) = y * (y' * β * sh G y') * sh G y := by
            simp only [mul_assoc]
        _ = algebraMap ℚ G.C s' * (y * β * sh G y) := by
            rw [h2']; simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc]
        _ = _ := by rw [h2, ← mul_assoc, ← map_mul, ← map_mul, mul_comm (s' : ℚ)]
    · change 0 < ((s * s' : ℚˣ) : ℚ)
      rw [Units.val_mul]; exact mul_pos hs hs'
  inv_mem' := by
    rintro ⟨y, s⟩ ⟨h2, hs⟩
    change (y : G.C) * β * sh G y = algebraMap ℚ G.C s * β at h2
    refine ⟨?_, ?_⟩
    · change ((y⁻¹ : G.Cˣ) : G.C) * β * sh G ((y⁻¹ : G.Cˣ) : G.C) =
        algebraMap ℚ G.C ((s⁻¹ : ℚˣ) : ℚ) * β
      have e : sh G y * sh G ((y⁻¹ : G.Cˣ) : G.C) = 1 := by
        simp only [sh]
        rw [← MulOpposite.unop_mul, ← map_mul, Units.inv_mul, map_one, MulOpposite.unop_one]
      have hs' : algebraMap ℚ G.C ((s⁻¹ : ℚˣ) : ℚ) * algebraMap ℚ G.C (s : ℚ) = 1 := by
        rw [← map_mul, Units.inv_mul, map_one]
      calc ((y⁻¹ : G.Cˣ) : G.C) * β * sh G ((y⁻¹ : G.Cˣ) : G.C)
          = algebraMap ℚ G.C ((s⁻¹ : ℚˣ) : ℚ) * (((y⁻¹ : G.Cˣ) : G.C) * (algebraMap ℚ G.C (s : ℚ) * β) *
              sh G ((y⁻¹ : G.Cˣ) : G.C)) := by
            rw [← mul_assoc, ← mul_assoc, ← mul_assoc, Algebra.commutes ((s⁻¹ : ℚˣ) : ℚ), mul_assoc ((y⁻¹ : G.Cˣ) : G.C) _ (algebraMap ℚ G.C (s : ℚ)), hs', mul_one]
        _ = algebraMap ℚ G.C ((s⁻¹ : ℚˣ) : ℚ) * ((((y⁻¹ : G.Cˣ) : G.C) * y) * β *
              (sh G y * sh G ((y⁻¹ : G.Cˣ) : G.C))) := by
            rw [← h2]; simp only [mul_assoc]
        _ = _ := by rw [Units.inv_mul, e, one_mul, mul_one]
    · change 0 < ((s⁻¹ : ℚˣ) : ℚ)
      rw [Units.val_inv_eq_inv_val]; exact inv_pos.2 hs

def toAfF (G : HTGroup p) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t) :
    grp G β →* G.GAf :=
  MonoidHom.codRestrict
    ((((MulAut.conj x).toMonoidHom.comp (Units.map (inC G (AfP p)).toMonoidHom)).prodMap
      (Units.map (algebraMap ℚ (AfP p)).toMonoidHom)).comp (grp G β).subtype) _ fun y => by
      have h := congrArg (inC G (AfP p)) y.2.1
      rw [map_mul, map_mul, map_mul] at h
      have e1 : inC G (AfP p) (sh G y.1.1) = (starT G.star (AfP p) (inC G (AfP p) y.1.1)).unop :=
        (starT_tmul G.star (AfP p) 1 _).symm
      have e2 : inC G (AfP p) (algebraMap ℚ G.C y.1.2) =
          algebraMap (AfP p) (AfP p ⊗[ℚ] G.C) (algebraMap ℚ (AfP p) y.1.2) := by
        rw [← IsScalarTower.algebraMap_apply]
        exact (Algebra.TensorProduct.includeRight : G.C →ₐ[ℚ] AfP p ⊗[ℚ] G.C).commutes _
      rw [e1, e2] at h
      exact conj_mul_star (starT G.star (AfP p)) (inC G (AfP p) β) x
        (Units.map (inC G (AfP p)).toMonoidHom y.1.1) t _ hx h

def toP1 (G : HTGroup p) (β : G.Cˣ) : grp G β →* Gr G 1 :=
  ((inclG G 1).comp (locC G)).comp (grp G β).subtype

def toV (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) : grp G β →* GL (Fin G.n) ℂ :=
  (Units.map (G.psi v).toMonoidHom).comp ((MonoidHom.fst _ _).comp (grp G β).subtype)

def herm (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) : Matrix (Fin G.n) (Fin G.n) ℂ :=
  G.gram v * G.psi v ((β⁻¹ : G.Cˣ) : G.C)

def PosV (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) : Type :=
  {x : Fin G.n → ℂ // 0 < (star x ⬝ᵥ (herm G v β *ᵥ x)).re}

abbrev Dat (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) : Type := (G.GAf × Gr G 1) × PosV G v β

def Same (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) β x t) (Kf : Subgroup G.GAf) (K' : Subgroup (Gr G 1)) (a b : Dat G v β) : Prop :=
  ∃ (y : grp G β) (k : G.GAf × Gr G 1) (c : ℂ), k.1 ∈ Kf ∧ k.2 ∈ K' ∧ c ≠ 0 ∧
    b.1 = ((toAfF G β x t hx y, toP1 G β y) : G.GAf × Gr G 1) * a.1 * k ∧
    b.2.1 = c • ((toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ a.2.1)

def Pts (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) β x t) (Kf : Subgroup G.GAf) (K' : Subgroup (Gr G 1)) : Type :=
  Quot (Same G v β x t hx Kf K')

def FixL (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) (y : grp G β) (z : Fin G.n → ℂ) : Prop :=
  ∃ c : ℂ, (toV G v β y : Matrix (Fin G.n) (Fin G.n) ℂ) *ᵥ z = c • z

def Stab (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) β x t) (Kf : Subgroup G.GAf) (K' : Subgroup (Gr G 1)) (a : Dat G v β) : Type :=
  {y : grp G β // a.1.1⁻¹ * toAfF G β x t hx y * a.1.1 ∈ Kf ∧ a.1.2⁻¹ * toP1 G β y * a.1.2 ∈ K' ∧
    FixL G v β y a.2.1}

def cxSumAt (G : HTGroup p) (v : InfinitePlace G.F) (wt : Polynomial G.F → ℂ) (β : G.Cˣ)
    (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ)
    (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ) : ℂ :=
  ∑ᶠ q : Pts G v β x t hx Kf K',
    ((Nat.card (Stab G v β x t hx Kf K' (Quot.out q)) : ℕ) : ℂ)⁻¹ *
      ∑ᶠ y : grp G β, if FixL G v β y (Quot.out q).2.1 then
        f ((Quot.out q).1.1⁻¹ * toAfF G β x t hx y * (Quot.out q).1.1) *
          f' ((Quot.out q).1.2⁻¹ * toP1 G β y * (Quot.out q).1.2) *
          wt (minpoly G.F (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)) else 0

structure Form (G : HTGroup p) where

  β : G.Cˣ
  sym : sh G β = β
  trivAf : ∃ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ), Triv G (AfP p) β x t
  trivR : ∃ z : (ℝ ⊗[ℚ] G.C)ˣ, Triv G ℝ β z 1

def Form.Rel {G : HTGroup p} (P Q : Form G) : Prop :=
  ∃ (y : G.Cˣ) (s : ℚ), 0 < s ∧ (Q.β : G.C) = algebraMap ℚ G.C s * (y * P.β * sh G y)

def FCls (G : HTGroup p) : Type := Quot (Form.Rel (G := G))

def cxSum (G : HTGroup p) (v : InfinitePlace G.F) (wt : Polynomial G.F → ℂ) (P : Form G) (Kf : Subgroup G.GAf)
    (f : G.GAf → ℂ) (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ) : ℂ :=
  cxSumAt G v wt P.β P.trivAf.choose P.trivAf.choose_spec.choose P.trivAf.choose_spec.choose_spec Kf f K' f'

def cxTotal (G : HTGroup p) (v : InfinitePlace G.F) (wt : Polynomial G.F → ℂ) (Kf : Subgroup G.GAf)
    (f : G.GAf → ℂ) (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ) : ℂ :=
  ∑ᶠ q : FCls G, cxSum G v wt (Quot.out q) Kf f K' f'

def RegAf (G : HTGroup p) (g : G.GAf) : Prop :=
  ∃ w : AwayP p, ∀ a b : w.1.adicCompletion ℚ ⊗[ℚ] G.C,
    Commute a ((ubcMap (AfP.eval w) g).1.1 : w.1.adicCompletion ℚ ⊗[ℚ] G.C) →
    Commute b ((ubcMap (AfP.eval w) g).1.1 : w.1.adicCompletion ℚ ⊗[ℚ] G.C) → Commute a b

def Form.one (G : HTGroup p) : Form G := ⟨1, sh_one_eq G, ⟨1, 1, by simp [Triv, inC]⟩, ⟨1, by simp [Triv, inC]⟩⟩

theorem fixL_one (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) (z : Fin G.n → ℂ) : FixL G v β 1 z :=
  ⟨1, by simp [toV]⟩

theorem same_refl (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) β x t) (Kf : Subgroup G.GAf) (K' : Subgroup (Gr G 1)) (a : Dat G v β) :
    Same G v β x t hx Kf K' a a :=
  ⟨1, 1, 1, Kf.one_mem, K'.one_mem, one_ne_zero, by simp, by simp [toV]⟩

def Stab.one (G : HTGroup p) (v : InfinitePlace G.F) (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ)
    (hx : Triv G (AfP p) β x t) (Kf : Subgroup G.GAf) (K' : Subgroup (Gr G 1)) (a : Dat G v β) :
    Stab G v β x t hx Kf K' a :=
  ⟨1, by simpa using Kf.one_mem, by simpa using K'.one_mem, fixL_one G v β _⟩



theorem finitePlacesAway_nonempty (p : ℕ) [Fact p.Prime] : Nonempty (AwayP p) := by
  obtain ⟨q, hq, hqp⟩ := Nat.exists_infinite_primes (p+1)
  have hq' : Prime (q : ℤ) := Nat.prime_iff_prime_int.1 hqp
  refine ⟨⟨⟨Ideal.span {(q:ℤ)}, (Ideal.span_singleton_prime hq'.ne_zero).2 hq', by simpa using hqp.ne_zero⟩, fun h => ?_⟩⟩
  have h1 : (q:ℤ) ∣ (p:ℤ) := Ideal.mem_span_singleton.1 (by
    have : (p:ℤ) ∈ Ideal.span {(p:ℤ)} := Ideal.mem_span_singleton_self _
    rw [← h] at this; exact this)
  have h2 : q ∣ p := Int.natCast_dvd_natCast.1 h1
  have := Nat.le_of_dvd (Fact.out : p.Prime).pos h2
  omega

theorem sigG_one (G : HTGroup p) (g : Gr G 1) : sigG G 1 g = g := by
  refine Prod.ext ?_ (funext fun i => ?_)
  · show GlobalTheory.LKLoc.sig p (Q0 p) 1 1 g.1 = g.1
    refine Units.ext (Matrix.ext fun i j => ?_)
    exact DFunLike.congr_fun (frobQ_degree_one p) ((g.1 : Matrix (Fin 1) (Fin 1) (Qr p 1)) i j)
  · show sigRes p (G.Fw i) G.n 1 (g.2 i) = g.2 i
    rw [sigRes_degree_one]; rfl


end GlobalTheory.LKCx
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.MarkedSumIrr
noncomputable section

open GlobalTheory.LKTrip GlobalTheory.LKRes
open scoped Classical

namespace GlobalTheory.LKMid

variable {p : ℕ} [Fact p.Prime]

def markedSumIrr (G : HTGroup p) (wt sel : Polynomial G.F → ℂ) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (r : ℕ)
    (K : Subgroup (Gr G r)) (φ : Gr G r → ℂ) : ℂ :=
  ∑ᶠ q : Cls G, if Irreducible (Quot.out q).pol ∧ (Quot.out q).Mark (sel (Quot.out q).pol) then
    wt (Quot.out q).pol * (Quot.out q).term Kf f r K φ else 0

end GlobalTheory.LKMid
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.MemStdLatticeIffIntegralCoords
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField
open Formalism.IndefR Formalism.IndefR.principalLevelFrame GlobalTheory.StdFrame
open scoped TensorProduct Matrix

namespace GlobalTheory.StdFrameModel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.StdFrame.instCMHostS

variable {D : D7}

theorem hostF_eq (D : D7) : D.host.F = maximalRealSubfield D.host.E := rfl

abbrev sw (D : D7) : Af D.host.F ⊗[D.host.F] D.host.E ≃+* ReciprocityTheory.Aut.AL D.host.E := StdFrame.tensCastR (hostF_eq D)

theorem sw_tmul (a : Af D.host.F) (x : D.host.E) : sw D (a ⊗ₜ x) = x ⊗ₜ a := rfl

theorem sw_sig (y : ReciprocityTheory.Aut.AL D.host.E) :
    (sw D).symm (ReciprocityTheory.Aut.conjAL D.host.E y) = sigR (Af D.host.F) D.sp.cm.sig ((sw D).symm y) := by
  induction y using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingEquiv.map_zero, RingHom.map_zero]
  | tmul x a => rfl
  | add x y hx hy => rw [RingHom.map_add (f := _), RingEquiv.map_add (e := _), RingEquiv.map_add (e := _), RingHom.map_add (f := _), hx, hy]

theorem mem_GA_iff {V : HSp D} (hg : V.gram = 1) (κ : GL (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)) :
    κ ∈ ReciprocityTheory.Aut.GA D.host.E V.rank ↔
      Formalism.UG.bc (sw D).symm.toRingHom κ ∈ HR (Af D.host.F) D.sp.cm.sig V.gram := by
  have h1 : JR (F := D.host.F) (Af D.host.F) V.gram = 1 := by
    rw [hg, JR]; exact Matrix.map_one _ (map_zero _) (map_one _)
  change κ.1 * ReciprocityTheory.Aut.conjT _ κ.1 = 1 ↔
    Formalism.UG.cT (sigR (Af D.host.F) D.sp.cm.sig) (κ.1.map (sw D).symm.toRingHom) * JR (F := D.host.F) (Af D.host.F) V.gram *
      κ.1.map (sw D).symm.toRingHom = JR (F := D.host.F) (Af D.host.F) V.gram
  have h2 : Formalism.UG.cT (sigR (Af D.host.F) D.sp.cm.sig) (κ.1.map (sw D).symm.toRingHom) =
      (ReciprocityTheory.Aut.conjT (ReciprocityTheory.Aut.conjAL D.host.E) κ.1).map (sw D).symm.toRingHom := by
    ext i j
    exact (sw_sig _).symm
  rw [h1, Matrix.mul_one, h2, ← Matrix.map_mul, mul_eq_one_comm,
    ← Matrix.map_one (sw D).symm.toRingHom (map_zero _) (map_one _)]
  exact ⟨fun h => by rw [h], fun h => Matrix.map_injective (sw D).symm.injective h⟩

theorem exists_lift {V : HSp D} (hg : V.gram = 1) (κ : Formalism.AUTREP.GAf D.host.E V.rank) :
    ∃ g : GA D V, infHom V g = 1 ∧ finHom V g = Formalism.UG.bc (sw D).symm.toRingHom κ.1 :=
  GlobalTheory.UnitarySplit.ga_glue V 1 _ (one_mem _) ((mem_GA_iff hg κ.1).1 κ.2)

def unitPsi {V : HSp D} (hg : V.gram = 1) : RowPsi V V.rank where
  ψ := MonoidHom.mk' (fun κ => (exists_lift hg κ).choose) fun a b => by
    refine GlobalTheory.UnitarySplit.ga_ext V ?_ ?_
    · rw [map_mul, (exists_lift hg _).choose_spec.1, (exists_lift hg _).choose_spec.1, (exists_lift hg _).choose_spec.1, mul_one]
    · rw [map_mul, (exists_lift hg _).choose_spec.2, (exists_lift hg _).choose_spec.2, (exists_lift hg _).choose_spec.2,
        ← map_mul]
      rfl
  inj := fun a b h => by
    have h1 := congrArg (finHom V) h
    simp only [MonoidHom.mk'_apply] at h1
    rw [(exists_lift hg _).choose_spec.2, (exists_lift hg _).choose_spec.2] at h1
    exact Subtype.ext (Units.ext (Matrix.map_injective (sw D).symm.injective (congrArg Units.val h1)))
  into := fun κ => (exists_lift hg κ).choose_spec.1
  onto := fun g hgf => by
    have e : Formalism.UG.bc (sw D).symm.toRingHom (Formalism.UG.bc (sw D).toRingHom (finHom V g)) = finHom V g := by
      ext i j
      exact (sw D).symm_apply_apply _
    refine ⟨⟨Formalism.UG.bc (sw D).toRingHom (finHom V g), (mem_GA_iff hg _).2 (by
      rw [e]; exact GlobalTheory.UnitarySplit.finHom_mem V g)⟩, GlobalTheory.UnitarySplit.ga_ext V ?_ ?_⟩
    · exact (exists_lift hg _).choose_spec.1.trans (Eq.symm hgf)
    · exact (exists_lift hg _).choose_spec.2.trans e

theorem finMat_unitPsi {V : HSp D} (hg : V.gram = 1) (κ : Formalism.AUTREP.GAf D.host.E V.rank) :
    finMat D.sp.cm.sig V.gram ((unitPsi hg).ψ κ) = κ.1.1.map (sw D).symm :=
  congrArg Units.val (exists_lift hg κ).choose_spec.2

theorem mem_std_lattice_iff_integral_coords {V : HSp D} (h : OrthFrame V) (x : Fin V.rank → D.host.E) :
    x ∈ L0c D V ↔ ∀ a, x a ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := h.mem_iff x

theorem tmul_mem (o : 𝓞 D.host.E) {a : Af D.host.F} (ha : a ∈ intAf D.host.F) :
    sw D (a ⊗ₜ (o : D.host.E)) ∈ ReciprocityTheory.Aut.ALint D.host.E := by
  have e : sw D (a ⊗ₜ (o : D.host.E)) =
      ((o : D.host.E) ⊗ₜ (1 : Af D.host.F) : ReciprocityTheory.Aut.AL D.host.E) * ((1 : D.host.E) ⊗ₜ a) := by
    rw [sw_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [e]
  exact Subring.mul_mem _ (Subring.subset_closure (Or.inl ⟨o, rfl⟩)) (Subring.subset_closure (Or.inr ⟨a, ha, rfl⟩))

theorem int_of_mem {V : HSp D} (h : OrthFrame V) {y : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E}
    (hy : y ∈ latHat D.host.F D.host.E (L0c D V)) (i : Fin V.rank) : sw D (y i) ∈ ReciprocityTheory.Aut.ALint D.host.E := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hy
    obtain ⟨o, ho⟩ := Submodule.mem_one.1 ((mem_std_lattice_iff_integral_coords h x).1 hx i)
    have := tmul_mem o ha
    rw [show (o : D.host.E) = x i from ho] at this
    exact this
  | zero => rw [Pi.zero_apply, RingEquiv.map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [Pi.add_apply, RingEquiv.map_add (e := _)]; exact add_mem hy hz
  | neg y _ hy => rw [Pi.neg_apply, RingEquiv.map_neg]; exact neg_mem hy

theorem smul_gen {M : ℕ} (L : Set (Fin M → D.host.E)) (c : Af D.host.F ⊗[D.host.F] D.host.E)
    (hc : ∀ a ∈ intAf D.host.F, ∀ x ∈ L, c • (fun i => a ⊗ₜ[D.host.F] x i) ∈ latHat D.host.F D.host.E L)
    {w : Fin M → Af D.host.F ⊗[D.host.F] D.host.E} (hw : w ∈ latHat D.host.F D.host.E L) :
    c • w ∈ latHat D.host.F D.host.E L := by
  induction hw using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hy
    exact hc a ha x hx
  | zero => rw [smul_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [smul_add]; exact add_mem hy hz
  | neg y _ hy => rw [smul_neg]; exact neg_mem hy

theorem smul_closure {A B : Type} [CommRing A] [CommRing B] {M : ℕ} (e : B →+* A) (S : AddSubgroup (Fin M → A)) (T : Set B)
    (h : ∀ t ∈ T, ∀ w ∈ S, e t • w ∈ S) {r : B} (hr : r ∈ Subring.closure T) : ∀ w ∈ S, e r • w ∈ S := by
  induction hr using Subring.closure_induction with
  | mem r hr => exact h r hr
  | zero => intro w _; rw [map_zero, zero_smul]; exact zero_mem _
  | one => intro w hw; rwa [map_one, one_smul]
  | add x y _ _ hx hy => intro w hw; rw [map_add (f := _), add_smul]; exact add_mem (hx w hw) (hy w hw)
  | neg x _ hx => intro w hw; rw [map_neg, neg_smul]; exact neg_mem (hx w hw)
  | mul x y _ _ hx hy => intro w hw; rw [map_mul, mul_smul]; exact hx _ (hy w hw)

theorem smul_mem {V : HSp D} (h : OrthFrame V) {r : ReciprocityTheory.Aut.AL D.host.E} (hr : r ∈ ReciprocityTheory.Aut.ALint D.host.E) :
    ∀ w ∈ latHat D.host.F D.host.E (L0c D V), (sw D).symm r • w ∈ latHat D.host.F D.host.E (L0c D V) := by
  refine smul_closure (sw D).symm.toRingHom _ _ (fun r hr w hw => ?_) hr
  rcases hr with ⟨o, rfl⟩ | ⟨b, hb, rfl⟩
  · refine smul_gen _ _ (fun a ha x hx => AddSubgroup.subset_closure ⟨a, ha, (o : D.host.E) • x, ?_, ?_⟩) hw
    · rw [mem_std_lattice_iff_integral_coords h] at hx ⊢
      exact fun i => Submodule.smul_mem _ o (hx i)
    · funext i
      change ((1 : Af D.host.F) ⊗ₜ[D.host.F] (o : D.host.E)) * (a ⊗ₜ[D.host.F] x i) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      rfl
  · refine smul_gen _ _ (fun a ha x hx => AddSubgroup.subset_closure ⟨b * a, fun v => ?_, x, hx, ?_⟩) hw
    · rw [map_mul]
      exact mul_mem (hb v) (ha v)
    · funext i
      change ((b : Af D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E)) * (a ⊗ₜ[D.host.F] x i) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem one_mem_intAf (F : Type) [Field F] [NumberField F] : (1 : Af F) ∈ intAf F := fun v => by
  show evalV F v 1 ∈ _
  rw [map_one]
  exact one_mem _

theorem single_mem {V : HSp D} (h : OrthFrame V) (j : Fin V.rank) :
    (Pi.single j 1 : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) ∈ latHat D.host.F D.host.E (L0c D V) := by
  refine AddSubgroup.subset_closure ⟨1, one_mem_intAf _, Pi.single j 1, ?_, ?_⟩
  · rw [mem_std_lattice_iff_integral_coords h]
    intro a
    rw [Pi.single_apply]
    split_ifs
    · exact Submodule.mem_one.2 ⟨1, map_one _⟩
    · exact zero_mem _
  · funext i
    rw [Pi.single_apply, Pi.single_apply]
    split_ifs
    · rfl
    · rw [TensorProduct.tmul_zero]

theorem mem_latHat_iff {V : HSp D} (h : OrthFrame V) (y : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    y ∈ latHat D.host.F D.host.E (L0c D V) ↔ ∀ i, sw D (y i) ∈ ReciprocityTheory.Aut.ALint D.host.E := by
  refine ⟨int_of_mem h, fun hy => ?_⟩
  rw [pi_eq_sum_univ' y]
  refine sum_mem fun i _ => ?_
  have := smul_mem h (hy i) _ (single_mem h i)
  rw [RingEquiv.symm_apply_apply] at this
  exact this

theorem mulVec_mem {V : HSp D} (h : OrthFrame V) {κ : Formalism.AUTREP.GAf D.host.E V.rank}
    (hκ : κ ∈ ReciprocityTheory.Aut.Umax D.host.E V.rank) {y : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E}
    (hy : y ∈ latHat D.host.F D.host.E (L0c D V)) :
    (κ.1.1.map (sw D).symm.toRingHom) *ᵥ y ∈ latHat D.host.F D.host.E (L0c D V) := by
  rw [mem_latHat_iff h] at hy ⊢
  intro i
  change (sw D).toRingHom (∑ j, (sw D).symm (κ.1.1 i j) * y j) ∈ _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum (sw D).toRingHom]
  refine sum_mem fun j _ => ?_
  change sw D _ ∈ _
  rw [RingEquiv.map_mul, RingEquiv.apply_symm_apply]
  exact mul_mem (hκ i j) (hy j)

theorem stdPsi_unitPsi {V : HSp D} (h : OrthFrame V) : StdFrame.StdPsi (hostF_eq D) (unitPsi h.gram_eq) := by
  refine ⟨⟨1, 1, mul_one _, mul_one _, fun κ => ?_⟩, fun κ => ⟨fun hκ => ⟨(unitPsi h.gram_eq).into κ, fun y => ?_, by simp⟩, ?_⟩⟩
  · rw [finMat_unitPsi, Matrix.one_mul, Matrix.mul_one]
  · rw [finMat_unitPsi]
    refine ⟨mulVec_mem h hκ, fun hy => ?_⟩
    have := mulVec_mem h (inv_mem hκ) hy
    erw [Matrix.mulVec_mulVec, ← Matrix.map_mul] at this
    rw [show (κ⁻¹).1.1 * κ.1.1 = 1 from Units.inv_mul κ.1, Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _),
      Matrix.one_mulVec] at this
    exact this
  · rintro ⟨-, hk, -⟩ i j
    have := (mem_latHat_iff h _).1 ((hk _).1 (single_mem h j)) i
    rw [finMat_unitPsi, Matrix.mulVec_single_one] at this
    change sw D ((sw D).symm (κ.1.1 i j)) ∈ _ at this
    rwa [RingEquiv.apply_symm_apply] at this

section Conj

variable (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)

open ReciprocityTheory.Aut

variable {L}

end Conj

end GlobalTheory.StdFrameModel

end
end
