module

public import Formalism.LocalToGlobal.GlobalTheory.UnramifiedDiagonal.HeckeRamifiedZeroOfMatchingsAndDu

@[expose] public section

section -- merged from Formalism.LocalToGlobal.GlobalTheory.UnramifiedTrace.DuFormulaOfFibreCount
section -- merged from Formalism.LocalToGlobal.GlobalTheory.UnramifiedTrace.EopUEq
section -- merged from Formalism.LocalToGlobal.GlobalTheory.UnramifiedTrace.NatTr0Sum
noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0 NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct Classical

variable {D : D7} {u : D.what₂.Word}

def kU (T : Forms0 D u) (κ : T.cls0.lev.U) :
    UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
  ⟨κ.1, ((T.cls0.lev.U_eq _).1 κ.2).1⟩

def hcomp (T : Forms0 D u)
    (η : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ : T.cls0.lev.U)
    (μ : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) :
    UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) :=
  η * kU T κ * μ * (kU T κ)⁻¹

theorem natTr0_sum (T : Forms0 D u) (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (κ : T.cls0.lev.U) {ι : Type*} (S : Finset ι) (F : ι → (D.mem u).C.Y 0 → ℂ) :
    natTr0 T γ κ (fun s => ∑ i ∈ S, F i s) = fun s => ∑ i ∈ S, natTr0 T γ κ (F i) s := by
  funext s
  simp only [natTr0, Finset.mul_sum]


set_option maxHeartbeats 4000000 in
theorem dnU_term (T : Forms0 D u) (v : (D.mem u).A.vT) (ψ : Fn D u 0)
    {G : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) → Fr D 0 (Nat.zero_le _) → ℂ}
    (hG : G ∈ AdFun T.cls0.lev (embT D))
    (hψ : ∀ c, ψ c = fun s => G (T.cls0.y c) (T.val0.eY s))
    (c : (D.mem u).C.cls 0) (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c))
    (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (η : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ : T.cls0.lev.U)
    (hrel : bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 *
      (T.cls0.y ((D.fm u).dn 0 v c g)).1 = (T.cls0.y c).1 * η.1 * κ.1)
    (htr : ∀ h, (D.fm u).dnT 0 v c g h = natTr0 T γ κ h)
    (Mu : {x : (D.fm u).lv 0 v ((D.fm u).dn 0 v c g) // (D.fm u).fv 0 v ((D.fm u).dn 0 v c g) x = 1} →
      UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hMu : ∀ x, IsUpMvF T v ((D.fm u).dn 0 v c g) x.1 (Mu x)) :
    (D.fm u).dnT 0 v c g (Uop D u 0 v ψ ((D.fm u).dn 0 v c g)) =
      fun s => ∑ x, G (T.cls0.y c * hcomp T η κ (Mu x)) (T.val0.eY s) := by
  rw [htr, U_op_eq_move_sum T v ψ hG hψ ((D.fm u).dn 0 v c g) Mu hMu,
    natTr0_sum T γ κ Finset.univ (fun x s => G (T.cls0.y ((D.fm u).dn 0 v c g) * Mu x) (T.val0.eY s))]
  funext s
  refine Finset.sum_congr rfl fun x _ => ?_
  have hx : (T.cls0.y c * hcomp T η κ (Mu x)).1 =
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 *
        (T.cls0.y ((D.fm u).dn 0 v c g) * Mu x).1 * (κ⁻¹).1 := by
    simp only [hcomp, kU, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← mul_assoc (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1), hrel]
    simp only [mul_assoc]
  have key := hG γ.1 γ.2 (T.cls0.y ((D.fm u).dn 0 v c g) * Mu x) (T.cls0.y c * hcomp T η κ (Mu x)) κ⁻¹ hx
    (T.val0.eY s) _ (is_translate_inverse T γ s)
  rw [key, map_inv, Units.val_inv_eq_inv_val]
  rfl

end Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

end
end

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0 NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct Classical

section Pairs

variable (D : D7) (u : D.what₂.Word)

abbrev PD (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0) : Type :=
  Σ g : {g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) // g ((D.fm u).te 0 v c) = 1},
    {x : (D.fm u).lv 0 v ((D.fm u).dn 0 v c g.1) // (D.fm u).fv 0 v ((D.fm u).dn 0 v c g.1) x = 1}

abbrev PE (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0) : Type :=
  Σ g : {g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) // g ≠ 0},
    {x : (D.fm u).lv 0 v ((D.fm u).dn 0 v c g.1) // (D.fm u).fv 0 v ((D.fm u).dn 0 v c g.1) x = 1}

end Pairs

variable {D : D7} {u : D.what₂.Word}

def DnMvs (T : Forms0 D u) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0)
    (γ : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) → UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (η : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) →
      UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (κ : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) → T.cls0.lev.U) : Prop :=
  ∀ g, g ≠ 0 → (∀ v', v' ≠ (T.atT.eV v).1 → bc (prV (E := D.host.E) v') (η g).1 = 1) ∧
    bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (γ g).1 *
      (T.cls0.y ((D.fm u).dn 0 v c g)).1 = (T.cls0.y c).1 * (η g).1 * (κ g).1 ∧
    ∀ h, (D.fm u).dnT 0 v c g h = natTr0 T (γ g) (κ g) h

def DUFib0F (T : Forms0 D u) : Prop :=
  ∀ (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0),
  ∃ (γ : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) → UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (η : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) →
      UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (κ : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) → T.cls0.lev.U)
    (Mu : ∀ g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c),
      {x : (D.fm u).lv 0 v ((D.fm u).dn 0 v c g) // (D.fm u).fv 0 v ((D.fm u).dn 0 v c g) x = 1} →
        UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)),
    DnMvs T v c γ η κ ∧ (∀ g x, IsUpMvF T v ((D.fm u).dn 0 v c g) x.1 (Mu g x)) ∧
    ∃ (πD : PD D u v c → (D.fm u).lk 0 v c) (πE : PE D u v c → (D.fm u).lk 0 v c)
      (τ : ((D.mem u).A.Fv v)ˣ ≃ ((D.mem u).A.Fv v)ˣ),
      (∀ x, (Finset.univ.filter (fun q => πE q = x)).card =
        if x = 0 then 0 else (D.mem u).A.T ^ (D.R.N 0 - 1)) ∧
      (∀ x, (Finset.univ.filter (fun p => πD p = x)).card =
        if x = (D.fm u).te 0 v c then (D.mem u).A.T ^ (D.R.N 0 - 1)
        else if x ∈ Submodule.span ((D.mem u).A.Fv v) {(D.fm u).te 0 v c} then 0
        else (D.mem u).A.T ^ (D.R.N 0 - 2)) ∧
      ∀ G ∈ AdFun T.cls0.lev (embT D),
        (∀ p, πD p = (D.fm u).te 0 v c →
          G (T.cls0.y c * hcomp T (η p.1.1) (κ p.1.1) (Mu p.1.1 p.2)) = G (T.cls0.y c)) ∧
        (∀ p q, πD p = πE q → G (T.cls0.y c * hcomp T (η p.1.1) (κ p.1.1) (Mu p.1.1 p.2)) =
          G (T.cls0.y c * hcomp T (η q.1.1) (κ q.1.1) (Mu q.1.1 q.2))) ∧
        (∀ p q, πE p = πE q → G (T.cls0.y c * hcomp T (η p.1.1) (κ p.1.1) (Mu p.1.1 p.2)) =
          G (T.cls0.y c * hcomp T (η q.1.1) (κ q.1.1) (Mu q.1.1 q.2))) ∧
        (∀ (a : ((D.mem u).A.Fv v)ˣ) q, πE q = (a : (D.mem u).A.Fv v) • (D.fm u).te 0 v c →
          ∀ (k : ℤ), (k : (D.mem u).A.Fv v) = ((τ a : ((D.mem u).A.Fv v)ˣ) : (D.mem u).A.Fv v) →
          ∀ δ, IsDia T.cls0.lev (T.atT.eV v).1 (T.atT.eV v).2 k δ →
          G (T.cls0.y c * hcomp T (η q.1.1) (κ q.1.1) (Mu q.1.1 q.2)) = G (T.cls0.y c * δ))


set_option maxHeartbeats 4000000 in
theorem dopU_eq (T : Forms0 D u) (v : (D.mem u).A.vT) (ψ : Fn D u 0)
    {G : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) → Fr D 0 (Nat.zero_le _) → ℂ}
    (hG : G ∈ AdFun T.cls0.lev (embT D))
    (hψ : ∀ c, ψ c = fun s => G (T.cls0.y c) (T.val0.eY s)) (c : (D.mem u).C.cls 0)
    (γ : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) → UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (η : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) →
      UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (κ : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) → T.cls0.lev.U)
    (Mu : ∀ g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c),
      {x : (D.fm u).lv 0 v ((D.fm u).dn 0 v c g) // (D.fm u).fv 0 v ((D.fm u).dn 0 v c g) x = 1} →
        UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hmv : DnMvs T v c γ η κ) (hMu : ∀ g x, IsUpMvF T v ((D.fm u).dn 0 v c g) x.1 (Mu g x)) :
    Dop D u 0 v (Uop D u 0 v ψ) c = fun s => ∑ p : PD D u v c,
      G (T.cls0.y c * hcomp T (η p.1.1) (κ p.1.1) (Mu p.1.1 p.2)) (T.val0.eY s) := by
  funext s
  simp only [Formalism.MainNotions.product_first_zeroth_parts.Dop, LinearMap.pi_apply, LinearMap.sum_apply, Finset.sum_apply]
  rw [Finset.sum_subtype (Finset.univ.filter (fun x : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) =>
    x ((D.fm u).te 0 v c) = 1))
    (p := fun x : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) => x ((D.fm u).te 0 v c) = 1) (by intro x; simp),
    Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp only [LinearMap.comp_apply, LinearMap.proj_apply, LinearEquiv.coe_coe]
  have hg0 : g.1 ≠ 0 := by
    intro h0; have := g.2; rw [h0, LinearMap.zero_apply] at this; exact zero_ne_one this
  obtain ⟨-, h2, h3⟩ := hmv g.1 hg0
  exact congrFun (dnU_term T v ψ hG hψ c g.1 (γ g.1) (η g.1) (κ g.1) h2 h3 (Mu g.1) (hMu g.1)) s


set_option maxHeartbeats 4000000 in
theorem eopU_eq (T : Forms0 D u) (v : (D.mem u).A.vT) (ψ : Fn D u 0)
    {G : UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) → Fr D 0 (Nat.zero_le _) → ℂ}
    (hG : G ∈ AdFun T.cls0.lev (embT D))
    (hψ : ∀ c, ψ c = fun s => G (T.cls0.y c) (T.val0.eY s)) (c : (D.mem u).C.cls 0)
    (γ : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) → UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (η : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) →
      UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (κ : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) → T.cls0.lev.U)
    (Mu : ∀ g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c),
      {x : (D.fm u).lv 0 v ((D.fm u).dn 0 v c g) // (D.fm u).fv 0 v ((D.fm u).dn 0 v c g) x = 1} →
        UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (hmv : DnMvs T v c γ η κ) (hMu : ∀ g x, IsUpMvF T v ((D.fm u).dn 0 v c g) x.1 (Mu g x)) :
    Eop D u 0 v (Uop D u 0 v ψ) c = fun s => ∑ p : PE D u v c,
      G (T.cls0.y c * hcomp T (η p.1.1) (κ p.1.1) (Mu p.1.1 p.2)) (T.val0.eY s) := by
  funext s
  simp only [Formalism.MainNotions.product_first_zeroth_parts.Eop, LinearMap.pi_apply, LinearMap.sum_apply, Finset.sum_apply]
  rw [Finset.sum_subtype (Finset.univ.filter (fun x : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) => x ≠ 0))
    (p := fun x : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) => x ≠ 0) (by intro x; simp),
    Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp only [LinearMap.comp_apply, LinearMap.proj_apply, LinearEquiv.coe_coe]
  obtain ⟨-, h2, h3⟩ := hmv g.1 g.2
  exact congrFun (dnU_term T v ψ hG hψ c g.1 (γ g.1) (η g.1) (κ g.1) h2 h3 (Mu g.1) (hMu g.1)) s

end Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

end
end

section -- merged from Formalism.LocalToGlobal.GlobalTheory.UnramifiedTrace.SumFib
open scoped Classical

namespace Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

theorem sum_fib {X P : Type*} [Fintype X] [DecidableEq X] [Fintype P] (π : P → X) (V : P → ℂ) (w : X → ℂ)
    (hV : ∀ p, V p = w (π p)) :
    ∑ p, V p = ∑ x, ((Finset.univ.filter (fun p => π p = x)).card : ℂ) * w x := by
  have key : ∀ x, ∑ p ∈ Finset.univ.filter (fun p => π p = x), w (π p) =
      ((Finset.univ.filter (fun p => π p = x)).card : ℂ) * w x := by
    intro x
    rw [Finset.sum_congr rfl (g := fun _ => w x) (fun p hp => by rw [(Finset.mem_filter.1 hp).2]),
      Finset.sum_const, nsmul_eq_mul]
  simp_rw [hV]
  rw [← Finset.sum_fiberwise Finset.univ π (fun p => w (π p))]
  exact Finset.sum_congr rfl (fun x _ => key x)

theorem comb_du {K X PD PE : Type*} [Field K] [Fintype K] [DecidableEq K] [AddCommGroup X] [Module K X] [Fintype X]
    [DecidableEq X] {iPD : Fintype PD} {iPE : Fintype PE} (te : X) (hte0 : te ≠ 0) (Tn n1 n2 : ℕ) (hTn : Tn ≠ 0)
    (πD : PD → X) (πE : PE → X) (VD : PD → ℂ) (VE : PE → ℂ) (Φ : ℂ) (Dl : Kˣ → ℂ) (τ : Kˣ ≃ Kˣ)
    (hcE : ∀ x, (Finset.univ.filter (fun q => πE q = x)).card = if x = 0 then 0 else Tn ^ n1)
    (hcD : ∀ x, (Finset.univ.filter (fun p => πD p = x)).card =
      if x = te then Tn ^ n1 else if x ∈ Submodule.span K {te} then 0 else Tn ^ n2)
    (hself : ∀ p, πD p = te → VD p = Φ)
    (hDE : ∀ p q, πD p = πE q → VD p = VE q)
    (hEE : ∀ p q, πE p = πE q → VE p = VE q)
    (hline : ∀ (a : Kˣ) q, πE q = (a : K) • te → VE q = Dl (τ a)) :
    ∑ p, VD p = (Tn : ℂ) ^ n1 * Φ - (Tn : ℂ) ^ n2 * ∑ a, Dl a + (Tn : ℂ) ^ n2 * (((Tn : ℂ) ^ n1)⁻¹ * ∑ p, VE p) := by
  have hTn' : (0 : ℕ) < Tn ^ n1 := pow_pos (Nat.pos_of_ne_zero hTn) _
  have hA : ((Tn : ℂ) ^ n1) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hTn)
  have hfibE : ∀ x : X, x ≠ 0 → ∃ q, πE q = x := by
    intro x hx
    have hc : 0 < (Finset.univ.filter (fun q => πE q = x)).card := by rw [hcE x, if_neg hx]; exact hTn'
    obtain ⟨q, hq⟩ := Finset.card_pos.1 hc
    exact ⟨q, (Finset.mem_filter.1 hq).2⟩
  obtain ⟨wE, hwE⟩ : ∃ wE : X → ℂ, ∀ q, VE q = wE (πE q) :=
    ⟨fun x => if h : ∃ q, πE q = x then VE h.choose else 0, fun q => by
      have h : ∃ q', πE q' = πE q := ⟨q, rfl⟩
      simp only [dif_pos h]
      exact hEE _ _ h.choose_spec.symm⟩
  have hVD : ∀ p, VD p = (if πD p = te then Φ else wE (πD p)) := by
    intro p
    split_ifs with h
    · exact hself p h
    · have h0 : πD p ≠ 0 := by
        intro h0
        have hc := hcD 0
        rw [if_neg (Ne.symm hte0), if_pos (Submodule.zero_mem _)] at hc
        have hm : p ∈ Finset.univ.filter (fun p => πD p = 0) := Finset.mem_filter.2 ⟨Finset.mem_univ _, h0⟩
        rw [Finset.card_eq_zero.1 hc] at hm
        simp at hm
      obtain ⟨q, hq⟩ := hfibE _ h0
      rw [hDE p q hq.symm, hwE q, hq]
  have hD0 : ∑ p, VD p = ∑ x, ((Finset.univ.filter (fun p => πD p = x)).card : ℂ) *
      (if x = te then Φ else wE x) := sum_fib πD VD _ hVD
  have hE0 : ∑ q, VE q = ∑ x, ((Finset.univ.filter (fun q => πE q = x)).card : ℂ) * wE x :=
    sum_fib πE VE wE hwE
  have e1 : ∀ x : X, ((Finset.univ.filter (fun p => πD p = x)).card : ℂ) * (if x = te then Φ else wE x) =
      (if x = te then (Tn : ℂ) ^ n1 * Φ else 0) +
        (Tn : ℂ) ^ n2 * (if x ∈ Submodule.span K {te} then 0 else wE x) := by
    intro x
    rw [hcD x]
    by_cases h1 : x = te
    · subst h1; simp [Submodule.mem_span_singleton_self]
    · by_cases h2 : x ∈ Submodule.span K {te} <;> simp [h1, h2]
  have e2 : ∀ x : X, ((Finset.univ.filter (fun q => πE q = x)).card : ℂ) * wE x =
      (Tn : ℂ) ^ n1 * ((if x ∈ Submodule.span K {te} then 0 else wE x) +
        (if x ∈ Submodule.span K {te} ∧ x ≠ 0 then wE x else 0)) := by
    intro x
    rw [hcE x]
    by_cases h1 : x = 0
    · subst h1; simp
    · by_cases h2 : x ∈ Submodule.span K {te} <;> simp [h1, h2]
  have hD1 : ∑ x, ((Finset.univ.filter (fun p => πD p = x)).card : ℂ) * (if x = te then Φ else wE x) =
      (Tn : ℂ) ^ n1 * Φ + (Tn : ℂ) ^ n2 * ∑ x : X, (if x ∈ Submodule.span K {te} then 0 else wE x) := by
    rw [Finset.sum_congr rfl (fun x _ => e1 x), Finset.sum_add_distrib, ← Finset.mul_sum]
    simp
  have hE1 : ∑ x, ((Finset.univ.filter (fun q => πE q = x)).card : ℂ) * wE x =
      (Tn : ℂ) ^ n1 * (∑ x : X, (if x ∈ Submodule.span K {te} then 0 else wE x) +
        ∑ x : X, (if x ∈ Submodule.span K {te} ∧ x ≠ 0 then wE x else 0)) := by
    rw [Finset.sum_congr rfl (fun x _ => e2 x), ← Finset.mul_sum, Finset.sum_add_distrib]
  have hS2 : ∑ x : X, (if x ∈ Submodule.span K {te} ∧ x ≠ 0 then wE x else 0) = ∑ a, Dl a := by
    rw [← Finset.sum_filter, ← Equiv.sum_comp τ Dl]
    symm
    refine Finset.sum_bij (fun a _ => (a : K) • te) ?_ ?_ ?_ ?_
    · intro a _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self te), smul_ne_zero a.ne_zero hte0⟩
    · intro a _ b _ h
      exact Units.ext (smul_left_injective K hte0 h)
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hx.1
      have hc0 : c ≠ 0 := by
        rintro rfl
        exact hx.2 (by rw [← hc, zero_smul])
      exact ⟨Units.mk0 c hc0, Finset.mem_univ _, by simp [hc]⟩
    · intro a _
      obtain ⟨q, hq⟩ := hfibE _ (smul_ne_zero a.ne_zero hte0)
      rw [← hq, ← hwE q, hline a q hq]
  rw [hD0, hD1, hE0, hE1, hS2, inv_mul_cancel_left₀ hA]
  ring

end Formalism.L2.GlobalTheoryTheory.UnramifiedTrace
end

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0 NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct Classical

variable {D : D7} {u : D.what₂.Word}


set_option maxHeartbeats 4000000 in
theorem du_formula_of_fibre_count (T : Forms0 D u) (hF : DUFib0F T) : DUFormulaLevelZero D u := by
  intro v φ hφ
  obtain ⟨G, hG, hGφ⟩ := S0.forms_from_adelic_function T 0 (Nat.zero_le _) rfl φ hφ
  have hGA := (Submodule.mem_inf.1 hG).1
  choose k hk δ hδ using fun a => S0.diamond_elements_exist_all T 0 (Nat.zero_le _) rfl v a
  funext c
  have : Finite ((D.fm u).lk 0 v c) := Module.finite_of_finite ((D.mem u).A.Fv v)
  letI : Fintype ((D.fm u).lk 0 v c) := Fintype.ofFinite _
  have hdia : ∀ a, dia D u 0 v a φ c = fun s => G (T.cls0.y c * δ a) (T.val0.eY s) := by
    intro a
    show (D.fm u).dilT 0 v a c (φ ((D.fm u).dil 0 v a c)) = _
    rw [hGφ]
    exact T.val0.dilT v a (k a) (hk a) c (δ a) (hδ a) G hGA
  obtain ⟨γ, η, κ, Mu, hmv, hMu, πD, πE, τ, hcE, hcD, hval⟩ := hF v c
  obtain ⟨hself, hDE, hEE, hline⟩ := hval G hGA
  funext s
  rw [norm_eq_sum_diamond]
  simp only [Formalism.MainNotions.product_first_zeroth_parts.trp, LinearMap.smul_apply, LinearMap.comp_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul, Finset.sum_apply]
  rw [dopU_eq T v φ hGA hGφ c γ η κ Mu hmv hMu, eopU_eq T v φ hGA hGφ c γ η κ Mu hmv hMu]
  simp only [hdia]
  exact comb_du ((D.fm u).te 0 v c) ((D.fm u).te_ne 0 v c) (D.mem u).A.T (D.R.N 0 - 1) (D.R.N 0 - 2)
    (D.mem u).A.T_prime.ne_zero πD πE _ _ (φ c s) (fun a => G (T.cls0.y c * δ a) (T.val0.eY s)) τ
    hcE hcD
    (fun p hp => by rw [hGφ c]; exact congrFun (hself p hp) _) (fun p q h => congrFun (hDE p q h) _)
    (fun p q h => congrFun (hEE p q h) _)
    (fun a q hq => congrFun (hline a q hq (k (τ a)) (hk (τ a)) (δ (τ a)) (hδ (τ a))) _)

theorem dUAll_of (h : ∀ (D : D7) (u : D.what₂.Word) (T : Forms0 D u), DUFib0F T) : Formalism.L2.GlobalTheoryTheory.UnramifiedDiagonal.DUAll :=
  fun D u T => du_formula_of_fibre_count T (h D u T)

end Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

end
end

section -- merged from Formalism.LocalToGlobal.GlobalTheory.UnramifiedTrace.CardFilterSubtype
namespace Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

private theorem eq_pow_sub_of_mul_pow_eq_pow {c q k n : ℕ} (hq : 1 < q) (hc : 1 ≤ c) (h : c * q ^ k = q ^ n) :
    c = q ^ (n - k) := by
  have hkn : k ≤ n := by
    by_contra hlt
    push_neg at hlt
    have h1 : q ^ n < q ^ k := Nat.pow_lt_pow_right hq hlt
    have h2 : q ^ k ≤ c * q ^ k := Nat.le_mul_of_pos_left _ hc
    omega
  have hpos : 0 < q ^ k := by positivity
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [h, ← pow_add, Nat.sub_add_cancel hkn]

theorem card_fib_mul {V W : Type*} [AddCommGroup V] [AddCommGroup W] [Fintype V] [Fintype W] [DecidableEq W] (f : V →+ W)
    (hf : Function.Surjective f) (w : W) :
    (Finset.univ.filter (fun v => f v = w)).card * Fintype.card W = Fintype.card V := by
  have hall : ∀ w', (Finset.univ.filter (fun v => f v = w')).card =
      (Finset.univ.filter (fun v => f v = w)).card := by
    intro w'
    obtain ⟨a, ha⟩ := hf w'
    obtain ⟨b, hb⟩ := hf w
    refine Finset.card_bij' (fun x _ => x + (b - a)) (fun x _ => x - (b - a)) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      rw [map_add (f := _), map_sub, hx, ha, hb]
      abel
    · intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      rw [map_sub, map_sub, hx, ha, hb]
      abel
    · intro x _
      abel
    · intro x _
      abel
  calc (Finset.univ.filter (fun v => f v = w)).card * Fintype.card W
      = ∑ w' : W, (Finset.univ.filter (fun v => f v = w')).card := by
        rw [Finset.sum_congr rfl (fun w' _ => hall w'), Finset.sum_const, Finset.card_univ,
          smul_eq_mul, mul_comm]
    _ = Finset.univ.card := (Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)).symm
    _ = Fintype.card V := Finset.card_univ

variable {K X : Type*} [Field K] [Fintype K] [DecidableEq K] [AddCommGroup X] [Module K X] [FiniteDimensional K X]
  [Fintype (Module.Dual K X)]

theorem exists_dual_one {Y : Type*} [AddCommGroup Y] [Module K Y] [FiniteDimensional K Y] (y : Y) (hy : y ≠ 0) :
    ∃ g : Module.Dual K Y, g y = 1 := by
  have h1 : ∃ g : Module.Dual K Y, g y ≠ 0 := by
    by_contra h
    push_neg at h
    exact hy ((Module.forall_dual_apply_eq_zero_iff K y).1 h)
  obtain ⟨g, hg⟩ := h1
  exact ⟨(g y)⁻¹ • g, by simp [hg]⟩

theorem card_dual : Fintype.card (Module.Dual K X) = Fintype.card K ^ Module.finrank K X := by
  rw [Module.card_eq_pow_finrank (K := K), Subspace.dual_finrank_eq]

theorem card_dual_one (x : X) (hx : x ≠ 0) :
    (Finset.univ.filter (fun g : Module.Dual K X => g x = 1)).card = Fintype.card K ^ (Module.finrank K X - 1) := by
  obtain ⟨g1, hg1⟩ := exists_dual_one (K := K) x hx
  let f : Module.Dual K X →+ K :=
    { toFun := fun g => g x, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hsurj : Function.Surjective f := fun c => ⟨c • g1, by simp [f, hg1]⟩
  have h : (Finset.univ.filter (fun g : Module.Dual K X => g x = 1)).card * Fintype.card K ^ 1 =
      Fintype.card K ^ Module.finrank K X := by
    rw [pow_one, ← card_dual]
    exact card_fib_mul f hsurj 1
  have hc : 1 ≤ (Finset.univ.filter (fun g : Module.Dual K X => g x = 1)).card :=
    Finset.card_pos.2 ⟨g1, by simp [hg1]⟩
  exact eq_pow_sub_of_mul_pow_eq_pow Fintype.one_lt_card hc h

theorem card_dual_two (te x : X) (hte : te ≠ 0) (hx : x ∉ Submodule.span K {te}) :
    (Finset.univ.filter (fun g : Module.Dual K X => g te = 1 ∧ g x = 1)).card =
      Fintype.card K ^ (Module.finrank K X - 2) := by
  have hte' : te ∉ Submodule.span K {x} := by
    intro h
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 h
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact hte (by rw [← hc, zero_smul])
    apply hx
    rw [← hc]
    exact Submodule.mem_span_singleton.2 ⟨c⁻¹, by rw [smul_smul, inv_mul_cancel₀ hc0, one_smul]⟩
  have hq1 : Submodule.Quotient.mk (p := Submodule.span K {te}) x ≠ 0 := by
    rwa [Ne, Submodule.Quotient.mk_eq_zero]
  have hq2 : Submodule.Quotient.mk (p := Submodule.span K {x}) te ≠ 0 := by
    rwa [Ne, Submodule.Quotient.mk_eq_zero]
  obtain ⟨h2, hh2⟩ := exists_dual_one (K := K) _ hq1
  obtain ⟨h1, hh1⟩ := exists_dual_one (K := K) _ hq2
  let g2 : Module.Dual K X := h2.comp (Submodule.span K {te}).mkQ
  let g1 : Module.Dual K X := h1.comp (Submodule.span K {x}).mkQ
  have g2te : g2 te = 0 := by
    simp only [g2, LinearMap.comp_apply, Submodule.mkQ_apply]
    rw [(Submodule.Quotient.mk_eq_zero _).2 (Submodule.mem_span_singleton_self te), map_zero]
  have g2x : g2 x = 1 := hh2
  have g1x : g1 x = 0 := by
    simp only [g1, LinearMap.comp_apply, Submodule.mkQ_apply]
    rw [(Submodule.Quotient.mk_eq_zero _).2 (Submodule.mem_span_singleton_self x), map_zero]
  have g1te : g1 te = 1 := hh1
  let f : Module.Dual K X →+ K × K :=
    { toFun := fun g => (g te, g x), map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hsurj : Function.Surjective f := by
    rintro ⟨a, b⟩
    refine ⟨a • g1 + b • g2, ?_⟩
    simp [f, g1te, g1x, g2te, g2x]
  have h : (Finset.univ.filter (fun g : Module.Dual K X => g te = 1 ∧ g x = 1)).card *
      Fintype.card K ^ 2 = Fintype.card K ^ Module.finrank K X := by
    rw [← card_dual, sq, ← Fintype.card_prod]
    have h3 := card_fib_mul f hsurj (1, 1)
    have h4 : (Finset.univ.filter (fun g : Module.Dual K X => f g = (1, 1))) =
        Finset.univ.filter (fun g : Module.Dual K X => g te = 1 ∧ g x = 1) := by
      ext g
      simp [f, Prod.ext_iff]
    rw [h4] at h3
    exact h3
  have hc : 1 ≤ (Finset.univ.filter (fun g : Module.Dual K X => g te = 1 ∧ g x = 1)).card :=
    Finset.card_pos.2 ⟨g1 + g2, by simp [g1te, g1x, g2te, g2x]⟩
  exact eq_pow_sub_of_mul_pow_eq_pow Fintype.one_lt_card hc h

theorem card_dual_line (te x : X) (hx : x ∈ Submodule.span K {te}) (hne : x ≠ te) :
    (Finset.univ.filter (fun g : Module.Dual K X => g te = 1 ∧ g x = 1)).card = 0 := by
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro g - ⟨h1, h2⟩
  apply hne
  rw [map_smul, h1, smul_eq_mul, mul_one] at h2
  rw [h2, one_smul]

theorem card_sig_fib {A : Type*} {B : A → Type*} [Fintype A] [∀ a, Fintype (B a)] {Y : Type*} [DecidableEq Y]
    (ι : ∀ a, B a → Y) (P : A → Y → Prop) [∀ a y, Decidable (P a y)] (hι : ∀ a b, P a (ι a b)) (hu : ∀ a y, P a y → ∃! b, ι a b = y) (y : Y) :
    (Finset.univ.filter (fun p : (Σ a, B a) => ι p.1 p.2 = y)).card = (Finset.univ.filter (fun a => P a y)).card := by
  refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
  · rintro ⟨a, b⟩ hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
    rw [← hp]
    exact hι a b
  · rintro ⟨a, b⟩ hp ⟨a', b'⟩ hp' h
    simp only at h
    subst h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hp'
    have hP : P a y := by rw [← hp]; exact hι a b
    have hbb := (hu a y hP).unique hp hp'
    rw [hbb]
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    obtain ⟨b, hb, -⟩ := hu a y ha
    exact ⟨⟨a, b⟩, by simp [hb], rfl⟩

theorem card_filter_subtype {α : Type*} [Fintype α] (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    [Fintype {a // p a}] :
    (Finset.univ.filter (fun a : {a // p a} => q a.1)).card = (Finset.univ.filter (fun a => p a ∧ q a)).card := by
  refine Finset.card_bij (fun a _ => a.1) ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    exact ⟨a.2, ha⟩
  · intro a _ b _ h
    exact Subtype.ext h
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    exact ⟨⟨b, hb.1⟩, by simp [hb.2], rfl⟩

end Formalism.L2.GlobalTheoryTheory.UnramifiedTrace
end

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Formalism.L2.Forms Formalism.L2.GlobalTheoryTheory.LocalLatticeBases Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.S0 NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct Classical

variable {D : D7} {u : D.what₂.Word}

def DUPt0F (T : Forms0 D u) : Prop :=
  ∀ (v : (D.mem u).A.vT) (c : (D.mem u).C.cls 0),
  ∃ (γ : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) → UJ (sigD D : D.host.E →+* D.host.E) (gramN D 0 (Nat.zero_le _)))
    (η : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) →
      UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F))
    (κ : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) → T.cls0.lev.U)
    (Mu : ∀ g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c),
      {x : (D.fm u).lv 0 v ((D.fm u).dn 0 v c g) // (D.fm u).fv 0 v ((D.fm u).dn 0 v c g) x = 1} →
        UPts (sigD D) (gramN D 0 (Nat.zero_le _)) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)),
    DnMvs T v c γ η κ ∧ (∀ g x, IsUpMvF T v ((D.fm u).dn 0 v c g) x.1 (Mu g x)) ∧
    ∃ (ι : ∀ g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c),
        {x : (D.fm u).lv 0 v ((D.fm u).dn 0 v c g) // (D.fm u).fv 0 v ((D.fm u).dn 0 v c g) x = 1} → (D.fm u).lk 0 v c)
      (τ : ((D.mem u).A.Fv v)ˣ ≃ ((D.mem u).A.Fv v)ˣ),
      (∀ g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c), g ≠ 0 → ∀ x, g (ι g x) = 1) ∧
      (∀ g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c), g ≠ 0 → ∀ y, g y = 1 → ∃! x, ι g x = y) ∧
      ∀ G ∈ AdFun T.cls0.lev (embT D),
        (∀ p : PD D u v c, ι p.1.1 p.2 = (D.fm u).te 0 v c →
          G (T.cls0.y c * hcomp T (η p.1.1) (κ p.1.1) (Mu p.1.1 p.2)) = G (T.cls0.y c)) ∧
        (∀ (p : PD D u v c) (q : PE D u v c), ι p.1.1 p.2 = ι q.1.1 q.2 →
          G (T.cls0.y c * hcomp T (η p.1.1) (κ p.1.1) (Mu p.1.1 p.2)) =
          G (T.cls0.y c * hcomp T (η q.1.1) (κ q.1.1) (Mu q.1.1 q.2))) ∧
        (∀ p q : PE D u v c, ι p.1.1 p.2 = ι q.1.1 q.2 →
          G (T.cls0.y c * hcomp T (η p.1.1) (κ p.1.1) (Mu p.1.1 p.2)) =
          G (T.cls0.y c * hcomp T (η q.1.1) (κ q.1.1) (Mu q.1.1 q.2))) ∧
        (∀ (a : ((D.mem u).A.Fv v)ˣ) (q : PE D u v c), ι q.1.1 q.2 = (a : (D.mem u).A.Fv v) • (D.fm u).te 0 v c →
          ∀ (k : ℤ), (k : (D.mem u).A.Fv v) = ((τ a : ((D.mem u).A.Fv v)ˣ) : (D.mem u).A.Fv v) →
          ∀ δ, IsDia T.cls0.lev (T.atT.eV v).1 (T.atT.eV v).2 k δ →
          G (T.cls0.y c * hcomp T (η q.1.1) (κ q.1.1) (Mu q.1.1 q.2)) = G (T.cls0.y c * δ))

set_option maxHeartbeats 4000000 in
theorem duFib_of_pt (T : Forms0 D u) (h : DUPt0F T) : DUFib0F T := by
  intro v c
  obtain ⟨γ, η, κ, Mu, hmv, hMu, ι, τ, hι, hu, hval⟩ := h v c
  have hK : Fintype.card ((D.mem u).A.Fv v) = (D.mem u).A.T := (D.mem u).A.card_Fv v
  have hr : Module.finrank ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) = D.R.N 0 := (D.fm u).lk_rank 0 v c
  have hte := (D.fm u).te_ne 0 v c
  refine ⟨γ, η, κ, Mu, hmv, hMu, fun p => ι p.1.1 p.2, fun q => ι q.1.1 q.2, τ, fun y => ?_, fun y => ?_, hval⟩
  · refine (card_sig_fib (A := {g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) // g ≠ 0})
      (fun g x => ι g.1 x) (fun g y => g.1 y = 1) (fun g x => hι g.1 g.2 x) (fun g y hy => hu g.1 g.2 y hy) y).trans ?_
    rw [card_filter_subtype (fun g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) => g ≠ 0) (fun g => g y = 1)]
    split_ifs with hy
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro g - ⟨-, h1⟩
      rw [hy, map_zero] at h1
      exact zero_ne_one h1
    · rw [Finset.filter_congr (q := fun g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) => g y = 1)
        (fun g _ => ⟨fun h => h.2, fun h => ⟨fun h0 => by rw [h0, LinearMap.zero_apply] at h; exact zero_ne_one h, h⟩⟩),
        card_dual_one y hy, hK, hr]
  · refine (card_sig_fib (A := {g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) // g ((D.fm u).te 0 v c) = 1})
      (fun g x => ι g.1 x) (fun g y => g.1 y = 1) (fun g x => hι g.1 (fun h0 => ?_) x)
      (fun g y hy => hu g.1 (fun h0 => ?_) y hy) y).trans ?_
    · have := g.2; rw [h0, LinearMap.zero_apply] at this; exact zero_ne_one this
    · have := g.2; rw [h0, LinearMap.zero_apply] at this; exact zero_ne_one this
    rw [card_filter_subtype (fun g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) => g ((D.fm u).te 0 v c) = 1)
      (fun g => g y = 1)]
    split_ifs with h1 h2
    · rw [h1, Finset.filter_congr (q := fun g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk 0 v c) =>
        g ((D.fm u).te 0 v c) = 1) (fun g _ => and_self_iff), card_dual_one _ hte, hK, hr]
    · exact card_dual_line _ y h2 h1
    · rw [card_dual_two _ y hte h2, hK, hr]

end Formalism.L2.GlobalTheoryTheory.UnramifiedTrace

end
