module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.InertInSec
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalAlgebraHolds
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.BaseChangeWeyl.BcWeyl
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.InertFrames.UnifOfP
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.InertFrames.SatUniqA

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.InertInSecAlt
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical

namespace PositivityTheory.Rg.BcB.F.FX

theorem inertInSec : InertInSec := by
  intro E _ _ _ S hS w hw
  obtain ⟨u, ⟨huS, hu⟩, -⟩ := hS w
  by_cases h : u = w
  · exact h ▸ huS
  · exact absurd ⟨u, h, hu⟩ hw

end PositivityTheory.Rg.BcB.F.FX

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.SatCompAt
section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.BaseChangeWeyl.IrredCompSurj
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.LemB

section Conj

variable {L : Type} [Field L] (s : L →+* L) {n : ℕ}

theorem conj_mem_GU (P Q X : Matrix (Fin n) (Fin n) L) (hPQ : P * Q = 1) (hX : cT s X * 1 * X = 1) :
    cT s (Q * X * P) * (cT s P * P) * (Q * X * P) = cT s P * P := by
  have h1 : cT s Q * cT s P = 1 := by rw [← cT_mul, hPQ, cT_one]
  rw [Matrix.mul_one] at hX
  rw [cT_mul, cT_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (cT s Q) (cT s P), h1, Matrix.one_mul, ← Matrix.mul_assoc P Q, hPQ, Matrix.one_mul,
    ← Matrix.mul_assoc (cT s X) X, hX, Matrix.one_mul]

theorem conj_mem_UJ (P Q Y : Matrix (Fin n) (Fin n) L) (hPQ : P * Q = 1)
    (hY : cT s Y * (cT s P * P) * Y = cT s P * P) :
    cT s (P * Y * Q) * 1 * (P * Y * Q) = 1 := by
  have h1 : cT s Q * cT s P = 1 := by rw [← cT_mul, hPQ, cT_one]
  rw [Matrix.mul_one, cT_mul, cT_mul]
  calc cT s Q * (cT s Y * cT s P) * (P * Y * Q) = cT s Q * (cT s Y * (cT s P * P) * Y) * Q := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by
        rw [hY]
        simp only [Matrix.mul_assoc]
        rw [hPQ, Matrix.mul_one, h1]

def conjU (b : GL (Fin n) L) (hb : cT s b.val * b.val = antiJ L n) (H : Subgroup (GL (Fin n) L))
    (hH : ∀ g, g ∈ H ↔ g ∈ UJ s (1 : Matrix (Fin n) (Fin n) L)) : H ≃* GU s n where
  toFun x := ⟨b⁻¹ * x.1 * b, by
    have hx : cT s (x.1 : Matrix (Fin n) (Fin n) L) * 1 * x.1 = 1 := (hH _).1 x.2
    change cT s _ * antiJ L n * _ = antiJ L n
    rw [← hb]
    simp only [Units.val_mul]
    exact conj_mem_GU s _ _ _ (Units.mul_inv b) hx⟩
  invFun y := ⟨b * y.1 * b⁻¹, by
    refine (hH _).2 ?_
    have hy : cT s (y.1 : Matrix (Fin n) (Fin n) L) * antiJ L n * y.1 = antiJ L n := y.2
    rw [← hb] at hy
    change cT s _ * 1 * _ = 1
    simp only [Units.val_mul]
    exact conj_mem_UJ s _ _ _ (Units.mul_inv b) hy⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv y := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

theorem conjU_val (b : GL (Fin n) L) (hb : cT s b.val * b.val = antiJ L n) (H : Subgroup (GL (Fin n) L))
    (hH : ∀ g, g ∈ H ↔ g ∈ UJ s (1 : Matrix (Fin n) (Fin n) L)) (x : H) :
    ((conjU s b hb H hH x : GU s n) : GL (Fin n) L) = b⁻¹ * x.1 * b := rfl

end Conj

theorem irred_comp_surj {H H' X : Type} [Group H] [Group H'] [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ H X) (φ : H' →* H) (hφ : Function.Surjective φ) (h : ρ.IsIrreducible) :
    Representation.IsIrreducible (ρ.comp φ) := by
  obtain ⟨h0, h1⟩ := (GlobalTheory.CuspRep.isIrreducible_iff _).1 h
  refine (GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨h0, fun W hW => h1 W fun g v hv => ?_⟩
  obtain ⟨g', rfl⟩ := hφ g
  exact hW g' v hv

end PositivityTheory.Rg.BcB.F.LemB

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LemA
namespace PositivityTheory.Rg.BcB.F.Inert

theorem lem_b : SatUniq := satUniq

end PositivityTheory.Rg.BcB.F.Inert
end

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.FX

open PositivityTheory.Rg.BcB.F.LemB in
theorem satCompAt : SatCompAt := by
  intro E _ _ _ n π hπ w hw σ b' ϖ ϖ' q q' α α' hσ hb' hϖ' hI hI' hS hS'
  apply PositivityTheory.Rg.BcB.F.LemB.bcWeyl
  obtain ⟨b, hbK, hb, p, hp, σ1, hc, hsat⟩ := hS
  obtain ⟨p0, hp0, hc0⟩ := hσ

  have hcj : ∀ x : E, cj w (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x) := by
    have hex : ∃ s : w.adicCompletion E →+* w.adicCompletion E, Continuous s ∧
        ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x) := by
      by_contra hne
      obtain ⟨x, -, hx⟩ := hI.2.2.2.2.1
      have hid : cj w = RingHom.id _ := by rw [cj, dite_eq_right hne]
      rw [hid, RingHom.id_apply, sub_self, map_zero] at hx
      exact zero_ne_one hx
    have hcj' : cj w = hex.choose := by rw [cj, dite_eq_left hex]
    intro x
    rw [hcj']
    exact hex.choose_spec.2 x
  have hUL : ∀ g, g ∈ UL n w ↔ g ∈ UJ (cj w) (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
    intro g
    rw [UL, if_neg hw]
  obtain ⟨e, he⟩ := GlobalTheory.DefU.Inert.locU_equiv E n w (cj w) hcj hI.2.1
  let f := conjU (cj w) b hb (UL n w) hUL
  let u : locU n w → UL n w := fun x => ⟨(e x).1, (hUL _).2 (e x).2⟩
  have hu : ∀ g : UL n w, u (e.symm ⟨g.1, (hUL _).1 g.2⟩) = g := fun g => Subtype.ext (by simp [u])
  have hpf : ∀ x, p x = f (u x) := fun x => Subtype.ext ((hp x).trans (by rw [conjU_val, he]))
  have hp0u : ∀ x, p0 x = u x := fun x => Subtype.ext ((hp0 x).trans (by simp only [u]; rw [he]))
  have hps : Function.Surjective p := fun y =>
    ⟨e.symm ⟨(f.symm y).1, (hUL _).1 (f.symm y).2⟩, by rw [hpf, hu, MulEquiv.apply_symm_apply]⟩
  have hps0 : Function.Surjective p0 := fun y =>
    ⟨e.symm ⟨y.1, (hUL _).1 y.2⟩, by rw [hp0u, hu]⟩

  obtain ⟨r, -, -, hr⟩ := GlobalTheory.DefU.LocRet.exists_ret E n w
  let Ψ : GlobalTheory.DefU.AutSub E n := ⟨π, hπ⟩
  obtain ⟨-, F0, hF0, hFm, hF⟩ := hc0
  obtain ⟨-, F1, hF1, hFm', hF'⟩ := hc
  let F : Representation.IntertwiningMap (σ.ρ.comp p0) (Ψ.rep.comp (locU n w).subtype) :=
    ⟨F0.codRestrict π hFm, fun x => LinearMap.ext fun v => Subtype.ext (hF x v)⟩
  let F' : Representation.IntertwiningMap (σ1.ρ.comp p) (Ψ.rep.comp (locU n w).subtype) :=
    ⟨F1.codRestrict π hFm', fun x => LinearMap.ext fun v => Subtype.ext (hF' x v)⟩
  have hG0 : F ≠ 0 := fun h => hF0 (LinearMap.ext fun v => congrArg Subtype.val (DFunLike.congr_fun h v))
  have hG1 : F' ≠ 0 := fun h => hF1 (LinearMap.ext fun v => congrArg Subtype.val (DFunLike.congr_fun h v))
  obtain ⟨-, h2⟩ := GlobalTheory.CuspRep.CompUniq.isotypic (UA E n) (locU n w) Ψ.V σ.V σ1.V Ψ.rep (locU n w).subtype
    (σ.ρ.comp p0) (σ1.ρ.comp p) Ψ.isIrreducible_rep (irred_comp_surj σ.ρ p0 hps0 σ.irred)
    (irred_comp_surj σ1.ρ p hps σ1.irred) (fun g => ⟨r g, fun y => hr g y⟩) F hG0
  obtain ⟨T⟩ := h2 F' hG1

  have hs1 : SatUL b (ϖ : w.adicCompletion E) q σ α := by
    refine ⟨f, σ1, fun x => rfl, hsat, ⟨{ toLinearEquiv := T.toLinearEquiv, isIntertwining' := fun g => ?_ }⟩⟩
    have h1 : p (e.symm ⟨g.1, (hUL _).1 g.2⟩) = f g := by rw [hpf, hu]
    have h0 : p0 (e.symm ⟨g.1, (hUL _).1 g.2⟩) = g := by rw [hp0u, hu]
    have := T.isIntertwining' (e.symm ⟨g.1, (hUL _).1 g.2⟩)
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, h1, h0] at this
    exact this

  have hne : (ϖ : w.adicCompletion E) ≠ 0 := ϖ.ne_zero
  have hunif : IsUnifAt ϖ := by
    refine ⟨?_, hI.2.2.1⟩
    have hv := hI.2.2.2.1
    have h0 : Valued.v (ϖ : w.adicCompletion E) ≠ 0 := by rw [hv]; exact WithZero.coe_ne_zero
    have hu1 : ∀ h : Valued.v (ϖ : w.adicCompletion E) ≠ 0, WithZero.unzero h = Multiplicative.ofAdd (-1 : ℤ) := fun h =>
      WithZero.coe_injective (by rw [WithZero.coe_unzero, hv])
    show ordL (ϖ : w.adicCompletion E) = 1
    unfold ordL
    rw [dite_eq_right h0, hu1]
    simp
  exact PositivityTheory.Rg.BcB.F.Inert.lem_b E n w hw b b' ϖ ϖ' q q' σ α α' ⟨hbK, hb⟩ hb' hunif hϖ' hI hI' hs1 hS'

end PositivityTheory.Rg.BcB.F.FX

end
end
