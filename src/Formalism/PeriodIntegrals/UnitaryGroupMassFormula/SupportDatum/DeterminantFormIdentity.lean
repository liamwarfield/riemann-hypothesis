module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SupportDatum.Blocks

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SupportDatum.PowModTwoOfSq
noncomputable section

namespace PI.SupportDatumW

open NumberField IsDedekindDomain Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups ValuativeRel
open scoped BigOperators ComplexOrder
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem twist_mul {D : Formalism.BasicNotions.D7} (p : PlF D) (s : ℕ) (x : (D.s.atP p).Ep) :
    twist p s x = x * twist p s 1 := by
  unfold twist
  rcases (D.s.atP p).split with _ | sg
  · simp
  · apply sg.e.injective
    ext <;> simp [mul_comm]

theorem twist_one_pow {D : Formalism.BasicNotions.D7} (p : PlF D) (s : ℕ) :
    twist p s (1 : (D.s.atP p).Ep) = twist p 1 (1 : (D.s.atP p).Ep) ^ s := by
  unfold twist
  rcases (D.s.atP p).split with _ | sg
  · simp
  · apply sg.e.injective
    ext <;> simp

theorem twist_sq {D : Formalism.BasicNotions.D7} (p : PlF D) :
    twist p 1 (1 : (D.s.atP p).Ep) ^ 2 = 1 := by
  unfold twist
  rcases (D.s.atP p).split with _ | sg
  · simp
  · apply sg.e.injective
    ext <;> simp

def hF (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (p : PlF D) (a s : ℕ) : (D.s.atP p).Ep :=
  Ring.inverse ((algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * (D.s.atP p).ιE (uP p : D.host.E)) ^
    (nu D.R.rS a (a + s - 1))) * twist p s 1 * Ring.inverse (qE p)

end PI.SupportDatumW
end
end

noncomputable section

namespace PI.SupportDatumW

open NumberField IsDedekindDomain Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups ValuativeRel
open scoped BigOperators ComplexOrder
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem modBlocks_some {A B : Type} [Monoid B] (f : ℕ → ℕ → A → B) (bs : List (A × ℕ)) (a : ℕ)
    (l : List (Bˣ × ℕ+)) (h : modBlocks f a bs = some l) :
    l.map (fun x => ((x.1 : B), (x.2 : ℕ))) = mapBlocks f a bs := by
  induction bs generalizing a l with
  | nil =>
    simp only [modBlocks, Option.some.injEq] at h
    subst h
    simp [mapBlocks]
  | cons b rest ih =>
    obtain ⟨t, s⟩ := b
    simp only [modBlocks] at h
    split_ifs at h with hu
    obtain ⟨l', hl', rfl⟩ := Option.map_eq_some_iff.mp h
    simp [mapBlocks, ih (a + s) l' hl']

theorem mapBlocks_snd {A B : Type} (f : ℕ → ℕ → A → B) (bs : List (A × ℕ)) (a : ℕ) :
    (mapBlocks f a bs).map Prod.snd = bs.map Prod.snd := by
  induction bs generalizing a with
  | nil => simp [mapBlocks]
  | cons b rest ih =>
    obtain ⟨t, s⟩ := b
    simp [mapBlocks, ih]

theorem blkDet_append {K : Type} [CommRing K] (l1 l2 : List (K × ℕ)) :
    blkDet (l1 ++ l2) = blkDet l1 * blkDet l2 := by
  induction l1 with
  | nil => simp [blkDet]
  | cons b rest ih =>
    obtain ⟨t, s⟩ := b
    simp only [List.cons_append, blkDet, ih]
    ring

end PI.SupportDatumW
