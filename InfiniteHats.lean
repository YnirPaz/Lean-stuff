import Mathlib.Data.Set.Finite
import Mathlib.Tactic

/-
This file formalizes a solution to the following problen:

Countably many people stand in a row, each wearing a black hat or a white hat and all facing
towards positive infinity (so that the first sees everyone's hats except their own).
Simultaneously, each guesses the color of their own hat. To win, all but finitely many of them
need to be right. Find a strategy that guarantees a victory.

Solution: define two infinite lines of hats as equivalent if they differ at only finitely many places.
This is an equivalence relation, so using the axiom of choice the players can pick a representative
from each equivalence class.
When a person sees a part of the infinite line ahead of them, they know what equivalence class this
line is in, so they pretend that the line is the representative of that class and guess accordingly.
The actual line only differs from the representative at finitely many places, so past a certain point
they all guess correctly.
-/

open Classical
noncomputable section

def shiftBack {α : Type _} (f : ℕ → α) (sh : ℕ) : ℕ → α := fun n ↦ f (n + sh)

inductive Hat where
  | black : Hat
  | white : Hat

def Line := ℕ → Hat

-- strategy for a single person: the line they see ↦ the color they guess
def Strat := Line → Hat

def Strategy := ℕ → Strat

def pad (l : Line) (s : ℕ) : Line := fun n ↦ if n + 1 ≤ s then Hat.white else l (n - s)

-- given a strategy and a line, n ↦ true if the n'th person guesses right, false if wrong
def runGame (s : Strategy) (line : Line) : ℕ → Bool := fun n ↦
  decide (line n = s n (shiftBack line (n + 1)))

def corrects (s : Strategy) (line : Line) : Set ℕ := {n | runGame s line n}

def eveEq (l₁ l₂ : Line) : Prop := ∃ N, ∀ n, N < n → l₁ n = l₂ n

infix:50 " ~~ " => eveEq

theorem eveEq_refl : Reflexive eveEq := fun _ ↦ ⟨0, fun _ _ ↦ rfl⟩

theorem eveEq_symm : Symmetric eveEq := fun _ _ ⟨n, hn⟩ ↦ ⟨n, fun m hm ↦ (hn m hm).symm⟩

theorem eveEq_trans : Transitive eveEq := fun _ _ _ ⟨N₁, hN₁⟩ ⟨N₂, hN₂⟩ ↦
  ⟨max N₁ N₂, fun n hn ↦ Eq.trans (hN₁ n (max_lt_iff.mp hn).1) (hN₂ n (max_lt_iff.mp hn).2)⟩

theorem eveEq_equiv : Equivalence eveEq := ⟨@eveEq_refl, @eveEq_symm, @eveEq_trans⟩

instance eveEqSetoid : Setoid Line where
  r     := eveEq
  iseqv := eveEq_equiv

def LineClass := Quotient eveEqSetoid

def chooseRep (c : LineClass) : Line := choose (Quot.exists_rep c)

theorem eveEq_rep (l : Line) : l ~~ chooseRep (⟦l⟧) :=
  eveEq_symm (Quotient.exact (choose_spec (Quot.exists_rep (⟦l⟧))))

theorem eveEq_pad_shift (l : Line) (n : ℕ) : l ~~ pad (shiftBack l n) n :=
  ⟨n, fun m nltm ↦ by
    dsimp [pad, shiftBack]
    have := Nat.not_le_of_lt (Nat.succ_eq_add_one m ▸ (Nat.lt_succ_of_lt nltm))
    rw [if_neg this, Nat.sub_add_cancel (le_of_lt nltm)]⟩

/-
the n'th person assumes everyone they can't see are wearing white hats and guesses the
color of the n'th hat in the representative of the equivalence class of that line
-/
def winningStrat : Strategy := fun n l ↦ chooseRep ⟦pad l (n + 1)⟧ n

theorem exists_winning_strategy : ∃ s : Strategy, ∀ line : Line,
    Set.Finite (corrects s line)ᶜ := by
  use winningStrat
  intro l
  set M := (corrects winningStrat l)ᶜ
  have := eveEq_rep l
  set rl := chooseRep ⟦l⟧
  rcases this with ⟨N, hN⟩
  have : ∀ n, N < n → n ∈ Mᶜ := fun n Nltn ↦ by
    have aux : Mᶜ = corrects winningStrat l := compl_compl (corrects winningStrat l)
    rw [aux]
    dsimp [corrects, runGame, winningStrat]
    have lRpad := eveEq_pad_shift l (n + 1)
    rw [decide_eq_true_eq]
    set l' := pad (shiftBack l (n + 1)) (n + 1)
    have this : rl = chooseRep (Quotient.mk eveEqSetoid l') := congrArg chooseRep (Quotient.sound lRpad)
    exact this ▸ (hN n Nltn)
  let A := {n : ℕ | n ≤ N}
  have Afin : Set.Finite A := Set.finite_le_nat N
  suffices H : M ⊆ A
  · exact Afin.subset H
  intro m hM
  dsimp
  by_contra h
  have := this m (lt_of_not_le h)
  trivial
