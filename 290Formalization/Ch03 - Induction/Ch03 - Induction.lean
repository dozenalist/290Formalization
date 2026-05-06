import «290Formalization».«Ch02 - Logic and Proofs».«Ch02 - Logic»



def SumUpTo (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => f 0
  | n + 1 => f (n + 1) + SumUpTo f n





class inductive cFinite (α : Type) : Prop where
  | hasInj (k : ℕ) (f : α → Fin k) (h : Function.Injective f) : cFinite α

export cFinite (hasInj)


class dFinite (α : Type) where
  par : ℕ
  function : α → Fin par
  hasInj : Function.Injective function


variable (a b : Type)

instance [h : dFinite a] : cFinite a :=
  let ⟨p, f, h⟩ := h
  hasInj p f h
