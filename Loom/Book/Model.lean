/-!
# The document model (L6)

The book pipeline is projection-native: `Extract` walks instruction
declarations and produces this model; renderers typeset it. No free-typed
facts — every table cell and quoted constant arrives from a checked term.
Scoped ruthlessly: it exists to serve ISA books, not to compete with
general documentation systems (Rule 5).
-/

namespace Loom.Book

/-- Inline text with a little structure: `code` spans render monospace. -/
inductive Inline where
  | text (s : String)
  | code (s : String)
deriving Repr

/-- One block of the document. -/
inductive Block where
  | heading (level : Nat) (text : String)
  | para (content : String)
  | table (header : List String) (rows : List (List String))
  | list (items : List String)
deriving Repr

/-- A document. -/
structure Doc where
  title : String
  blocks : List Block
deriving Repr

end Loom.Book
