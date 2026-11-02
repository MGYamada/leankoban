import Tools.Solver
import Leankoban.Engine
import Leankoban.Levels.Data

/-!
# `lake exe genproofs`：100 面の可解性証明を生成する

ゲームに組み込まれた盤面 `Levels.all` だけを入力に、生成器とは独立にソルバーで解き直す。
得られた手順を `Engine.check` で確認してから、各面の証明ファイル `Proofs/LevelNNN.lean` と、
全面をまとめた `Proofs.lean` を書き出す。証明の中身はカーネルによる計算（`decide +kernel`）だけ。
-/

open Leankoban Leankoban.Tools

def pad3 (n : Nat) : String :=
  let s := toString n
  "".pushn '0' (3 - s.length) ++ s

def quote (s : String) : String := "\"" ++ s ++ "\""

/-- 長い LURD 文字列を、1 つの文字列リテラルのまま折り返す（行末の `\` は Lean の文字列ギャップ）。
`++` で連結すると `String.append` が `propext` を持ち込むので使わない。 -/
def wrapLurd (s : String) (width : Nat := 72) : String := Id.run do
  let cs := s.toList
  let mut chunks : List String := []
  let mut rest := cs
  while !rest.isEmpty do
    chunks := chunks ++ [String.ofList (rest.take width)]
    rest := rest.drop width
  if chunks.isEmpty then chunks := [""]
  return quote ("\\\n    ".intercalate chunks)

def proofFile (i : Nat) (rows : List String) (sol : Solution) : String :=
  let n := pad3 i
  let boxes := (Level.ofRows rows).boxes.length
  let board := ",\n    ".intercalate (rows.map quote)
  s!"import Leankoban.Soundness
import Leankoban.Levels.Data

/-!
# 面 {i} の可解性証明

箱 {boxes} 個。証明書の解は押し {sol.pushes} 回・手数 {sol.moves}（押し数最小の解）。

この証明が依存するのは、ルール仕様 `Leankoban.Spec`、実行系 `Leankoban.Engine`、
健全性定理 `Leankoban.Soundness.certify`、そしてカーネルによる計算だけで、公理は一切使わない。
（`lake exe genproofs` が自動生成。手で編集しない。）
-/

namespace Leankoban.Proofs.Level{n}

open Leankoban

/-- ゲームが読み込む盤面 `Levels.level{n}` を、ここに絵として展開したもの。 -/
theorem board_eq : Levels.level{n} = [
    {board}] := rfl

/-- 解の手順（LURD 記法。小文字は歩く手、大文字は箱を押す手）。 -/
def solution : String :=
    {wrapLurd sol.lurd}

/-- **面 {i} はクリア可能である。** -/
theorem solvable :
    WellFormed (Level.ofRows Levels.level{n}) ∧ Solvable (Level.ofRows Levels.level{n}) :=
  Soundness.certify Levels.level{n} solution (by decide +kernel)

end Leankoban.Proofs.Level{n}
"

def rootFile (count : Nat) : String := Id.run do
  let imports := (List.range count).map fun i => s!"import Proofs.Level{pad3 (i + 1)}"
  let mut proof := "Soundness.forall_mem_nil"
  for i in (List.range count).reverse do
    proof := s!"Soundness.forall_mem_cons_intro Proofs.Level{pad3 (i + 1)}.solvable\n    ({proof})"
  -- 入れ子が深くなりすぎないよう、行頭の字下げは固定にする
  return "\n".intercalate imports ++ s!"

/-!
# 全 {count} 面の可解性

ゲームに収録された全 {count} 面（`Leankoban.Levels.all`）が、どれも `WellFormed` かつ `Solvable` であること。
各面の証明は `Proofs/LevelNNN.lean` にある。（`lake exe genproofs` が自動生成。手で編集しない。）
-/

namespace Leankoban

set_option maxRecDepth 16384 in
/-- **ゲームに収録された全 {count} 面はクリア可能である。** -/
theorem all_levels_solvable :
    ∀ rows ∈ Levels.all, WellFormed (Level.ofRows rows) ∧ Solvable (Level.ofRows rows) :=
  {proof}

end Leankoban
"

def main (_args : List String) : IO UInt32 := do
  IO.FS.createDirAll "Proofs"
  let levels := Levels.all
  let mut i := 0
  let mut totalMoves := 0
  for rows in levels do
    i := i + 1
    match solveRows rows with
    | none =>
      IO.eprintln s!"面 {i}: 解けませんでした"
      return 1
    | some sol =>
      if !Engine.check rows sol.lurd then
        IO.eprintln s!"面 {i}: ソルバーの解が検査を通りませんでした"
        return 1
      totalMoves := totalMoves + sol.moves
      IO.FS.writeFile s!"Proofs/Level{pad3 i}.lean" (proofFile i rows sol)
      IO.eprintln s!"面 {i}: 押し {sol.pushes}・手数 {sol.moves}（探索 {sol.explored} 局面）→ Proofs/Level{pad3 i}.lean"
  IO.FS.writeFile "Proofs.lean" (rootFile levels.length)
  IO.eprintln s!"{levels.length} 個の証明ファイルと Proofs.lean を書き出しました（総手数 {totalMoves}）"
  return 0
