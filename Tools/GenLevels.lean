import Tools.Generator
import Std.Data.HashSet

/-!
# `lake exe genlevels`：100 面を生成する

段階ごとに候補を多めに作り、難易度スコアの高いものを選んでから易しい順に並べる。
seed を固定しているので、何度実行しても同じ `Leankoban/Levels/Data.lean` が得られる。

使い方: `lake exe genlevels [--seed N] [--out PATH]`
-/

open Leankoban Leankoban.Tools

structure Tier where
  name       : String
  count      : Nat     -- この段階で採用する面の数
  candidates : Nat     -- 集める候補の数（この中からスコアの高い順に選ぶ）
  attempts   : Nat     -- 試行回数の上限
  params     : Params

def tiers : List Tier := [
  { name := "入門", count := 5, candidates := 30, attempts := 6000,
    params := { boxes := 1, hMin := 4, hMax := 5, wMin := 4, wMax := 6, pieces := 3,
                minPush := 4, floorMin := 10, floorMax := 24 } },
  { name := "初級", count := 10, candidates := 60, attempts := 10000,
    params := { boxes := 2, hMin := 4, hMax := 6, wMin := 5, wMax := 6, pieces := 4,
                minPush := 6, floorMin := 12, floorMax := 28 } },
  { name := "初中級", count := 15, candidates := 90, attempts := 15000,
    params := { boxes := 2, hMin := 6, hMax := 7, wMin := 6, wMax := 7, pieces := 7,
                minPush := 10, floorMin := 18, floorMax := 36 } },
  { name := "中級", count := 20, candidates := 120, attempts := 20000,
    params := { boxes := 3, hMin := 6, hMax := 7, wMin := 6, wMax := 8, pieces := 8,
                minPush := 12, floorMin := 20, floorMax := 40 } },
  { name := "中上級", count := 20, candidates := 120, attempts := 20000,
    params := { boxes := 3, hMin := 7, hMax := 8, wMin := 7, wMax := 9, pieces := 10,
                minPush := 18, floorMin := 26, floorMax := 48 } },
  { name := "上級", count := 15, candidates := 90, attempts := 20000,
    params := { boxes := 4, hMin := 7, hMax := 8, wMin := 7, wMax := 9, pieces := 10,
                minPush := 20, floorMin := 28, floorMax := 50 } },
  { name := "達人", count := 10, candidates := 60, attempts := 20000,
    params := { boxes := 4, hMin := 8, hMax := 9, wMin := 8, wMax := 10, pieces := 13,
                minPush := 26, floorMin := 32, floorMax := 58, cap := 500000 } },
  { name := "最難関", count := 5, candidates := 25, attempts := 20000,
    params := { boxes := 5, hMin := 8, hMax := 10, wMin := 9, wMax := 10, pieces := 15,
                minPush := 30, floorMin := 36, floorMax := 64, cap := 800000 } }
]

def pad3 (n : Nat) : String :=
  let s := toString n
  "".pushn '0' (3 - s.length) ++ s

def quote (s : String) : String := "\"" ++ s ++ "\""

def renderData (seed : Nat) (levels : Array (String × Generated)) : String := Id.run do
  let mut out := "/-!\n# 盤面データ（自動生成）\n\n"
  out := out ++ s!"`lake exe genlevels --seed {seed}` が生成した 100 面。手で編集しない。\n"
  out := out ++ "各面の doc コメントの押し数・手数は、生成時のソルバーが見つけた解の値。\n-/\n\n"
  out := out ++ "namespace Leankoban.Levels\n\n"
  for h : i in [0:levels.size] do
    let (tierName, g) := levels[i]
    let n := pad3 (i + 1)
    out := out ++ s!"/-- 面 {i + 1}（{tierName}）箱 {g.boxes} 個・最小押し数 {g.depth}・手数 {g.moves} -/\n"
    out := out ++ s!"def level{n} : List String := [\n"
    out := out ++ ",\n".intercalate (g.rows.map fun r => "  " ++ quote r)
    out := out ++ "]\n\n"
  out := out ++ "/-- 全 100 面（ゲームが読む順）。 -/\n"
  out := out ++ "def all : List (List String) := [\n"
  let names := (List.range levels.size).map fun i => "level" ++ pad3 (i + 1)
  let mut lines : List String := []
  let mut cur := " "
  for nm in names do
    if cur.length + nm.length + 2 > 90 then
      lines := lines ++ [cur]
      cur := " "
    cur := cur ++ " " ++ nm ++ ","
  lines := lines ++ [cur]
  let body := "\n".intercalate lines
  out := out ++ (body.dropEnd 1).toString ++ "]\n\nend Leankoban.Levels\n"
  return out

def parseArgs : List String → Nat × String → Nat × String
  | "--seed" :: v :: rest, (_, o) => parseArgs rest (v.toNat?.getD 20261102, o)
  | "--out" :: v :: rest, (s, _) => parseArgs rest (s, v)
  | _ :: rest, acc => parseArgs rest acc
  | [], acc => acc

def main (args : List String) : IO UInt32 := do
  let (seed, outPath) := parseArgs args (20261102, "Leankoban/Levels/Data.lean")
  let mut rng : Rng := ⟨seed.toUInt64⟩
  let mut seen : Std.HashSet String := {}
  let mut chosen : Array (String × Generated) := #[]
  let t0 ← IO.monoMsNow
  for t in tiers do
    let mut cands : Array Generated := #[]
    let mut tries := 0
    while cands.size < t.candidates && tries < t.attempts do
      tries := tries + 1
      let (r, g) := (tryGenerate t.params).run rng
      rng := g
      if let some c := r then
        let canon := canonical c.rows
        if !seen.contains canon then
          seen := seen.insert canon
          cands := cands.push c
    if cands.size < t.count then
      IO.eprintln s!"段階「{t.name}」: 候補が {cands.size} 面しか作れませんでした（必要 {t.count}）"
      return 1
    -- スコアの高い順に count 面を選び、易しい順に並べ直す
    let best := (cands.qsort (fun a b => a.score > b.score)).extract 0 t.count
    let best := best.qsort (fun a b => a.score < b.score || (a.score == b.score && a.moves < b.moves))
    for c in best do
      chosen := chosen.push (t.name, c)
    let t1 ← IO.monoMsNow
    let pushes := best.map (·.depth)
    IO.eprintln s!"段階「{t.name}」: 試行 {tries} 回・候補 {cands.size} 面 → {t.count} 面採用（押し数 {pushes.toList}）[{(t1 - t0) / 1000} 秒]"
  IO.FS.writeFile outPath (renderData seed chosen)
  IO.eprintln s!"{chosen.size} 面を {outPath} に書き出しました"
  return 0
