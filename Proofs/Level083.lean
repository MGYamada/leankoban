import Leankoban.Soundness
import Leankoban.Levels.Data

/-!
# 面 83 の可解性証明

箱 4 個。証明書の解は押し 38 回・手数 118（押し数最小の解）。

この証明が依存するのは、ルール仕様 `Leankoban.Spec`、実行系 `Leankoban.Engine`、
健全性定理 `Leankoban.Soundness.certify`、そしてカーネルによる計算だけで、公理は一切使わない。
（`lake exe genproofs` が自動生成。手で編集しない。）
-/

namespace Leankoban.Proofs.Level083

open Leankoban

/-- ゲームが読み込む盤面 `Levels.level083` を、ここに絵として展開したもの。 -/
theorem board_eq : Levels.level083 = [
    "   #######",
    "  ##     #",
    "###    . #",
    "#     #  #",
    "#    $@$ #",
    "#  #######",
    "# .  $ $ #",
    "#     .  #",
    "#   ##  .#",
    "##########"] := rfl

/-- 解の手順（LURD 記法。小文字は歩く手、大文字は箱を押す手）。 -/
def solution : String :=
    "LLLullddrUluRRdrUluRRRurrdddLLLLLulDDDrdrrruLLLdrrrrruLLLLdldlluRRlluurD\
    lddrruRuLdrRlldlluRRurrdRullldRurrrDldRuullldR"

/-- **面 83 はクリア可能である。** -/
theorem solvable :
    WellFormed (Level.ofRows Levels.level083) ∧ Solvable (Level.ofRows Levels.level083) :=
  Soundness.certify Levels.level083 solution (by decide +kernel)

end Leankoban.Proofs.Level083
