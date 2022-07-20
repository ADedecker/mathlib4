import Lean

open Lean Meta

initialize zifyExt : SimpExtension ←
  registerSimpAttr `zify_set (extName := `Tactic.Zify.zifyExt) $
    "TODO"

namespace Attr
/-- TODO -/
syntax (name := zifyAttr) "zify_simps" : attr
end Attr

initialize registerBuiltinAttribute {
  name := `zifyAttr
  descr := "attribute for zify"
  add := fun decl _stx kind => MetaM.run' $
          addSimpTheorem zifyExt decl (post := true) (inv := false) kind (eval_prio default)
}
