#include "share/atspre_staload.hats"
#use array as A
#use xml-tree as X

(* The byte just past a text node's span may be past the end of the
   document: reading it must not type-check. *)
#pub fn text_past_end {l:agz}{n:pos}
  (data: !$A.borrow(byte, l, n), len: int n, node: !$X.xml_node(n, 1)): int

implement text_past_end (data, len, node) =
  case+ node of
  | $X.xml_text(off, k) => byte2int0($A.read<byte>(data, off + k))
  | $X.xml_element(_, _, _, _) => ~1
