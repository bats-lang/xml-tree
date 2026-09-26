#include "share/atspre_staload.hats"
#use array as A
#use xml-tree as X

(* The first byte of a text node, read from the document at the node's
   offset. The offset is indexed, so after checking it against the
   buffer the read needs no cast; without the check it is rejected. *)
#pub fn text_first_byte {l:agz}{n:pos}
  (data: !$A.borrow(byte, l, n), len: int n, node: !$X.xml_node(1)): int

implement text_first_byte (data, len, node) =
  case+ node of
  | $X.xml_text(off, _) =>
      if off < 0 then ~1 else if off >= len then ~1 else byte2int0($A.read<byte>(data, off))
  | $X.xml_element(_, _, _, _) => ~1
