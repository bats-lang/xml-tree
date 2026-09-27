#include "share/atspre_staload.hats"
#use array as A
#use xml-tree as X

(* The first byte of a text node, read from the document at the node's
   offset. A text node's span [off, off + k) is proven inside the
   document, with k > 0, so the read needs no check. *)
#pub fn text_first_byte {l:agz}{n:pos}
  (data: !$A.borrow(byte, l, n), len: int n, node: !$X.xml_node(n, 1)): int

implement text_first_byte (data, len, node) =
  case+ node of
  | $X.xml_text(off, _) => byte2int0($A.read<byte>(data, off))
  | $X.xml_element(_, _, _, _) => ~1
