int main1(){
  int bnu, q6l, w0u, c, at;
  bnu=1*2;
  q6l=1;
  w0u=q6l;
  c=bnu;
  at=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant q6l == 1;
  loop invariant ( (at == 0 && c == 2 && w0u == 1 && bnu == 2 && q6l == 1) ||
                    (at == 2 && c == 0 && w0u == 4 && bnu == 5 && q6l == 1) );
  loop invariant (bnu == 2) ==> (at == 0 && w0u == 1 && c == 2);
  loop invariant at >= 0;
  loop invariant c >= 0;
  loop invariant bnu == q6l + 1 || bnu == q6l + 4;
  loop invariant w0u == q6l || w0u == q6l * 4;
  loop assigns at, c, w0u, bnu;
*/
while (1) {
      if (!(q6l+5<=bnu)) {
          break;
      }
      at = at + bnu;
      c = c/4;
      w0u = w0u*4;
      bnu = (q6l+5)-1;
  }
}