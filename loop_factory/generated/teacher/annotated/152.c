int main1(int m){
  int w, q, x;

  w=38;
  q=0;
  x=q;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant x == 0;
  loop invariant q % 5 == 0;
  loop invariant q >= 0;
  loop invariant q <= w + 4;
  loop invariant m == \at(m, Pre);
  loop invariant 0 <= q;
  loop invariant w == 38;
  loop assigns x, q;
*/
while (q<w) {
      x = x+q;
      x = x-x;
      q = q+5;
  }

}
