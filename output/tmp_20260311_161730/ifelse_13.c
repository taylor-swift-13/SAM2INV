int main1(){
  int p6l, n80, p, vj;
  p6l=180;
  n80=3;
  p=1;
  vj=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant n80 >= 3;
  loop invariant n80 <= p6l;
  loop invariant 1 <= p;
  loop invariant p <= 11;
  loop invariant (vj == 1) || (vj == -1);
  loop invariant ((p + n80) % 2) == 0;
  loop invariant (p - n80) <= -2;
  loop assigns n80, p, vj;
*/
while (n80<p6l) {
      if (!(p<11)) {
          vj = -1;
      }
      if (p<=1) {
          vj = 1;
      }
      n80++;
      p += vj;
  }
/*@
  assert !(n80<p6l) &&
         (n80 >= 3);
*/

}