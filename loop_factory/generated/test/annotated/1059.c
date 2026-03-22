int main1(int d,int l){
  int x4, e2, ln, s5f, bbn, ub;
  x4=16;
  e2=4;
  ln=1;
  s5f=0;
  bbn=-3;
  ub=8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ln == 1 + s5f * d;
  loop invariant bbn == -3 + s5f;
  loop invariant ub == 8 + ((s5f + 1) / 2);
  loop invariant 0 <= s5f <= x4;
  loop invariant x4 == 16;
  loop invariant l == \at(l, Pre);
  loop assigns s5f, ln, bbn, ub;
*/
while (1) {
      if (!(s5f<x4)) {
          break;
      }
      s5f = s5f + 1;
      ln += d;
      bbn = bbn + 1;
      ub = ub+(s5f%2);
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant e2 >= 4;
  loop invariant ub >= 8;
  loop invariant l >= \at(l, Pre);
  loop invariant s5f >= 0;
  loop invariant (e2 - 4) % 16 == 0;
  loop invariant ln == 1 + d * s5f;
  loop assigns ub, e2, l, x4;
*/
while (ln+1<=x4) {
      ub = ub + e2;
      e2 += s5f;
      l = l+(ub%2);
      x4 = (ln+1)-1;
  }
}