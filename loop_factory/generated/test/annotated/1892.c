int main1(int m){
  int e5, ku4, jj, lq, xs, yws, xa, j5u;
  e5=m+20;
  ku4=0;
  jj=1;
  lq=-1;
  xs=e5;
  yws=m;
  xa=m+3;
  j5u=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j5u == ku4;
  loop invariant xs == e5 + 2 * j5u;
  loop invariant lq <= ku4;
  loop invariant (ku4 == 0) ==> (lq == -1);
  loop invariant ((lq == -1) || (lq % 2 == 0));
  loop invariant 0 <= j5u;
  loop invariant e5 == \at(m,Pre) + 20;
  loop assigns m, xs, xa, yws, j5u, ku4, lq, jj;
*/
while (ku4 < e5) {
      if (!(!(((ku4 % 2) == 0)))) {
          lq = ku4;
          ku4 = ku4 + 1;
      }
      else {
          jj = ku4;
          ku4 = ku4 + 1;
      }
      if (xs+2<e5) {
          xs = xs + xa;
      }
      m = m + lq;
      j5u = j5u + 1;
      xa = xa + lq;
      xs += 2;
      yws = yws + xs;
  }
}