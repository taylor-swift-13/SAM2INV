int main1(int e){
  int to, oi, bj, ks;
  to=e;
  oi=5;
  bj=0;
  ks=e;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant to == \at(e, Pre);
  loop invariant ks == \at(e, Pre) + 2*(oi - 5);
  loop invariant bj == oi*oi - 2*oi - 15;
  loop invariant e == \at(e, Pre) + (oi*oi + oi - 30)/2;
  loop invariant 5 <= oi;
  loop assigns bj, oi, ks, e;
*/
while (oi<=to) {
      bj = bj+2*oi-1;
      oi = oi + 1;
      ks += 2;
      e += oi;
  }
}