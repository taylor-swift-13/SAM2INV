int main1(int m,int p){
  int e, g, v;

  e=(p%15)+14;
  g=0;
  v=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant e == (\at(p, Pre) % 15) + 14;
  loop invariant p == \at(p, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant v >= \at(p, Pre);
  loop invariant e == \at(p, Pre) % 15 + 14 && p == \at(p, Pre) && m == \at(m, Pre);

  loop invariant e == \at(p, Pre) % 15 + 14;
  loop invariant 0 <= e && e <= 28;
  loop invariant e == (\at(p, Pre) % 15) + 14 && 0 <= e && e <= 28;
  loop invariant v == \at(p, Pre) || v >= 0;
  loop invariant e == \at(p,Pre) % 15 + 14;
  loop invariant v >= \at(p,Pre);
  loop invariant p == \at(p,Pre);
  loop invariant m == \at(m,Pre);
  loop assigns v;
*/
while (1) {
      v = v+2;
      if (v*v<=e+3) {
          v = v*v+v;
      }
      v = v*v+v;
  }

}
