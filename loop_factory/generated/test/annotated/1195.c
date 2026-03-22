int main1(){
  int od, hs, ub, c, bw, t9a;
  od=29;
  hs=1;
  ub=od;
  c=4;
  bw=od;
  t9a=hs;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= t9a <= 6;
  loop invariant ub + c <= 33;
  loop invariant 0 <= bw <= od;
  loop invariant 0 <= ub;
  loop invariant 0 <= c;
  loop assigns ub, c, t9a, bw;
*/
while (ub!=c) {
      if (ub>c) {
          ub = ub - c;
          t9a = t9a + bw;
      }
      else {
          c = c - ub;
          bw += t9a;
      }
      bw = bw*bw+bw;
      bw = bw%4;
      t9a = t9a%7;
  }
}