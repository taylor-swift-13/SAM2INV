int main1(){
  int uh4, ck2q, y6y2, jy, sd, qo0, u09, q;
  uh4=(1%37)+12;
  ck2q=0;
  y6y2=0;
  jy=0;
  sd=2;
  qo0=0;
  u09=0;
  q=5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant jy == y6y2*(y6y2-1)/2;
  loop invariant sd == 2 + (y6y2*(y6y2+3))/2;
  loop invariant 0 <= y6y2;
  loop invariant y6y2 <= uh4;
  loop invariant (y6y2 >= 1) ==> (q == sd + qo0 + u09 - 1);
  loop invariant 0 <= qo0;
  loop invariant 0 <= q;
  loop assigns jy, y6y2, sd, qo0, q;
*/
while (y6y2<uh4) {
      jy += y6y2;
      y6y2++;
      sd += y6y2;
      qo0 = qo0 + jy;
      q = sd+qo0+u09;
      sd += 1;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= u09;
  loop invariant 0 <= qo0;
  loop invariant 0 <= uh4;
  loop invariant 0 <= jy;
  loop invariant q >= 5;
  loop assigns qo0, jy, u09, q, uh4;
*/
while (jy<=y6y2-1) {
      qo0 = qo0 + jy;
      uh4 = uh4 + ck2q;
      jy += 1;
      u09 = u09 + 1;
      q += u09;
  }
}