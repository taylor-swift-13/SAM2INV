int main1(){
  int oei, f0, d4, f, m0, avpk, u;
  oei=61;
  f0=0;
  d4=-4;
  f=f0;
  m0=f0;
  avpk=f0;
  u=2;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant avpk == f0 + (f0/2);
  loop invariant (f0 <= oei/2) ==> (f == f0);
  loop invariant (f0 > oei/2) ==> (f == oei/2);
  loop invariant 0 <= f0 <= oei;
  loop invariant (f0 <= oei/2) ==> (d4 == -4 + 2*f0);
  loop invariant (f0 >= oei/2) ==> (d4 == f0 + 26);
  loop invariant (f0 > oei/2)  ==> (d4 == -4 + f0 + oei/2);
  loop invariant 0 <= m0;
  loop assigns avpk, d4, f, f0, m0, u;
*/
while (1) {
      if (!(f0 < oei)) {
          break;
      }
      if (!(!(f0 < (oei/2)))) {
          d4 += 2;
          f = f + 1;
      }
      else {
          d4 += 1;
      }
      f0 = f0 + 1;
      if ((f0%2)==0) {
          avpk += 1;
      }
      m0 += f;
      u += d4;
      m0 = m0 + 3;
      avpk += 1;
  }
}