int main1(int c,int p){
  int dj, k, aw, uqq;
  dj=p;
  k=0;
  aw=3;
  uqq=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant aw == 3 + c * uqq;
  loop invariant dj == \at(p, Pre);
  loop invariant uqq >= 0;
  loop assigns uqq, aw;
*/
while (1) {
      if (!(uqq<dj)) {
          break;
      }
      uqq++;
      aw = aw + c;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant dj == \at(p, Pre) + c * k;
  loop invariant 0 <= k <= uqq;
  loop invariant dj == p + k * c;
  loop assigns dj, k;
*/
while (k<uqq) {
      dj = dj + c;
      k += 1;
  }
}