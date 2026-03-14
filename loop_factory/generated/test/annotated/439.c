int main1(){
  int n83j, l, l6, qmv, pn, zz;
  n83j=1+3;
  l=-1;
  l6=0;
  qmv=n83j;
  pn=n83j;
  zz=l;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant zz == l + (n83j - l) * (l6 / 4);
  loop invariant (l6 % 4) == 0;
  loop invariant qmv == n83j - (l6 % 4);
  loop invariant zz == -1 + (l6 / 4) * (n83j - l);
  loop invariant 0 <= l6 <= n83j;
  loop assigns qmv, zz, l6;
*/
while (1) {
      if (!(l6<n83j)) {
          break;
      }
      qmv = n83j-l6;
      zz = zz+n83j-l;
      l6 += 4;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant qmv <= pn;
  loop invariant qmv >= 0;
  loop assigns qmv;
*/
while (1) {
      if (!(qmv+1<=pn)) {
          break;
      }
      qmv++;
  }
}