int main1(int y,int x){
  int e5, m, ju, sflb, les, pz, gt;
  e5=x;
  m=0;
  ju=y;
  sflb=0;
  les=m;
  pz=e5;
  gt=6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m == 0;
  loop invariant gt == 6;
  loop invariant (sflb == ju * m);
  loop invariant ju == \at(y, Pre);
  loop invariant (e5 == \at(x, Pre) || e5 == m);
  loop invariant ju == y;
  loop assigns gt, sflb, e5;
*/
while (1) {
      if (!(m+1<=e5)) {
          break;
      }
      gt = gt + m;
      sflb = sflb+ju*m;
      e5 = (m+1)-1;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (les == 0);
  loop invariant (pz >= x);
  loop invariant pz >= \at(x, Pre);
  loop invariant gt == 6 + ((pz - \at(x, Pre)) * y);
  loop assigns gt, pz, ju;
*/
while (1) {
      if (!(pz<=les-1)) {
          break;
      }
      gt = gt + y;
      pz = pz + 1;
      ju = ju + gt;
  }
}