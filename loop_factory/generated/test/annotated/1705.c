int main1(int v){
  int r, x30, a, ij, zev;
  r=31;
  x30=0;
  a=0;
  ij=x30;
  zev=r;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ij == a*(a+3)/2;
  loop invariant 0 <= a;
  loop invariant a <= r;
  loop invariant (a == 0) ==> (zev == r);
  loop invariant (a > 0) ==> (zev == 1);
  loop assigns a, ij, zev;
*/
while (a<r) {
      a++;
      if (!(!(a<=zev))) {
          zev = a;
      }
      ij = ij + a;
      ij++;
  }
}