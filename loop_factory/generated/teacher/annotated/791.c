int main1(int a,int m){
  int z, p, v, k;

  z=m+17;
  p=2;
  v=0;
  k=4;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z == m + 17;
  loop invariant m == \at(m, Pre);
  loop invariant a == \at(a, Pre);
  loop invariant v >= 0;
  loop invariant k >= 4;
  loop invariant z == \at(m, Pre) + 17;
  loop invariant 0 <= v;
  loop invariant z < 0 || v <= z;

  loop invariant (v < z/2) ==> (k == 4);

  loop invariant (k % 2) == 0;

  loop invariant v < z/2 ==> k == 4;
  loop assigns k, v;
*/
while (v<z) {
      if (v>=z/2) {
          k = k+2;
      }
      v = v+1;
  }

}
