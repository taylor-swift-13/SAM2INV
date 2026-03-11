int main1(int m,int n){
  int h, j, v, k;

  h=(m%24)+16;
  j=1;
  v=j;
  k=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h == \at(m, Pre) % 24 + 16;
  loop invariant j >= 1;
  loop invariant v >= 1;
  loop invariant v >= j;
  loop invariant v <= 4 * j * j;

  loop invariant (\at(m, Pre) % 24) + 16 == h
                   && m == \at(m, Pre)
                   && n == \at(n, Pre)
                   && j >= 1
                   && v >= 1;
  loop invariant (j % 3 == 0) ==> (v % 4 == 0 && k % 4 == 0);
  loop invariant h == (\at(m, Pre) % 24) + 16;
  loop invariant m == \at(m, Pre) && n == \at(n, Pre);
  loop invariant (v - 1) % 7 == 0;
  loop invariant m == \at(m, Pre) && h == \at(m, Pre) % 24 + 16 && n == \at(n, Pre);
  loop invariant j >= 1 && v >= 1;
  loop invariant m == \at(m, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant v == 1 || v % 4 == 0;
  loop invariant k == \at(m, Pre) || k % 4 == 0;
  loop invariant m == \at(m, Pre) && n == \at(n, Pre) && h == (\at(m, Pre) % 24) + 16;
  loop invariant (j == 1 || j % 3 == 0) && (v == 1 || v % 4 == 0) && (k == \at(m, Pre) || k % 4 == 0);
  loop invariant ((j==1 && v==1 && k==m) || (j>1 && v % 4 == 0 && k % 4 == 0));
  loop invariant h == \at(m, Pre) % 24 + 16 && m == \at(m, Pre) && n == \at(n, Pre) && j >= 1;
  loop invariant h == \at(m, Pre) % 24 + 16 && m == \at(m, Pre) && n == \at(n, Pre);

  loop assigns v, k, j;
*/
while (j<h) {
      v = v*4+4;
      k = k*v+4;
      j = j*3;
  }
/*@
  assert !(j<h) &&
         (h == \at(m, Pre) % 24 + 16);
*/


}
