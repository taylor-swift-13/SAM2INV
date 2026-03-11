int main1(int a,int m){
  int r, k, v;

  r=10;
  k=3;
  v=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant a == \at(a, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant r == 10;
  loop invariant 0 <= v <= 64;
  loop invariant (k - 3) % 5 == 0;
  loop invariant k >= 3;
  loop invariant ((k - 3) % 5) == 0;
  loop invariant k <= r;
  loop invariant 0 <= v && v <= 64;
  loop invariant a == \at(a, Pre) && m == \at(m, Pre) && r == 10;
  loop invariant k <= r && 0 <= v && v <= 64;
  loop invariant k % 5 == 3;
  loop invariant v >= 0;
  loop invariant v <= 64;
  loop invariant k % 5 == 3 && k <= r && 0 <= v && v <= 64;
  loop invariant a == \at(a, Pre) && m == \at(m, Pre);

  loop assigns v, k;
*/
while (k<=r-5) {
      v = v%9;
      v = v*v;
      k = k+5;
  }
/*@
  assert !(k<=r-5) &&
         (a == \at(a, Pre));
*/


}
