int main1(int b,int q){
  int l, d, k;

  l=32;
  d=0;
  k=q;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l == 32;
  loop invariant d == 0;
  loop invariant d <= l;
  loop invariant q == \at(q, Pre);
  loop invariant k % 2 == 0 || k == \at(q, Pre);

  loop invariant b == \at(b, Pre) && q == \at(q, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant k == \at(q, Pre) || k % 2 == 0;
  loop invariant l == 32 && d == 0 && q == \at(q, Pre);
  loop invariant b == \at(b, Pre) && 0 <= d && d <= l;
  loop invariant l == 32 && d == 0 && d <= l && ((k == \at(q, Pre)) || (k % 2 == 0));
  loop invariant (k == \at(q, Pre)) || (k % 2 == 0);
  loop invariant 0 <= d && d <= l;
  loop invariant q == \at(q, Pre) && b == \at(b, Pre);
  loop invariant l == 32 && d == 0 && 0 <= d && d <= l && q == \at(q, Pre) && b == \at(b, Pre);
  loop assigns k;
*/
while (d<l) {
      k = k+3;
      if (k+7<l) {
          k = k+2;
      }
      k = k+k;
  }
/*@
  assert !(d<l) &&
         (l == 32);
*/


}
