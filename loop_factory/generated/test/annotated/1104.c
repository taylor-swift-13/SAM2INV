int main1(int d){
  int iiiz, i, k2, k5q, q9q, g;
  iiiz=d;
  i=0;
  k2=0;
  k5q=0;
  q9q=i;
  g=4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k5q == k2*(k2-1)/2;
  loop invariant q9q == 3*k2;
  loop invariant g == 4 + 3*(k2*(k2+1)/2);
  loop invariant k2 >= 0;
  loop invariant iiiz == \at(d,Pre);
  loop invariant d == iiiz + k2*(k2+1)/2;
  loop invariant (iiiz >= 0) ==> (k2 <= iiiz);
  loop assigns d, g, k2, k5q, q9q;
*/
while (k2<=iiiz-1) {
      k5q = k5q + k2;
      k2++;
      q9q = q9q + 3;
      d = d + k2;
      g = g + q9q;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k2 >= 0;
  loop invariant iiiz == \at(d,Pre);
  loop assigns k2;
*/
for (; k2-1>=0; k2 -= 1) {
  }
}