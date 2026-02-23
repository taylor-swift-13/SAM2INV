int main1(int q){
  int w, k, d, r;

  w=q-7;
  k=w;
  d=w;
  r=q;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant \at(q, Pre) - 7 <= d;
  loop invariant d <= w;
  loop invariant q == \at(q, Pre);
  loop invariant w == \at(q, Pre) - 7;
  loop invariant d >= \at(q, Pre) - 7;
  loop invariant w == q - 7;
  loop invariant w - d >= 0;
  loop invariant q - 7 <= d;
  loop assigns d;
*/
while (d<w) {
      if (d<w) {
          d = d+1;
      }
  }

}
