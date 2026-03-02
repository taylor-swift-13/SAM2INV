int main1(int m,int q){
  int h, k, v;

  h=q;
  k=h;
  v=h;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h == \at(q, Pre);
  loop invariant k <= \at(q, Pre);
  loop invariant (v == \at(q, Pre)) || (-3 <= v && v <= 3);
  loop invariant q == \at(q, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant k >= 0 || k == \at(q, Pre);
  loop invariant v == \at(q, Pre) || (-3 <= v && v <= 3);
  loop invariant (\at(q, Pre) >= 0) ==> k >= 0;
  loop invariant (v == h) || (0 <= v && v <= 3);
  loop invariant (v == \at(q, Pre) || (-3 <= v && v <= 3));
  loop invariant h == \at(q, Pre) && q == \at(q, Pre) && k <= \at(q, Pre);
  loop invariant (v == \at(q, Pre) || (v >= -3 && v <= 3));
  loop invariant (v == \at(q, Pre) || (0 <= v && v < 4));
  loop invariant h == \at(q, Pre) && k <= \at(q, Pre);
  loop invariant q == \at(q, Pre) && m == \at(m, Pre);
  loop invariant v == \at(q, Pre) || (0 <= v && v <= 3);
  loop assigns k, v;
*/
while (k-1>=0) {
      if (v+6<h) {
          v = v%4;
      }
      k = k-1;
  }

}
