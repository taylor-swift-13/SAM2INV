int main1(int m,int q){
  int b, l, v;

  b=m;
  l=0;
  v=2;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l == 0;
  loop invariant b == m;
  loop invariant v >= 2;
  loop invariant (v - 2) % 3 == 0;
  loop invariant m == \at(m, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant v % 3 == 2;
  loop assigns v;
*/
while (1) {
      v = v+3;
      if (q<l+2) {
          v = v+l;
      }
  }

}
