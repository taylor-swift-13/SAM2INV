int main1(int a,int b,int q){
  int r, z, v, m, g, l;

  r=q;
  z=0;
  v=8;
  m=b;
  g=0;
  l=q;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant g == 0;
  loop invariant r == q;

  loop invariant (\at(b, Pre) < 0) ==> (m == \at(b, Pre));
  loop invariant v >= 8;
  loop invariant r == \at(q, Pre);
  loop invariant v % 2 == 0;
  loop invariant m <= \at(b,Pre);
  loop invariant a == \at(a, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant q == \at(q, Pre);
  loop assigns m, v;
*/
while (1) {
      if (v>=r) {
          break;
      }
      if (g<=m) {
          m = g;
      }
      v = v+1;
      v = v*2;
  }

}
