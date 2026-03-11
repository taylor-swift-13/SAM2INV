int main1(int d,int g){
  int xshy, b, vl;
  xshy=d+11;
  b=xshy;
  vl=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b <= xshy;
  loop invariant g == \at(g, Pre);
  loop invariant vl == 0;
  loop invariant d == \at(d, Pre) + 2 * \at(g, Pre) * (xshy - b);
  loop invariant xshy == \at(d, Pre) + 11;
  loop assigns d, g, b;
*/
for (; b-1>=0; b = b - 1) {
      d = d + g;
      g += vl;
      d = d + g;
  }
}