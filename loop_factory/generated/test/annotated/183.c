int main1(int d,int g){
  int xshy, b, vl;
  xshy=d+11;
  b=1;
  vl=b;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant g == \at(g, Pre);
  loop invariant b == 1;
  loop invariant vl >= 1;
  loop invariant d >= \at(d, Pre);
  loop invariant xshy == \at(d, Pre) + 11;
  loop assigns vl, d;
*/
while (b+3<=xshy) {
      vl++;
      vl = vl+vl*vl*vl*vl*vl;
      d += b;
  }
}