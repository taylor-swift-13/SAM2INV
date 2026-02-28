int main1(int b,int m){
  int r, g, v;

  r=54;
  g=0;
  v=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= g && g <= r && r == 54;
  loop invariant v >= \at(m,Pre) && v <= \at(m,Pre) + g*(g-1)/2 && m == \at(m,Pre);
  loop invariant r == 54;
  loop invariant m == \at(m, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant 0 <= g;
  loop invariant g <= r;
  loop invariant v >= m;
  loop invariant v >= \at(m, Pre);
  loop invariant v <= \at(m, Pre) + (g*(g-1))/2;
  loop invariant v <= \at(m, Pre) + g*(g-1)/2;
  loop invariant v <= m + g*(r-1);
  loop assigns v, g;
*/
while (g<r) {
      if (v+7<r) {
          v = v+g;
      }
      g = g+1;
  }

}
