int main1(int t){
  int l6, iy, r2, whk3;
  l6=t+20;
  iy=-2;
  r2=0;
  whk3=iy;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant whk3 == iy + r2;
  loop invariant r2 >= 0;
  loop invariant whk3 == r2 - 2;
  loop invariant t == \at(t, Pre) + r2*(l6 - iy) - 2*r2 + (r2*(r2 + 1))/2;
  loop invariant l6 == \at(t, Pre) + 20;
  loop invariant t == \at(t, Pre) + r2*(l6 + 1) + r2*(r2 - 1)/2;
  loop invariant t == \at(t, Pre) + r2*(l6+2) + (r2*r2 - 3*r2)/2;
  loop assigns t, r2, whk3;
*/
while (r2<=l6-1) {
      whk3 = whk3 + 1;
      t = t+l6-iy;
      r2 += 1;
      t = t + whk3;
  }
}