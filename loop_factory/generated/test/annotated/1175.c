int main1(int h){
  int jp, v1y, iy4q, un23;
  jp=(h%60)+60;
  v1y=(h%9)+2;
  iy4q=0;
  un23=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h >= \at(h, Pre);
  loop invariant iy4q >= 0;
  loop invariant v1y == (\at(h, Pre) % 9) + 2;
  loop invariant jp == (\at(h, Pre) % 60) + 60;
  loop invariant v1y * iy4q + un23 <= jp;
  loop invariant 0 <= un23;
  loop assigns h, iy4q, un23;
*/
while (jp>v1y*iy4q+un23) {
      if (un23==v1y-1) {
          un23 = 0;
          iy4q++;
      }
      else {
          un23++;
      }
      h = h+(iy4q%5);
  }
}