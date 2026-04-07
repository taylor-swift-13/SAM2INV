int main1(int j){
  int h3, q6, l08t, z2, z, hw, hi, sd, fx;
  h3=j+21;
  q6=h3;
  l08t=-4;
  z2=j;
  z=j;
  hw=j;
  hi=1;
  sd=h3;
  fx=q6;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant h3 == \at(j, Pre) + 21;
  loop invariant j == \at(j, Pre) + 3 * (sd - (\at(j, Pre) + 21));
  loop invariant (q6 == h3) || (q6 == 0);
  loop invariant z2 >= \at(j, Pre);
  loop invariant z >= \at(j, Pre);
  loop invariant l08t >= -4;
  loop invariant sd >= \at(j, Pre) + 21;
  loop assigns fx, hi, hw, j, l08t, q6, sd, z, z2;
*/
while (1) {
      if (!(q6>=1)) {
          break;
      }
      if (q6%5==2) {
          l08t++;
      }
      else {
          z2++;
      }
      if (q6%5==3) {
          z += 1;
      }
      else {
      }
      hi = (hi+l08t)%6;
      j = j + 3;
      hw = (hw+z2)%2;
      fx += z;
      sd += 1;
      q6 = 0;
  }
}