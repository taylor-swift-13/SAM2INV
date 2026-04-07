int main1(int s){
  int k4n, ae, lrw, z, axz;
  k4n=s;
  ae=0;
  lrw=0;
  z=0;
  axz=s;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k4n == \at(s, Pre);
  loop invariant z == ae * \at(s, Pre);
  loop invariant 2 * lrw == \at(s, Pre) * ae * (ae - 1);
  loop invariant 6 * (axz - \at(s, Pre)) == \at(s, Pre) * ae * (ae + 1) * (ae - 1);
  loop invariant ae >= 0;
  loop invariant (k4n >= 0) ==> (ae <= k4n);
  loop invariant z == ae * s;
  loop invariant lrw == s * ae * (ae - 1) / 2;
  loop invariant axz == \at(s, Pre) + \at(s, Pre) * ae * (ae + 1) * (ae - 1) / 6;
  loop invariant k4n == s;
  loop assigns lrw, ae, axz, z;
*/
while (1) {
      if (!(ae < k4n)) {
          break;
      }
      lrw += z;
      ae = ae + 1;
      axz = axz + lrw;
      z = z + s;
  }
}