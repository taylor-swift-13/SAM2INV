int main1(int m,int l){
  int z, ha, d, az, wr;
  z=24;
  ha=-2;
  d=-3;
  az=20;
  wr=m*3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant az == 20 + 6*(wr - 3*\at(m,Pre));
  loop invariant d == -3 + 3*(wr - 3*\at(m,Pre))*(wr - 3*\at(m,Pre)) + 17*(wr - 3*\at(m,Pre));
  loop invariant ha == ((wr - 3*\at(m,Pre)) * (wr - 3*\at(m,Pre)) * (wr - 3*\at(m,Pre)))
                          + 7 * ((wr - 3*\at(m,Pre)) * (wr - 3*\at(m,Pre)))
                          - 11 * (wr - 3*\at(m,Pre)) - 2;
  loop invariant z == 24;
  loop invariant ha == (wr - 3*\at(m, Pre))*(wr - 3*\at(m, Pre))*(wr - 3*\at(m, Pre)) + 7*(wr - 3*\at(m, Pre))*(wr - 3*\at(m, Pre)) - 11*(wr - 3*\at(m, Pre)) - 2;
  loop invariant l == \at(l, Pre) + 3*(wr - 3*\at(m, Pre))*(wr - 3*\at(m, Pre)) + 23*(wr - 3*\at(m, Pre));
  loop assigns ha, d, az, wr, m, l;
*/
while (wr<=z) {
      ha += d;
      d = d + az;
      wr += 1;
      az += 6;
      m = m+(az%6);
      l = l + az;
  }
}