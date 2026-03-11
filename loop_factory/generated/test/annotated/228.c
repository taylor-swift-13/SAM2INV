int main1(int l,int z){
  int gw, s9, e2, vf, h7, d5;
  gw=z;
  s9=gw+3;
  e2=0;
  vf=0;
  h7=l;
  d5=gw;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant d5 == \at(z, Pre) + 3 * vf;
  loop invariant gw == \at(z, Pre);
  loop invariant e2 == vf * l;
  loop invariant vf >= 0;
  loop invariant 2 * h7 == 2 * l + l * vf * (vf + 1);
  loop invariant 2*(h7 - \at(l,Pre)) == l * vf * (vf + 1);
  loop invariant (\at(z,Pre) >= 0) ==> (vf <= gw);
  loop assigns vf, e2, h7, d5;
*/
while (vf<gw) {
      vf++;
      e2 += l;
      h7 = h7 + e2;
      d5 = d5 + 3;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 6 * vf - 3 * gw == 2 * d5 - 5 * \at(z, Pre);
  loop invariant 3 * s9 - 3 * l * vf == 3 * (\at(z, Pre) + 3) - l * (d5 - \at(z, Pre));
  loop invariant vf >= \at(z, Pre);
  loop assigns gw, vf, s9, e2;
*/
while (vf<d5) {
      gw += 2;
      vf++;
      s9 += l;
      e2 += s9;
  }
}