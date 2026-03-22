int main1(int i){
  int oz8i, lzk, msm, s9p0, d, pf, jfz, ip;
  oz8i=64;
  lzk=0;
  msm=i;
  s9p0=oz8i;
  d=4;
  pf=-2;
  jfz=4;
  ip=5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i == \at(i, Pre) + 2*lzk;
  loop invariant 0 <= lzk <= oz8i;
  loop invariant jfz == lzk + 4;
  loop invariant msm >= \at(i, Pre);
  loop invariant msm <= \at(i, Pre) + lzk;
  loop invariant ip >= 5;
  loop invariant ip <= 5 + lzk;
  loop invariant (s9p0 - 64) + (ip - 5) == lzk;
  loop invariant s9p0 <= oz8i + lzk;
  loop assigns lzk, msm, s9p0, ip, d, pf, jfz, i;
*/
while (1) {
      if (!(lzk < oz8i)) {
          break;
      }
      lzk++;
      if ((lzk % i) == 1) {
          msm = msm + 1;
      }
      if ((lzk % i) == 0) {
          s9p0 += 1;
      }
      else {
          ip++;
      }
      d = d + msm;
      pf += s9p0;
      d++;
      jfz = jfz + 1;
      i = (2)+(i);
      pf += d;
  }
}