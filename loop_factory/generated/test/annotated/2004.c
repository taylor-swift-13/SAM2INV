int main1(){
  int zfj, mg7z, d0a, o, zkto, nh9;
  zfj=1+3;
  mg7z=0;
  d0a=zfj;
  o=mg7z;
  zkto=13;
  nh9=mg7z;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (mg7z == 0) || (mg7z == zfj);
  loop invariant d0a == zfj;
  loop invariant o == nh9;
  loop invariant (zfj - mg7z) >= 0;
  loop invariant nh9 % 4 == 0;
  loop invariant 0 <= nh9 <= 4 * zfj;
  loop invariant d0a >= 1;
  loop invariant 0 <= mg7z;
  loop invariant (mg7z == 0 ==> nh9 == 0) && (mg7z == zfj ==> nh9 == 4);
  loop assigns d0a, o, nh9, mg7z;
*/
while (mg7z < zfj) {
      d0a = d0a * (1 + ((mg7z++) % 2) * (zkto - 1));
      o += 4;
      nh9 += 4;
      mg7z = zfj;
  }
}