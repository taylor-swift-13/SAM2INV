int main1(int g,int e){
  int nln, jd, liy;
  nln=161;
  jd=-9060;
  liy=-1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ((liy + 1) % 3) == 0;
  loop invariant nln == 161;
  loop invariant e == \at(e, Pre);
  loop invariant g == \at(g, Pre) + 163 * ((liy + 1) / 3);
  loop invariant jd == -9060 + ((liy + 1) * (liy - 10)) / 6;
  loop assigns g, jd, liy;
*/
while (jd+8<0) {
      jd = jd+liy-3;
      liy = liy + 3;
      g += nln;
      g += 2;
  }
}