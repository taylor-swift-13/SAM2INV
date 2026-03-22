int main1(int f,int s){
  int pyz, ddg, vz, x7;
  pyz=s+8;
  ddg=pyz;
  vz=ddg;
  x7=7;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant pyz == s + 8;
  loop invariant x7 >= 7;
  loop invariant pyz == \at(s, Pre) + 8;
  loop invariant (ddg == pyz) || (ddg == 5);
  loop assigns ddg, vz, x7;
*/
while (1) {
      if (!(ddg>5)) {
          break;
      }
      x7++;
      vz = x7*x7;
      ddg = 5;
  }
}