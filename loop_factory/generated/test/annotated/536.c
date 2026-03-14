int main1(){
  int ysb3, aka, j1, vpz9, a, libz;
  ysb3=1+14;
  aka=3;
  j1=aka;
  vpz9=ysb3;
  a=0;
  libz=-1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant libz - a == -1;
  loop invariant ysb3 == 1 + 14;
  loop invariant (aka == 3) || (aka == ysb3);
  loop invariant j1 <= 3;
  loop invariant aka % 2 == 1;
  loop invariant vpz9 - ysb3 == a;
  loop invariant a >= 0;
  loop invariant j1 + vpz9 - libz == 19;
  loop assigns a, libz, vpz9, j1, aka;
*/
while (1) {
      if (!(aka<ysb3)) {
          break;
      }
      if (aka%2==0) {
          j1 += 1;
      }
      else {
          vpz9++;
      }
      if (aka%2==1) {
          a++;
      }
      else {
      }
      libz++;
      aka = ysb3;
  }
}