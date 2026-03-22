int main1(int a){
  int twd, oal, p1, z;
  twd=a-1;
  oal=0;
  p1=(a%28)+10;
  z=twd;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant z == twd + oal*(oal+1)/2;
  loop invariant oal >= 0;
  loop invariant twd == a - 1;
  loop invariant p1 == ((a % 28) + 10) - (oal * (oal - 1)) / 2;
  loop invariant p1 == (((\at(a, Pre)) % 28) + 10) - oal*(oal-1)/2;
  loop invariant z  == ((\at(a, Pre)) - 1) + oal*(oal+1)/2;
  loop assigns oal, p1, z;
*/
while (p1>oal) {
      p1 -= oal;
      oal++;
      z += oal;
  }
}