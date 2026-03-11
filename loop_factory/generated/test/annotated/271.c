int main1(int g,int z){
  int r, d22x, v5, rm;
  r=g+15;
  d22x=r;
  v5=0;
  rm=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r == g + 15;
  loop invariant d22x <= r;
  loop invariant rm == 1 || rm == -1;
  loop invariant 0 <= v5;
  loop invariant v5 <= 9;
  loop assigns d22x, v5, rm;
*/
while (d22x<r) {
      if (v5>=9) {
          rm = -1;
      }
      if (!(v5>0)) {
          rm = 1;
      }
      v5 = v5 + rm;
      d22x += 1;
  }
}