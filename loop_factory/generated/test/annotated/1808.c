int main1(){
  int a3y, za, d, orb, r;
  a3y=0;
  za=0;
  d=(1%28)+10;
  orb=0;
  r=a3y;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant d == 11 - za*(za - 1)/2;
  loop invariant r == 11*za - za*(za + 1)*(za - 1)/6;
  loop invariant za >= 0;
  loop invariant orb >= 0;
  loop invariant r >= 0;
  loop invariant d >= 0;
  loop assigns d, r, za, orb;
*/
while (1) {
      if (!(d>za)) {
          break;
      }
      d = d - za;
      r += d;
      za = (1)+(za);
      orb = orb+(d%5);
  }
}