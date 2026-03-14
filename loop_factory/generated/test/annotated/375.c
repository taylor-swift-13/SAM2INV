int main1(){
  int j, vcb, gn2a, p9x, xp, yz5, fsk;
  j=176;
  vcb=0;
  gn2a=0;
  p9x=(1%28)+10;
  xp=j;
  yz5=vcb;
  fsk=20;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant gn2a >= 0;
  loop invariant p9x == 11 - gn2a*(gn2a - 1)/2;
  loop invariant p9x >= 0;
  loop invariant j == 176;
  loop invariant vcb == 0;
  loop invariant fsk == 20;
  loop invariant gn2a <= 5;
  loop invariant 1 <= p9x;
  loop invariant xp >= 176;
  loop assigns fsk, gn2a, p9x, xp;
*/
while (p9x>gn2a) {
      p9x -= gn2a;
      fsk = fsk + vcb;
      gn2a = (1)+(gn2a);
      xp = xp+(p9x%2);
      xp = xp*3;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant gn2a >= 0;
  loop invariant yz5 == vcb;
  loop invariant p9x >= 0;
  loop invariant j == 176;
  loop invariant vcb >= 0;
  loop assigns gn2a, p9x, yz5, vcb;
*/
while (gn2a>0) {
      p9x = p9x+1*1;
      yz5 = yz5+1*1;
      vcb = vcb+1*1;
      gn2a--;
      p9x = p9x*3;
  }
}