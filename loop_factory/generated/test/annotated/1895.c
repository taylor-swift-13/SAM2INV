int main1(){
  int xp, fo8v, s65, ld, iyb, hy, m5, ir5;
  xp=1;
  fo8v=4;
  s65=xp;
  ld=6;
  iyb=-5;
  hy=fo8v;
  m5=3;
  ir5=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant xp <= fo8v;
  loop invariant s65 >= 1;
  loop invariant hy >= 4;
  loop invariant ir5 % 3 == 0;
  loop invariant (1 <= xp);
  loop invariant iyb == -5;
  loop invariant ir5 >= 0;
  loop invariant 0 <= fo8v;
  loop invariant hy % fo8v == 0;
  loop invariant m5 <= ld + iyb + hy;
  loop assigns s65, ld, m5, iyb, ir5, hy, xp;
*/
while (fo8v+1<=xp) {
      if (!(!(fo8v<xp/2))) {
          s65 = s65 + 1;
      }
      else {
          s65 += ld;
      }
      if ((fo8v%2)==0) {
          ld = hy-ld;
      }
      m5 += s65;
      iyb = iyb+(fo8v%2);
      ir5 = ir5 + 3;
      m5 = ld+iyb+hy;
      ld++;
      hy = hy + fo8v;
      xp = (fo8v+1)-1;
  }
}