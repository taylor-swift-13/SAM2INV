int main1(int y){
  int dj, ja, m, ppy, tey;
  dj=10;
  ja=0;
  m=0;
  ppy=y;
  tey=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m == -ja;
  loop invariant tey == -ja*(ja + 1)/2;
  loop invariant 0 <= ja;
  loop invariant ja <= dj;
  loop invariant ppy == y + dj*ja - ja*(ja+1)/2;
  loop invariant ppy == \at(y, Pre) + dj * ja - ja * (ja + 1) / 2;
  loop assigns m, ja, ppy, tey;
*/
while (ja < dj) {
      m -= 1;
      ja += 1;
      ppy = ppy+dj-ja;
      tey = tey + m;
  }
}