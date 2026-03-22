int main1(int n,int v){
  int pc, xy9, q9, wh;
  pc=3;
  xy9=0;
  q9=(n%28)+10;
  wh=pc;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant wh == pc * (xy9 + 1);
  loop invariant q9 + (xy9*(xy9-1))/2 == ((\at(n,Pre) % 28) + 10);
  loop invariant wh == 3 + pc * xy9;
  loop invariant 0 <= xy9;
  loop invariant q9 + (xy9*(xy9 - 1))/2 == (n % 28) + 10;
  loop assigns q9, wh, xy9;
*/
while (q9>xy9) {
      q9 -= xy9;
      wh = wh + pc;
      xy9++;
  }
}