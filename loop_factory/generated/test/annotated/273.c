int main1(int c,int z){
  int r4, n, wh, dq3, o, s8;
  r4=79;
  n=0;
  wh=31;
  dq3=0;
  o=1;
  s8=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant o == n + 1;
  loop invariant wh + dq3 == 31;
  loop invariant 0 <= wh <= 31;
  loop invariant 0 <= n <= r4;
  loop invariant 1 <= o <= 80;
  loop invariant s8 >= 0;
  loop assigns wh, o, n, dq3, s8;
*/
while (1) {
      if (!(wh>0&&n<r4)) {
          break;
      }
      if (wh<=o) {
          s8 = wh;
      }
      else {
          s8 = o;
      }
      wh = wh - s8;
      o = o + 1;
      n += 1;
      dq3 = dq3 + s8;
  }
}