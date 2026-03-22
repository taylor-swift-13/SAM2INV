int main1(int r,int w){
  int lu, xve, ax;
  lu=18;
  xve=0;
  ax=5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ax == 5 + (xve/6) * (r+w);
  loop invariant xve % 6 == 0;
  loop invariant 0 <= xve <= lu;
  loop assigns ax, xve;
*/
while (1) {
      if (!(xve<lu)) {
          break;
      }
      ax = ax+r+w;
      xve += 6;
  }
}