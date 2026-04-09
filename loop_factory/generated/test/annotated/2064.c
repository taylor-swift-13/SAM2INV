int main1(){
  int c2e, ly, l, dqs;
  c2e=(1%19)+16;
  ly=0;
  l=0;
  dqs=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= ly;
  loop invariant ly <= c2e;
  loop invariant l == (ly % 2);
  loop invariant dqs == (ly % 2);
  loop invariant (l == 0) || (l == 1);
  loop invariant (dqs == 0) || (dqs == 1);
  loop assigns ly, l, dqs;
*/
while (ly < c2e) {
      ly++;
      l = 1 - l;
      dqs = (1)+(-(dqs));
  }
}