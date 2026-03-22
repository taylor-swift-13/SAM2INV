int main1(int i,int s){
  int ks, c, t, t6, yn;
  ks=10;
  c=2;
  t=0;
  t6=(i%28)+10;
  yn=c;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t6 == ((\at(i,Pre) % 28) + 10) - t*(t-1)/2;
  loop invariant yn == c + (ks - c) * t;
  loop invariant t >= 0;
  loop invariant t6 == (i % 28) + 10 - t * (t - 1) / 2;
  loop invariant t6 + t*(t-1)/2 == (i % 28) + 10;
  loop invariant yn == c + 8 * t;
  loop assigns t6, yn, t;
*/
while (1) {
      if (!(t6>t)) {
          break;
      }
      t6 -= t;
      yn = (ks-c)+(yn);
      t += 1;
  }
}