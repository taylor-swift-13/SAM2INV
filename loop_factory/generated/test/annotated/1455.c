int main1(){
  int me, m, w, ngqg;
  me=1;
  m=0;
  w=-6;
  ngqg=me;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ngqg == me;
  loop invariant 0 <= m <= me;
  loop invariant w == -6 + m * (ngqg + 1);
  loop assigns m, w;
*/
while (1) {
      if (!(m < me)) {
          break;
      }
      w = w + ngqg;
      m++;
      w += 1;
  }
}