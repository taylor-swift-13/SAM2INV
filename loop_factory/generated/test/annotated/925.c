int main1(){
  int n1, la2, lh, bzg;
  n1=1-9;
  la2=1;
  lh=0;
  bzg=n1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant bzg == (lh + 1) * n1;
  loop invariant lh >= 0;
  loop invariant la2 >= 1;
  loop assigns bzg, la2, lh;
*/
while (1) {
      if (!(la2<=n1)) {
          break;
      }
      la2 = 2*la2;
      bzg = (n1)+(bzg);
      lh += 1;
  }
}