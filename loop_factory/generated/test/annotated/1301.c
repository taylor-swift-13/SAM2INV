int main1(){
  int j, p28, g1, y, rv1u, lka, i5bj;
  j=1;
  p28=j;
  g1=0;
  y=0;
  rv1u=0;
  lka=(1%18)+5;
  i5bj=p28;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant g1 == y;
  loop invariant rv1u == g1;
  loop invariant lka <= 6;
  loop invariant i5bj == 16 + (lka - lka*lka)/2;
  loop invariant lka >= 0;
  loop invariant i5bj == j + 6*g1 - g1*(g1+1)/2;
  loop invariant g1 + lka == 6;
  loop assigns g1, y, lka, rv1u, i5bj;
*/
while (1) {
      if (!(lka>=1)) {
          break;
      }
      g1 = g1+1*1;
      y = y+1*1;
      lka--;
      rv1u = rv1u+1*1;
      i5bj += lka;
  }
}