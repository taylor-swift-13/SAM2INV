int main1(int a){
  int fw, w, p0, x;
  fw=36;
  w=0;
  p0=0;
  x=5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant x == 5 - w;
  loop invariant p0 == w * (11 - w) / 2;
  loop invariant w <= fw;
  loop assigns p0, w, x;
*/
while (1) {
      if (!(w<fw&&x>0)) {
          break;
      }
      p0 += x;
      w += 1;
      x--;
  }
}