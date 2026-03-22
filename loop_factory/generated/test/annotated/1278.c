int main1(){
  int ts, y, uwr, zlb, prq;
  ts=(1%25)+17;
  y=0;
  uwr=10;
  zlb=1;
  prq=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant prq == y;
  loop invariant zlb == y + 1;
  loop invariant ts == (1 % 25) + 17;
  loop invariant 0 <= uwr <= 10;
  loop invariant 1 <= zlb <= ts+1;
  loop assigns prq, uwr, y, zlb;
*/
while (uwr>0&&zlb<=ts) {
      if (uwr>zlb) {
          uwr -= zlb;
      }
      else {
          uwr = 0;
      }
      y++;
      prq = prq + 1;
      zlb++;
  }
}