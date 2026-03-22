int main1(){
  int uq, ysq, r2;
  uq=1;
  ysq=0;
  r2=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (ysq % 3) == ((3 - (r2 % 3)) % 3);
  loop invariant uq == 1;
  loop invariant 0 <= ysq <= 3;
  loop invariant 0 <= r2 <= uq;
  loop invariant (r2 == 0) <==> (ysq == 0);
  loop assigns r2, ysq;
*/
while (r2<=uq-1) {
      r2 += 1;
      ysq = (ysq+1)%3;
      ysq++;
  }
}