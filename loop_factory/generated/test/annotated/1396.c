int main1(int t,int m){
  int x8, lr, p6, wril, k6gi, rrh;
  x8=(t%15)+10;
  lr=x8;
  p6=lr;
  wril=lr;
  k6gi=-4;
  rrh=8;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k6gi == 2*rrh - 20;
  loop invariant wril == lr + (rrh - 8)*(rrh - 8) - 5*(rrh - 8);
  loop invariant rrh >= 8;
  loop invariant lr == ((\at(t,Pre)) % 15) + 10;
  loop invariant x8 == ((\at(t, Pre) % 15) + 10);
  loop assigns p6, wril, t, k6gi, rrh;
*/
while (rrh<=x8) {
      p6 += wril;
      wril = wril + k6gi;
      t += lr;
      k6gi += 2;
      rrh += 1;
      t = t*2;
  }
}