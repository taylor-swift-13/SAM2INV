int main1(){
  int ztt0, p6t, qj, u7h;
  ztt0=100;
  p6t=0;
  qj=1*2;
  u7h=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant qj == 2 - p6t;
  loop invariant u7h == p6t*(p6t + 1)/2;
  loop invariant p6t <= ztt0;
  loop invariant ztt0 == 100;
  loop invariant 0 <= p6t;
  loop assigns p6t, qj, u7h;
*/
while (p6t < ztt0) {
      qj--;
      p6t = p6t + 1;
      u7h += p6t;
  }
}