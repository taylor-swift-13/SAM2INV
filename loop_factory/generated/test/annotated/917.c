int main1(){
  int fe2y, t, p, p6, fjd;
  fe2y=1*5;
  t=0;
  p=0;
  p6=fe2y;
  fjd=3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t == p % 3;
  loop invariant p6 == fe2y + p;
  loop invariant fjd == 3 + p*(p + 1)/2;
  loop invariant 0 <= p <= fe2y;
  loop assigns p, t, p6, fjd;
*/
while (1) {
      if (!(p<=fe2y-1)) {
          break;
      }
      p++;
      t = (t+1)%3;
      p6++;
      fjd += p;
  }
}