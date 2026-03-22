int main1(){
  int m, hn, hk, g5e;
  m=1+4;
  hn=(1%40)+2;
  hk=0;
  g5e=m;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant g5e - m >= hk % 2;
  loop invariant m == 5;
  loop invariant 1 <= hn <= m;
  loop invariant 0 <= hk <= m;
  loop invariant g5e >= m;
  loop assigns hk, g5e, hn;
*/
while (1) {
      if (!(hn!=hk)) {
          break;
      }
      hk = hn;
      g5e = g5e+(hk%2);
      hn = (hn+m/hn)/2;
  }
}