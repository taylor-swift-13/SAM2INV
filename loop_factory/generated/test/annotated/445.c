int main1(){
  int v9r, m, rc, es, uq, lv;
  v9r=1*5;
  m=0;
  rc=-1;
  es=v9r;
  uq=1+6;
  lv=1*3;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant es >= 0;
  loop invariant (rc == -1 ==> es == v9r) && (rc != -1 ==> es + rc == v9r + 1);
  loop invariant -1 <= rc;
  loop invariant rc <= v9r;
  loop invariant es >= 1;
  loop invariant uq >= 7;
  loop assigns es, rc, uq;
*/
while (1) {
      if (!(rc<v9r)) {
          break;
      }
      es = (v9r)+(-(rc));
      rc = rc + 1;
      uq += es;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m <= v9r;
  loop invariant rc == v9r - m;
  loop invariant lv == 3 + m*v9r - m*(m + 1)/2;
  loop invariant 0 <= m;
  loop assigns m, rc, lv;
*/
while (m<v9r) {
      m++;
      rc = v9r-m;
      lv = lv + rc;
  }
}