int main1(int j){
  int n, btt, ly, nl;
  n=73;
  btt=0;
  ly=0;
  nl=n;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ly == btt;
  loop invariant nl == n - btt;
  loop invariant btt <= n;
  loop assigns btt, ly, nl;
*/
while (btt < n) {
      ly++;
      nl = (nl)+(-(1));
      btt = btt + 1;
  }
}