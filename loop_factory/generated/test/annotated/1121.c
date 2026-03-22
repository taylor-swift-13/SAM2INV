int main1(int a,int y){
  int o, bsu, j, ts, oc;
  o=9;
  bsu=o;
  j=0;
  ts=0;
  oc=a;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j == 2 * (bsu - 9);
  loop invariant ts == (bsu - 9) * (bsu - 10);
  loop invariant bsu >= 9;
  loop invariant 4*ts == j*(j - 2);
  loop invariant j >= 0;
  loop assigns ts, j, bsu;
*/
while (bsu-2>=0) {
      ts += j;
      j += 2;
      bsu = bsu + 1;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant oc == a;
  loop invariant ts >= 0;
  loop invariant bsu <= oc;
  loop invariant 0 <= j;
  loop assigns o, bsu, ts;
*/
while (bsu<oc) {
      o = o + a;
      bsu = bsu + 1;
      ts += j;
  }
}