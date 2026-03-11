int main1(int x,int n){
  int w98, kdsi, d4j, qij;
  w98=n;
  kdsi=0;
  d4j=1;
  qij=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (qij == 1 || qij == -1);
  loop invariant ((d4j + kdsi) % 2 == 1);
  loop invariant w98 == \at(n, Pre);
  loop invariant 1 <= d4j;
  loop invariant d4j <= 6;
  loop invariant kdsi >= 0 && (w98 <= 0 || kdsi <= w98);
  loop invariant d4j <= 1 + kdsi;
  loop assigns kdsi, d4j, qij;
*/
while (kdsi<w98) {
      if (!(d4j<6)) {
          qij = -1;
      }
      if (d4j<=1) {
          qij = 1;
      }
      kdsi++;
      d4j += qij;
  }
}