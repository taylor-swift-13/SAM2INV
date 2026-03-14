int main1(int a,int l){
  int g, j, o2, np, db3, qqw;
  g=l*3;
  j=0;
  o2=1;
  np=0;
  db3=10;
  qqw=l;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant np == (o2 - 1) * o2 * (2 * o2 - 1) / 6;
  loop invariant qqw == l + (o2 - 1) * j;
  loop invariant j == 0;
  loop invariant o2 >= 1;
  loop assigns np, o2, qqw;
*/
while (o2<=g) {
      np = np+o2*o2;
      o2 += 1;
      qqw += j;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant db3 == 10 + j*(j+1)/2;
  loop invariant qqw == l;
  loop invariant 0 <= j;
  loop assigns o2, j, db3;
*/
while (j<qqw) {
      o2 = qqw-j;
      j++;
      db3 += j;
  }
}