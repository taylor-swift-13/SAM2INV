int main1(int n){
  int yd, lq3, fk, ny, y3l, gq, v;
  yd=(n%37)+7;
  lq3=0;
  fk=0;
  ny=(n%28)+10;
  y3l=20;
  gq=yd;
  v=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ny + (fk*(fk-1))/2 == (\at(n,Pre) % 28) + 10;
  loop invariant y3l == 20 + 2*fk;
  loop invariant ny == ((n % 28) + 10) - (fk*(fk-1))/2;
  loop assigns fk, gq, ny, y3l, v;
*/
while (ny>fk) {
      ny = ny - fk;
      y3l += 2;
      fk += 1;
      v = v + ny;
      gq = gq+(fk%2);
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant yd == (\at(n, Pre) % 37) + 7;
  loop invariant lq3 >= 0;
  loop assigns lq3, n, ny;
*/
while (1) {
      if (!(ny>lq3)) {
          break;
      }
      ny -= lq3;
      lq3 += 1;
      n = (lq3)+(n);
  }
}