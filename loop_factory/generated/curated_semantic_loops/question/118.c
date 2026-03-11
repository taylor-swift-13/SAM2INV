int main1(int k,int m){
  int h, c, y, v;

  h=m;
  c=h+4;
  y=c;
  v=k;

  /* >>> LOOP INVARIANT TO FILL <<< */

while (c>h) {
      v = y;
      y = y+2;
  }
/*@
  assert !(c>h) &&
         (h == m);
*/

}
