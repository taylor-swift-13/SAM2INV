int main1(int b,int p){
  int c, v, m;

  c=(p%6)+10;
  v=1;
  m=v;

  /* >>> LOOP INVARIANT TO FILL <<< */

while (v<=c/3) {
      v = v*3;
  }
/*@
  assert !(v<=c/3) &&
         (v >= 1);
*/

}
