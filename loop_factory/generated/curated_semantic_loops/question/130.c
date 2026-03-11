int main1(int b,int p){
  int c, k, v, y;

  c=(p%24)+17;
  k=0;
  v=k;
  y=p;

  /* >>> LOOP INVARIANT TO FILL <<< */

while (k+1<=c) {
      v = v+2;
      v = v*2;
      y = y+v;
  }
/*@
  assert !(k+1<=c) &&
         (v % 4 == 0);
*/

}
