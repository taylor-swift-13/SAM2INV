int main1(int a,int n){
  int m, v, w, x;

  m=(a%11)+14;
  v=m;
  w=-2;
  x=2;

  /* >>> LOOP INVARIANT TO FILL <<< */

while (v>=1) {
      w = w*4;
      v = v-1;
  }
/*@
  assert !(v>=1) &&
         (v <= m);
*/

}
