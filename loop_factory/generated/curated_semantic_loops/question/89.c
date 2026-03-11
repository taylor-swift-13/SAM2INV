int main1(int a,int n){
  int h, k, v, i;

  h=56;
  k=2;
  v=a;
  i=-3;

  /* >>> LOOP INVARIANT TO FILL <<< */

while (k+2<=h) {
      if (v+4<=h) {
          v = v+4;
      }
      else {
          v = h;
      }
  }
/*@
  assert !(k+2<=h) &&
         (a == \at(a, Pre));
*/

}
