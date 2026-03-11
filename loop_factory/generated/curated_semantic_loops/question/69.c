int main1(int b,int m){
  int a, i, v;

  a=m;
  i=a;
  v=a;

  /* >>> LOOP INVARIANT TO FILL <<< */

while (i>=2) {
      if (i+4<=v+a) {
          v = v+v;
      }
      else {
          v = v+i;
      }
      v = i;
      i = i-2;
  }
/*@
  assert !(i>=2) &&
         (m == \at(m, Pre));
*/

}
