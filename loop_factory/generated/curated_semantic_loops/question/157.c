int main1(int m,int q){
  int d, f, v;

  d=m;
  f=d;
  v=q;

  /* >>> LOOP INVARIANT TO FILL <<< */

while (f-4>=0) {
      v = v+4;
      if ((f%7)==0) {
          v = v-v;
      }
      v = v+1;
  }
/*@
  assert !(f-4>=0) &&
         (d == m);
*/

}
