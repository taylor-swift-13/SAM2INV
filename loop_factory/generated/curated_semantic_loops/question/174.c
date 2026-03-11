int main1(int b,int m){
  int z, t, v;

  z=(b%20)+10;
  t=1;
  v=z;

  /* >>> LOOP INVARIANT TO FILL <<< */

while (t*3<=z) {
      v = v*2;
      v = v*v;
      t = t*3;
  }
/*@
  assert !(t*3<=z) &&
         (v >= z);
*/

}
