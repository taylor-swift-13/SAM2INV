int main1(int k,int p){
  int b, w, v, e;

  b=(k%33)+7;
  w=b+3;
  v=b;
  e=-4;

  /* >>> LOOP INVARIANT TO FILL <<< */

while (w>b) {
      v = v+w;
      w = w-2;
  }
/*@
  assert !(w>b) &&
         (b == \at(k, Pre) % 33 + 7);
*/

}
