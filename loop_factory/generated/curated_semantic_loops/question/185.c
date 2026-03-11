int main1(int k,int p){
  int l, w, v;

  l=69;
  w=l;
  v=p;

  /* >>> LOOP INVARIANT TO FILL <<< */

while (w>3) {
      v = v*v;
      w = w-4;
  }
/*@
  assert !(w>3) &&
         ((69 - w) % 4 == 0);
*/

}
