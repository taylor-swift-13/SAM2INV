int main1(int b,int k){
  int l, v, r;

  l=16;
  v=0;
  r=b;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant l == 16;
  loop invariant b == \at(b, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant (r == \at(b, Pre)) || (r >= 0);
  loop invariant r >= \at(b, Pre);
  loop invariant r >= b;
  loop assigns r;
*/
while (1) {
      r = r+4;
      r = r*r;
  }

}
