int main1(int m,int n){
  int t, l, b;

  t=35;
  l=0;
  b=l;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b == 0;
  loop invariant l % 4 == 0;
  loop invariant 0 <= l && l <= t + 3;
  loop invariant m == \at(m,Pre);
  loop invariant n == \at(n,Pre);
  loop invariant l >= 0;
  loop invariant l <= t + 3;
  loop invariant t == 35;
  loop invariant (b == 0);
  loop invariant ((l % 4) == 0);
  loop invariant (l <= t + 4);
  loop invariant l <= t + 1;
  loop assigns b, l;
*/
while (l<t) {
      b = b-b;
      l = l+4;
  }

}
