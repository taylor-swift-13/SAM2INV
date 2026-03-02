int main1(int k,int n){
  int p, c, v, y;

  p=k;
  c=0;
  v=k;
  y=-2;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k == \at(k, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant p == k;
  loop invariant v == k;
  loop invariant y % 2 == 0;
  loop invariant v == \at(k, Pre);
  loop invariant p == \at(k, Pre);
  loop invariant p == v;
  loop invariant k == \at(k, Pre) && n == \at(n, Pre) && p == k;
  loop assigns y;
*/
while (1) {
      y = y+v;
      y = y+y;
  }

}
