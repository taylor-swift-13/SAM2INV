int main1(int n,int q){
  int r, w, p;

  r=n-7;
  w=r+4;
  p=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant n == \at(n, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant r == \at(n, Pre) - 7;
  loop invariant w > 0 ==> w <= \at(n, Pre) - 3;
  loop invariant w <= \at(n, Pre) - 3;

  loop invariant w <= r + 4;
  loop assigns w;
*/
while (w>0) {
      w = w/2;
  }

}
