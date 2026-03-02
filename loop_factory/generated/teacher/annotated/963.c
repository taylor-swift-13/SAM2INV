int main1(int b,int n){
  int i, r, v;

  i=n+19;
  r=i;
  v=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i == n + 19;
  loop invariant r <= i;

  loop invariant b == \at(b, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant i == \at(n, Pre) + 19;

  loop invariant i == \at(n, Pre) + 19 && b == \at(b, Pre) && r <= i;
  loop invariant i == \at(n,Pre) + 19;
  loop invariant n == \at(n,Pre);
  loop invariant b == \at(b,Pre);


  loop invariant i == n + 19 && r <= i;
  loop invariant b == \at(b, Pre) && n == \at(n, Pre);
  loop invariant (n == 0) ==> (v == 0);
  loop invariant (n != 0) ==> (v != 0);
  loop invariant i - r >= 0;
  loop invariant r <= \at(n, Pre) + 19;
  loop assigns v, r;
*/
while (r>=1) {
      v = v*2;
      r = r-1;
  }

}
