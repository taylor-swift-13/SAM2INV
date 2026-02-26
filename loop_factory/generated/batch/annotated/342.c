int main1(int a,int n){
  int c, i, d, v;

  c=67;
  i=c;
  d=c;
  v=i;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant d >= 67;
  loop invariant (d == 67) ==> (v == 67);
  loop invariant (d > 67) ==> (v == d - 2);
  loop invariant i == 67;
  loop invariant a == \at(a, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant i >= 0;
  loop invariant v <= d;
  loop invariant c == 67;
  loop invariant (d - 67) % 3 == 0;
  loop invariant d >= i;
  loop invariant (d - i) % 3 == 0;
  loop invariant (d - v) % 2 == 0;
  loop invariant v >= i;
  loop assigns d, v;
*/
while (i>0) {
      v = d;
      d = d+2;
      d = d+1;
      v = v+1;
  }

}
