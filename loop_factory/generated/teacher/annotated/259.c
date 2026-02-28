int main1(int a,int n){
  int c, i, d, v;

  c=67;
  i=c;
  d=3;
  v=5;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i == 67;
  loop invariant c == 67;
  loop invariant a == \at(a, Pre) && n == \at(n, Pre) && d >= 3 && v >= 5 && (v == 5 ==> d == 3) && (v > 5 ==> (d % 2) == 0);
  loop invariant i == c;
  loop invariant a == \at(a, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant v >= 5;
  loop invariant d >= 3;
  loop invariant d >= 2*v - 7;
  loop invariant d >= v - 2;
  loop assigns d, v;
*/
while (i-2>=0) {
      d = d+1;
      v = v+1;
      d = d*2;
  }

}
