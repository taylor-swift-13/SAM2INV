int main1(int n,int p){
  int m, r, v;

  m=n;
  r=3;
  v=4;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m == \at(n, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant 0 <= v && v <= 6;
  loop invariant n == \at(n, Pre) && p == \at(p, Pre);
  loop invariant 0 <= v && v < 7;
  loop invariant v == v % 7;
  loop invariant n == \at(n, Pre) && p == \at(p, Pre) && 0 <= v && v <= 6;
  loop assigns v;
*/
while (1) {
      v = v+3;
      v = v%7;
  }

}
