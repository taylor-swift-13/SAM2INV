int main1(int k,int n){
  int d, b, v;

  d=k;
  b=0;
  v=d;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant d == k;
  loop invariant k == \at(k, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant 0 <= b;

  loop invariant (b == 0) ==> (v == d);
  loop invariant d == k && b >= 0 && (b == 0 ==> v == d) && (v <= d || v <= 4);
  loop invariant d == \at(k, Pre);
  loop invariant b <= d || d < 0;
  loop invariant (b == 0 ==> v == \at(k, Pre)) && (b >= 1 ==> 0 <= v && v <= 4);
  loop assigns b, v;
*/
while (b+1<=d) {
      v = v%3;
      v = v*v;
      b = b+1;
  }

}
