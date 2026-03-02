int main1(int k,int n){
  int d, b, v;

  d=k;
  b=0;
  v=d;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b >= 0;
  loop invariant (b == 0) ==> (v == d);
  loop invariant (b > 0) ==> (v == d % 3);
  loop invariant d == k && k == \at(k,Pre) && n == \at(n,Pre);
  loop invariant (b == 0) ==> (v == k);
  loop invariant (b > 0) ==> (v == k % 3);
  loop invariant d == k;
  loop invariant k == \at(k, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant b >= 0 && (v == k || v == k % 3) && (k == \at(k,Pre));
  loop invariant v == k % 3 || b == 0;
  loop invariant d == k && (v - d) % 3 == 0;
  loop invariant b >= 0 && k == \at(k, Pre) && n == \at(n, Pre);
  loop invariant (b != 0) ==> (v == k % 3);
  loop invariant (v == k) || (v == k % 3);
  loop assigns b, v;
*/
while (1) {
      v = v%3;
      b = b+1;
  }

}
