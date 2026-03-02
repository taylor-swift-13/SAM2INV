int main1(int a,int m){
  int s, k, v;

  s=23;
  k=1;
  v=a;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant s == 23 && a == \at(a, Pre) && m == \at(m, Pre);
  loop invariant k <= s && k >= 1;
  loop invariant s == 23;
  loop invariant a == \at(a, Pre) && m == \at(m, Pre) && 1 <= k <= s;
  loop invariant a == \at(a, Pre);
  loop invariant m == \at(m, Pre);

  loop invariant k <= s;
  loop invariant k >= 1;
  loop invariant k <= s && (k == 1 || k == 2 || k == 4 || k == 8 || k == 16);
  loop invariant (k == 1) || (k == 2) || (k == 4) || (k == 8) || (k == 16);
  loop invariant k > 0;

  loop assigns k;
*/
while (k*2<=s) {
      k = k*2;
  }

}
