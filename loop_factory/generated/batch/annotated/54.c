int main1(int a,int n){
  int b, v, i, f, r, s;

  b=a+13;
  v=0;
  i=3;
  f=-6;
  r=b;
  s=v;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant i == 3 + v;
  loop invariant v == 0 || v <= b;
  loop invariant v >= 0;
  loop invariant r == b;
  loop invariant v >= 1 ==> s == v + 2 + f + r;
  loop invariant a == \at(a, Pre) && n == \at(n, Pre);
  loop invariant b == a + 13;
  loop invariant i >= 3;

  loop invariant f == -6;
  loop invariant a == \at(a, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant (v == 0) ==> (s == 0);
  loop invariant (v > 0) ==> (s == i + a + 6);
  loop invariant i == v + 3;

  loop invariant (v == 0 && s == 0) || (v > 0 && s == i - 1 + f + r);
  loop assigns s, i, v;
*/
while (v<b) {
      s = i+f+r;
      i = i+1;
      v = v+1;
  }

}
