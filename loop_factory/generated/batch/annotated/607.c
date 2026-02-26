int main1(int a,int m){
  int l, u, v;

  l=(a%9)+17;
  u=1;
  v=a;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant u == 1;
  loop invariant 9 <= l <= 25;
  loop invariant 1 <= l/3;
  loop invariant l == (a % 9) + 17;
  loop invariant u >= 1;
  loop invariant u <= l/3 + 1;

  loop invariant a == \at(a, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant l == a % 9 + 17;
  loop invariant v % 2 == 0 || v == a;
  loop invariant l >= 9;
  loop invariant l <= 25;
  loop invariant u <= l/3;
  loop assigns v;
*/
while (u<=l/3) {
      v = v+4;
      v = v+v;
  }

}
