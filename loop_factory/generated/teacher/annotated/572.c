int main1(int a,int k){
  int n, v, u;

  n=k;
  v=3;
  u=a;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant n == \at(k, Pre);
  loop invariant a == \at(a, Pre);
  loop invariant k == \at(k, Pre);
  loop invariant v >= 3;
  loop invariant n == k;
  loop invariant v >= 3 && (u == a || (0 <= u && u <= 16));
  loop assigns u, v;
*/
while (1) {
      u = u%5;
      u = u*u;
      v = v+1;
  }

}
