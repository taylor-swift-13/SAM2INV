int main1(int a,int n){
  int r, u, v;

  r=68;
  u=0;
  v=4;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant u % 4 == 0;
  loop invariant u <= r;
  loop invariant r == 68;
  loop invariant 0 <= v;
  loop invariant v <= 25;
  loop invariant a == \at(a, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant 0 <= u;
  loop invariant v == 0 || v == 1 || v == 4 || v == 9 || v == 16 || v == 25;
  loop invariant u >= 0;
  loop assigns u, v;
*/
while (u+4<=r) {
      v = v%6;
      v = v*v;
      u = u+4;
  }

}
