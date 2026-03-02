int main1(int m,int p){
  int u, t, v;

  u=59;
  t=0;
  v=6;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant u == 59;
  loop invariant t == 0;
  loop invariant t <= u;
  loop invariant m == \at(m, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant (v == 0 || v == 1 || v == 6) && t == 0 && u == 59;
  loop invariant m == \at(m, Pre) && p == \at(p, Pre) && t <= u;
  loop invariant m == \at(m, Pre) && p == \at(p, Pre);

  loop invariant 0 <= t && t <= u;
  loop assigns v;
*/
while (t<=u-1) {
      v = v+3;
      v = v%2;
  }

}
