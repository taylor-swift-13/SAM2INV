int main1(int m){
  int u, x, v, s;

  u=36;
  x=0;
  v=u;
  s=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m == \at(m, Pre);
  loop invariant u == 36;
  loop invariant x >= 0;
  loop invariant x <= u;
  loop invariant 0 <= x;
  loop assigns x;
*/
while (x+1<=u) {
      x = x+1;
  }

}
