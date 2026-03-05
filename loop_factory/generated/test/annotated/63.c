int main1(int t,int u){
  int f, u0, mt;
  f=33;
  u0=0;
  mt=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant f == 33;
  loop invariant u0 == 0;
  loop invariant t == \at(t, Pre);
  loop invariant mt >= 1;
  loop invariant mt % 2 == 1;
  loop invariant (u - \at(u, Pre)) % (f - u0) == 0;
  loop invariant mt <= 2*f + 1;
  loop invariant u >= \at(u, Pre);
  loop assigns mt, u;
*/
while (mt<=f) {
      mt = mt + mt;
      mt = mt + 1;
      u = u+f-u0;
  }
}