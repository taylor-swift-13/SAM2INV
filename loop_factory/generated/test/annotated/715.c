int main1(){
  int jnm, t, ot, u;
  jnm=1+14;
  t=(1%40)+2;
  ot=0;
  u=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant u == 0;
  loop invariant jnm == 15;
  loop invariant ot >= 0;
  loop invariant t == 3 || t == 4;
  loop invariant ot == 0 || ot == 3 || ot == 4;
  loop assigns ot, t, u;
*/
while (t!=ot) {
      ot = t;
      t = (t+jnm/t)/2;
      u = u+t-t;
  }
}