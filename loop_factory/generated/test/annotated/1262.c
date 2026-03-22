int main1(){
  int u, pbt, ixn, wcby, lxd;
  u=1*5;
  pbt=1;
  ixn=pbt;
  wcby=0;
  lxd=u;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant wcby == 0;
  loop invariant pbt <= u;
  loop invariant ixn >= 1;
  loop invariant lxd >= u;
  loop invariant lxd - 2*ixn == 3;
  loop invariant u == 5;
  loop assigns wcby, ixn, lxd, pbt;
*/
while (pbt<=u-1) {
      wcby = wcby/2;
      ixn = ixn*2;
      lxd = lxd + ixn;
      pbt = u;
  }
}