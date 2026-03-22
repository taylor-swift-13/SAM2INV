int main1(){
  int u, pbt, ixn, wcby, lxd;

  u=1*5;
  pbt=1;
  ixn=pbt;
  wcby=0;
  lxd=u;

  while (pbt<=u-1) {
      wcby = wcby/2;
      ixn = ixn*2;
      lxd = lxd + ixn;
      pbt = u;
  }

}
