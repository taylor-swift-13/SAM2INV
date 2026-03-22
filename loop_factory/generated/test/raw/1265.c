int main1(){
  int ct, n7, vnw, zsm, u;

  ct=1;
  n7=1;
  vnw=n7;
  zsm=ct;
  u=-1;

  while (n7<ct) {
      vnw = vnw*4;
      zsm = zsm/4;
      u = u+(zsm%2);
      n7 = ct;
  }

}
