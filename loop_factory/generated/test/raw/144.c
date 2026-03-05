int main1(int b){
  int sf, xz, k, gly, u17, vms, qzy;

  sf=(b%14)+17;
  xz=3;
  k=3;
  gly=3;
  u17=0;
  vms=8;
  qzy=0;

  while (xz<sf) {
      if (xz%3==0) {
          if (k>0) {
              k = k - 1;
              u17 += 1;
          }
      }
      else {
          if (k<vms) {
              k += 1;
              gly += 1;
          }
      }
      qzy += 1;
      xz += 1;
      vms = vms+(xz%2);
  }

}
