int main1(int k,int v){
  int fp, rz, zsg;

  fp=26;
  rz=0;
  zsg=1;

  while (rz<fp) {
      if (zsg>=7) {
          zsg = -1;
      }
      if (zsg<=1) {
          zsg = 1;
      }
      zsg += zsg;
      rz += 1;
      k += zsg;
  }

}
