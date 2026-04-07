int main1(){
  int qjh, dlua, ha, gy, zx;

  qjh=1+8;
  dlua=0;
  ha=qjh;
  gy=qjh;
  zx=2;

  while (dlua < qjh) {
      dlua += 1;
      zx = dlua % 3;
      gy += zx;
      ha += zx;
  }

}
