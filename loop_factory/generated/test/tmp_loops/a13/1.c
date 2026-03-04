int main1(int w,int z){
  int dxh, ibz;

  dxh=0;
  ibz=(z%15)+3;

  while (ibz!=0) {
      ibz -= 1;
      z += dxh;
  }

}
