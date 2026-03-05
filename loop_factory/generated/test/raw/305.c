int main1(int z){
  int rz, mb, nkyb;

  rz=z;
  mb=0;
  nkyb=0;

  while (mb<rz) {
      if (mb%2==0) {
          if (nkyb>0) {
              nkyb -= 1;
              nkyb++;
          }
      }
      else {
          if (nkyb>0) {
              nkyb -= 1;
              nkyb++;
          }
      }
      mb = mb + 1;
      z += rz;
  }

}
