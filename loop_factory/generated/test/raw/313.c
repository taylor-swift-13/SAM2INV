int main1(int i,int a){
  int erx, zi, hv0;

  erx=(i%22)+8;
  zi=erx;
  hv0=1;

  while (zi-1>=0) {
      if (hv0==1) {
          hv0 = 2;
      }
      else {
          if (hv0==2) {
              hv0 = 1;
          }
      }
      i += hv0;
      i = i + 3;
  }

}
