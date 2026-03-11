int main1(){
  int rh, ly8, ov, z0y;

  rh=64;
  ly8=0;
  ov=rh;
  z0y=13;

  while (ly8+6<=rh) {
      if (ly8<rh/2) {
          ov = ov + z0y;
      }
      else {
          ov++;
      }
      rh = (ly8+6)-1;
  }

}
