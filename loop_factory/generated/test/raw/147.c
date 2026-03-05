int main1(int z,int u){
  int lm0;

  lm0=(u%18)+5;

  while (lm0>0) {
      lm0 = lm0+z*z;
      lm0 = lm0+u*u;
  }

}
