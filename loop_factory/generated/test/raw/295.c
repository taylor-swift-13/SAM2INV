int main1(int r){
  int wpus, vrqi, nehb;

  wpus=r-1;
  vrqi=0;
  nehb=1;

  while (vrqi<wpus) {
      if (nehb>=5) {
          nehb = -1;
      }
      if (nehb<=1) {
          nehb = 1;
      }
      nehb = nehb + nehb;
      vrqi = vrqi + 1;
      r = r + nehb;
  }

}
