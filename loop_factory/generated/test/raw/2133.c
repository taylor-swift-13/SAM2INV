int main1(int b){
  int pvt, y, w;

  pvt=b;
  y=0;
  w=0;

  while (1) {
      if (!(y<pvt)) {
          break;
      }
      if (!(!(y<pvt/2))) {
          w = w - 3;
      }
      else {
          w = w + 3;
      }
      y++;
      b += pvt;
  }

}
