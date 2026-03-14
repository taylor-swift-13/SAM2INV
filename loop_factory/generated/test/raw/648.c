int main1(int b){
  int ew, om, y, wrx;

  ew=38;
  om=-4;
  y=0;
  wrx=om;

  while (y<ew) {
      y++;
      b += om;
      wrx = ew-y;
  }

  while (1) {
      if (!(y<=om-1)) {
          break;
      }
      y++;
  }

}
