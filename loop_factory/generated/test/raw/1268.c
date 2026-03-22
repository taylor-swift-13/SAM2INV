int main1(){
  int bl, roo, gfy, avjr, xbx, ry;

  bl=1;
  roo=0;
  gfy=roo;
  avjr=bl;
  xbx=1;
  ry=bl;

  while (gfy<=bl) {
      avjr = avjr*gfy;
      if (gfy<bl) {
          xbx = xbx*gfy;
      }
      gfy += 1;
      ry = ry+(xbx%2);
  }

}
