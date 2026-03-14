int main1(){
  int i, e1r, y, od, oy, kt;

  i=(1%39)+10;
  e1r=0;
  y=0;
  od=i;
  oy=0;
  kt=e1r;

  while (1) {
      if (!(y+1<=i)) {
          break;
      }
      if (oy<i) {
          od = y;
      }
      y++;
      oy += 2;
  }

  while (oy-4>=0) {
      kt = kt + i;
      oy++;
  }

}
