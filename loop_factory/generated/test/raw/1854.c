int main1(int z,int s){
  int uvz, f, p4, ys8, h, w6w, qq, ps;

  uvz=s;
  f=0;
  p4=0;
  ys8=0;
  h=0;
  w6w=0;
  qq=0;
  ps=0;

  while (f<=uvz-1) {
      if (!(!(f%8==0))) {
          if (f%6==0) {
              ys8++;
              qq += 2;
          }
          else {
              if (f%4==0) {
                  h += 1;
                  qq = qq + 3;
              }
              else {
                  if (1) {
                      w6w++;
                      qq += 4;
                  }
              }
          }
      }
      else {
          p4 += 1;
          qq++;
      }
      f = f + 1;
      ps = ps+f%6;
      s = s + uvz;
      s = s + s;
  }

}
